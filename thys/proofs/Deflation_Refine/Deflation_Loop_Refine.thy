theory Deflation_Loop_Refine
  imports
    "IsaRRI_LLVM.Hybrid_Solver_Pipeline"
    "IsaRRI_Refine.Hybrid_Keystone"
    "IsaRRI_Refine.Deflation_Recursion"
    "IsaRRI_Refine.Deflation_Bridge"
    "IsaRRI_Refine.Stack_Bound"
begin

text \<open>\<^bold>\<open>No parameter is named \<open>init\<close> in this theory.\<close> \<open>init\<close> parses as an existing constant whose type
  involves \<open>'a::llvm_rep list\<close>, so a definition using it as a bound variable is rejected with
  \<open>No type arity list :: llvm_rep\<close>.\<close>


text \<open>The deflating loop's simulation invariant. It replaces only the abstraction slot of
  \<open>hybrid_state_invar\<close>; the coupling, budget, cap and payload clauses carry over by type.

  Per remaining worklist node \<open>(l, r, k, Q)\<close>:
  \<^enum> \<open>defl_invar P0 Q a b\<close> for the node's dyadic box (\<open>Q dvd P0\<close>, same interior roots), which licenses reading the
    node's abstract count off \<open>Q\<close> and its soundness off \<open>P0\<close>;
  \<^enum> coverage: every root of \<open>P0\<close> in the root box lies in some accumulated interval, in some pending box, or is an
    endpoint root a pending node will shed (a per-root existential, not a multiset equality of intervals);
  \<^enum> soundness: every accumulated triple satisfies \<open>dsc_pair_ok P0\<close>, inherited node-locally from
    @{thm [source] newdsc_pol_defl_sound}.

  At exit (empty worklist), (2) collapses to conjunct 4 of the target SPEC and (3) is conjunct 3; conjuncts 1--2 come
  from the shared plumbing.\<close>

text \<open>\<^bold>\<open>The concrete-level divisor relation\<close>: a node's polynomial divides its
  carried init and agrees on interior roots of the node's dyadic box. This is what replaces
  \<open>node_frame\<close> in the coupling -- the shed roots sit at box ENDPOINTS
  (\<open>Deflation_Bridge.defl_children_roots_in_box\<close>), which is exactly why the interior-root
  clause survives the shed.\<close>

definition defl_node_rel :: "int list \<Rightarrow> int list \<Rightarrow> bool" where
  \<comment> \<open>\<^bold>\<open>Two rings, one frame.\<close> The divisibility is stated in \<open>\<int>[x]\<close>, because that is what the kernel produces:
     in the local frame the divisor \<open>1 - 2x\<close> is primitive, so by Gauss's lemma the synthetic division stays integral.
     The root agreement is over \<open>\<real>\<close>, the ring of the abstract recursion; \<open>Poly ini\<close> is an \<open>int poly\<close>, so it is mapped
     before being evaluated at a real point.

     \<^bold>\<open>The relation is local.\<close> \<open>carried_init_same_den\<close> and its \<open>carried_left\<close>/\<open>carried_right\<close> children are polynomials
     in the node's own local variable, which ranges over \<open>(0, 1)\<close> whatever the box, so they are compared on \<open>(0, 1)\<close>
     rather than on the node's global box. This is also the right notion: the Descartes count is taken over the local
     \<open>(0, 1)\<close>, so ``same roots in \<open>(0, 1)\<close>'' is what licenses reading the count off the deflated polynomial. The box
     parameters do not appear.\<close>
  "defl_node_rel ini q \<longleftrightarrow>
     Poly q dvd Poly ini
     \<and> (\<forall>t::real. 0 < t \<longrightarrow> t < 1 \<longrightarrow>
          (poly (map_poly real_of_int (Poly ini)) t = 0)
            = (poly (map_poly real_of_int (Poly q)) t = 0))"

lemma defl_node_rel_refl: "defl_node_rel xs xs"
  unfolding defl_node_rel_def by (auto intro: dvd_refl)

lemma defl_node_relD_dvd: "defl_node_rel ini q \<Longrightarrow> Poly q dvd Poly ini"
  unfolding defl_node_rel_def by simp

lemma defl_node_relD_roots:
  "defl_node_rel ini q \<Longrightarrow> 0 < t \<Longrightarrow> t < 1 \<Longrightarrow>
     (poly (map_poly real_of_int (Poly ini)) t = 0)
       = (poly (map_poly real_of_int (Poly q)) t = 0)"
  unfolding defl_node_rel_def by simp

section \<open>What the two child maps do to polynomial values\<close>

text \<open>\<open>Deflation_Bridge\<close> relates a fired child to its own parent (@{thm [source] defl_left_child_exact} and related
  lemmas), which the child-build contract uses. The coupling needs something different: it ties every node to the
  init recomputed from the root, so the split step pushes @{const defl_node_rel} through
  @{const carried_left}/@{const carried_right}, which requires knowing what those maps do to a polynomial's values.

  Both maps are dilations. @{const carried_left} multiplies coefficient \<open>i\<close> by \<open>2\<^sup>(\<^sup>n\<^sup>-\<^sup>1\<^sup>-\<^sup>i\<^sup>)\<close>
  (@{thm [source] defl_carried_left_nth}), which is \<open>2\<^sup>(\<^sup>n\<^sup>-\<^sup>1\<^sup>) \<cdot> P(t/2)\<close>; @{const carried_right} is \<open>taylor_shift_list 1\<close> of that,
  the same thing at \<open>(t+1)/2\<close>. The two half-boxes of the local \<open>(0,1)\<close>, \<open>(0,1/2)\<close> and \<open>(1/2,1)\<close>, are the images of \<open>(0,1)\<close>
  under \<open>t \<mapsto> t/2\<close> and \<open>t \<mapsto> (t+1)/2\<close>, which is why the root clause of @{const defl_node_rel} survives both maps.

  \<^bold>\<open>The scalar \<open>2\<^sup>(\<^sup>n\<^sup>-\<^sup>1\<^sup>)\<close> is kept explicit.\<close> It depends on the length of the map's own input, so it does not cancel between
  a node and a shorter divisor of it. It is harmless here, since it is a nonzero constant and both uses below are about
  vanishing, but it is why the divisibility half of the congruence is a separate argument.\<close>

lemma defl_poly_of_int_Poly_sum:
  fixes t :: real
  shows "poly (of_int_poly (Poly xs) :: real poly) t
       = (\<Sum>i<length xs. real_of_int (xs ! i) * t ^ i)"
proof (induction xs)
  case Nil show ?case by simp
next
  case (Cons a xs)
  have "(\<Sum>i<length (a # xs). real_of_int ((a # xs) ! i) * t ^ i)
      = real_of_int a + (\<Sum>i<length xs. real_of_int (xs ! i) * t ^ Suc i)"
    \<comment> \<open>\<open>del: sum.lessThan_Suc\<close> is the point: that rule is \<open>[simp]\<close> and peels the TOP index
       off, giving \<open>(\<Sum>i<n. \<dots>) + f n\<close> -- the opposite end from the one the \<open>Poly\<close> recursion
       needs. With it deleted the SHIFT rule fires and peels index \<open>0\<close>.\<close>
    by (simp add: sum.lessThan_Suc_shift del: sum.lessThan_Suc)
  also have "\<dots> = real_of_int a + t * (\<Sum>i<length xs. real_of_int (xs ! i) * t ^ i)"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = poly (of_int_poly (Poly (a # xs)) :: real poly) t"
    using Cons by (simp add: of_int_hom.map_poly_pCons_hom)
  finally show ?case by simp
qed

lemma defl_pow_half_shift:
  assumes i: "i < n"
  shows "(2::real) ^ (n - 1) * (1 / 2) ^ i = 2 ^ (n - Suc i)"
proof -
  have "(2::real) ^ (n - 1) * (1 / 2) ^ i = 2 ^ (n - 1) / 2 ^ i"
    by (simp add: power_one_over)
  also have "\<dots> = 2 ^ (n - 1 - i)" using i by (simp add: power_diff)
  finally show ?thesis using i by simp
qed

lemma defl_poly_carried_left:
  fixes t :: real
  shows "poly (of_int_poly (Poly (carried_left xs)) :: real poly) t
       = 2 ^ (length xs - 1) * poly (of_int_poly (Poly xs) :: real poly) (t / 2)"
proof -
  have "poly (of_int_poly (Poly (carried_left xs)) :: real poly) t
      = (\<Sum>i<length xs. real_of_int (carried_left xs ! i) * t ^ i)"
    using defl_poly_of_int_Poly_sum[of "carried_left xs" t] by simp
  also have "\<dots> = (\<Sum>i<length xs.
                     2 ^ (length xs - 1) * (real_of_int (xs ! i) * (t / 2) ^ i))"
  proof (rule sum.cong[OF refl])
    fix i assume "i \<in> {..<length xs}"
    hence i: "i < length xs" by simp
    have "real_of_int (carried_left xs ! i) * t ^ i
        = real_of_int (xs ! i) * 2 ^ (length xs - Suc i) * t ^ i"
      by (simp add: defl_carried_left_nth[OF i])
    also have "\<dots> = 2 ^ (length xs - 1) * (real_of_int (xs ! i) * ((1 / 2) ^ i * t ^ i))"
      using defl_pow_half_shift[OF i] by (simp add: algebra_simps)
    finally show "real_of_int (carried_left xs ! i) * t ^ i
        = 2 ^ (length xs - 1) * (real_of_int (xs ! i) * (t / 2) ^ i)"
      by (simp add: power_divide power_one_over)
  qed
  also have "\<dots> = 2 ^ (length xs - 1)
                    * (\<Sum>i<length xs. real_of_int (xs ! i) * (t / 2) ^ i)"
    by (simp add: sum_distrib_left)
  also have "\<dots> = 2 ^ (length xs - 1) * poly (of_int_poly (Poly xs) :: real poly) (t / 2)"
    using defl_poly_of_int_Poly_sum[of xs "t / 2"] by simp
  finally show ?thesis .
qed

lemma defl_poly_carried_right:
  fixes t :: real
  shows "poly (of_int_poly (Poly (carried_right xs)) :: real poly) t
       = 2 ^ (length xs - 1) * poly (of_int_poly (Poly xs) :: real poly) ((t + 1) / 2)"
proof -
  have "poly (of_int_poly (Poly (carried_right xs)) :: real poly) t
      = poly (of_int_poly (pcompose (Poly (carried_left xs)) [:1, 1:]) :: real poly) t"
    by (simp add: carried_right_def Poly_taylor_shift_list)
  also have "\<dots> = poly (of_int_poly (Poly (carried_left xs)) :: real poly) (1 + t)"
    by (simp add: of_int_hom.map_poly_pcompose poly_pcompose)
  also have "\<dots> = 2 ^ (length xs - 1)
                    * poly (of_int_poly (Poly xs) :: real poly) ((1 + t) / 2)"
    by (rule defl_poly_carried_left)
  finally show ?thesis by (simp add: add.commute)
qed

text \<open>\<^bold>\<open>The ROOT half of the congruence\<close>, which is the half the reject and accept arms consume.
  \<open>t \<mapsto> t/2\<close> maps the local \<open>(0,1)\<close> INTO \<open>(0,1)\<close>, and so does \<open>t \<mapsto> (t+1)/2\<close> -- so the root
  agreement @{const defl_node_rel} asserts on the parent's \<open>(0,1)\<close> is available at exactly the
  points the children's \<open>(0,1)\<close> asks about, with room to spare. The nonzero scalar drops out
  because both sides are statements about VANISHING.\<close>

lemma defl_node_rel_roots_carried_left:
  assumes rel: "defl_node_rel A B" and t0: "0 < t" and t1: "t < 1"
  shows "(poly (of_int_poly (Poly (carried_left A)) :: real poly) t = 0)
       = (poly (of_int_poly (Poly (carried_left B)) :: real poly) t = 0)"
proof -
  have h0: "0 < t / 2" using t0 by simp
  have h1: "t / 2 < 1" using t1 by simp
  have "(poly (of_int_poly (Poly (carried_left A)) :: real poly) t = 0)
      = (poly (of_int_poly (Poly A) :: real poly) (t / 2) = 0)"
    by (simp add: defl_poly_carried_left)
  also have "\<dots> = (poly (of_int_poly (Poly B) :: real poly) (t / 2) = 0)"
    by (rule defl_node_relD_roots[OF rel h0 h1])
  also have "\<dots> = (poly (of_int_poly (Poly (carried_left B)) :: real poly) t = 0)"
    by (simp add: defl_poly_carried_left)
  finally show ?thesis .
qed

lemma defl_node_rel_roots_carried_right:
  assumes rel: "defl_node_rel A B" and t0: "0 < t" and t1: "t < 1"
  shows "(poly (of_int_poly (Poly (carried_right A)) :: real poly) t = 0)
       = (poly (of_int_poly (Poly (carried_right B)) :: real poly) t = 0)"
proof -
  have h0: "0 < (t + 1) / 2" using t0 by simp
  have h1: "(t + 1) / 2 < 1" using t1 by simp
  have "(poly (of_int_poly (Poly (carried_right A)) :: real poly) t = 0)
      = (poly (of_int_poly (Poly A) :: real poly) ((t + 1) / 2) = 0)"
    by (simp add: defl_poly_carried_right)
  also have "\<dots> = (poly (of_int_poly (Poly B) :: real poly) ((t + 1) / 2) = 0)"
    by (rule defl_node_relD_roots[OF rel h0 h1])
  also have "\<dots> = (poly (of_int_poly (Poly (carried_right B)) :: real poly) t = 0)"
    by (simp add: defl_poly_carried_right)
  finally show ?thesis .
qed



lemma defl_of_int_poly_via_rat:
  fixes p :: "int poly"
  shows "(of_int_poly p :: real poly) = map_poly real_of_rat (map_poly rat_of_int p)"
  by (simp add: map_poly_map_poly o_def)


section \<open>Divisibility through the child maps, over \<open>\<real>\<close>\<close>

text \<open>Over \<open>\<int>[x]\<close>, the cofactor of @{const carried_left} is integral only under a canonicity clause. The smallness
  lemma used for the width bound (@{thm [source] Bernstein_changes_small_interval_le_1_of_dvd}) is over \<open>real poly\<close>, where
  the scalar \<open>2\<^sup>(\<^sup>n\<^sup>-\<^sup>1\<^sup>)\<close> is a unit, and there both maps carry \<open>dvd\<close> with no canonicity clause: the cofactor is
  \<open>smult (2\<^sup>(\<^sup>n\<^sup>A\<^sup>-\<^sup>1\<^sup>)/2\<^sup>(\<^sup>n\<^sup>X\<^sup>-\<^sup>1\<^sup>)) (C \<circ> h)\<close>, and over a field that scalar is a unit whatever the two lengths are.

  \<^bold>\<open>Why this is needed.\<close> The \<open>wide\<close> premise of \<open>defl_body_step\<close> (\<open>\<delta> < b - a\<close> at the popped node) is derived from the
  count, not from the invariant: @{const hybrid_cap_invar} yields @{thm [source] hybrid_cap_invar_nondeg} and a depth
  budget, but no lower bound on the box by \<open>\<delta>\<close>. The non-deflating stack takes it from \<open>small_fast\<close> and \<open>2 \<le> count\<close> on the
  branches that push. Here the count belongs to the node's possibly deflated exact object, and the bound that covers
  those, @{thm [source] Bernstein_changes_small_interval_le_1_of_dvd} (the engine of
  @{thm [source] defl_chain_smallness_uniform}), is indexed by \<open>dvd\<close>. These four lemmas carry that index.\<close>

lemma defl_carried_left_real_pcompose:
  "(of_int_poly (Poly (carried_left xs)) :: real poly)
     = smult (2 ^ (length xs - 1)) (of_int_poly (Poly xs) \<circ>\<^sub>p [:0, 1/2:])"
proof (rule poly_eq_poly_eq_iff[THEN iffD1], rule ext)
  fix t :: real
  show "poly (of_int_poly (Poly (carried_left xs)) :: real poly) t
      = poly (smult (2 ^ (length xs - 1))
                (of_int_poly (Poly xs) \<circ>\<^sub>p [:0, 1/2:]) :: real poly) t"
    by (simp add: defl_poly_carried_left poly_pcompose)
qed

lemma defl_carried_right_real_pcompose:
  "(of_int_poly (Poly (carried_right xs)) :: real poly)
     = smult (2 ^ (length xs - 1)) (of_int_poly (Poly xs) \<circ>\<^sub>p [:1/2, 1/2:])"
proof (rule poly_eq_poly_eq_iff[THEN iffD1], rule ext)
  fix t :: real
  show "poly (of_int_poly (Poly (carried_right xs)) :: real poly) t
      = poly (smult (2 ^ (length xs - 1))
                (of_int_poly (Poly xs) \<circ>\<^sub>p [:1/2, 1/2:]) :: real poly) t"
    by (simp add: defl_poly_carried_right poly_pcompose add_divide_distrib add.commute)
qed

lemma defl_carried_left_dvd_real:
  assumes d: "(of_int_poly (Poly X) :: real poly) dvd (of_int_poly (Poly A) :: real poly)"
  shows "(of_int_poly (Poly (carried_left X)) :: real poly)
           dvd (of_int_poly (Poly (carried_left A)) :: real poly)"
proof -
  obtain C where C: "(of_int_poly (Poly A) :: real poly) = of_int_poly (Poly X) * C"
    using d ..
  have "(of_int_poly (Poly (carried_left A)) :: real poly)
      = smult (2 ^ (length A - 1))
          ((of_int_poly (Poly X) \<circ>\<^sub>p [:0, 1/2:]) * (C \<circ>\<^sub>p [:0, 1/2:]))"
    by (simp add: defl_carried_left_real_pcompose C pcompose_mult)
  also have "\<dots> = (of_int_poly (Poly (carried_left X)) :: real poly)
                   * smult (2 ^ (length A - 1) / 2 ^ (length X - 1)) (C \<circ>\<^sub>p [:0, 1/2:])"
    by (simp add: defl_carried_left_real_pcompose mult_smult_left mult_smult_right
                  smult_smult)
  finally show ?thesis ..
qed

lemma defl_carried_right_dvd_real:
  assumes d: "(of_int_poly (Poly X) :: real poly) dvd (of_int_poly (Poly A) :: real poly)"
  shows "(of_int_poly (Poly (carried_right X)) :: real poly)
           dvd (of_int_poly (Poly (carried_right A)) :: real poly)"
proof -
  obtain C where C: "(of_int_poly (Poly A) :: real poly) = of_int_poly (Poly X) * C"
    using d ..
  have "(of_int_poly (Poly (carried_right A)) :: real poly)
      = smult (2 ^ (length A - 1))
          ((of_int_poly (Poly X) \<circ>\<^sub>p [:1/2, 1/2:]) * (C \<circ>\<^sub>p [:1/2, 1/2:]))"
    by (simp add: defl_carried_right_real_pcompose C pcompose_mult)
  also have "\<dots> = (of_int_poly (Poly (carried_right X)) :: real poly)
                   * smult (2 ^ (length A - 1) / 2 ^ (length X - 1)) (C \<circ>\<^sub>p [:1/2, 1/2:])"
    by (simp add: defl_carried_right_real_pcompose mult_smult_left mult_smult_right
                  smult_smult)
  finally show ?thesis ..
qed


section \<open>The general child map, and the deflation step\<close>

text \<open>@{thm [source] newton_wcand_def} is \<open>carried_init_same_den m (2 ^ (2 ^ e + 2)) (m + 4) Q\<close>,
  so one lemma about that operator covers the WINDOW child and the SEED as well as the two
  split children (@{thm [source] carried_init_same_den_zero_one} makes \<open>carried_left\<close> a special
  case). @{thm [source] cdlr_Poly_carried_init_same_den_int} is the polynomial identity over
  \<open>\<rat>\<close>; this maps it to \<open>\<real>\<close>, where the \<open>d\<^sup>(\<^sup>n\<^sup>-\<^sup>1\<^sup>)\<close> scalar is a unit.\<close>

lemma defl_cisd_real_pcompose:
  fixes d :: int
  assumes d0: "d \<noteq> 0"
  shows "(of_int_poly (Poly (carried_init_same_den l d r xs)) :: real poly)
       = smult (real_of_int d ^ (length xs - 1))
           (of_int_poly (Poly xs)
              \<circ>\<^sub>p [: real_of_int l / real_of_int d,
                     (real_of_int r - real_of_int l) / real_of_int d :])"
proof -
  have "(of_int_poly (Poly (carried_init_same_den l d r xs)) :: real poly)
      = map_poly real_of_rat (map_poly rat_of_int (Poly (carried_init_same_den l d r xs)))"
    by (rule defl_of_int_poly_via_rat)
  also have "\<dots> = map_poly real_of_rat
        (smult ((rat_of_int d) ^ (length xs - 1))
           (pcompose (map_poly rat_of_int (Poly xs))
             [: rat_of_int l / rat_of_int d, (rat_of_int r - rat_of_int l) / rat_of_int d :]))"
    by (simp only: cdlr_Poly_carried_init_same_den_int[OF d0])
  also have "\<dots> = smult (real_of_int d ^ (length xs - 1))
           (of_int_poly (Poly xs)
              \<circ>\<^sub>p [: real_of_int l / real_of_int d,
                     (real_of_int r - real_of_int l) / real_of_int d :])"
    \<comment> \<open>\<open>map_poly_smult\<close> is a PLAIN name with two hom side conditions, not a member of the
       \<open>of_rat_hom\<close> locale --- \<open>of_rat_hom.map_poly_smult\<close> does not exist.\<close>
    by (simp add: of_rat_hom.map_poly_pcompose map_poly_smult
                  defl_of_int_poly_via_rat[symmetric]
                  of_rat_divide of_rat_diff of_rat_power of_rat_mult
                  of_rat_hom.map_poly_pCons_hom of_rat_of_int_eq)
  finally show ?thesis .
qed

lemma defl_cisd_dvd_real:
  fixes d :: int
  assumes d0: "d \<noteq> 0"
    and dvd: "(of_int_poly (Poly X) :: real poly) dvd (of_int_poly (Poly A) :: real poly)"
  shows "(of_int_poly (Poly (carried_init_same_den l d r X)) :: real poly)
           dvd (of_int_poly (Poly (carried_init_same_den l d r A)) :: real poly)"
proof -
  obtain C where C: "(of_int_poly (Poly A) :: real poly) = of_int_poly (Poly X) * C"
    using dvd ..
  have dnz: "real_of_int d \<noteq> 0" using d0 by simp
  have "(of_int_poly (Poly (carried_init_same_den l d r A)) :: real poly)
      = smult (real_of_int d ^ (length A - 1))
          ((of_int_poly (Poly X) \<circ>\<^sub>p [: real_of_int l / real_of_int d,
                                     (real_of_int r - real_of_int l) / real_of_int d :])
           * (C \<circ>\<^sub>p [: real_of_int l / real_of_int d,
                     (real_of_int r - real_of_int l) / real_of_int d :]))"
    by (simp add: defl_cisd_real_pcompose[OF d0] C pcompose_mult)
  also have "\<dots> = (of_int_poly (Poly (carried_init_same_den l d r X)) :: real poly)
        * smult (real_of_int d ^ (length A - 1) / real_of_int d ^ (length X - 1))
            (C \<circ>\<^sub>p [: real_of_int l / real_of_int d,
                    (real_of_int r - real_of_int l) / real_of_int d :])"
    by (simp add: defl_cisd_real_pcompose[OF d0] mult_smult_left mult_smult_right
                  smult_smult dnz d0)
  finally show ?thesis ..
qed

text \<open>\<^bold>\<open>And the DEFLATION step itself\<close>, which is the easy direction: the kernel's exactness
  identities already say the shed polynomial is a factor, and \<open>of_int_poly\<close> is a ring
  homomorphism, so the real image inherits it.\<close>

lemma defl_half_list_dvd_real:
  assumes "defl_half_cert qs = 0"
  shows "(of_int_poly (Poly (defl_half_list qs)) :: real poly)
           dvd (of_int_poly (Poly qs) :: real poly)"
proof -
  \<comment> \<open>\<open>simp only\<close> and an explicit homomorphism step: a bare \<open>simp\<close> normalises \<open>[:1, -2:] * X\<close> into \<open>pCons\<close> form on one
     side of the equation and then cannot close the goal.\<close>
  have "(of_int_poly (Poly qs) :: real poly) = of_int_poly ([:1, -2:] * Poly (defl_half_list qs))"
    by (simp only: defl_half_exact[OF assms])
  also have "\<dots> = of_int_poly [:1, -2:] * of_int_poly (Poly (defl_half_list qs))"
    by (rule of_int_poly_hom.hom_mult)
  also have "\<dots> = of_int_poly (Poly (defl_half_list qs)) * of_int_poly [:1, -2:]"
    by (rule mult.commute)
  finally show ?thesis ..
qed

lemma defl_one_list_dvd_real:
  assumes "defl_one_cert qs = 0"
  shows "(of_int_poly (Poly (defl_one_list qs)) :: real poly)
           dvd (of_int_poly (Poly qs) :: real poly)"
proof -
  \<comment> \<open>\<open>simp only\<close> and an explicit homomorphism step: a bare \<open>simp\<close> normalises \<open>[:1, -1:] * X\<close> into \<open>pCons\<close> form on one
     side of the equation and then cannot close the goal.\<close>
  have "(of_int_poly (Poly qs) :: real poly) = of_int_poly ([:1, -1:] * Poly (defl_one_list qs))"
    by (simp only: defl_one_exact[OF assms])
  also have "\<dots> = of_int_poly [:1, -1:] * of_int_poly (Poly (defl_one_list qs))"
    by (rule of_int_poly_hom.hom_mult)
  also have "\<dots> = of_int_poly (Poly (defl_one_list qs)) * of_int_poly [:1, -1:]"
    by (rule mult.commute)
  finally show ?thesis ..
qed


section \<open>The child divisibility chain\<close>

text \<open>\<^bold>\<open>What the width bound needs, and where the information is.\<close> The \<open>wide\<close> premise of \<open>defl_body_step\<close> is derived
  from the count, and the bound covering a possibly deflated object, @{thm [source] Bernstein_changes_small_interval_le_1_of_dvd},
  is indexed by \<open>dvd\<close>. Both child-build contracts provide it: \<open>defl_split_children_agrees\<close> and
  \<open>defl_split_children_escalate_gagrees\<close> each conclude \<open>\<exists>XL. \<dots> \<and> defl_node_rel (carried_left X) XL \<and> \<dots>\<close>, and
  @{const defl_node_rel} includes divisibility.

  \<^bold>\<open>The chain connects that to the child's own init\<close>: the contract relates the child to \<open>carried_left X\<close>, the map
  lemmas above carry the parent's divisibility across the same map, and @{thm [source] carried_init_same_den_compose}
  collapses nested frames exactly, so \<open>carried_left\<close> of the node init is the left child's init, with no scalar and no
  canonicity clause. The escalating continuations (\<open>defl_split_children_escalate_ggbind\<close> / \<open>_ggbind_decomp\<close>) use \<open>_dvd\<close>
  variants, in the shape of \<open>defl_split_children_gbind_pay\<close>, so that the divisibility reaches their arm.\<close>

lemma defl_node_relD_dvd_real:
  assumes "defl_node_rel ini q"
  shows "(of_int_poly (Poly q) :: real poly) dvd (of_int_poly (Poly ini) :: real poly)"
proof -
  obtain C where C: "Poly ini = Poly q * C" using defl_node_relD_dvd[OF assms] ..
  have "(of_int_poly (Poly ini) :: real poly) = of_int_poly (Poly q * C)"
    by (simp only: C)
  also have "\<dots> = of_int_poly (Poly q) * of_int_poly C" by (rule of_int_poly_hom.hom_mult)
  finally show ?thesis ..
qed

lemma defl_carried_right_as_cisd: "carried_init_same_den 1 2 2 Q = carried_right Q"
  by (simp add: carried_init_same_den_def carried_right_def carried_left_def)

lemma defl_child_left_init:
  "carried_left (carried_init_same_den l (2 ^ k) r rp)
     = carried_init_same_den (2 * l) (2 ^ Suc k) (l + r) rp"
  using carried_init_same_den_compose[of "2 ^ k" 2 0 1 l r rp]
  by (simp add: carried_init_same_den_zero_one[symmetric] mult.commute)

lemma defl_child_right_init:
  "carried_right (carried_init_same_den l (2 ^ k) r rp)
     = carried_init_same_den (l + r) (2 ^ Suc k) (2 * r) rp"
  using carried_init_same_den_compose[of "2 ^ k" 2 1 1 l r rp]
  by (simp add: defl_carried_right_as_cisd[symmetric] mult.commute algebra_simps)

lemma defl_child_left_dvd_chain:
  assumes dX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)"
    and rel: "defl_node_rel (carried_left X) XL"
  shows "(of_int_poly (Poly XL) :: real poly)
           dvd (of_int_poly (Poly (carried_init_same_den (2 * l) (2 ^ Suc k) (l + r) rp))
                 :: real poly)"
proof -
  have "(of_int_poly (Poly XL) :: real poly) dvd (of_int_poly (Poly (carried_left X)))"
    by (rule defl_node_relD_dvd_real[OF rel])
  also have "(of_int_poly (Poly (carried_left X)) :: real poly)
               dvd (of_int_poly (Poly (carried_left (carried_init_same_den l (2 ^ k) r rp))))"
    by (rule defl_carried_left_dvd_real[OF dX])
  finally show ?thesis by (simp only: defl_child_left_init)
qed

lemma defl_child_right_dvd_chain:
  assumes dX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)"
    and rel: "defl_node_rel (carried_right X) XR"
  shows "(of_int_poly (Poly XR) :: real poly)
           dvd (of_int_poly (Poly (carried_init_same_den (l + r) (2 ^ Suc k) (2 * r) rp))
                 :: real poly)"
proof -
  have "(of_int_poly (Poly XR) :: real poly) dvd (of_int_poly (Poly (carried_right X)))"
    by (rule defl_node_relD_dvd_real[OF rel])
  also have "(of_int_poly (Poly (carried_right X)) :: real poly)
               dvd (of_int_poly (Poly (carried_right (carried_init_same_den l (2 ^ k) r rp))))"
    by (rule defl_carried_right_dvd_real[OF dX])
  finally show ?thesis by (simp only: defl_child_right_init)
qed

section \<open>The window child's init, as a scalar identity\<close>

text \<open>\<open>defl_window_init_wrel\<close> relates the window child's own init to the window
  map applied to the node's init, but only as a \<open>defl_node_wrel\<close> --- its own banner says
  the two lists "are equal only up to a positive scalar, so a list identity is the wrong
  target". \<^bold>\<open>Divisibility needs more than roots\<close>, so the scalar has to be exhibited. It is the
  same computation as \<open>defl_node_init_pcompose_seed\<close>: @{thm [source] defl_cisd_real_pcompose}
  on each side, and \<open>defl_window_point_compose\<close>'s identity says the two affine
  maps agree.\<close>

lemma defl_window_init_scalar:
  fixes l r m :: int and k E :: nat
  shows "\<exists>c::real. c \<noteq> 0 \<and>
      (of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4)
                            (carried_init_same_den l (2 ^ k) r rp))) :: real poly)
        = smult c (of_int_poly (Poly (carried_init_same_den (l * 2 ^ E + m * (r - l))
                       (2 ^ (k + E)) (l * 2 ^ E + (m + 4) * (r - l)) rp)) :: real poly)"
proof -
  define P0 where "P0 = (of_int_poly (Poly rp) :: real poly)"
  define N where "N = carried_init_same_den l (2 ^ k) r rp"
  define A where "A = real_of_int l / 2 ^ k"
  define B where "B = (real_of_int r - real_of_int l) / 2 ^ k"
  define M where "M = real_of_int m / 2 ^ E"
  define W where "W = (real_of_int (m + 4) - real_of_int m) / 2 ^ E"
  have dE: "(2::int) ^ E \<noteq> 0" and dk: "(2::int) ^ k \<noteq> 0" and dkE: "(2::int) ^ (k + E) \<noteq> 0"
    by simp_all
  have inner: "(of_int_poly (Poly N) :: real poly) = smult (((2::real) ^ k) ^ (length rp - 1))
                 (P0 \<circ>\<^sub>p [: A, B :])"
    unfolding N_def P0_def A_def B_def
    using defl_cisd_real_pcompose[OF dk, of l r rp] by simp
  have outer: "(of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4) N)) :: real poly)
                 = smult (((2::real) ^ E) ^ (length N - 1))
                     ((of_int_poly (Poly N) :: real poly) \<circ>\<^sub>p [: M, W :])"
    unfolding M_def W_def
    using defl_cisd_real_pcompose[OF dE, of m "m + 4" N] by simp
  have rhs: "(of_int_poly (Poly (carried_init_same_den (l * 2 ^ E + m * (r - l))
                   (2 ^ (k + E)) (l * 2 ^ E + (m + 4) * (r - l)) rp)) :: real poly)
             = smult (((2::real) ^ (k + E)) ^ (length rp - 1))
                 (P0 \<circ>\<^sub>p [: real_of_int (l * 2 ^ E + m * (r - l)) / 2 ^ (k + E),
                           (real_of_int (l * 2 ^ E + (m + 4) * (r - l))
                              - real_of_int (l * 2 ^ E + m * (r - l))) / 2 ^ (k + E) :])"
    unfolding P0_def
    using defl_cisd_real_pcompose[OF dkE,
            of "l * 2 ^ E + m * (r - l)" "l * 2 ^ E + (m + 4) * (r - l)" rp]
    by simp
  \<comment> \<open>the two affine maps agree, coefficient by coefficient --- the constant term is
     \<open>defl_window_point_compose\<close> at \<open>t = 0\<close> and the slope is its \<open>t\<close>-coefficient;
     both fall out of the same \<open>power_add\<close> rearrangement, so they are proved directly.\<close>
  have c1: "A + B * M = real_of_int (l * 2 ^ E + m * (r - l)) / 2 ^ (k + E)"
    unfolding A_def B_def M_def by (simp add: power_add field_simps)
  have c2: "B * W = (real_of_int (l * 2 ^ E + (m + 4) * (r - l))
                       - real_of_int (l * 2 ^ E + m * (r - l))) / 2 ^ (k + E)"
    unfolding W_def B_def by (simp add: power_add field_simps)
  have compose: "([: A, B :] :: real poly) \<circ>\<^sub>p [: M, W :]
                   = [: real_of_int (l * 2 ^ E + m * (r - l)) / 2 ^ (k + E),
                        (real_of_int (l * 2 ^ E + (m + 4) * (r - l))
                           - real_of_int (l * 2 ^ E + m * (r - l))) / 2 ^ (k + E) :]"
    by (simp add: pcompose_pCons c1 c2)
  have lhs: "(of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4) N)) :: real poly)
             = smult ((((2::real) ^ E) ^ (length N - 1)) * (((2::real) ^ k) ^ (length rp - 1)))
                 (P0 \<circ>\<^sub>p [: real_of_int (l * 2 ^ E + m * (r - l)) / 2 ^ (k + E),
                           (real_of_int (l * 2 ^ E + (m + 4) * (r - l))
                              - real_of_int (l * 2 ^ E + m * (r - l))) / 2 ^ (k + E) :])"
    by (simp add: outer inner pcompose_smult compose c1 c2 flip: pcompose_assoc)
  have nz: "(((2::real) ^ E) ^ (length N - 1)) * (((2::real) ^ k) ^ (length rp - 1))
              / (((2::real) ^ (k + E)) ^ (length rp - 1)) \<noteq> 0" by simp
  show ?thesis
    unfolding N_def[symmetric]
    by (rule exI[of _ "(((2::real) ^ E) ^ (length N - 1)) * (((2::real) ^ k) ^ (length rp - 1))
                        / (((2::real) ^ (k + E)) ^ (length rp - 1))"])
       (simp add: lhs rhs nz)
qed

lemma defl_window_child_dvd:
  fixes l r m :: int and k E :: nat
  assumes dvdX: "(of_int_poly (Poly X) :: real poly)
                   dvd (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)"
  shows "(of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4) X)) :: real poly)
           dvd (of_int_poly (Poly (carried_init_same_den (l * 2 ^ E + m * (r - l))
                  (2 ^ (k + E)) (l * 2 ^ E + (m + 4) * (r - l)) rp)) :: real poly)"
proof -
  have step: "(of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4) X)) :: real poly)
                dvd (of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4)
                       (carried_init_same_den l (2 ^ k) r rp))) :: real poly)"
    by (rule defl_cisd_dvd_real[OF _ dvdX]) simp
  obtain c :: real where c0: "c \<noteq> 0"
    and ceq: "(of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4)
                   (carried_init_same_den l (2 ^ k) r rp))) :: real poly)
              = smult c (of_int_poly (Poly (carried_init_same_den (l * 2 ^ E + m * (r - l))
                     (2 ^ (k + E)) (l * 2 ^ E + (m + 4) * (r - l)) rp)) :: real poly)"
    using defl_window_init_scalar[of m E l k r rp] by blast
  have "(of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4) X)) :: real poly)
          dvd smult (1 / c) (smult c (of_int_poly (Poly (carried_init_same_den
                 (l * 2 ^ E + m * (r - l)) (2 ^ (k + E))
                 (l * 2 ^ E + (m + 4) * (r - l)) rp)) :: real poly))"
    using step unfolding ceq by (rule dvd_smult)
  thus ?thesis using c0 by simp
qed

section \<open>The relation the coupling carries\<close>

text \<open>\<^bold>\<open>Why the coupling carries a weaker relation than @{const defl_node_rel}.\<close> @{const defl_node_rel} combines
  divisibility with root agreement. Divisibility is right for the fired children (it is what
  \<open>defl_fired_left_node_rel\<close> proves), but the loop's two reading arms do not use it:

    \<^item> the reject arm needs \<open>roots_in = 0\<close>, transferred by agreement of the root sets;
    \<^item> the accept arm needs \<open>roots_in = 1\<close>, transferred the same way and made simple by \<open>P\<^sub>0\<close>'s squarefreeness, already a
      caller obligation;

  and otherwise divisibility provides only non-vanishing of the node polynomial, a side condition of the Bernstein
  lemmas.

  \<^bold>\<open>Carrying divisibility in \<open>\<int>[x]\<close> would cost a canonicity clause.\<close> Over \<open>\<rat>\<close> the map @{const carried_left} is
  \<open>P \<mapsto> smult (2\<^sup>(\<^sup>n\<^sup>-\<^sup>1\<^sup>)) (P \<circ> x/2)\<close> with \<open>n\<close> the length of its own input, so from \<open>A = B * C\<close> the cofactor is
  \<open>smult (2\<^sup>(\<^sup>n\<^sup>A\<^sup>-\<^sup>n\<^sup>B\<^sup>)) (C \<circ> x/2)\<close>, integral only when \<open>degree C \<le> n\<^sub>A - n\<^sub>B\<close>, i.e. when \<open>B\<close> has no trailing zero coefficient
  (\<open>degree (Poly B) = length B - 1\<close>), a condition that would have to be preserved through four maps.

  So the coupling carries the weaker relation its consumers read, with non-vanishing included so that one clause serves
  both. @{const defl_node_rel} implies it whenever the left-hand polynomial is nonzero, so the facts about the fired
  children still apply. (Divisibility over \<open>\<real>\<close>, where the scalar is a unit, is carried separately; see the
  divisibility chain.)\<close>

definition defl_node_wrel :: "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "defl_node_wrel ini q \<longleftrightarrow>
     (of_int_poly (Poly q) :: real poly) \<noteq> 0
     \<and> (\<forall>t::real. 0 < t \<longrightarrow> t < 1 \<longrightarrow>
          (poly (of_int_poly (Poly ini) :: real poly) t = 0)
            = (poly (of_int_poly (Poly q) :: real poly) t = 0))"

lemma defl_node_wrelD_nz: "defl_node_wrel ini q \<Longrightarrow> (of_int_poly (Poly q) :: real poly) \<noteq> 0"
  unfolding defl_node_wrel_def by simp

lemma defl_node_wrelD_roots:
  "defl_node_wrel ini q \<Longrightarrow> 0 < t \<Longrightarrow> t < 1 \<Longrightarrow>
     (poly (of_int_poly (Poly ini) :: real poly) t = 0)
       = (poly (of_int_poly (Poly q) :: real poly) t = 0)"
  unfolding defl_node_wrel_def by simp

lemma defl_node_wrel_refl:
  assumes "(of_int_poly (Poly xs) :: real poly) \<noteq> 0"
  shows "defl_node_wrel xs xs"
  using assms unfolding defl_node_wrel_def by simp

lemma defl_node_wrel_trans:
  assumes "defl_node_wrel a b" and "defl_node_wrel b c"
  shows "defl_node_wrel a c"
  using assms unfolding defl_node_wrel_def by simp

text \<open>\<^bold>\<open>@{const defl_node_rel} implies it\<close>, so the facts about the fired children carry over to the coupling.
  Non-vanishing comes from divisibility: a divisor of a nonzero polynomial is nonzero.\<close>

lemma defl_node_wrel_of_rel:
  assumes rel: "defl_node_rel ini q"
    and nz: "(of_int_poly (Poly ini) :: real poly) \<noteq> 0"
  shows "defl_node_wrel ini q"
proof -
  have "Poly q dvd Poly ini" by (rule defl_node_relD_dvd[OF rel])
  hence "(of_int_poly (Poly q) :: real poly) dvd of_int_poly (Poly ini)"
    by (simp add: of_int_poly_hom.hom_dvd)
  hence qnz: "(of_int_poly (Poly q) :: real poly) \<noteq> 0" using nz by auto
  show ?thesis
    unfolding defl_node_wrel_def
    using qnz defl_node_relD_roots[OF rel] by simp
qed

text \<open>\<^bold>\<open>And it IS a congruence for both child maps\<close>, which is the whole reason for the weakening.
  Non-vanishing survives because @{const carried_left} multiplies each coefficient by a NONZERO
  scalar, so it cannot turn a nonzero polynomial into the zero one -- read off the evaluation
  lemma at a point where the parent does not vanish.\<close>

lemma defl_carried_left_nz:
  assumes nz: "(of_int_poly (Poly xs) :: real poly) \<noteq> 0"
  shows "(of_int_poly (Poly (carried_left xs)) :: real poly) \<noteq> 0"
proof
  assume z: "(of_int_poly (Poly (carried_left xs)) :: real poly) = 0"
  have "\<And>t::real. poly (of_int_poly (Poly xs) :: real poly) t = 0"
  proof -
    fix t :: real
    have "poly (of_int_poly (Poly (carried_left xs)) :: real poly) (2 * t) = 0"
      using z by simp
    thus "poly (of_int_poly (Poly xs) :: real poly) t = 0"
      by (simp add: defl_poly_carried_left)
  qed
  hence "poly (of_int_poly (Poly xs) :: real poly) = poly 0" by auto
  hence "(of_int_poly (Poly xs) :: real poly) = 0" by (simp add: poly_eq_poly_eq_iff)
  thus False using nz by simp
qed

lemma defl_carried_right_nz:
  assumes nz: "(of_int_poly (Poly xs) :: real poly) \<noteq> 0"
  shows "(of_int_poly (Poly (carried_right xs)) :: real poly) \<noteq> 0"
proof
  assume z: "(of_int_poly (Poly (carried_right xs)) :: real poly) = 0"
  have "\<And>t::real. poly (of_int_poly (Poly xs) :: real poly) t = 0"
  proof -
    fix t :: real
    have "poly (of_int_poly (Poly (carried_right xs)) :: real poly) (2 * t - 1) = 0"
      using z by simp
    thus "poly (of_int_poly (Poly xs) :: real poly) t = 0"
      by (simp add: defl_poly_carried_right)
  qed
  hence "poly (of_int_poly (Poly xs) :: real poly) = poly 0" by auto
  hence "(of_int_poly (Poly xs) :: real poly) = 0" by (simp add: poly_eq_poly_eq_iff)
  thus False using nz by simp
qed

lemma defl_node_wrel_carried_left:
  assumes rel: "defl_node_wrel A B"
  shows "defl_node_wrel (carried_left A) (carried_left B)"
  unfolding defl_node_wrel_def
proof (intro conjI allI impI)
  show "(of_int_poly (Poly (carried_left B)) :: real poly) \<noteq> 0"
    by (rule defl_carried_left_nz[OF defl_node_wrelD_nz[OF rel]])
next
  fix t :: real assume t0: "0 < t" and t1: "t < 1"
  have h0: "0 < t / 2" using t0 by simp
  have h1: "t / 2 < 1" using t1 by simp
  show "(poly (of_int_poly (Poly (carried_left A)) :: real poly) t = 0)
      = (poly (of_int_poly (Poly (carried_left B)) :: real poly) t = 0)"
    using defl_node_wrelD_roots[OF rel h0 h1]
    by (simp add: defl_poly_carried_left)
qed

lemma defl_node_wrel_carried_right:
  assumes rel: "defl_node_wrel A B"
  shows "defl_node_wrel (carried_right A) (carried_right B)"
  unfolding defl_node_wrel_def
proof (intro conjI allI impI)
  show "(of_int_poly (Poly (carried_right B)) :: real poly) \<noteq> 0"
    by (rule defl_carried_right_nz[OF defl_node_wrelD_nz[OF rel]])
next
  fix t :: real assume t0: "0 < t" and t1: "t < 1"
  have h0: "0 < (t + 1) / 2" using t0 by simp
  have h1: "(t + 1) / 2 < 1" using t1 by simp
  show "(poly (of_int_poly (Poly (carried_right A)) :: real poly) t = 0)
      = (poly (of_int_poly (Poly (carried_right B)) :: real poly) t = 0)"
    using defl_node_wrelD_roots[OF rel h0 h1]
    by (simp add: defl_poly_carried_right)
qed

text \<open>\<^bold>\<open>The deflating truncation coupling\<close>: the non-deflating shape with the pinned exact object replaced by an
  existential.

  Truncation and deflation are two independent departures from the exact init, and the coupling carries both: the
  stored polynomial need not divide anything once \<open>carried_retrunc_mop\<close> has fired, since a truncated polynomial divides
  nothing. So the exact object is quantified: there is some \<open>X\<close> that the stored polynomial frames in the usual sense
  (@{const node_frame}, within the guard's error bound), and that stands in @{const defl_node_rel} to the node's own
  carried init. Taking \<open>X\<close> to be the init recovers @{const hybrid_trunc_coupling}, so the deflating coupling is a
  relaxation of the non-deflating one.

  The exact-lock clause remains, with a different right-hand side: a locked node holds the deflated exact polynomial,
  not the init (the lock is taken together with the shed).\<close>

text \<open>\<^bold>\<open>The cached-count clause is part of this bundle, not a separate clause of the invariant.\<close> Without a count
  clause, the reject arm could not preserve the invariant: @{const hybrid_branch_zero_monadic} discards the popped
  node's box, so keeping \<open>defl_pending_covers\<close> requires knowing that the box holds no root of \<open>P\<^sub>0\<close>, which is read off
  \<open>cnt = 0\<close> only. Likewise the accept arm, where \<open>defl_acc_isolates\<close> needs \<open>cnt = 1\<close> to mean \<open>dsc_pair_ok\<close>.

  \<^bold>\<open>Why it shares the existential.\<close> The count is @{const hybrid_cs_ok} against the count of the node's own exact
  polynomial, which after a shed is the deflated child, not the carried init, so it must name the same \<open>X\<close> as the frame.
  Two separate existentials would let the witnesses differ, and the clause would say nothing about the stored polynomial.
  (@{const hybrid_cs_coupling} can be a separate clause because there the exact object is given by a formula.)

  The supplier matches: @{thm [source] hybrid_split_pair_state_correct} concludes
  \<open>hybrid_cs_ok gl cl (carried_descartes_count XL)\<close> for its ghost \<open>XL\<close>, which \<open>defl_split_children_gbind\<close> provides as
  the deflated exact child.\<close>

text \<open>\<^bold>\<open>ONE node's share of the coupling, named\<close>, so that the pop/push preservation lemmas
  and the split step's per-child obligation all speak about the same object. The classic pair
  (\<open>hybrid_trunc_coupling\<close> + \<open>hybrid_cs_coupling\<close>) can leave its per-node content inline
  because there the exact polynomial is a FORMULA; here it is quantified, so factoring it out is
  what keeps the witness from having to be re-produced at every consumer.\<close>

definition defl_node_ok ::
  "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  \<comment> \<open>\<^bold>\<open>The relation here is @{const defl_node_wrel}, not @{const defl_node_rel}\<close> (see below for why the
     divisibility half is not pushed through the child maps in \<open>\<int>[x]\<close>). \<^bold>\<open>The length clause is needed\<close>: a non-deflating
     child has length exactly \<open>length rp\<close>, which gives its word bounds, but a deflated child is one shorter on the firing
     branch, so the bound is carried.\<close>
  "defl_node_ok rp l r k q g c \<longleftrightarrow>
     (\<exists>X. node_frame X q g
        \<and> defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X
        \<and> hybrid_cs_ok g c (carried_descartes_count X)
        \<and> length X \<le> length rp
        \<and> (g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g)
        \<comment> \<open>\<^bold>\<open>The payload, stated about \<open>X\<close>, not about the node's init.\<close> This clause of @{const hybrid_pay_invar} does
           not carry over to the deflating stack because of the window push: it records \<open>2\<^sup>4\<^sup>2 + v\<close> with \<open>v\<close> the count of
           the possibly deflated object, while @{const hybrid_child_pay_ok} bounds the count of the node's init, and a
           Descartes count does not transport between the two. Stated inside the existential that names \<open>X\<close>, it is
           provable.\<close>
        \<and> (4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104)
        \<and> (4398046511104 \<le> g \<longrightarrow> q = X)
        \<comment> \<open>\<^bold>\<open>Divisibility, about \<open>X\<close> for the same reason as the payload.\<close> A truncation is not a divisor, so the clause
           cannot be about the stored \<open>qtodo\<close> entry, only about the exact object named by the existential. It is over \<open>\<real>\<close>
           rather than \<open>\<int>[x]\<close>, where the cofactor scalar is a unit.

           \<^bold>\<open>What uses it.\<close> The \<open>wide\<close> premise of \<open>defl_body_step\<close>. The non-deflating stack derives \<open>\<delta> < b - a\<close> from
           \<open>2 \<le> count\<close> via @{const carried_repr_scalar}; a deflated node is a divisor of its init rather than a
           representation of it, and a Descartes count does not transport across @{const defl_node_wrel}, so divisibility
           is the hypothesis that reaches the count (\<open>defl_node_wide_of_count2\<close>).\<close>
        \<and> (of_int_poly (Poly X) :: real poly)
             dvd (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly))
     \<comment> \<open>the CEILING half of the same atom. Outside the existential, because it names no
        polynomial --- it is what bounds the guard for the word caps.\<close>
     \<and> g \<le> 4398046511104 + length rp
     \<and> (4 < c \<longrightarrow> 4398046511104 \<le> g)"

text \<open>\<^bold>\<open>The last clause is outside the existential\<close>: it names no polynomial and is a statement about the two scalar
  columns \<open>cs\<close> and \<open>gs\<close>. It makes the cached count safe to ignore at a general guard.

  \<^bold>\<open>The hazard.\<close> @{const hybrid_window_v_monadic}'s first branch returns the cached \<open>cnt - 2\<close> whenever \<open>4 \<le> cnt\<close>,
  without reading the polynomial. On the non-deflating stack that is sound, since the node's exact object is its init,
  so the cached count describes the polynomial @{const hybrid_cond_escalate_monadic} hands the window. Here, at
  \<open>0 < g < 2\<^sup>4\<^sup>2\<close>, the escalation rebuilds the node to its init while the cache describes the deflated exact object \<open>X\<close>, and
  \<open>carried_descartes_count\<close> does not transport across @{const defl_node_wrel} (the shed root is at a local-frame endpoint
  or outside the box, so the two polynomials agree on roots in \<open>(0,1)\<close> but may disagree on sign variations). A stale count
  reaching @{const newton_window_pick_bail} could lose a root, so this is excluded structurally.

  \<^bold>\<open>The code satisfies it.\<close> A class above \<open>4\<close> has one producer, the window push, which stores \<open>v + 2\<close> together with the
  lock guard \<open>2\<^sup>4\<^sup>2 + v\<close>. Every other producer is @{const hybrid_class_of}, capped at \<open>4\<close> by
  @{thm [source] carried_descartes_count_g_monadic_le3} (\<open>defl_classify_prebuilt_le4\<close> below), and the sentinel \<open>4\<close> is
  resolved at pop. So the clause gives the general-guard arm \<open>c < 4\<close>.\<close>

lemma defl_node_okI:
  assumes "node_frame X q g"
    and "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and "hybrid_cs_ok g c (carried_descartes_count X)"
    and "length X \<le> length rp"
    and "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and "4398046511104 \<le> g \<longrightarrow> q = X"
    and "4 < c \<longrightarrow> 4398046511104 \<le> g"
    \<comment> \<open>\<^bold>\<open>Last\<close>, so that no existing \<open>[OF \<dots>]\<close> position moves.\<close>
    and "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    and "g \<le> 4398046511104 + length rp"
    \<comment> \<open>\<^bold>\<open>Last\<close>, so that no existing \<open>[OF \<dots>]\<close> position moves.\<close>
    and "(of_int_poly (Poly X) :: real poly)
             dvd (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)"
  shows "defl_node_ok rp l r k q g c"
  using assms unfolding defl_node_ok_def by blast

lemma defl_node_okE:
  assumes "defl_node_ok rp l r k q g c"
  obtains X where "node_frame X q g"
    and "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and "hybrid_cs_ok g c (carried_descartes_count X)"
    and "length X \<le> length rp"
    and "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and "4398046511104 \<le> g \<longrightarrow> q = X"
    and "4 < c \<longrightarrow> 4398046511104 \<le> g"
    and "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    and "g \<le> 4398046511104 + length rp"
    and "(of_int_poly (Poly X) :: real poly)
             dvd (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)"
  using assms unfolding defl_node_ok_def by blast

definition defl_trunc_coupling ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    gmp_poly \<Rightarrow> bool" where
  "defl_trunc_coupling todo qtodo cs gs rp \<longleftrightarrow>
     (case todo of (lns, rns, ks) \<Rightarrow>
        length lns = length qtodo \<and> length rns = length qtodo \<and>
        length ks = length qtodo \<and> length gs = length qtodo \<and>
        length cs = length qtodo \<and>
        (\<forall>i < length qtodo.
           defl_node_ok rp (lns ! i) (rns ! i) (ks ! i)
             (qtodo ! i) (gs ! i) (cs ! i)))"

text \<open>\<^bold>\<open>The seed satisfies it, and the witness is the init itself\<close> -- nothing has been
  deflated or truncated yet, so \<open>X := P\<close> with @{thm [source] node_frame_exact} and
  @{thm [source] defl_node_rel_refl}. Mirrors @{thm [source] hybrid_trunc_coupling_init}
  line for line, which is the check that the relaxation really does contain the classic case.\<close>

lemma defl_trunc_coupling_init:
  assumes P_eq: "P = carried_init_same_den l_num (2 ^ k) r_num rp"
    and c_ok: "hybrid_cs_ok 0 c (carried_descartes_count P)"
    \<comment> \<open>the seed class is @{const hybrid_class_of}'s, so \<open>\<le> 4\<close> --- see the note on
       @{const defl_node_ok}'s last clause. Stated as a hypothesis rather than derived
       because the seed's classify is the CALLER's, not this lemma's.\<close>
    and c_le: "c \<le> 4"
    and Pnz: "(of_int_poly (Poly P) :: real poly) \<noteq> 0"
  shows "defl_trunc_coupling ([l_num], [r_num], [k]) [P] [c] [0] rp"
  \<comment> \<open>the witness must be given: \<open>auto\<close> will not guess \<open>X\<close>, and the \<open>\<exists>\<close> is the whole
     difference from @{thm [source] hybrid_trunc_coupling_init}. Since the per-node content
     was factored, the witness is supplied ONCE through @{thm [source] defl_node_okI} rather
     than by an \<open>exI\<close> under a \<open>clarsimp\<close>.\<close>
proof -
  have nf: "node_frame P P 0" by (simp add: node_frame_exact)
  have nr: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) P"
    using P_eq Pnz by (simp add: defl_node_wrel_refl)
  have lenP: "length P \<le> length rp"
    by (simp add: P_eq truncate_length_carried_init_same_den)
  have bud: "(0::nat) \<le> (k + 1) * length rp \<or> 4398046511104 \<le> (0::nat)" by simp
  have lk: "4398046511104 \<le> (0::nat) \<longrightarrow> P = P" by simp
  have cg: "4 < c \<longrightarrow> 4398046511104 \<le> (0::nat)" using c_le by simp
  \<comment> \<open>at the seed both halves of the payload atom are degenerate: the guard is \<open>0\<close>, so the antecedent is false and
     the ceiling is immediate.\<close>
  have pay0: "4398046511106 \<le> (0::nat) \<longrightarrow> carried_descartes_count P \<le> 0 - 4398046511104"
    by simp
  have ceil0: "(0::nat) \<le> 4398046511104 + length rp" by simp
  \<comment> \<open>at the seed the witness is the init, so divisibility is reflexivity.\<close>
  have dvd0: "(of_int_poly (Poly P) :: real poly)
                dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                      :: real poly)"
    unfolding P_eq by (rule dvd_refl)
  have "defl_node_ok rp l_num r_num k P 0 c"
    by (rule defl_node_okI[OF nf nr c_ok lenP bud lk cg pay0 ceil0 dvd0])
  thus ?thesis unfolding defl_trunc_coupling_def by simp
qed

text \<open>\<^bold>\<open>Pop and push\<close>, clones of @{thm [source] hybrid_cs_coupling_pop} /
  @{thm [source] hybrid_cs_coupling_push}. With the per-node content factored into
  @{const defl_node_ok} they are the classic proofs verbatim -- the existential never has to be
  opened, which is the point of the factoring.\<close>

lemma defl_trunc_coupling_pop:
  assumes c: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
  shows "defl_trunc_coupling (butlast lns, butlast rns, butlast ks)
           (butlast qtodo) (butlast cs) (butlast gs) rp"
  using c unfolding defl_trunc_coupling_def by (auto simp: nth_butlast)

lemma defl_trunc_coupling_push:
  assumes c: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and ok1: "defl_node_ok rp l1 r1 k1 q1 g1 c1"
    and ok2: "defl_node_ok rp l2 r2 k2 q2 g2 c2"
  shows "defl_trunc_coupling (lns @ [l1, l2], rns @ [r1, r2], ks @ [k1, k2])
           (qtodo @ [q1, q2]) (cs @ [c1, c2]) (gs @ [g1, g2]) rp"
  using c ok1 ok2 unfolding defl_trunc_coupling_def
  by (auto simp: nth_append less_Suc_eq)

text \<open>\<^bold>\<open>And by one slot\<close>: the window arm's push, and the split arm's push of the left child only.\<close>
lemma defl_trunc_coupling_push1:
  assumes c: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and ok1: "defl_node_ok rp l1 r1 k1 q1 g1 c1"
  shows "defl_trunc_coupling (lns @ [l1], rns @ [r1], ks @ [k1])
           (qtodo @ [q1]) (cs @ [c1]) (gs @ [g1]) rp"
  using c ok1 unfolding defl_trunc_coupling_def
  by (auto simp: nth_append less_Suc_eq)

text \<open>\<^bold>\<open>And what the POP reads off\<close>: the coupling's clause for the node the loop is about to
  dispatch on. @{thm [source] defl_trunc_coupling_pop} says the REST of the worklist still
  couples; this says the popped node itself is well-formed, which is what every arm lemma takes
  as its hypothesis. Together they are the whole of what the loop body needs from the invariant's
  third clause at pop time.\<close>

lemma defl_trunc_coupling_last:
  assumes c: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and ne: "qtodo \<noteq> []"
  shows "defl_node_ok rp (last lns) (last rns) (last ks)
           (last qtodo) (last gs) (last cs)"
proof -
  have len: "length lns = length qtodo" "length rns = length qtodo"
    "length ks = length qtodo" "length gs = length qtodo" "length cs = length qtodo"
    using c unfolding defl_trunc_coupling_def by simp_all
  have i: "length qtodo - 1 < length qtodo" using ne by (cases qtodo) auto
  have node: "defl_node_ok rp (lns ! (length qtodo - 1)) (rns ! (length qtodo - 1))
      (ks ! (length qtodo - 1)) (qtodo ! (length qtodo - 1))
      (gs ! (length qtodo - 1)) (cs ! (length qtodo - 1))"
    using c i unfolding defl_trunc_coupling_def by simp
  \<comment> \<open>\<open>last_conv_nth\<close> needs each list's OWN non-emptiness, which the length agreements give.\<close>
  have nes: "lns \<noteq> []" "rns \<noteq> []" "ks \<noteq> []" "gs \<noteq> []" "cs \<noteq> []"
    using ne len by auto
  show ?thesis
    using node
    by (simp add: last_conv_nth[OF nes(1)] last_conv_nth[OF nes(2)] last_conv_nth[OF nes(3)]
                  last_conv_nth[OF ne] last_conv_nth[OF nes(4)] last_conv_nth[OF nes(5)] len)
qed

text \<open>\<^bold>\<open>And the classic coupling IMPLIES it\<close>, which is worth having as a theorem rather than as
  a remark: it says the deflating loop's invariant is genuinely weaker, so any node the classic
  stack could have produced is one this coupling admits.\<close>

lemma defl_trunc_coupling_of_hybrid:
  assumes a: "hybrid_trunc_coupling (lns, rns, ks) qtodo gs rp"
    and b: "hybrid_cs_coupling (lns, rns, ks) qtodo cs gs rp"
    \<comment> \<open>\<^bold>\<open>Non-vanishing is a genuine EXTRA hypothesis, not bookkeeping.\<close> The classic coupling
       pins each node to its init by a FORMULA and never has to say the init is nonzero;
       @{const defl_node_wrel} bundles non-vanishing precisely because the deflating arms need
       it as a Bernstein side condition, so it has to come from somewhere. Here it is supplied;
       in the loop it is re-established at every step from the parent's.\<close>
    and nz: "\<And>i. i < length qtodo \<Longrightarrow>
        (of_int_poly (Poly (carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp))
           :: real poly) \<noteq> 0"
    \<comment> \<open>\<^bold>\<open>The class bound is the second genuine extra hypothesis\<close>, for the same reason as
       \<open>nz\<close>: @{const hybrid_cs_coupling} does not carry it, because the classic stack never
       needs it (its cached count always describes the polynomial the window is handed).\<close>
    and cle: "\<And>i. i < length qtodo \<Longrightarrow> cs ! i \<le> 4"
    \<comment> \<open>\<^bold>\<open>The third extra hypothesis.\<close> On the non-deflating stack every node holds its init, so
       @{const hybrid_child_pay_ok} is the deflating payload atom at \<open>X := init\<close>; @{const hybrid_trunc_coupling} does
       not carry it, so it is supplied.\<close>
    and apay: "hybrid_pay_invar (lns, rns, ks) gs rp"
  shows "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
  \<comment> \<open>Explicit rather than a \<open>clarsimp\<close>/\<open>auto\<close> chain: both @{thm [source] defl_node_wrel_refl}
     and \<open>nz\<close> carry premises, so as simp/intro rules they fire only if \<open>auto\<close> happens to
     discharge those first -- and it does not. Deriving the six conjuncts by name is shorter
     than the failure was.\<close>
proof -
  have node: "\<And>i. i < length qtodo \<Longrightarrow>
      defl_node_ok rp (lns ! i) (rns ! i) (ks ! i) (qtodo ! i) (gs ! i) (cs ! i)"
  proof -
    fix i assume i: "i < length qtodo"
    let ?X = "carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp"
    have f: "node_frame ?X (qtodo ! i) (gs ! i)"
      using a i unfolding hybrid_trunc_coupling_def by simp
    have w: "defl_node_wrel ?X ?X" by (rule defl_node_wrel_refl[OF nz[OF i]])
    have c: "hybrid_cs_ok (gs ! i) (cs ! i) (carried_descartes_count ?X)"
      using b i unfolding hybrid_cs_coupling_def by simp
    have l: "length ?X \<le> length rp"
      by (simp add: truncate_length_carried_init_same_den)
    have bud: "gs ! i \<le> (ks ! i + 1) * length rp \<or> 4398046511104 \<le> gs ! i"
      using a i unfolding hybrid_trunc_coupling_def by simp
    have lk: "4398046511104 \<le> gs ! i \<longrightarrow> qtodo ! i = ?X"
      using a i unfolding hybrid_trunc_coupling_def by simp
    have cg: "4 < cs ! i \<longrightarrow> 4398046511104 \<le> gs ! i" using cle[OF i] by simp
    have glen: "i < length gs" using a i unfolding hybrid_trunc_coupling_def by simp
    have atom: "hybrid_child_pay_ok (lns ! i) (ks ! i) (rns ! i) rp (gs ! i)"
      by (rule hybrid_pay_invarD[OF apay glen])
    have pay: "4398046511106 \<le> gs ! i \<longrightarrow> carried_descartes_count ?X \<le> gs ! i - 4398046511104"
      by (rule hybrid_child_pay_okD[OF atom refl])
    have ceil: "gs ! i \<le> 4398046511104 + length rp"
      using atom unfolding hybrid_child_pay_ok_def by simp
    \<comment> \<open>on the non-deflating stack every node's object is its own init, so again reflexivity.\<close>
    have dvd: "(of_int_poly (Poly ?X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den (lns ! i) (2 ^ (ks ! i))
                        (rns ! i) rp)) :: real poly)"
      by (rule dvd_refl)
    show "defl_node_ok rp (lns ! i) (rns ! i) (ks ! i) (qtodo ! i) (gs ! i) (cs ! i)"
      by (rule defl_node_okI[OF f w c l bud lk cg pay ceil dvd])
  qed
  show ?thesis
    using a b node
    unfolding hybrid_trunc_coupling_def hybrid_cs_coupling_def defl_trunc_coupling_def
    by simp
qed

section \<open>The loop-level target, and what the exit reads off\<close>

text \<open>\<^bold>\<open>What the deflating stack provides to the power-substitution entry.\<close> The consumer is the \<open>qsolve\<close>
  hypothesis of \<open>Power_Sub_Entry_Sound\<close>, whose conjuncts are an interval-vector invariant, a length bound, and the pair
  \<open>pow_sub_reduced_isolates\<close> / \<open>pow_sub_reduced_covers\<close>: isolation and coverage, not a multiset equality, which
  @{thm [source] newdsc_pol_defl_sound} / @{thm [source] newdsc_pol_defl_complete} provide. They are restated here
  rather than imported because the power-substitution theories come later in the build; the bridge is definitional
  unfolding at the consumer.\<close>

definition defl_acc_isolates :: "real poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "defl_acc_isolates P0 acc \<longleftrightarrow>
     (\<forall>j < length (dyadic_interval_vec_triples acc).
        case dyadic_interval_vec_triples acc ! j of ((A, B), m) \<Rightarrow>
          dsc_pair_ok P0 (real_of_int A / 2 ^ m, real_of_int B / 2 ^ m))"

definition defl_acc_covers :: "real poly \<Rightarrow> real \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "defl_acc_covers P0 lo acc \<longleftrightarrow>
     (\<forall>y::real. lo < y \<longrightarrow> poly P0 y = 0 \<longrightarrow>
        (\<exists>j A B m. j < length (dyadic_interval_vec_triples acc)
           \<and> dyadic_interval_vec_triples acc ! j = ((A, B), m)
           \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
              \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y))))"

text \<open>\<^bold>\<open>A pending node's box, as a real interval.\<close> The worklist stores numerators and a shared
  depth per node, so the box of entry \<open>i\<close> is \<open>(l\<^sub>i/2\<^sup>k\<^sup>i, r\<^sub>i/2\<^sup>k\<^sup>i)\<close>. Coverage is stated against
  these rather than against the abstract recursion's boxes because the loop is a WORKLIST and
  the recursion is a TREE -- the bridge between the two shapes is the classic keystone's
  \<open>hybrid_alpha_nodes\<close> machinery, and a deflating clone of it follows.\<close>

definition defl_todo_box :: "gmp_dyadic_interval_vec \<Rightarrow> nat \<Rightarrow> real \<times> real" where
  "defl_todo_box todo i =
     (case todo of (lns, rns, ks) \<Rightarrow>
        (real_of_int (lns ! i) / 2 ^ (ks ! i), real_of_int (rns ! i) / 2 ^ (ks ! i)))"

definition defl_pending_covers ::
  "real poly \<Rightarrow> real \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "defl_pending_covers P0 lo todo acc \<longleftrightarrow>
     (\<forall>y::real. lo < y \<longrightarrow> poly P0 y = 0 \<longrightarrow>
        (\<exists>j A B m. j < length (dyadic_interval_vec_triples acc)
           \<and> dyadic_interval_vec_triples acc ! j = ((A, B), m)
           \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
              \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y)))
      \<or> (\<exists>i < length (fst (snd todo)). fst (defl_todo_box todo i) < y
             \<and> y < snd (defl_todo_box todo i)))"

text \<open>\<^bold>\<open>The loop invariant.\<close> Three clauses, and the third is the only one that mentions
  deflation at all: the accumulated windows are sound for \<open>P\<^sub>0\<close>, every root not yet accumulated
  is still inside some pending box, and every pending node's polynomial stands in
  @{const defl_node_rel} to its own carried init. The first two are what the exit needs; the
  third is what the SPLIT step must re-establish, and is where
  \<open>Deflation_Bridge.defl_children_roots_in_box\<close> is consumed.\<close>

definition defl_loop_invar ::
  "real poly \<Rightarrow> real \<Rightarrow> hybrid_state \<Rightarrow> bool" where
  "defl_loop_invar P0 lo st \<longleftrightarrow>
     (case st of ((todo, qtodo, es, ss, cs, gs, rp), acc) \<Rightarrow>
        defl_acc_isolates P0 acc
        \<and> defl_pending_covers P0 lo todo acc
        \<and> defl_trunc_coupling todo qtodo cs gs rp)"

text \<open>\<^bold>\<open>The exit, and it is the easy half.\<close> \<open>hybrid_loop_cond\<close> is false exactly when the
  worklist is empty, and an empty worklist has no box for a root to hide in -- so the pending
  disjunct of clause 2 collapses and coverage is read off directly. Nothing about deflation
  enters here, which is the point of stating the invariant this way: the deflating content is
  confined to the split step.\<close>

lemma defl_loop_invar_exit:
  assumes inv: "defl_loop_invar P0 lo ((todo, qtodo, es, ss, cs, gs, rp), acc)"
    and empty: "fst (snd todo) = []"
  shows "defl_acc_isolates P0 acc" and "defl_acc_covers P0 lo acc"
proof -
  show "defl_acc_isolates P0 acc"
    using inv unfolding defl_loop_invar_def by simp
  show "defl_acc_covers P0 lo acc"
    using inv empty
    unfolding defl_loop_invar_def defl_pending_covers_def defl_acc_covers_def
    by auto
qed

text \<open>\<^bold>\<open>The seed, correspondingly trivial\<close>: nothing is accumulated, the single pending node is
  the root box, and its polynomial is its own init, so @{thm [source] defl_node_rel_refl}
  discharges the coupling. Stated about the CLAUSES rather than about
  @{const defl_main_list_monadic}'s seed block, so that it is reusable when the seed's own
  \<open>ASSERT\<close> cascade is threaded through \<open>refine_vcg\<close>.\<close>

lemma defl_acc_isolates_empty:
  assumes "dyadic_interval_vec_triples acc = []"
  shows "defl_acc_isolates P0 acc"
  using assms unfolding defl_acc_isolates_def by simp

section \<open>The fired children\<close>

text \<open>\<^bold>\<open>The split step's mathematics.\<close> When the deflation fires, @{const defl_children_monadic} returns
  \<open>trunc_list 1 (defl_one_list ql)\<close> and \<open>trunc_list 1 (map uminus (tl qr))\<close> (@{thm [source] defl_children_monadic_correct}).
  Composing that with the bridge's exactness and evenness theorems gives each child as an explicit cofactor of its
  parent, which is what the invariant's @{const defl_node_rel} clause needs.

  \<^bold>\<open>The scalars \<open>2\<close> and \<open>-2\<close>\<close> are the factors the halving divides out of the operand. A nonzero scalar changes no root,
  but they must appear in the factorisation, or the divisibility is false in \<open>\<int>[x]\<close>.\<close>

text \<open>The two scalar identities the factorisations pivot on, stated separately so that the
  \<open>simp only:\<close> steps below never have to see a plain \<open>simp\<close>.\<close>

text \<open>\<^bold>\<open>Do not re-prove \<open>defl_Poly_map_uminus\<close>\<close> -- \<open>Deflation_Op.thy\<close> has it and that
  theory IS in this graph, via \<open>Solvers_Base\<close>. \<open>lint-thy.sh\<close>'s C9 duplicate-name check found
  both the reachable copy and an unreachable same-shaped one in \<open>Kiou_Bound_Refine\<close>, which is
  the useful distinction: C9 sees the whole repo while the build sees only the ancestry, so a
  name it flags may be reusable OR may still be undefined here -- check which before renaming.
  (And the induction must run over a FREE list: \<open>induction "tl (\<dots>)"\<close> does not generalise the
  term, so the step case arrives with the original still in the goal.)\<close>

lemma two_lin: "[:2, -2:] = smult (2::int) [:1, -1:]" by simp

lemma two_x: "[:0, -2:] = smult (-2::int) [:0, 1:]" by simp

lemma defl_fired_left_factor:
  assumes ne: "0 < length Q" and mid: "carried_right Q ! 0 = 0"
  shows "Poly (carried_left Q)
       = [:2, -2:] * Poly (trunc_list 1 (defl_one_list (carried_left Q)))"
proof -
  have ev: "\<forall>y \<in> set (defl_one_list (carried_left Q)). (2::int) dvd y"
    by (rule defl_left_child_all_even[OF ne mid])
  have dbl: "map ((*) 2) (trunc_list 1 (defl_one_list (carried_left Q)))
           = defl_one_list (carried_left Q)"
    by (rule trunc_list_1_exact[OF ev])
  have sm: "Poly (defl_one_list (carried_left Q))
          = smult 2 (Poly (trunc_list 1 (defl_one_list (carried_left Q))))"
    by (subst dbl[symmetric]) (rule Poly_map_double)
  have "Poly (carried_left Q) = [:1, -1:] * Poly (defl_one_list (carried_left Q))"
    by (rule defl_left_child_exact[OF ne mid])
  also have "\<dots> = [:1, -1:] * smult 2 (Poly (trunc_list 1 (defl_one_list (carried_left Q))))"
    by (simp only: sm)
  \<comment> \<open>\<^bold>\<open>\<open>simp only:\<close> with the three named rewrites, not a plain \<open>simp\<close>.\<close> A full \<open>simp\<close> normalises \<open>[:2, -2:] * p\<close> into
     \<open>smult 2 p + pCons 0 (- smult 2 p)\<close>, after which the goal is no longer about a product. Both sides are driven to
     \<open>smult 2 ([:1, -1:] * p)\<close>.\<close>
  also have "\<dots> = [:2, -2:] * Poly (trunc_list 1 (defl_one_list (carried_left Q)))"
    by (simp only: two_lin mult_smult_left mult_smult_right)
  finally show ?thesis .
qed

lemma defl_fired_right_factor:
  assumes ne: "0 < length Q" and mid: "carried_right Q ! 0 = 0"
  shows "Poly (carried_right Q)
       = [:0, -2:] * Poly (trunc_list 1 (map uminus (tl (carried_right Q))))"
proof -
  have ev0: "\<forall>y \<in> set (tl (carried_right Q)). (2::int) dvd y"
    by (rule defl_right_child_all_even[OF ne mid])
  have ev: "\<forall>y \<in> set (map uminus (tl (carried_right Q))). (2::int) dvd y"
    using ev0 by auto
  have dbl: "map ((*) 2) (trunc_list 1 (map uminus (tl (carried_right Q))))
           = map uminus (tl (carried_right Q))"
    by (rule trunc_list_1_exact[OF ev])
  have neg: "Poly (map uminus (tl (carried_right Q))) = - Poly (tl (carried_right Q))"
    by (rule defl_Poly_map_uminus)
  have sm: "Poly (tl (carried_right Q))
          = smult (-2) (Poly (trunc_list 1 (map uminus (tl (carried_right Q)))))"
  proof -
    have "Poly (map uminus (tl (carried_right Q)))
        = smult 2 (Poly (trunc_list 1 (map uminus (tl (carried_right Q)))))"
      by (subst dbl[symmetric]) (rule Poly_map_double)
    thus ?thesis using neg by simp
  qed
  have "Poly (carried_right Q) = [:0, 1:] * Poly (tl (carried_right Q))"
    by (rule defl_right_child_exact[OF ne mid])
  also have "\<dots> = [:0, 1:] * smult (-2) (Poly (trunc_list 1 (map uminus (tl (carried_right Q)))))"
    by (simp only: sm)
  also have "\<dots> = [:0, -2:] * Poly (trunc_list 1 (map uminus (tl (carried_right Q))))"
    by (simp only: two_x mult_smult_left mult_smult_right)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>What the factorisations buy, in the two forms the invariant asks for.\<close> Divisibility is
  immediate; the root clause is the one that matters, and it says the shed root sits at a
  local-frame ENDPOINT -- \<open>x = 1\<close> for the left child, \<open>x = 0\<close> for the right. So no root
  strictly inside the local \<open>(0, 1)\<close> moves, which is exactly the hypothesis
  @{thm [source] defl_invar_left} / @{thm [source] defl_invar_right} consume one tier up.\<close>

lemma defl_fired_left_dvd:
  assumes ne: "0 < length Q" and mid: "carried_right Q ! 0 = 0"
  shows "Poly (trunc_list 1 (defl_one_list (carried_left Q))) dvd Poly (carried_left Q)"
  by (subst defl_fired_left_factor[OF ne mid]) (rule dvd_triv_right)

lemma defl_fired_right_dvd:
  assumes ne: "0 < length Q" and mid: "carried_right Q ! 0 = 0"
  shows "Poly (trunc_list 1 (map uminus (tl (carried_right Q)))) dvd Poly (carried_right Q)"
  by (subst defl_fired_right_factor[OF ne mid]) (rule dvd_triv_right)

lemma defl_fired_left_roots:
  assumes ne: "0 < length Q" and mid: "carried_right Q ! 0 = 0"
  shows "(poly (map_poly real_of_int (Poly (carried_left Q))) x = 0)
       = (x = 1 \<or> poly (map_poly real_of_int
             (Poly (trunc_list 1 (defl_one_list (carried_left Q))))) x = 0)"
proof -
  have "poly (map_poly real_of_int (Poly (carried_left Q))) x
      = poly (map_poly real_of_int
            ([:2, -2:] * Poly (trunc_list 1 (defl_one_list (carried_left Q))))) x"
    by (simp only: defl_fired_left_factor[OF ne mid])
  also have "\<dots> = poly (map_poly real_of_int [:2, -2:]) x
                 * poly (map_poly real_of_int
                       (Poly (trunc_list 1 (defl_one_list (carried_left Q))))) x"
    by (simp only: of_int_poly_hom.hom_mult poly_mult)
  also have "\<dots> = (2 - 2 * x) * poly (map_poly real_of_int
                       (Poly (trunc_list 1 (defl_one_list (carried_left Q))))) x"
    by simp
  finally show ?thesis by auto
qed

lemma defl_fired_right_roots:
  assumes ne: "0 < length Q" and mid: "carried_right Q ! 0 = 0"
  shows "(poly (map_poly real_of_int (Poly (carried_right Q))) x = 0)
       = (x = 0 \<or> poly (map_poly real_of_int
             (Poly (trunc_list 1 (map uminus (tl (carried_right Q)))))) x = 0)"
proof -
  have "poly (map_poly real_of_int (Poly (carried_right Q))) x
      = poly (map_poly real_of_int
            ([:0, -2:] * Poly (trunc_list 1 (map uminus (tl (carried_right Q)))))) x"
    by (simp only: defl_fired_right_factor[OF ne mid])
  also have "\<dots> = poly (map_poly real_of_int [:0, -2:]) x
                 * poly (map_poly real_of_int
                       (Poly (trunc_list 1 (map uminus (tl (carried_right Q)))))) x"
    by (simp only: of_int_poly_hom.hom_mult poly_mult)
  also have "\<dots> = (- 2 * x) * poly (map_poly real_of_int
                       (Poly (trunc_list 1 (map uminus (tl (carried_right Q)))))) x"
    by simp
  finally show ?thesis by auto
qed

section \<open>The fired children satisfy the node relation\<close>

text \<open>Divisibility is the factorisation read as a cofactor; the root clause holds because the only root the shed
  removes lies at a local-frame endpoint (\<open>t = 1\<close> for the left child, \<open>t = 0\<close> for the right), and
  @{const defl_node_rel} quantifies over the open \<open>(0, 1)\<close>, which excludes both. So deflation does not change the node's
  Descartes count, which is taken over that open local interval, and the count may be read off the deflated
  polynomial.\<close>

theorem defl_fired_left_node_rel:
  assumes ne: "0 < length Q" and mid: "carried_right Q ! 0 = 0"
  shows "defl_node_rel (carried_left Q) (trunc_list 1 (defl_one_list (carried_left Q)))"
  unfolding defl_node_rel_def
proof (intro conjI allI impI)
  show "Poly (trunc_list 1 (defl_one_list (carried_left Q))) dvd Poly (carried_left Q)"
    by (rule defl_fired_left_dvd[OF ne mid])
next
  fix t :: real
  assume t0: "0 < t" and t1: "t < 1"
  \<comment> \<open>\<open>t \<noteq> 1\<close> is what kills the shed factor's own root; it is the ONLY thing the box
     hypotheses are used for.\<close>
  show "(poly (map_poly real_of_int (Poly (carried_left Q))) t = 0)
      = (poly (map_poly real_of_int
            (Poly (trunc_list 1 (defl_one_list (carried_left Q))))) t = 0)"
    using defl_fired_left_roots[OF ne mid, of t] t1 by auto
qed

theorem defl_fired_right_node_rel:
  assumes ne: "0 < length Q" and mid: "carried_right Q ! 0 = 0"
  shows "defl_node_rel (carried_right Q)
           (trunc_list 1 (map uminus (tl (carried_right Q))))"
  unfolding defl_node_rel_def
proof (intro conjI allI impI)
  show "Poly (trunc_list 1 (map uminus (tl (carried_right Q)))) dvd Poly (carried_right Q)"
    by (rule defl_fired_right_dvd[OF ne mid])
next
  fix t :: real
  assume t0: "0 < t" and t1: "t < 1"
  show "(poly (map_poly real_of_int (Poly (carried_right Q))) t = 0)
      = (poly (map_poly real_of_int
            (Poly (trunc_list 1 (map uminus (tl (carried_right Q)))))) t = 0)"
    using defl_fired_right_roots[OF ne mid, of t] t0 by auto
qed

text \<open>\<^bold>\<open>And the NON-firing case is the identity\<close>, which is what makes
  @{const defl_children_monadic}'s \<open>\<not> fire\<close> branch a pure \<open>RETURN\<close> at the proof level as
  well as at the code level: nothing to re-establish, by @{thm [source] defl_node_rel_refl}.

  \<^bold>\<open>Two corollaries with Isar case proofs, not one with a \<open>cases\<close>-then-\<open>simp_all\<close>.\<close>
  A \<open>lemma\<close> with two \<open>shows\<close> gives \<open>cases\<close> only the FIRST goal, so the second arrives at
  \<open>simp_all\<close> still carrying its \<open>if\<close> as an implication and the supplied facts do not close it.
  The failure reads as the facts not applying, which is not what is wrong.\<close>

corollary defl_children_node_rel_left:
  assumes ne: "0 < length Q" and mid: "carried_right Q ! 0 = 0"
  shows "defl_node_rel (carried_left Q)
           (if fire then trunc_list 1 (defl_one_list (carried_left Q)) else carried_left Q)"
proof (cases fire)
  case True
  thus ?thesis using defl_fired_left_node_rel[OF ne mid] by simp
next
  case False
  thus ?thesis using defl_node_rel_refl by simp
qed

corollary defl_children_node_rel_right:
  assumes ne: "0 < length Q" and mid: "carried_right Q ! 0 = 0"
  shows "defl_node_rel (carried_right Q)
           (if fire then trunc_list 1 (map uminus (tl (carried_right Q)))
            else carried_right Q)"
proof (cases fire)
  case True
  thus ?thesis using defl_fired_right_node_rel[OF ne mid] by simp
next
  case False
  thus ?thesis using defl_node_rel_refl by simp
qed

text \<open>\<^bold>\<open>Transitivity, for the path from a node to a descendant.\<close> The loop re-deflates at every
  firing node on a path, so the coupling's clause has to compose -- and it does, because both
  conjuncts do: divisibility is transitive, and two agreements on the open local interval
  compose to one.\<close>

lemma defl_node_rel_trans:
  assumes "defl_node_rel a b" and "defl_node_rel b c"
  shows "defl_node_rel a c"
  using assms unfolding defl_node_rel_def by (auto elim: dvd_trans)

section \<open>Ingredients of the child-build transport\<close>

text \<open>\<^bold>\<open>The retruncation preserves the frame against its OWN input, at either admissible
  guard.\<close> Under \<open>gex\<close> the guard handed to @{const carried_retrunc_mop} inside
  @{const defl_split_children_monadic} is \<open>0\<close> or \<open>\<ge> 2\<^sup>4\<^sup>2\<close> and nothing else --
  @{const truncate_child_guards_mop} returns \<open>(g, g)\<close> on both exact branches, and the
  lock override is the literal \<open>2\<^sup>4\<^sup>2\<close>. Splitting once here keeps that case analysis out of the
  composite proof, where it would otherwise multiply with the fire cases.

  The input is the DEFLATED child, a concrete list, so it is its own exact frame
  (@{thm [source] node_frame_exact}) and no hypothesis about it is needed beyond non-emptiness
  and the word bound.\<close>

lemma defl_SPEC_conj:
  assumes "m \<le> SPEC A" and "m \<le> SPEC B"
  shows "m \<le> SPEC (\<lambda>x. A x \<and> B x)"
  using assms by (auto simp: pw_le_iff refine_pw_simps)

lemma defl_retrunc_frame_any:
  assumes gin_ex: "gin = 0 \<or> 4398046511104 \<le> gin"
    and ne: "0 < length child"
    and lb: "length child + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>The length equation is handed over EXPLICITLY\<close>, as on the \<open>_gate\<close> variant and for the
       same reason: consumers meet \<open>length ql \<le> length Q\<close> on the retrunc OUTPUT, @{const node_frame}
       is opaque, and a \<open>dest:\<close> rule at the closer rewrites the equation the WRONG way and stalls.\<close>
  shows "carried_retrunc_mop child gin \<le> SPEC (\<lambda>(ys, g'). node_frame child ys g'
           \<and> length ys = length child
           \<and> g' \<le> max gin 1
           \<and> (4398046511104 \<le> gin \<longrightarrow> g' = gin \<and> ys = child))"
proof (cases "gin = 0")
  case True
  have fr: "node_frame child child gin" using True by (simp add: node_frame_exact)
  have gle: "gin \<le> 4398046511104" using True by simp
  have lk: "4398046511104 \<le> gin \<longrightarrow> child = child" by simp
  have A: "carried_retrunc_mop child gin \<le> SPEC (\<lambda>(ys, g'). node_frame child ys g')"
    by (rule order_trans[OF cdlr_retrunc_child[OF fr lb gle lk]]) auto
  have B: "carried_retrunc_mop child gin \<le> SPEC (\<lambda>(ys, g'). g' \<le> max gin 1)"
    by (rule cdlr_retrunc_child_gbound)
  show ?thesis
    by (rule order_trans[OF defl_SPEC_conj[OF A B]])
       (auto simp: True dest: cdlr_node_frame_len)
next
  case False
  hence lockg: "4398046511104 \<le> gin" using gin_ex by simp
  show ?thesis
    by (rule order_trans[OF cdlr_retrunc_child_lock_frame[OF lockg refl ne lb]]) auto
qed


text \<open>\<^bold>\<open>And the shape the split step actually calls it at\<close>, which is the one worth feeding to
  \<open>refine_vcg\<close>: the guard is \<open>if fired \<and> lockok then 2\<^sup>4\<^sup>2 else g\<close>, and under \<open>gex\<close> the three
  reachable cases (\<open>g = 0\<close> unlocked, \<open>g \<ge> 2\<^sup>4\<^sup>2\<close> unlocked, and the lock override) collapse to one
  conclusion. \<^bold>\<open>The TRICHOTOMY conjunct \<open>g' \<le> 1 \<or> 2\<^sup>4\<^sup>2 \<le> g'\<close> is the one the coupling's budget
  clause needs\<close> and \<open>g' \<le> max g 2\<^sup>4\<^sup>2\<close> alone does not give it: at \<open>g = 0\<close> the lock override
  returns \<open>2\<^sup>4\<^sup>2\<close> exactly, which is inside \<open>max g 2\<^sup>4\<^sup>2\<close> but is NOT below the child's budget
  \<open>(k + 2) * length rp\<close> -- so without the trichotomy the coupling's disjunction cannot be
  decided at all.\<close>

lemma defl_retrunc_frame_gate:
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g"
    and ne: "0 < length child"
    and lb: "length child + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_retrunc_mop child (if b then 4398046511104 else g)
       \<le> SPEC (\<lambda>(ys, g'). node_frame child ys g'
             \<and> length ys = length child
             \<and> g' \<le> max g 4398046511104
             \<and> (g' \<le> 1 \<or> 4398046511104 \<le> g')
             \<and> (4398046511104 \<le> g' \<longrightarrow> ys = child))"
proof -
  have gin_ex: "(if b then 4398046511104 else g) = 0
      \<or> 4398046511104 \<le> (if b then 4398046511104 else g)"
    using gex by simp
  \<comment> \<open>\<^bold>\<open>The length equation is passed explicitly\<close>, although it follows from the frame: the split step's closers meet
     \<open>length ql \<le> length Q\<close> on the re-truncation output, and @{const node_frame} is opaque, so a \<open>simp\<close> with only the frame
     cannot take that step, and the fallback \<open>auto\<close> case-splits the length arithmetic against the fire dichotomy
     without finishing.\<close>
  show ?thesis
    by (rule order_trans[OF defl_retrunc_frame_any[OF gin_ex ne lb]])
       (use gex in \<open>auto simp: max_def dest: cdlr_node_frame_len split: if_splits\<close>)
qed

text \<open>\<^bold>\<open>The fire signal, read as a statement about the COEFFICIENT rather than about the
  polynomial.\<close> Under \<open>gex\<close> @{const truncate_mid_decide_monadic} is a bare
  \<open>RETURN (if 0 < mids \<or> mids < 0 then 0 else 1)\<close>, so it never returns the escalate sentinel
  and never reads \<open>len\<close>. Stating the outcome as \<open>carried_right Q ! 0 = 0\<close> -- not as
  \<open>poly \<dots> (1/2) = 0\<close> -- is what lets the split step feed
  @{thm [source] defl_fired_left_node_rel} directly; the polynomial form is one rewrite away by
  @{thm [source] carried_right_nth0_zero_iff} and is recovered where the caller wants it.\<close>

lemma defl_decide_fire_iff:
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g"
    and mids_eq: "mids = sgn (carried_right Q ! 0)"
  shows "truncate_mid_decide_monadic g len mids midbl
       \<le> SPEC (\<lambda>code. code \<noteq> 2 \<and> ((code = 1) = (carried_right Q ! 0 = 0)))"
  unfolding truncate_mid_decide_monadic_def
  using gex mids_eq by (auto simp: sgn_if split: if_splits)

text \<open>\<^bold>\<open>And the child guards collapse on both exact branches.\<close> Kept as its own \<open>\<le> SPEC\<close> fact
  so the composite never has to unfold @{const truncate_child_guards_mop}'s five-way cascade --
  unfolding it inline lets \<open>simp\<close> distribute the cascade through the continuation, which is the
  \<open>mid_guard_mop\<close> trap recorded at @{thm [source] truncate_mid_decide_agrees}.\<close>

lemma defl_child_guards_exact:
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g"
  shows "truncate_child_guards_mop g len \<le> SPEC (\<lambda>r. r = (g, g))"
  unfolding truncate_child_guards_mop_def using gex by auto

section \<open>The child-build transport\<close>

text \<open>\<^bold>\<open>The deflating twin of \<open>truncate_children_mid_agrees\<close>\<close>, and the shape is deliberately
  the same so that \<open>defl_branch_split_monadic\<close>'s arm lemmas can be the classic ones with one
  fed rule swapped: that branch has literally the same tail as
  @{const hybrid_branch_split_monadic}, only its child build differs.

  \<^bold>\<open>What changes in the conclusion, and why it must.\<close> The classic contract concludes
  \<open>node_frame (carried_left X) ql gl\<close> -- the stored child frames the EXACT child. After a shed
  that is false: the child frames the DEFLATED exact child instead. So the exact object is
  existentially quantified and tied back to \<open>carried_left X\<close> by @{const defl_node_rel}, exactly
  as in @{const defl_trunc_coupling}. Setting \<open>XL := carried_left X\<close> on a non-firing node
  recovers the classic conjunct.

  \<open>3 \<le> length Q\<close> is the caller's gate (\<open>defl_branch_split_monadic\<close> tests \<open>3 \<le> len\<close>), and it
  is load-bearing rather than cosmetic: the right child is \<open>tl\<close> of its parent, so at
  \<open>length Q = 1\<close> it would be EMPTY and the retruncation's own non-emptiness premise fails.\<close>

theorem defl_split_children_agrees:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and Qlen3: "3 \<le> length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the three word bounds @{thm [source] carried_left_right_skip_right_correct} takes: the op's two ASSERTs and the
       ramp's \<open>kb\<close>.\<close>
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
  shows "defl_split_children_monadic g len lockok Q
      \<le> SPEC (\<lambda>(ql, gl, qr, gr, fired, rz).
          (\<exists>XL. node_frame XL ql gl \<and> defl_node_rel (carried_left X) XL
                \<and> (4398046511104 \<le> gl \<longrightarrow> ql = XL)) \<and>
          (\<not> rz \<longrightarrow> (\<exists>XR. node_frame XR qr gr \<and> defl_node_rel (carried_right X) XR
                \<and> (4398046511104 \<le> gr \<longrightarrow> qr = XR))) \<and>
          (rz \<longrightarrow> carried_descartes_count (carried_right X) = 0 \<and> \<not> fired) \<and>
          gl \<le> max g 4398046511104 \<and> gr \<le> max g 4398046511104 \<and>
          (gl \<le> 1 \<or> 4398046511104 \<le> gl) \<and>
          (gr \<le> 1 \<or> 4398046511104 \<le> gr) \<and>
          0 < length ql \<and> length ql \<le> length Q \<and>
          0 < length qr \<and> length qr \<le> length Q \<and>
          (fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0) \<and>
          (\<not> fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0))"
proof -
  have Qne: "0 < length Q" using Qlen3 by linarith
  have QX: "Q = X"
  proof (cases "g = 0")
    case True
    have "X = Q" using frame True unfolding node_frame_def by simp
    thus ?thesis by (rule sym)
  next
    case False
    thus ?thesis using gex lock by simp
  qed
  have lb_l: "length (carried_left Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lb_r: "length (carried_right Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    using Qbound by simp_all
  have rne: "0 < length (carried_right Q)" using Qne by simp
  have lne: "0 < length (carried_left Q)" using Qne by simp
  have rneL: "carried_right Q \<noteq> []"
    using rne length_greater_0_conv[of "carried_right Q"] by blast
  have lneL: "carried_left Q \<noteq> []"
    using lne length_greater_0_conv[of "carried_left Q"] by blast
  have gg: "truncate_child_guards_mop g len = RETURN (g, g)"
    unfolding truncate_child_guards_mop_def using gex by auto
  have midpoly: "(carried_right Q ! 0 = 0)
      = (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0)"
    using carried_right_nth0_zero_iff[OF Qne] QX by simp
  have nrL: "carried_right Q ! 0 = 0 \<Longrightarrow>
      defl_node_rel (carried_left X) (trunc_list 1 (defl_one_list (carried_left Q)))"
    using defl_fired_left_node_rel[OF Qne] QX by simp
  have nrR: "carried_right Q ! 0 = 0 \<Longrightarrow>
      defl_node_rel (carried_right X) (trunc_list 1 (map uminus (tl (carried_right Q))))"
    using defl_fired_right_node_rel[OF Qne] QX by simp
  have nrLid: "defl_node_rel (carried_left X) (carried_left Q)"
    and nrRid: "defl_node_rel (carried_right X) (carried_right Q)"
    using QX by (simp_all add: defl_node_rel_refl)
  have lenfL: "length (trunc_list 1 (defl_one_list (carried_left Q))) = length Q - 1"
    and lenfR: "length (trunc_list 1 (map uminus (tl (carried_right Q)))) = length Q - 1"
    by (simp_all add: length_defl_one_list)
  have posL: "0 < length (trunc_list 1 (defl_one_list (carried_left Q)))"
    using lenfL Qlen3 by linarith
  have posR: "0 < length (trunc_list 1 (map uminus (tl (carried_right Q))))"
    using lenfR Qlen3 by linarith
  have posLL: "trunc_list 1 (defl_one_list (carried_left Q)) \<noteq> []"
    using posL length_greater_0_conv[of "trunc_list 1 (defl_one_list (carried_left Q))"]
    by blast
  have posRL: "trunc_list 1 (map uminus (tl (carried_right Q))) \<noteq> []"
    using posR length_greater_0_conv[of "trunc_list 1 (map uminus (tl (carried_right Q)))"]
    by blast
  have childspec: "defl_children_monadic fire (carried_left Q) (carried_right Q)
      \<le> SPEC (\<lambda>(ql', qr', fired).
            (fired = fire
             \<and> (fire \<longrightarrow> ql' = trunc_list 1 (defl_one_list (carried_left Q))
                          \<and> qr' = trunc_list 1 (map uminus (tl (carried_right Q))))
             \<and> (\<not> fire \<longrightarrow> ql' = carried_left Q \<and> qr' = carried_right Q))
            \<and> 0 < length ql' \<and> 0 < length qr'
            \<and> length ql' + 1 < max_snat LENGTH(gmp_poly_len)
            \<and> length qr' + 1 < max_snat LENGTH(gmp_poly_len))" for fire
    apply (rule SPEC_cons_rule[OF defl_children_monadic_correct[OF lneL rneL lb_l lb_r]])
    using Qlen3 Qbound posL posR lneL rneL posLL posRL
    by (auto simp: length_defl_one_list)
  \<comment> \<open>\<^bold>\<open>On \<open>rz\<close> the tail is deterministic.\<close> The interlock gives \<open>qr ! 0 \<noteq> 0\<close> for the stub \<open>[carried_right Q ! 0]\<close>, so under
     \<open>gex\<close> the decide returns \<open>0\<close> and the deflation takes its non-firing \<open>RETURN\<close>. Rewriting both away before the VCG
     leaves only the bit-length read and the two re-truncations; given as \<open>\<le> SPEC\<close> facts instead, the fire case split
     would produce many goals over raw tuple variables.\<close>
  have dec0: "mids \<noteq> 0 \<Longrightarrow> truncate_mid_decide_monadic g len mids midbl = RETURN 0"
    for mids :: int and midbl
    unfolding truncate_mid_decide_monadic_def using gex by (auto simp: linorder_neq_iff)
  have children0: "ql \<noteq> [] \<Longrightarrow> qr \<noteq> [] \<Longrightarrow>
      length ql + 1 < max_snat LENGTH(gmp_poly_len) \<Longrightarrow>
      length qr + 1 < max_snat LENGTH(gmp_poly_len) \<Longrightarrow>
      defl_children_monadic False ql qr = RETURN (ql, qr, False)" for ql qr
    unfolding defl_children_monadic_def by simp
  \<comment> \<open>and the FIRING decide, for the \<open>\<not> rz\<close> branch's own split on \<open>qr ! 0\<close>.\<close>
  have dec1: "truncate_mid_decide_monadic g len 0 midbl = RETURN 1" for midbl
    unfolding truncate_mid_decide_monadic_def using gex by auto
  show ?thesis
    unfolding defl_split_children_monadic_def defl_split_children_tail_monadic_def
      defl_children_rz_monadic_def PR_CONST_def
      poly_coeff_sgn_monadic_def poly_coeff_bitlen2_monadic_def
    using Qne Qbound Qbound2 dep
    apply (simp add: gg)
    apply (rule carried_left_right_skip_right_bind[OF Qne Qbound2 dep kb])
    subgoal for r rz
      apply (cases rz)
      \<comment> \<open>\<open>rz\<close>: the stub branch, decided before the VCG.\<close>
      subgoal
        apply (simp add: lb_l lneL dec0 children0 sgn_0_0)
        apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
            defl_retrunc_frame_any[OF gex, THEN order_trans])
        \<comment> \<open>18 small goals over a SIX-tuple equation; destructure, then close. The left witness is
           the undeflated child itself (\<open>Q = X\<close> under \<open>gex\<close>), and the right existential is
           vacuous: the tuple pins \<open>rz = True\<close>.\<close>
        apply (all \<open>clarsimp?\<close>)
        apply (all \<open>((insert Qbound, simp); fail)?\<close>)
        apply (all \<open>((rule exI[where x = "carried_left Q"], insert nrLid gex QX,
                      auto simp: max_def); fail)?\<close>)
        apply (all \<open>((insert QX gex midpoly, auto simp: max_def); fail)?\<close>)
        done
      \<comment> \<open>\<open>\<not> rz\<close>: the classic children. \<^bold>\<open>Split on the fire BEFORE the VCG\<close>, as the \<open>rz\<close> branch
         does: fed the decide as a disjunctive \<open>\<le> SPEC\<close>, the closers become very slow.\<close>
      subgoal
        apply (simp add: lb_l lb_r rne lne)
        apply (cases "carried_right Q ! 0 = 0")
        \<comment> \<open>fires: the decide says \<open>1\<close>, both children are the deflated ones.\<close>
        subgoal
          apply (simp add: dec1 lb_l lb_r lneL rneL)
          apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
              childspec[THEN order_trans]
              defl_retrunc_frame_gate[OF gex, THEN order_trans])
          apply (all \<open>clarsimp?\<close>)
          apply (all \<open>((insert Qlen3 Qbound lenfL lenfR posL posR, simp); fail)?\<close>)
          \<comment> \<open>three survivors: the two witnesses are the DEFLATED children the gate framed, and
             the mid-root fact. Witnesses are spelled \<open>Suc 0\<close>, the form the goal carries.\<close>
          apply (all \<open>((rule exI[where x = "trunc_list (Suc 0) (defl_one_list (carried_left Q))"],
                        insert nrL[unfolded One_nat_def], blast); fail)?\<close>)
          apply (all \<open>((rule exI[where x = "trunc_list (Suc 0) (map uminus (tl (carried_right Q)))"],
                        insert nrR[unfolded One_nat_def], blast); fail)?\<close>)
          apply (all \<open>((insert midpoly, simp); fail)?\<close>)
          done
        \<comment> \<open>does not fire: exactly the \<open>rz\<close> recipe, with the right child really built.\<close>
        subgoal
          apply (simp add: lb_l lb_r lneL rneL dec0 children0 sgn_0_0)
          apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
              defl_retrunc_frame_any[OF gex, THEN order_trans])
          apply (all \<open>clarsimp?\<close>)
          apply (all \<open>((insert Qbound, simp); fail)?\<close>)
          apply (all \<open>((rule exI[where x = "carried_left Q"], insert nrLid gex QX,
                        auto simp: max_def); fail)?\<close>)
          apply (all \<open>((rule exI[where x = "carried_right Q"], insert nrRid gex QX,
                        auto simp: max_def); fail)?\<close>)
          apply (all \<open>((insert QX gex midpoly, auto simp: max_def); fail)?\<close>)
          done
        done
      done
    done
qed


section \<open>The deflating payload bound, and its two suppliers\<close>

text \<open>\<^bold>\<open>The identity that turns a bare exact object into a \<open>carried_init_same_den\<close>\<close>,
  so that @{thm [source] hybrid_split_child_count_mono} applies at the node's OWN frame.\<close>

lemma defl_cisd_id: "carried_init_same_den 0 1 1 X = X"
  by (simp add: carried_init_same_den_def)

text \<open>\<^bold>\<open>The two child maps do not RAISE the Descartes count\<close> --- this is the deflating
  side's \<open>mono\<close> --- the classic one is stated between a child's INIT and its parent's INIT,
  and a deflated node has no init to be stated against.\<close>

lemma defl_child_count_mono:
  assumes ne: "0 < length X"
  shows "carried_descartes_count (carried_left X) \<le> carried_descartes_count X"
    and "carried_descartes_count (carried_right X) \<le> carried_descartes_count X"
proof -
  have lr: "(0::int) < 1" by simp
  show "carried_descartes_count (carried_left X) \<le> carried_descartes_count X"
    using hybrid_split_child_count_mono(1)[where k = 0, OF lr ne]
          carried_left_right_reconstruct(1)[of 0 0 1 X] defl_cisd_id
    by simp
  show "carried_descartes_count (carried_right X) \<le> carried_descartes_count X"
    using hybrid_split_child_count_mono(2)[where k = 0, OF lr ne]
          carried_left_right_reconstruct(2)[of 0 0 1 X] defl_cisd_id
    by simp
qed

text \<open>\<^bold>\<open>The re-truncation gate, strengthened\<close> with the clause the payload transfer needs.
  @{thm [source] defl_retrunc_frame_gate} gives \<open>g' \<le> max g 2\<^sup>4\<^sup>2\<close> and the trichotomy; the payload additionally needs that a
  child guard strictly above the lock literal can only be the parent's own guard passed through: the lock override returns
  the literal exactly, and it carries payload zero.\<close>

lemma defl_retrunc_frame_gate_pay:
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g"
    and ne: "0 < length child"
    and lb: "length child + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_retrunc_mop child (if b then 4398046511104 else g)
       \<le> SPEC (\<lambda>(ys, g'). node_frame child ys g'
             \<and> length ys = length child
             \<and> g' \<le> max g 4398046511104
             \<and> (g' \<le> 1 \<or> 4398046511104 \<le> g')
             \<and> (g' \<le> 4398046511104 \<or> g' = g)
             \<and> (b \<longrightarrow> g' \<le> 4398046511104)
             \<and> (4398046511104 \<le> g' \<longrightarrow> ys = child))"
proof -
  have gin_ex: "(if b then 4398046511104 else g) = 0
      \<or> 4398046511104 \<le> (if b then 4398046511104 else g)"
    using gex by simp
  show ?thesis
    by (rule order_trans[OF defl_retrunc_frame_any[OF gin_ex ne lb]])
       (use gex in \<open>auto simp: max_def dest: cdlr_node_frame_len split: if_splits\<close>)
qed

subsection \<open>The guard/child facts the payload transfer needs\<close>

text \<open>\<^bold>\<open>A separate small contract, not a strengthening of @{thm [source] defl_split_children_agrees}.\<close> Inside that
  lemma's two existentials the payload conjunct would make its witness-choosing \<open>auto\<close> search without finishing. So the
  scalar facts are their own \<open>\<le> SPEC\<close>, joined at the consumer by @{thm [source] defl_SPEC_conj}, where the witness is
  already fixed by the other contract.

  \<^bold>\<open>What it says.\<close> A child guard strictly above the lock literal can only be the parent's own guard passed through to a
  child that was neither shed nor truncated: the lock override returns the literal exactly (so it is excluded), the
  re-truncation either keeps its input guard or resets to \<open>\<le> 1\<close>, and a guard at or above the lock leaves the polynomial
  alone. \<open>lockok\<close> is a necessary hypothesis: without it a shed child can inherit the parent's locked guard, and a shed
  child's Descartes count is not bounded by its parent's.\<close>

text \<open>\<^bold>\<open>The three deterministic steps\<close> that let each children contract decide its branch before the VCG (see
  @{thm [source] defl_split_children_agrees}): under \<open>gex\<close> the decide is a \<open>RETURN\<close> of the sign test, and the
  non-firing deflation returns its operands.\<close>
lemma defl_decide_nz:
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g" and nz: "mids \<noteq> 0"
  shows "truncate_mid_decide_monadic g len mids midbl = RETURN 0"
  unfolding truncate_mid_decide_monadic_def using gex nz by (auto simp: linorder_neq_iff)

lemma defl_decide_z:
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g"
  shows "truncate_mid_decide_monadic g len 0 midbl = RETURN 1"
  unfolding truncate_mid_decide_monadic_def using gex by auto

lemma defl_children_nofire:
  assumes "ql \<noteq> []" and "qr \<noteq> []"
    and "length ql + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length qr + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "defl_children_monadic False ql qr = RETURN (ql, qr, False)"
  unfolding defl_children_monadic_def using assms by simp

lemma defl_split_children_gpay:
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g"
    and lok: "lockok"
    and Qlen3: "3 \<le> length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the three word bounds of @{thm [source] defl_split_children_agrees}.\<close>
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
  \<comment> \<open>on \<open>rz\<close> the right child is the stub, so \<open>qr = carried_right Q\<close> is claimed on \<open>\<not> rz\<close> only. The guard half holds on
     both branches, since the stub is re-truncated at the parent's guard.\<close>
  shows "defl_split_children_monadic g len lockok Q
      \<le> SPEC (\<lambda>(ql, gl, qr, gr, fired, rz).
          (4398046511104 < gl \<longrightarrow> ql = carried_left Q \<and> gl = g) \<and>
          (4398046511104 < gr \<longrightarrow> (\<not> rz \<longrightarrow> qr = carried_right Q) \<and> gr = g))"
proof -
  have Qne: "0 < length Q" using Qlen3 by linarith
  have lb_l: "length (carried_left Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lb_r: "length (carried_right Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    using Qbound by simp_all
  have rne: "0 < length (carried_right Q)" using Qne by simp
  have lne: "0 < length (carried_left Q)" using Qne by simp
  have rneL: "carried_right Q \<noteq> []"
    using rne length_greater_0_conv[of "carried_right Q"] by blast
  have lneL: "carried_left Q \<noteq> []"
    using lne length_greater_0_conv[of "carried_left Q"] by blast
  have lenfL: "length (trunc_list 1 (defl_one_list (carried_left Q))) = length Q - 1"
    and lenfR: "length (trunc_list 1 (map uminus (tl (carried_right Q)))) = length Q - 1"
    by (simp_all add: length_defl_one_list)
  have posL: "0 < length (trunc_list 1 (defl_one_list (carried_left Q)))"
    using lenfL Qlen3 by linarith
  have posR: "0 < length (trunc_list 1 (map uminus (tl (carried_right Q))))"
    using lenfR Qlen3 by linarith
  have posLL: "trunc_list 1 (defl_one_list (carried_left Q)) \<noteq> []"
    using posL length_greater_0_conv[of "trunc_list 1 (defl_one_list (carried_left Q))"]
    by blast
  have posRL: "trunc_list 1 (map uminus (tl (carried_right Q))) \<noteq> []"
    using posR length_greater_0_conv[of "trunc_list 1 (map uminus (tl (carried_right Q)))"]
    by blast
  have gg: "truncate_child_guards_mop g len = RETURN (g, g)"
    unfolding truncate_child_guards_mop_def using gex by auto
  have childspec: "defl_children_monadic fire (carried_left Q) (carried_right Q)
      \<le> SPEC (\<lambda>(ql', qr', fired).
            (fired = fire
             \<and> (fire \<longrightarrow> ql' = trunc_list 1 (defl_one_list (carried_left Q))
                          \<and> qr' = trunc_list 1 (map uminus (tl (carried_right Q))))
             \<and> (\<not> fire \<longrightarrow> ql' = carried_left Q \<and> qr' = carried_right Q))
            \<and> 0 < length ql' \<and> 0 < length qr'
            \<and> length ql' + 1 < max_snat LENGTH(gmp_poly_len)
            \<and> length qr' + 1 < max_snat LENGTH(gmp_poly_len))" for fire
    apply (rule SPEC_cons_rule[OF defl_children_monadic_correct[OF lneL rneL lb_l lb_r]])
    using Qlen3 Qbound posL posR lneL rneL posLL posRL
    by (auto simp: length_defl_one_list)
  \<comment> \<open>the retrunc gate at a NON-firing node, where its guard has simplified to the literal \<open>g\<close>.\<close>
  have gate0: "carried_retrunc_mop child g
      \<le> SPEC (\<lambda>(ys, g'). node_frame child ys g'
             \<and> length ys = length child
             \<and> g' \<le> max g 4398046511104
             \<and> (g' \<le> 1 \<or> 4398046511104 \<le> g')
             \<and> (g' \<le> 4398046511104 \<or> g' = g)
             \<and> (4398046511104 \<le> g' \<longrightarrow> ys = child))"
    if "0 < length child" and "length child + 1 < max_snat LENGTH(gmp_poly_len)" for child
    using defl_retrunc_frame_gate_pay[OF gex that, where b = False] by simp
  show ?thesis
    unfolding defl_split_children_monadic_def defl_split_children_tail_monadic_def
      defl_children_rz_monadic_def PR_CONST_def
      poly_coeff_sgn_monadic_def poly_coeff_bitlen2_monadic_def
    using Qne Qbound Qbound2 dep
    apply (simp add: gg)
    apply (rule carried_left_right_skip_right_bind[OF Qne Qbound2 dep kb])
    subgoal for r rz
      apply (cases rz)
      \<comment> \<open>\<open>rz\<close>: the stub branch --- no fire, both guards pass through the plain gate.\<close>
      subgoal
        apply (simp add: lb_l lneL defl_decide_nz[OF gex] defl_children_nofire sgn_0_0)
        apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans] gate0[THEN order_trans])
        apply (all \<open>clarsimp?\<close>)
        apply (all \<open>((insert Qbound, simp); fail)?\<close>)
        apply (all \<open>((insert gex, auto simp: max_def); fail)?\<close>)
        done
      subgoal
        apply (simp add: lb_l lb_r rne lne)
        apply (cases "carried_right Q ! 0 = 0")
        \<comment> \<open>fires: \<open>lockok\<close> sends both guards to the lock literal, so both clauses are vacuous.\<close>
        subgoal
          apply (simp add: defl_decide_z[OF gex] lb_l lb_r lneL rneL)
          apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
              childspec[THEN order_trans]
              defl_retrunc_frame_gate_pay[OF gex, THEN order_trans])
          apply (all \<open>clarsimp?\<close>)
          apply (all \<open>((insert Qlen3 Qbound lenfL lenfR posL posR, simp); fail)?\<close>)
          apply (all \<open>((insert lok, auto); fail)?\<close>)
          done
        \<comment> \<open>does not fire: the plain gate, as on \<open>rz\<close>, with the right child really built.\<close>
        subgoal
          apply (simp add: lb_l lb_r lneL rneL defl_decide_nz[OF gex] defl_children_nofire sgn_0_0)
          apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans] gate0[THEN order_trans])
          apply (all \<open>clarsimp?\<close>)
          apply (all \<open>((insert Qbound, simp); fail)?\<close>)
          apply (all \<open>((insert gex, auto simp: max_def); fail)?\<close>)
          done
        done
      done
    done
qed




text \<open>\<^bold>\<open>The two TWINS of the contract above\<close> -- the bind form and the DECOMPOSED form, for
  exactly the reason @{thm [source] hybrid_split_children_classic_gbind} records:
  \<open>refine_vcg\<close> produces the decomposed shape whenever the prefix sits under an outer bind (it
  has already split \<open>m \<bind> rest \<le> SPEC \<Phi>\<close> into \<open>m \<le> SPEC (\<lambda>x. rest x \<le> SPEC \<Phi>)\<close>), and the
  bind form then has no match. \<^bold>\<open>Supply BOTH to \<open>refine_vcg\<close>\<close>; do not try to convert one into
  the other.

  \<^bold>\<open>The continuation takes the two exact objects as EXTRA parameters\<close>, and that is the only
  structural difference from the classic twins. They are the existential witnesses of
  @{thm [source] defl_split_children_agrees}; \<open>clarsimp\<close> eliminates the \<open>\<exists>\<close> in the antecedent
  and hands them to \<open>cont\<close> as fresh variables. This is the whole content of the relaxation:
  the arm lemma gets to NAME the deflated exact child, which is precisely the object
  @{const defl_trunc_coupling} quantifies over -- so the arm step can re-establish the coupling
  without ever having to produce that witness itself.\<close>

text \<open>\<^bold>\<open>The right ghost, on both branches.\<close> The contract gives the right child's exact object only on \<open>\<not> rz\<close>, as
  \<open>\<not> rz \<longrightarrow> (\<exists>XR. \<dots>)\<close>; the variants still hand \<open>cont\<close> a named \<open>XR\<close>, with its facts guarded by the same \<open>\<not> rz\<close>. This
  elimination bridges the two shapes (on \<open>rz\<close> any witness will do, since the guard leaves it unconstrained).\<close>
lemma defl_ex_right_cases:
  assumes "\<not> rz \<longrightarrow> (\<exists>XR. P XR)"
  obtains XR where "\<not> rz \<longrightarrow> P XR"
  using assms by blast

lemma defl_split_children_gbind:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and Qlen3: "3 \<le> length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and cont: "\<And>XL XR ql gl qr gr fired rz.
        \<lbrakk>node_frame XL ql gl; defl_node_rel (carried_left X) XL;
          4398046511104 \<le> gl \<longrightarrow> ql = XL;
          \<not> rz \<longrightarrow> node_frame XR qr gr \<and> defl_node_rel (carried_right X) XR \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = XR);
          rz \<longrightarrow> carried_descartes_count (carried_right X) = 0 \<and> \<not> fired;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          gl \<le> 1 \<or> 4398046511104 \<le> gl; gr \<le> 1 \<or> 4398046511104 \<le> gr;
          0 < length ql; length ql \<le> length Q;
          0 < length qr; length qr \<le> length Q;
          fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          \<not> fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0\<rbrakk>
        \<Longrightarrow> f ql gl qr gr fired rz \<le> SPEC \<Phi>"
  shows "(doN { (ql, gl, qr, gr, fired, rz) \<leftarrow> defl_split_children_monadic g len lockok Q;
               f ql gl qr gr fired rz })
       \<le> SPEC \<Phi>"
  apply (refine_vcg defl_split_children_agrees[
        OF frame lock gex Qlen3 Qbound Qbound2 dep kb, THEN order_trans])
  apply clarsimp
  apply (erule defl_ex_right_cases)
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done

lemma defl_split_children_gbind_decomp:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and Qlen3: "3 \<le> length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and cont: "\<And>XL XR ql gl qr gr fired rz.
        \<lbrakk>node_frame XL ql gl; defl_node_rel (carried_left X) XL;
          4398046511104 \<le> gl \<longrightarrow> ql = XL;
          \<not> rz \<longrightarrow> node_frame XR qr gr \<and> defl_node_rel (carried_right X) XR \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = XR);
          rz \<longrightarrow> carried_descartes_count (carried_right X) = 0 \<and> \<not> fired;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          gl \<le> 1 \<or> 4398046511104 \<le> gl; gr \<le> 1 \<or> 4398046511104 \<le> gr;
          0 < length ql; length ql \<le> length Q;
          0 < length qr; length qr \<le> length Q;
          fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          \<not> fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0\<rbrakk>
        \<Longrightarrow> f ql gl qr gr fired rz \<le> SPEC \<Phi>"
  shows "defl_split_children_monadic g len lockok Q
       \<le> SPEC (\<lambda>x. (case x of (ql, gl, qr, gr, fired, rz) \<Rightarrow> f ql gl qr gr fired rz)
             \<le> SPEC \<Phi>)"
  apply (refine_vcg defl_split_children_agrees[
        OF frame lock gex Qlen3 Qbound Qbound2 dep kb, THEN order_trans])
  apply clarsimp
  apply (erule defl_ex_right_cases)
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done


section \<open>The \<open>gbind\<close> variants that also pass the child payload to the continuation\<close>

text \<open>\<^bold>\<open>Where the payload transfer is done\<close>, once, rather than at each of the two coupling lemmas.
  @{thm [source] defl_split_children_gpay} is joined to the contract by @{thm [source] defl_SPEC_conj} (both are \<open>\<le> SPEC\<close>
  over the same op), and the derivation then runs with the existential witness already fixed by the contract.

  \<^bold>\<open>The derivation, in three steps.\<close> Assume \<open>2\<^sup>4\<^sup>2 + 2 \<le> gl\<close>. Then \<open>2\<^sup>4\<^sup>2 < gl\<close>, so \<open>gpay\<close> gives \<open>ql = carried_left Q\<close> and
  \<open>gl = g\<close>; the contract's lock clause \<open>2\<^sup>4\<^sup>2 \<le> gl \<longrightarrow> ql = XL\<close> fixes the ghost to that child; and
  @{thm [source] defl_child_count_mono} carries the parent's payload down to it. Under \<open>gex\<close>, \<open>Q = X\<close>, so \<open>carried_left Q\<close> is
  the exact left child. The right payload is claimed on \<open>\<not> rz\<close> only, which is where \<open>gpay\<close> gives \<open>qr = carried_right Q\<close>.\<close>

lemma defl_split_children_gbind_pay:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and lok: "lockok"
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    and Qlen3: "3 \<le> length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and cont: "\<And>XL XR ql gl qr gr fired rz.
        \<lbrakk>node_frame XL ql gl; defl_node_rel (carried_left X) XL;
          4398046511104 \<le> gl \<longrightarrow> ql = XL;
          \<not> rz \<longrightarrow> node_frame XR qr gr \<and> defl_node_rel (carried_right X) XR \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = XR);
          rz \<longrightarrow> carried_descartes_count (carried_right X) = 0 \<and> \<not> fired;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          gl \<le> 1 \<or> 4398046511104 \<le> gl; gr \<le> 1 \<or> 4398046511104 \<le> gr;
          0 < length ql; length ql \<le> length Q;
          0 < length qr; length qr \<le> length Q;
          4398046511106 \<le> gl \<longrightarrow> carried_descartes_count XL \<le> gl - 4398046511104;
          \<not> rz \<longrightarrow> 4398046511106 \<le> gr \<longrightarrow> carried_descartes_count XR \<le> gr - 4398046511104;
          fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          \<not> fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0\<rbrakk>
        \<Longrightarrow> f ql gl qr gr fired rz \<le> SPEC \<Phi>"
  shows "(doN { (ql, gl, qr, gr, fired, rz) \<leftarrow> defl_split_children_monadic g len lockok Q;
               f ql gl qr gr fired rz })
       \<le> SPEC \<Phi>"
proof -
  have QX: "Q = X"
  proof (cases "g = 0")
    case True
    have "X = Q" using frame True unfolding node_frame_def by simp
    thus ?thesis by (rule sym)
  next
    case False
    thus ?thesis using gex lock by simp
  qed
  have Xlen3: "3 \<le> length X" using Qlen3 QX by simp
  have Xne: "0 < length X" using Xlen3 by linarith
  have monoL: "carried_descartes_count (carried_left X) \<le> carried_descartes_count X"
    and monoR: "carried_descartes_count (carried_right X) \<le> carried_descartes_count X"
    using defl_child_count_mono[OF Xne] by simp_all
  \<comment> \<open>\<^bold>\<open>The payload derivation as two rules.\<close> Each is stated over the three facts it needs, so the closer below is
     \<open>rule\<close> and \<open>assumption\<close>; a blanket \<open>auto\<close> would case-split the goals' extra \<open>rz \<longrightarrow> \<dots>\<close> / \<open>\<not> rz \<longrightarrow> \<dots>\<close> premises.\<close>
  have payL_ok: "4398046511104 < gl \<longrightarrow> XL = carried_left Q \<and> gl = g
      \<Longrightarrow> 4398046511106 \<le> gl \<longrightarrow> carried_descartes_count XL \<le> gl - 4398046511104"
    for XL gl
    using monoL pay QX by auto
  have payR_ok: "4398046511104 < gr \<longrightarrow> (\<not> rz \<longrightarrow> qr = carried_right Q) \<and> gr = g
      \<Longrightarrow> \<not> rz \<longrightarrow> node_frame XR qr gr \<and> defl_node_rel (carried_right X) XR \<and>
                  (4398046511104 \<le> gr \<longrightarrow> qr = XR)
      \<Longrightarrow> \<not> rz \<longrightarrow> 4398046511106 \<le> gr \<longrightarrow> carried_descartes_count XR \<le> gr - 4398046511104"
    for XR qr gr rz
    using monoR pay QX by auto
  show ?thesis
    apply (refine_vcg defl_SPEC_conj[OF
          defl_split_children_agrees[OF frame lock gex Qlen3 Qbound Qbound2 dep kb]
          defl_split_children_gpay[OF gex lok Qlen3 Qbound Qbound2 dep kb], THEN order_trans])
    apply clarsimp
    apply (erule defl_ex_right_cases)
    apply (rule cont)
    \<comment> \<open>STAGED, cheapest first: most goals are the contract's own conjuncts.\<close>
    apply (all \<open>(assumption; fail)?\<close>)
    apply (all \<open>(simp; fail)?\<close>)
    \<comment> \<open>the two payload goals, and only they reach here --- by rule, no search\<close>
    apply (all \<open>((rule payL_ok, assumption) | (rule payR_ok, assumption, assumption); fail)?\<close>)
    done
qed



text \<open>\<^bold>\<open>And the DECOMPOSED twin\<close>, for the reason
  @{thm [source] defl_split_children_gbind_decomp} records: \<open>refine_vcg\<close> produces the decomposed
  shape whenever the prefix sits under an outer bind, and the bind form then has no match.
  Supply BOTH.\<close>

lemma defl_split_children_gbind_decomp_pay:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and lok: "lockok"
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    and Qlen3: "3 \<le> length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and cont: "\<And>XL XR ql gl qr gr fired rz.
        \<lbrakk>node_frame XL ql gl; defl_node_rel (carried_left X) XL;
          4398046511104 \<le> gl \<longrightarrow> ql = XL;
          \<not> rz \<longrightarrow> node_frame XR qr gr \<and> defl_node_rel (carried_right X) XR \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = XR);
          rz \<longrightarrow> carried_descartes_count (carried_right X) = 0 \<and> \<not> fired;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          gl \<le> 1 \<or> 4398046511104 \<le> gl; gr \<le> 1 \<or> 4398046511104 \<le> gr;
          0 < length ql; length ql \<le> length Q;
          0 < length qr; length qr \<le> length Q;
          4398046511106 \<le> gl \<longrightarrow> carried_descartes_count XL \<le> gl - 4398046511104;
          \<not> rz \<longrightarrow> 4398046511106 \<le> gr \<longrightarrow> carried_descartes_count XR \<le> gr - 4398046511104;
          fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          \<not> fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0\<rbrakk>
        \<Longrightarrow> f ql gl qr gr fired rz \<le> SPEC \<Phi>"
  shows "defl_split_children_monadic g len lockok Q
       \<le> SPEC (\<lambda>x. (case x of (ql, gl, qr, gr, fired, rz) \<Rightarrow> f ql gl qr gr fired rz)
             \<le> SPEC \<Phi>)"
proof -
  have QX: "Q = X"
  proof (cases "g = 0")
    case True
    have "X = Q" using frame True unfolding node_frame_def by simp
    thus ?thesis by (rule sym)
  next
    case False
    thus ?thesis using gex lock by simp
  qed
  have Xlen3: "3 \<le> length X" using Qlen3 QX by simp
  have Xne: "0 < length X" using Xlen3 by linarith
  have monoL: "carried_descartes_count (carried_left X) \<le> carried_descartes_count X"
    and monoR: "carried_descartes_count (carried_right X) \<le> carried_descartes_count X"
    using defl_child_count_mono[OF Xne] by simp_all
  have payL_ok: "4398046511104 < gl \<longrightarrow> XL = carried_left Q \<and> gl = g
      \<Longrightarrow> 4398046511106 \<le> gl \<longrightarrow> carried_descartes_count XL \<le> gl - 4398046511104"
    for XL gl
    using monoL pay QX by auto
  have payR_ok: "4398046511104 < gr \<longrightarrow> (\<not> rz \<longrightarrow> qr = carried_right Q) \<and> gr = g
      \<Longrightarrow> \<not> rz \<longrightarrow> node_frame XR qr gr \<and> defl_node_rel (carried_right X) XR \<and>
                  (4398046511104 \<le> gr \<longrightarrow> qr = XR)
      \<Longrightarrow> \<not> rz \<longrightarrow> 4398046511106 \<le> gr \<longrightarrow> carried_descartes_count XR \<le> gr - 4398046511104"
    for XR qr gr rz
    using monoR pay QX by auto
  show ?thesis
    apply (refine_vcg defl_SPEC_conj[OF
          defl_split_children_agrees[OF frame lock gex Qlen3 Qbound Qbound2 dep kb]
          defl_split_children_gpay[OF gex lok Qlen3 Qbound Qbound2 dep kb], THEN order_trans])
    apply clarsimp
    apply (erule defl_ex_right_cases)
    apply (rule cont)
    apply (all \<open>(assumption; fail)?\<close>)
    apply (all \<open>(simp; fail)?\<close>)
    apply (all \<open>((rule payL_ok, assumption) | (rule payR_ok, assumption, assumption); fail)?\<close>)
    done
qed


section \<open>Reading a node's cached count as a statement about roots\<close>

text \<open>\<^bold>\<open>The three facts the reject and accept arms use.\<close> A node's cached class \<open>cs ! i\<close> is @{const hybrid_cs_ok}
  against @{const carried_descartes_count} of the node's own exact polynomial \<open>X\<close>, a local sign-variation count of a
  coefficient list. The arms need a statement about roots, and the route is three steps:

    \<^item> @{thm [source] carried_repr_init}, \<open>carried_repr P 0 1 P\<close> (a list is its own carried representation on the unit box),
      turns the count into \<open>descartes_list_int 0 1 X\<close>;
    \<^item> @{thm [source] descartes_list_int_eq_Bernstein_changes} turns that into \<open>Bernstein_changes (length X - 1) 0 1\<close> of the
      real image;
    \<^item> @{thm [source] Bernstein_changes_0_no_root} / @{thm [source] Bernstein_changes_1_one_root} read the root count off it.

  \<^bold>\<open>Why the local box \<open>(0, 1)\<close> and not the node's real box.\<close> The non-deflating proof works globally, rewriting a node's
  count as \<open>descartes_list_int a b rp\<close> via @{const carried_repr}, because every such node is a carried representation of the
  root list \<open>rp\<close>. A deflated node is not: it is a divisor of one, and the divisor is not an integer polynomial in global
  coordinates. So there is no \<open>rp'\<close> with \<open>carried_repr rp' a b X\<close>.

  \<^bold>\<open>The local route needs no such object\<close>: the count is read against \<open>X\<close> itself on \<open>(0, 1)\<close>, @{const defl_node_rel}
  carries the root statement to the node's carried init on the same \<open>(0, 1)\<close>, and
  @{thm [source] carried_init_same_den_eval_zero_iff} carries it to \<open>P\<^sub>0\<close> on the node's real box. No simulation of
  \<open>newdsc_pol_defl\<close> and no deflating version of the \<open>\<exists>pol\<close> apparatus is needed for the loop.\<close>

lemma defl_local_degree_le:
  "degree (map_poly real_of_int (Poly X) :: real poly) \<le> length X - 1"
proof -
  have "degree (Poly X :: int poly) \<le> length X - 1"
    by (simp add: degree_le coeff_Poly nth_default_beyond)
  thus ?thesis using degree_map_poly_le[of "real_of_int" "Poly X"] by simp
qed

lemma defl_local_count_eq_Bernstein:
  assumes ne: "0 < length X"
  shows "int (carried_descartes_count X)
       = Bernstein_changes (length X - 1) 0 1 (map_poly real_of_int (Poly X) :: real poly)"
proof -
  have c: "carried_descartes_count X = descartes_list_int 0 1 X"
    by (rule carried_repr_count[OF carried_repr_init])
  have b: "int (descartes_list_int (0::rat) 1 X)
      = Bernstein_changes (length X - 1) (of_rat 0) (of_rat 1)
          (map_poly of_int (Poly X) :: real poly)"
    by (rule descartes_list_int_eq_Bernstein_changes[OF ne]) simp
  show ?thesis using c b by simp
qed

text \<open>\<^bold>\<open>Reject\<close>: a zero cached count means the node's own polynomial has no root strictly inside the local box.
  \<open>roots_in\<close> counts with multiplicity, so \<open>= 0\<close> means no roots and needs no squarefreeness, unlike the accept case
  below.\<close>

lemma defl_node_count_zero_no_roots:
  assumes ne: "0 < length X"
    and nz: "(map_poly real_of_int (Poly X) :: real poly) \<noteq> 0"
    and cnt: "carried_descartes_count X = 0"
  shows "roots_in (map_poly real_of_int (Poly X) :: real poly) 0 1 = 0"
proof -
  have v0: "Bernstein_changes (length X - 1) 0 1
              (map_poly real_of_int (Poly X) :: real poly) = 0"
    using defl_local_count_eq_Bernstein[OF ne] cnt by simp
  show ?thesis
    by (rule Bernstein_changes_0_no_root[OF defl_local_degree_le nz _ v0]) simp
qed

text \<open>\<^bold>\<open>Accept\<close>: a cached count of one means exactly one root, with multiplicity, strictly
  inside the local box.\<close>

lemma defl_node_count_one_one_root:
  assumes ne: "0 < length X"
    and nz: "(map_poly real_of_int (Poly X) :: real poly) \<noteq> 0"
    and cnt: "carried_descartes_count X = 1"
  shows "roots_in (map_poly real_of_int (Poly X) :: real poly) 0 1 = 1"
proof -
  have v1: "Bernstein_changes (length X - 1) 0 1
              (map_poly real_of_int (Poly X) :: real poly) = 1"
    using defl_local_count_eq_Bernstein[OF ne] cnt by simp
  show ?thesis
    by (rule Bernstein_changes_1_one_root[OF defl_local_degree_le nz _ v1]) simp
qed



section \<open>The split arm re-establishes the coupling\<close>

text \<open>\<^bold>\<open>Monotonicity of the bit-length word bound.\<close> The classic split arm never needs this:
  every classic child has length EXACTLY \<open>length rp\<close>, so its word bounds are the root's verbatim
  (@{thm [source] hybrid_branch_split_exact_acc}'s "root-anchored bounds"). A DEFLATED child is
  one shorter on the firing branch, so the bounds have to travel DOWN a length, which needs
  \<open>nat_bitlen\<close> to be monotone. It is, and by its own definition: \<open>n < 2 ^ nat_bitlen n\<close> makes
  \<open>nat_bitlen n\<close> one of the exponents \<open>m\<close> is below, so the LEAST such for \<open>m\<close> cannot exceed it.\<close>

lemma defl_nat_bitlen_mono:
  assumes "m \<le> n" shows "nat_bitlen m \<le> nat_bitlen n"
proof -
  have "m < 2 ^ nat_bitlen n" using assms nat_bitlen_lt[of n] by simp
  thus ?thesis unfolding nat_bitlen_def by (rule Least_le)
qed

lemma defl_pb_mono:
  assumes le: "m \<le> n" and pb: "n * nat_bitlen n < N"
  shows "m * nat_bitlen m < N"
proof -
  have "m * nat_bitlen m \<le> n * nat_bitlen n"
    by (rule mult_le_mono[OF le defl_nat_bitlen_mono[OF le]])
  thus ?thesis using pb by simp
qed

subsection \<open>The class bound every child push satisfies\<close>

text \<open>\<^bold>\<open>The suppliers for @{const defl_node_ok}'s last clause\<close>, and they cost nothing: the
  g-guarded count kernel already caps its decisive answer at \<open>3\<close>
  (@{thm [source] carried_descartes_count_g_monadic_le3}) and @{const hybrid_class_of} turns a
  non-decisive one into the literal sentinel \<open>4\<close>, so \<^bold>\<open>every classified child is \<open>\<le> 4\<close>\<close>.

  \<^bold>\<open>Stated separately rather than added to @{thm [source] hybrid_split_pair_state_correct}\<close>,
  which lives in \<open>Hybrid_Keystone\<close> and whose \<open>SPEC\<close> no other consumer needs strengthened.
  Conjoining two \<open>\<le> SPEC\<close> facts about the SAME program is what @{thm [source] defl_SPEC_conj} is
  for, and the split tail below composes them in one \<open>order_trans\<close>.\<close>

lemma defl_count_g_class_le4:
  assumes lbound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length xs * nat_bitlen (length xs) < max_snat LENGTH(gmp_poly_len)"
    and gbound: "g + length xs < max_snat LENGTH(gmp_poly_len)"
  shows "carried_descartes_count_g_monadic xs g
       \<le> SPEC (\<lambda>(cnt, dec). hybrid_class_of dec cnt \<le> 4)"
  using carried_descartes_count_g_monadic_le3[OF lbound pbound gbound]
  by (fastforce simp: pw_le_iff refine_pw_simps hybrid_class_of_def)

lemma defl_classify_prebuilt_le4:
  assumes lbL: "length ql + 1 < max_snat LENGTH(gmp_poly_len)"
    and lbR: "length qr + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbL: "length ql * nat_bitlen (length ql) < max_snat LENGTH(gmp_poly_len)"
    and pbR: "length qr * nat_bitlen (length qr) < max_snat LENGTH(gmp_poly_len)"
    and gbL: "gl + length ql < max_snat LENGTH(gmp_poly_len)"
    and gbR: "gr + length qr < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_classify_prebuilt_monadic qtodo gs ql gl qr gr
       \<le> SPEC (\<lambda>(qtodo', gs', cl, cr). cl \<le> 4 \<and> cr \<le> 4)"
  \<comment> \<open>the word bounds are on the STORED children, not on the frame targets: this lemma says
     nothing about a ghost, so no @{thm [source] cdlr_node_frame_len} bridge is needed.\<close>
  unfolding hybrid_classify_prebuilt_monadic_def hybrid_pcc_result_monadic_def
    PR_CONST_def Let_def
  apply (refine_vcg defl_count_g_class_le4[OF lbL pbL gbL, THEN order_trans]
      defl_count_g_class_le4[OF lbR pbR gbR, THEN order_trans])
  subgoal using qcap by simp
  subgoal using lbL by simp
  subgoal using lbR by simp
  apply (simp add: cdlr_push2_eq[OF qcap] cdlr_append_eq)
  apply (insert gcap, auto simp: pw_le_iff refine_pw_simps)
  done

lemma defl_split_pair_state_le4:
  assumes lbL: "length ql + 1 < max_snat LENGTH(gmp_poly_len)"
    and lbR: "length qr + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbL: "length ql * nat_bitlen (length ql) < max_snat LENGTH(gmp_poly_len)"
    and pbR: "length qr * nat_bitlen (length qr) < max_snat LENGTH(gmp_poly_len)"
    and gbL: "gl + length ql < max_snat LENGTH(gmp_poly_len)"
    and gbR: "gr + length qr < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and scap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kcap: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_split_pair_state_monadic (lns, rns, ks) qtodo es ss cs gs rp
             l_num r_num k e s mid ql gl qr gr
       \<le> SPEC (\<lambda>(todo', qtodo', es', ss', cs', gs', rp').
           \<exists>cl cr. cs' = cs @ [cl, cr] \<and> cl \<le> 4 \<and> cr \<le> 4)"
  \<comment> \<open>the \<open>cs' = cs @ [cl, cr]\<close> conjunct is what lets @{thm [source] defl_SPEC_conj}'s two
     existentials be identified with each other at the call site --- without it the bound would
     be about a pair of numbers nothing ties to the classified children.\<close>
proof -
  have pc: "dyadic_interval_vec_push_children_monadic (lns, rns, ks) l_num r_num k
      \<le> SPEC (\<lambda>todo'. todo' = (lns @ [2 * l_num, l_num + r_num],
                                rns @ [l_num + r_num, 2 * r_num], ks @ [k + 1, k + 1]))"
    by (simp add: cdlr_push_children_eq[OF push kcap])
  show ?thesis
    unfolding hybrid_split_pair_state_monadic_def PR_CONST_def Let_def
    using qcap ecap scap ccap gcap push scap1
    apply (refine_vcg pc[THEN order_trans]
        defl_classify_prebuilt_le4[OF lbL lbR pbL pbR gbL gbR qcap gcap, THEN order_trans]
        dyadic_exp_push2_monadic_spec[THEN order_trans])
    apply (all \<open>(simp add: cdlr_append_eq; fail)?\<close>)
    done
qed

text \<open>\<^bold>\<open>The tail of the split arm, with the two exact children as ordinary variables.\<close> Everything below the child
  build is shared with the non-deflating arm (@{const hybrid_split_pair_state_monadic}), so the new content is that its
  ghosts \<open>XL\<close>/\<open>XR\<close> are instantiated to the deflated exact children rather than to \<open>carried_left X\<close>/\<open>carried_right X\<close>.

  \<^bold>\<open>That instantiation is why this is a separate lemma.\<close> In @{thm [source] hybrid_branch_split_exact_acc} the ghosts are
  fixed with \<open>[where XL = "carried_left X"]\<close> at the call site. Here the exact children are bound by
  \<open>defl_split_children_gbind\<close>'s continuation, so there is no name for a \<open>where\<close> at the outer level, and left to itself
  \<open>refine_vcg\<close> takes the ghost to be the stored child (via @{thm [source] node_frame_exact_any_g}), i.e. the count of a
  possibly truncated polynomial, from which the coupling is unprovable. With the children as variables of this lemma
  they are instantiated by \<open>where\<close>, and at the call site the premises are matched against the continuation's hypotheses
  by \<open>assumption\<close>.\<close>

lemma defl_split_tail_coupling:
  assumes coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and frameL: "node_frame XL ql gl" and frameR: "node_frame XR qr gr"
    \<comment> \<open>\<^bold>\<open>\<open>Suc k\<close>, not \<open>k + 1\<close>.\<close> @{thm [source] defl_node_okI}'s conclusion has the depth as a bare variable, so \<open>rule\<close>
       instantiates it to whatever the goal carries, and @{const hybrid_split_pair_state_monadic} pushes \<open>Suc k\<close>; stated
       as \<open>k + 1\<close> these premises would be a different term and the \<open>OF\<close> would not compose.\<close>
    and nrL: "defl_node_wrel
                (carried_init_same_den (2 * l_num) (2 ^ Suc k) (l_num + r_num) rp) XL"
    and nrR: "defl_node_wrel
                (carried_init_same_den (l_num + r_num) (2 ^ Suc k) (2 * r_num) rp) XR"
    and lockL: "4398046511104 \<le> gl \<longrightarrow> ql = XL"
    and lockR: "4398046511104 \<le> gr \<longrightarrow> qr = XR"
    and budL: "gl \<le> (k + 2) * length rp \<or> 4398046511104 \<le> gl"
    and budR: "gr \<le> (k + 2) * length rp \<or> 4398046511104 \<le> gr"
    and lenL: "length ql \<le> length rp" and lenR: "length qr \<le> length rp"
    \<comment> \<open>\<^bold>\<open>The two children's payload atoms\<close>, in the premise style of \<open>budL\<close>/\<open>budR\<close>. The \<open>_pay\<close> variants pass the first half to
       the arm's continuation; the ceiling half is \<open>gl \<le> max g 2\<^sup>4\<^sup>2\<close> against the parent's own ceiling.\<close>
    and payL: "4398046511106 \<le> gl \<longrightarrow> carried_descartes_count XL \<le> gl - 4398046511104"
    and payR: "4398046511106 \<le> gr \<longrightarrow> carried_descartes_count XR \<le> gr - 4398046511104"
    and ceilL: "gl \<le> 4398046511104 + length rp"
    and ceilR: "gr \<le> 4398046511104 + length rp"
    \<comment> \<open>\<^bold>\<open>The two children's divisibility\<close>, in the premise style of \<open>budL\<close>/\<open>budR\<close>. The arm derives each by
       \<open>defl_child_left_dvd_chain\<close> / \<open>defl_child_right_dvd_chain\<close> from the parent's clause and the contract's
       \<open>defl_node_rel\<close>.\<close>
    and dvdL: "(of_int_poly (Poly XL) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                        (l_num + r_num) rp)) :: real poly)"
    and dvdR: "(of_int_poly (Poly XR) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                        (2 * r_num) rp)) :: real poly)"
    \<comment> \<open>\<^bold>\<open>A direct word bound, NOT \<open>gl \<le> 2\<^sup>4\<^sup>2\<close>.\<close> The gate-open arm calls the split at the
       LOCK-WITH-PAYLOAD guard \<open>2\<^sup>4\<^sup>2 + v\<close>, which is strictly ABOVE \<open>2\<^sup>4\<^sup>2\<close> -- so a premise
       capping the child guard at the literal makes this lemma inapplicable there (the classic
       side hits the same thing and carries \<open>gcap_rp\<close>/\<open>gcap_lock\<close> as two separate instances).
       Bounding \<open>gl + length rp\<close> instead covers both call sites, and it is what
       @{thm [source] hybrid_split_pair_state_correct} actually needs.\<close>
    and glb: "gl + length rp < max_snat LENGTH(gmp_poly_len)"
    and grb: "gr + length rp < max_snat LENGTH(gmp_poly_len)"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kcap: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_split_pair_state_monadic (lns, rns, ks) qtodo es ss cs gs rp
             l_num r_num k e s mid ql gl qr gr
       \<le> SPEC (\<lambda>(todo', qtodo', es', ss', cs', gs', rp').
           defl_trunc_coupling todo' qtodo' cs' gs' rp')"
proof -
  \<comment> \<open>the ghosts' word bounds, travelling DOWN from the root's via the child length bound --
     the step the classic arm gets for free because its children have length \<open>length rp\<close>
     exactly.\<close>
  have lXL: "length XL = length ql" by (rule cdlr_node_frame_len[OF frameL])
  have lXR: "length XR = length qr" by (rule cdlr_node_frame_len[OF frameR])
  have leL: "length XL \<le> length rp" using lXL lenL by simp
  have leR: "length XR \<le> length rp" using lXR lenR by simp
  have lbL: "length XL + 1 < max_snat LENGTH(gmp_poly_len)" using leL rpb by simp
  have lbR: "length XR + 1 < max_snat LENGTH(gmp_poly_len)" using leR rpb by simp
  have pbL: "length XL * nat_bitlen (length XL) < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_pb_mono[OF leL rp_pb])
  have pbR: "length XR * nat_bitlen (length XR) < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_pb_mono[OF leR rp_pb])
  have gbL: "gl + length XL < max_snat LENGTH(gmp_poly_len)" using glb leL by simp
  have gbR: "gr + length XR < max_snat LENGTH(gmp_poly_len)" using grb leR by simp
  have lockL': "4398046511104 \<le> gl \<longrightarrow> XL = ql" using lockL by simp
  have lockR': "4398046511104 \<le> gr \<longrightarrow> XR = qr" using lockR by simp
  \<comment> \<open>the STORED children's own word bounds, for the class-bound supplier --- it speaks about
     \<open>ql\<close>/\<open>qr\<close> rather than about the ghosts, so it cannot reuse \<open>lbL\<close>/\<open>pbL\<close>/\<open>gbL\<close> above.\<close>
  have lbL': "length ql + 1 < max_snat LENGTH(gmp_poly_len)" using lenL rpb by simp
  have lbR': "length qr + 1 < max_snat LENGTH(gmp_poly_len)" using lenR rpb by simp
  have pbL': "length ql * nat_bitlen (length ql) < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_pb_mono[OF lenL rp_pb])
  have pbR': "length qr * nat_bitlen (length qr) < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_pb_mono[OF lenR rp_pb])
  have gbL': "gl + length ql < max_snat LENGTH(gmp_poly_len)" using glb lenL by simp
  have gbR': "gr + length qr < max_snat LENGTH(gmp_poly_len)" using grb lenR by simp
  show ?thesis
    apply (rule order_trans[OF defl_SPEC_conj[OF
        hybrid_split_pair_state_correct[where XL = XL and XR = XR,
          OF frameL frameR lockL' lockR' lbL lbR pbL pbR gbL gbR
             qcap gcap ecap sscap ccap push kcap scap1]
        defl_split_pair_state_le4[OF lbL' lbR' pbL' pbR' gbL' gbR'
             qcap gcap ecap sscap ccap push kcap scap1]]])
    apply clarsimp
    apply (rule defl_trunc_coupling_push[OF coup])
      apply (rule defl_node_okI[OF frameL nrL _ leL _ lockL _ payL ceilL dvdL])
        apply (assumption | simp)
       apply (insert budL, simp)[]
      apply simp
     apply (rule defl_node_okI[OF frameR nrR _ leR _ lockR _ payR ceilR dvdR])
       apply (assumption | simp)
      apply (insert budR, simp)[]
     apply simp
    done
qed


text \<open>\<^bold>\<open>The left-only tail.\<close> When the decide proves the right child empty, the split arm pushes one node through
  @{const hybrid_split_pair_state_left_monadic}. These are the one-child versions of the two lemmas above: the class
  bound, and the coupling push, which is @{thm [source] defl_trunc_coupling_push1} with the left child's
  @{const defl_node_ok}, discharged as in the two-child lemma.\<close>

lemma defl_classify_prebuilt_left_le4:
  assumes lbL: "length ql + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbL: "length ql * nat_bitlen (length ql) < max_snat LENGTH(gmp_poly_len)"
    and gbL: "gl + length ql < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_classify_prebuilt_left_monadic qtodo gs ql gl
       \<le> SPEC (\<lambda>(qtodo', gs', cl, cr). cl \<le> 4)"
proof -
  have qcap1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have gcap1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  show ?thesis
    unfolding hybrid_classify_prebuilt_left_monadic_def hybrid_pcc_result_monadic_def
      poly_vec_push_monadic_def PR_CONST_def Let_def
    apply (refine_vcg defl_count_g_class_le4[OF lbL pbL gbL, THEN order_trans])
    apply (all \<open>((insert qcap1 gcap1 lbL,
                  auto simp: cdlr_append_eq pw_le_iff refine_pw_simps); fail)?\<close>)
    done
qed

lemma defl_split_pair_state_left_le4:
  assumes lbL: "length ql + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbL: "length ql * nat_bitlen (length ql) < max_snat LENGTH(gmp_poly_len)"
    and gbL: "gl + length ql < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and scap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kcap: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_split_pair_state_left_monadic (lns, rns, ks) qtodo es ss cs gs rp
             l_num r_num k e s mid ql gl
       \<le> SPEC (\<lambda>(todo', qtodo', es', ss', cs', gs', rp'). \<exists>cl. cs' = cs @ [cl] \<and> cl \<le> 4)"
proof -
  have push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    using push unfolding dyadic_interval_vec_pushable2_def dyadic_interval_vec_pushable_def
    by simp
  have qcap1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have gcap1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  have ecap1: "length es + 1 < max_snat LENGTH(gmp_poly_len)" using ecap by simp
  have scap1': "length ss + 1 < max_snat LENGTH(gmp_poly_len)" using scap by simp
  have ccap1: "length cs + 1 < max_snat LENGTH(gmp_poly_len)" using ccap by simp
  show ?thesis
    unfolding hybrid_split_pair_state_left_monadic_def PR_CONST_def Let_def
    using qcap1 ecap1 scap1' ccap1 gcap1 push1 scap1
    apply (refine_vcg dyadic_iv_push_left_child_eq[OF push1 kcap, THEN order_trans]
        defl_classify_prebuilt_left_le4[OF lbL pbL gbL qcap gcap, THEN order_trans])
    apply (all \<open>(simp add: cdlr_append_eq; fail)?\<close>)
    done
qed

lemma defl_split_tail_coupling_left:
  assumes coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and frameL: "node_frame XL ql gl"
    and nrL: "defl_node_wrel
                (carried_init_same_den (2 * l_num) (2 ^ Suc k) (l_num + r_num) rp) XL"
    and lockL: "4398046511104 \<le> gl \<longrightarrow> ql = XL"
    and budL: "gl \<le> (k + 2) * length rp \<or> 4398046511104 \<le> gl"
    and lenL: "length ql \<le> length rp"
    and payL: "4398046511106 \<le> gl \<longrightarrow> carried_descartes_count XL \<le> gl - 4398046511104"
    and ceilL: "gl \<le> 4398046511104 + length rp"
    and dvdL: "(of_int_poly (Poly XL) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                        (l_num + r_num) rp)) :: real poly)"
    and glb: "gl + length rp < max_snat LENGTH(gmp_poly_len)"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kcap: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_split_pair_state_left_monadic (lns, rns, ks) qtodo es ss cs gs rp
             l_num r_num k e s mid ql gl
       \<le> SPEC (\<lambda>(todo', qtodo', es', ss', cs', gs', rp').
           defl_trunc_coupling todo' qtodo' cs' gs' rp')"
proof -
  have lXL: "length XL = length ql" by (rule cdlr_node_frame_len[OF frameL])
  have leL: "length XL \<le> length rp" using lXL lenL by simp
  have lbL: "length XL + 1 < max_snat LENGTH(gmp_poly_len)" using leL rpb by simp
  have pbL: "length XL * nat_bitlen (length XL) < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_pb_mono[OF leL rp_pb])
  have gbL: "gl + length XL < max_snat LENGTH(gmp_poly_len)" using glb leL by simp
  have lockL': "4398046511104 \<le> gl \<longrightarrow> XL = ql" using lockL by simp
  have lbL': "length ql + 1 < max_snat LENGTH(gmp_poly_len)" using lenL rpb by simp
  have pbL': "length ql * nat_bitlen (length ql) < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_pb_mono[OF lenL rp_pb])
  have gbL': "gl + length ql < max_snat LENGTH(gmp_poly_len)" using glb lenL by simp
  show ?thesis
    apply (rule order_trans[OF defl_SPEC_conj[OF
        hybrid_split_pair_state_left_correct[where XL = XL,
          OF frameL lockL' lbL pbL gbL qcap gcap ecap sscap ccap push kcap scap1]
        defl_split_pair_state_left_le4[OF lbL' pbL' gbL'
             qcap gcap ecap sscap ccap push kcap scap1]]])
    apply clarsimp
    apply (rule defl_trunc_coupling_push1[OF coup])
    apply (rule defl_node_okI[OF frameL nrL _ leL _ lockL _ payL ceilL dvdL])
      apply (assumption | simp)
     apply (insert budL, simp)[]
    apply simp
    done
qed


text \<open>\<^bold>\<open>The composition the split step performs\<close>, packaged so that the arm proof discharges the tail lemma's per-child
  premise with one \<open>rule\<close>. Three facts meet, in order:

    \<^item> the coupling gives \<open>defl_node_wrel init X\<close>: the popped node's exact polynomial against the init its own \<open>(l, r, k)\<close>
      recomputes from the root;
    \<^item> the congruence pushes that through @{const carried_left}, giving \<open>defl_node_wrel (carried_left init) (carried_left X)\<close>;
    \<^item> the contract gives \<open>defl_node_rel (carried_left X) XL\<close> (the shed, if it fired), which
      @{thm [source] defl_node_wrel_of_rel} weakens into the same relation;

  and @{thm [source] carried_init_child_left} identifies \<open>carried_left init\<close> with the child's own init, which the coupling
  asks about after the push. The middle step has no counterpart in the non-deflating proof, where every node holds its init
  exactly.\<close>

lemma defl_child_wrel_left:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and rel: "defl_node_rel (carried_left X) XL"
  shows "defl_node_wrel (carried_init_same_den (2 * l) (2 ^ Suc k) (l + r) rp) XL"
proof -
  have nzL: "(of_int_poly (Poly (carried_left X)) :: real poly) \<noteq> 0"
    by (rule defl_carried_left_nz[OF defl_node_wrelD_nz[OF wrel]])
  have step: "defl_node_wrel (carried_left X) XL"
    by (rule defl_node_wrel_of_rel[OF rel nzL])
  have cong: "defl_node_wrel (carried_left (carried_init_same_den l (2 ^ k) r rp))
                             (carried_left X)"
    by (rule defl_node_wrel_carried_left[OF wrel])
  have ini: "carried_left (carried_init_same_den l (2 ^ k) r rp)
      = carried_init_same_den (2 * l) (2 ^ Suc k) (l + r) rp"
    using carried_init_child_left[of "2 ^ k" l r rp] by simp
  show ?thesis using defl_node_wrel_trans[OF cong step] ini by simp
qed

lemma defl_child_wrel_right:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and rel: "defl_node_rel (carried_right X) XR"
  shows "defl_node_wrel (carried_init_same_den (l + r) (2 ^ Suc k) (2 * r) rp) XR"
proof -
  have nzR: "(of_int_poly (Poly (carried_right X)) :: real poly) \<noteq> 0"
    by (rule defl_carried_right_nz[OF defl_node_wrelD_nz[OF wrel]])
  have step: "defl_node_wrel (carried_right X) XR"
    by (rule defl_node_wrel_of_rel[OF rel nzR])
  have cong: "defl_node_wrel (carried_right (carried_init_same_den l (2 ^ k) r rp))
                             (carried_right X)"
    by (rule defl_node_wrel_carried_right[OF wrel])
  have ini: "carried_right (carried_init_same_den l (2 ^ k) r rp)
      = carried_init_same_den (l + r) (2 ^ Suc k) (2 * r) rp"
    using carried_init_child_right[of "2 ^ k" l r rp] by simp
  show ?thesis using defl_node_wrel_trans[OF cong step] ini by simp
qed



section \<open>The split arm re-establishes the coupling, end to end\<close>

text \<open>\<^bold>\<open>The exact/locked split arm.\<close> Under \<open>gex\<close> and the gate's \<open>3 \<le> len\<close> the escalate arm of
  @{const defl_branch_split_monadic} is unreachable, so this is the deflating twin of
  @{thm [source] hybrid_branch_split_exact_acc} -- with the CONCLUSION weakened from the state
  result to the coupling, which is all @{const defl_loop_invar} asks the split step for.

  The pieces meet in one \<open>refine_vcg\<close>: @{thm [source] defl_split_children_gbind} (and its
  decomposed twin) hand over the two DEFLATED exact children as continuation parameters,
  @{thm [source] defl_child_wrel_left}/\<open>_right\<close> compose them onto the children's own inits, and
  @{thm [source] defl_split_tail_coupling} pushes the result onto the worklist.\<close>

lemma defl_branch_split_exact_coupling:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    \<comment> \<open>\<^bold>\<open>The popped node's payload atom\<close>, read off @{const defl_node_ok}; the \<open>_pay\<close> variants carry it down to the two
       children.\<close>
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    and gceil: "g \<le> 4398046511104 + length rp"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qlen3: "3 \<le> length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and lenQrp: "length Q \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    \<comment> \<open>\<^bold>\<open>Last\<close>, immediately before \<open>shows\<close>, so that no existing \<open>[OF \<dots>]\<close> position in a caller moves.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
  shows "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (\<lambda>(wl, acc').
           case wl of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
             defl_trunc_coupling todo' qtodo' cs' gs' rp')"
proof -
  have Qne: "0 < length Q" using Qlen3 by linarith
  \<comment> \<open>the children contract's three word bounds, from what this arm carries: \<open>Q\<close> is no longer than \<open>rp\<close>, and \<open>rp\<close> is
     below \<open>2\<^sup>4\<^sup>0\<close>.\<close>
  have Qsmall: "length Q < 1099511627776" using lenQrp rp_small by linarith
  have Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)" by (rule small_len_b2[OF Qsmall])
  have dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)" by (rule small_len_dep[OF Qsmall])
  have kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    using gcap_rp lenQrp max.cobounded1[of g 4398046511104] by linarith
  have pm: "carried_push_mid_monadic (al, ar, ak) l_num r_num k
      \<le> SPEC (\<lambda>a. a = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1]))"
    by (simp add: cdlr_push_mid_eq[OF accpush])
  \<comment> \<open>\<^bold>\<open>The child budget needs a product bound, which linear arithmetic does not find.\<close> The contract gives the
     trichotomy \<open>gl \<le> 1 \<or> 2\<^sup>4\<^sup>2 \<le> gl\<close>, and the coupling asks for \<open>gl \<le> (k + 2) * length rp \<or> 2\<^sup>4\<^sup>2 \<le> gl\<close>. On the left disjunct
     that is \<open>1 \<le> (k+2)*length rp\<close>, true because \<open>rp\<close> is non-empty but a multiplication, so it is supplied by name.\<close>
  have one_le: "1 \<le> (k + 2) * length rp"
  proof -
    have "(1::nat) * 1 \<le> (k + 2) * length rp" using rpne by (intro mult_le_mono) auto
    thus ?thesis by simp
  qed
  \<comment> \<open>\<^bold>\<open>The child ceiling, stated at the atom.\<close> The contract gives \<open>gl \<le> max g 2\<^sup>4\<^sup>2\<close>, and \<open>linarith\<close> treats \<open>max g 2\<^sup>4\<^sup>2\<close> as an
     opaque atom, so \<open>gceil\<close> (about \<open>g\<close>) does not reach it, and the goal would fall through to the budget stage's \<open>auto\<close>.
     The atom is bridged here once.\<close>
  have gmax_ceil: "max g 4398046511104 \<le> 4398046511104 + length rp"
    using gceil by (simp add: max_def)
  \<comment> \<open>\<^bold>\<open>Every arithmetic closer below as a rule.\<close> The release stage puts the whole unguarded contract into each goal,
     and blanket \<open>linarith\<close> stages over those goals are slow. Each rule is proved once, here, in a context holding only the
     fact it needs. The budget rule comes in both spellings of the trichotomy the goals carry (\<open>1\<close> as stated, \<open>Suc 0\<close> once
     simplified).\<close>
  have gl_bound: "x \<le> max g 4398046511104 \<Longrightarrow> x + length rp < max_snat LENGTH(gmp_poly_len)"
    for x using gcap_rp by linarith
  have gl_ceil: "x \<le> max g 4398046511104 \<Longrightarrow> x \<le> 4398046511104 + length rp"
    for x using gmax_ceil by linarith
  have len_rp: "x \<le> length Q \<Longrightarrow> x \<le> length rp" for x using lenQrp by linarith
  have bud_ok: "x \<le> 1 \<or> 4398046511104 \<le> x \<Longrightarrow>
      x \<le> (k + 2) * length rp \<or> 4398046511104 \<le> x" for x
    using one_le by auto
  have bud_ok': "x \<le> Suc 0 \<or> 4398046511104 \<le> x \<Longrightarrow>
      x \<le> (k + 2) * length rp \<or> 4398046511104 \<le> x" for x
    using one_le by auto
  show ?thesis
    unfolding defl_branch_split_monadic_def poly_length_monadic_def PR_CONST_def
    using gex Qlen3 Qne Qbound kcap rpne rpb krp accpush qcap gcap ecap sscap ccap push scap1
    apply (refine_vcg
        defl_split_children_gbind_pay[OF frame lock gex TrueI pay Qlen3 Qbound Qbound2 dep kb]
        defl_split_children_gbind_decomp_pay[OF frame lock gex TrueI pay Qlen3 Qbound Qbound2 dep kb]
        defl_split_tail_coupling[OF coup, THEN order_trans]
        defl_split_tail_coupling_left[OF coup, THEN order_trans]
        pm[THEN order_trans])
    \<comment> \<open>\<^bold>\<open>Release the \<open>\<not> rz\<close>-guarded right-child facts\<close> against the branch's own \<open>\<not> rz\<close> (and the \<open>rz\<close> facts against \<open>rz\<close>),
       so the closers below see plain premises. Each step consumes one implication, so this terminates without search.\<close>
    apply (all \<open>((drule (1) mp)+)?\<close>)
    apply (all \<open>(elim conjE)?\<close>)
    \<comment> \<open>STAGED closers. \<open>assumption\<close> first, because most of the tail lemma's premises are
       literally the continuation's own hypotheses and anything cleverer risks picking a
       DIFFERENT instantiation of the ghost children (the trap
       @{thm [source] defl_split_tail_coupling} exists to avoid).\<close>
    apply (all \<open>(assumption; fail)?\<close>)
    \<comment> \<open>the two per-child compositions, by \<open>rule\<close> so the witness cannot drift\<close>
    apply (all \<open>((rule defl_child_wrel_left[OF wrel], assumption); fail)?\<close>)
    apply (all \<open>((rule defl_child_wrel_right[OF wrel], assumption); fail)?\<close>)
    \<comment> \<open>\<^bold>\<open>The two per-child divisibilities\<close>, placed immediately after their \<open>wrel\<close> counterparts and before any arithmetic
       stage, so that a \<open>dvd\<close> goal does not fall through to \<open>linarith\<close>/\<open>auto\<close>.\<close>
    apply (all \<open>((rule defl_child_left_dvd_chain[OF dvdX], assumption); fail)?\<close>)
    apply (all \<open>((rule defl_child_right_dvd_chain[OF dvdX], assumption); fail)?\<close>)
    \<comment> \<open>the word bound, the ceiling, the length and the budget: one rule each, no search\<close>
    apply (all \<open>((rule gl_bound, assumption); fail)?\<close>)
    apply (all \<open>((rule gl_ceil, assumption); fail)?\<close>)
    apply (all \<open>((rule len_rp, assumption); fail)?\<close>)
    apply (all \<open>((rule bud_ok, assumption) | (rule bud_ok', assumption); fail)?\<close>)
    \<comment> \<open>the ESCALATE arm is unreachable under the gate\<close>
    apply (all \<open>((insert gex Qlen3, simp); fail)?\<close>)
    apply (all \<open>((insert rpb rp_small rp_pb kcap scap1, simp); fail)?\<close>)
    apply (all \<open>(simp; fail)?\<close>)
    done
qed



section \<open>The node's box, over the reals\<close>

text \<open>\<^bold>\<open>Why a real-valued twin of @{thm [source] carried_init_same_den_eval_zero_iff} is needed.\<close>
  That bridge is stated over \<open>\<rat>\<close>, which is enough for the classic chain's uses (midpoints and
  box endpoints are dyadic). The deflating loop's COVERAGE clause quantifies over the real roots
  of \<open>P\<^sub>0\<close>, which are in general irrational, so the \<open>\<rat>\<close> form cannot be instantiated at them at
  all.

  The identity itself is already proven -- @{thm [source] cdlr_Poly_carried_init_same_den_int} is
  a POLYNOMIAL equation over \<open>\<rat>\<close> -- so the real form is obtained by pushing the ring hom
  \<open>real_of_rat\<close> through it, not by redoing the coefficient bookkeeping.\<close>

lemma defl_carried_init_poly_real:
  fixes d :: int
  assumes d0: "d \<noteq> 0"
  shows "(of_int_poly (Poly (carried_init_same_den l d r xs)) :: real poly)
       = smult (real_of_int d ^ (length xs - 1))
           (pcompose (of_int_poly (Poly xs) :: real poly)
             [: real_of_int l / real_of_int d,
                (real_of_int r - real_of_int l) / real_of_int d :])"
proof -
  have "(of_int_poly (Poly (carried_init_same_den l d r xs)) :: real poly)
      = map_poly real_of_rat (map_poly rat_of_int (Poly (carried_init_same_den l d r xs)))"
    by (rule defl_of_int_poly_via_rat)
  also have "\<dots> = map_poly real_of_rat (smult ((rat_of_int d) ^ (length xs - 1))
           (pcompose (map_poly rat_of_int (Poly xs))
             [: rat_of_int l / rat_of_int d,
                (rat_of_int r - rat_of_int l) / rat_of_int d :]))"
    by (simp only: cdlr_Poly_carried_init_same_den_int[OF d0])
  also have "\<dots> = smult (real_of_int d ^ (length xs - 1))
           (pcompose (of_int_poly (Poly xs) :: real poly)
             [: real_of_int l / real_of_int d,
                (real_of_int r - real_of_int l) / real_of_int d :])"
    by (simp add: of_rat_hom.map_poly_hom_smult of_rat_hom.map_poly_pcompose
                  of_rat_hom.map_poly_pCons_hom defl_of_int_poly_via_rat[symmetric]
                  of_rat_divide of_rat_diff of_rat_power)
  finally show ?thesis .
qed

lemma defl_carried_init_eval_real:
  fixes d :: int and t :: real
  assumes d0: "d \<noteq> 0"
  shows "poly (of_int_poly (Poly (carried_init_same_den l d r xs)) :: real poly) t
       = real_of_int d ^ (length xs - 1)
         * poly (of_int_poly (Poly xs) :: real poly)
             ((real_of_int l + (real_of_int r - real_of_int l) * t) / real_of_int d)"
  using defl_carried_init_poly_real[OF d0, of l r xs]
  by (simp add: poly_pcompose add_divide_distrib ac_simps)

text \<open>\<^bold>\<open>(c\<acute>) over \<open>\<real>\<close>\<close>: the node poly vanishes at a LOCAL point iff the ROOT poly vanishes at
  that point's image under the node's own affine map. The \<open>d\<^sup>n\<^sup>-\<^sup>1\<close> factor is nonzero, so the iff is
  exact -- and it is an iff, not an implication, which is what lets the reject arm read
  \<open>no roots\<close> in one direction and the coverage clause read \<open>this root is still somewhere\<close> in the
  other.\<close>

lemma defl_carried_init_zero_iff_real:
  fixes d :: int and t :: real
  assumes d0: "d \<noteq> 0"
  shows "(poly (of_int_poly (Poly (carried_init_same_den l d r xs)) :: real poly) t = 0)
       = (poly (of_int_poly (Poly xs) :: real poly)
            ((real_of_int l + (real_of_int r - real_of_int l) * t) / real_of_int d) = 0)"
  using defl_carried_init_eval_real[OF d0, of l r xs t] d0 by simp



section \<open>From a node's cached count to \<open>P\<^sub>0\<close>'s roots in the node's box\<close>

text \<open>\<^bold>\<open>The transfer, in one step.\<close> A node's polynomial lives in the LOCAL frame and its count is
  taken over the local \<open>(0,1)\<close>; the invariant's coverage clause is about \<open>P\<^sub>0\<close> on the node's real
  box. @{const defl_node_wrel} moves the first to the node's carried init (same local box -- that
  is why the relation was restated locally when the frame-confused draft was corrected), and
  @{thm [source] defl_carried_init_zero_iff_real} moves it from there to \<open>P\<^sub>0\<close> under the node's own
  affine map. Composing them once here keeps every arm from redoing it.\<close>

lemma defl_node_local_to_global:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and t0: "0 < t" and t1: "t < 1"
  shows "(poly (of_int_poly (Poly X) :: real poly) t = 0)
       = (poly (of_int_poly (Poly rp) :: real poly)
            ((real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k) = 0)"
proof -
  have d0: "(2::int) ^ k \<noteq> 0" by simp
  have "(poly (of_int_poly (Poly X) :: real poly) t = 0)
      = (poly (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly) t = 0)"
    using defl_node_wrelD_roots[OF wrel t0 t1] by simp
  also have "\<dots> = (poly (of_int_poly (Poly rp) :: real poly)
        ((real_of_int l + (real_of_int r - real_of_int l) * t) / real_of_int (2 ^ k)) = 0)"
    by (rule defl_carried_init_zero_iff_real[OF d0])
  finally show ?thesis by simp
qed

text \<open>\<^bold>\<open>The reject arm's fact.\<close> A zero cached count means \<open>P\<^sub>0\<close> has no root strictly inside the node's box, which licenses
  @{const hybrid_branch_zero_monadic} to discard the box without losing a root, and so keeps @{const defl_pending_covers}
  true across the reject step. The cached-count clause of the coupling exists for this.\<close>

lemma defl_node_box_no_roots:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and cnt: "carried_descartes_count X = 0"
    and ne: "0 < length X"
    and t0: "0 < t" and t1: "t < 1"
  shows "poly (of_int_poly (Poly rp) :: real poly)
           ((real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k) \<noteq> 0"
proof -
  have nz: "(of_int_poly (Poly X) :: real poly) \<noteq> 0" by (rule defl_node_wrelD_nz[OF wrel])
  have r0: "roots_in (of_int_poly (Poly X) :: real poly) 0 1 = 0"
    by (rule defl_node_count_zero_no_roots[OF ne nz cnt])
  have "proots_within (of_int_poly (Poly X) :: real poly) {x. 0 < x \<and> x < 1} = {}"
    by (rule proots_count_0_imp_empty[OF r0[unfolded roots_in_def] nz])
  hence "poly (of_int_poly (Poly X) :: real poly) t \<noteq> 0"
    using t0 t1 by (auto simp: proots_within_def)
  thus ?thesis using defl_node_local_to_global[OF wrel t0 t1] by simp
qed



section \<open>The accept arm's fact\<close>

text \<open>\<^bold>\<open>Multiplicity, without divisibility.\<close> @{const roots_in} is a @{const proots_count}, i.e. with multiplicity, so
  agreeing root sets do not by themselves transfer a count; @{thm [source] defl_invar_roots_in_eq} needs \<open>Q dvd P0\<close> to get
  \<open>square_free Q\<close>. Here the gap closes from the other side: going down from a count of one to a cardinality of one is free
  (every order at a root is at least \<open>1\<close>, so a sum of them equal to \<open>1\<close> forces a singleton). Going back up needs
  squarefreeness only for \<open>P\<^sub>0\<close>, which is a caller obligation. So the node's own polynomial never has to be shown
  squarefree.\<close>

lemma defl_proots_count_1_card:
  fixes p :: "real poly"
  assumes nz: "p \<noteq> 0" and c1: "proots_count p S = 1"
  shows "card (proots_within p S) = 1"
proof -
  have fin: "finite (proots_within p S)"
    using nz poly_roots_finite[of p]
    by (auto intro: finite_subset[of _ "{x. poly p x = 0}"] simp: proots_within_def)
  have ne: "proots_within p S \<noteq> {}"
  proof
    assume "proots_within p S = {}"
    hence "proots_count p S = 0" by (simp add: proots_count_def)
    thus False using c1 by simp
  qed
  have "card (proots_within p S) = (\<Sum>z\<in>proots_within p S. 1)" by simp
  also have "\<dots> \<le> (\<Sum>z\<in>proots_within p S. order z p)"
    \<comment> \<open>\<open>Suc_le_eq\<close>: the goal arrives as \<open>Suc 0 \<le> order z p\<close> and
       @{thm [source] order_gt_0_iff} is stated with \<open><\<close>, so without it \<open>simp\<close> never connects
       the two.\<close>
    by (rule sum_mono)
       (use nz in \<open>auto simp: proots_within_def order_gt_0_iff Suc_le_eq\<close>)
  also have "\<dots> = proots_count p S" by (simp add: proots_count_def)
  finally have le1: "card (proots_within p S) \<le> 1" using c1 by simp
  have "card (proots_within p S) \<noteq> 0" using ne fin by simp
  thus ?thesis using le1 by linarith
qed

text \<open>\<^bold>\<open>The node's affine map, and that it carries the local open box onto the real one.\<close> Stated
  about an ARBITRARY pair of polynomials related by the agreement, so it can serve both the
  accept arm and (with the same instance) any later coverage bookkeeping.\<close>

lemma defl_box_affine_inj:
  fixes l r :: int and k :: nat
  assumes lr: "l < r"
  shows "inj_on (\<lambda>t::real. (real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k)
           {t. 0 < t \<and> t < 1}"
proof (rule inj_onI)
  fix x y :: real
  assume eq: "(real_of_int l + (real_of_int r - real_of_int l) * x) / 2 ^ k
        = (real_of_int l + (real_of_int r - real_of_int l) * y) / 2 ^ k"
  have w: "real_of_int r - real_of_int l \<noteq> 0" using lr by simp
  from eq have "real_of_int l + (real_of_int r - real_of_int l) * x
              = real_of_int l + (real_of_int r - real_of_int l) * y"
    by (simp add: divide_cancel_right)
  hence "(real_of_int r - real_of_int l) * x = (real_of_int r - real_of_int l) * y" by simp
  thus "x = y" using w by simp
qed

lemma defl_box_proots_image:
  fixes l r :: int and k :: nat
  assumes lr: "l < r"
    and agree: "\<And>t::real. 0 < t \<Longrightarrow> t < 1 \<Longrightarrow>
        (poly PX t = 0)
          = (poly P0 ((real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k) = 0)"
  shows "proots_within P0 {y. real_of_int l / 2 ^ k < y \<and> y < real_of_int r / 2 ^ k}
       = (\<lambda>t::real. (real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k)
           ` proots_within PX {t. 0 < t \<and> t < 1}"
proof (rule set_eqI, rule iffI)
  have w: "real_of_int r - real_of_int l > 0" using lr by simp
  fix y :: real
  assume "y \<in> proots_within P0 {y. real_of_int l / 2 ^ k < y \<and> y < real_of_int r / 2 ^ k}"
  hence ylo: "real_of_int l / 2 ^ k < y" and yhi: "y < real_of_int r / 2 ^ k"
    and yz: "poly P0 y = 0" by (auto simp: proots_within_def)
  define t where "t = (y * 2 ^ k - real_of_int l) / (real_of_int r - real_of_int l)"
  have t0: "0 < t" using ylo w unfolding t_def by (simp add: field_simps)
  have t1: "t < 1" using yhi w unfolding t_def by (simp add: field_simps)
  have phi: "(real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k = y"
    using w unfolding t_def by (simp add: field_simps)
  have "poly PX t = 0" using agree[OF t0 t1] phi yz by simp
  hence "t \<in> proots_within PX {t. 0 < t \<and> t < 1}"
    using t0 t1 by (simp add: proots_within_def)
  thus "y \<in> (\<lambda>t::real. (real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k)
           ` proots_within PX {t. 0 < t \<and> t < 1}"
    using phi by (auto simp: image_iff)
next
  have w: "real_of_int r - real_of_int l > 0" using lr by simp
  fix y :: real
  assume "y \<in> (\<lambda>t::real. (real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k)
           ` proots_within PX {t. 0 < t \<and> t < 1}"
  then obtain t where t: "t \<in> proots_within PX {t. 0 < t \<and> t < 1}"
    and phi: "(real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k = y" by auto
  have t0: "0 < t" and t1: "t < 1" and tz: "poly PX t = 0"
    using t by (auto simp: proots_within_def)
  have "poly P0 y = 0" using agree[OF t0 t1] phi tz by simp
  \<comment> \<open>\<^bold>\<open>The two box bounds are PRODUCT facts\<close> -- \<open>y\<cdot>2\<^sup>k = l + (r-l)\<cdot>t\<close> with \<open>0 < t < 1\<close> -- so a
     linear-arithmetic closer cannot get them on its own. Supply the two products' signs, then
     the divisions come off with @{thm [source] pos_divide_less_eq} /
     @{thm [source] pos_less_divide_eq}.\<close>
  moreover have y2k: "y * 2 ^ k = real_of_int l + (real_of_int r - real_of_int l) * t"
    using phi by (simp add: field_simps)
  moreover have pos: "0 < (real_of_int r - real_of_int l) * t" using w t0 by simp
  moreover have lt: "(real_of_int r - real_of_int l) * t < real_of_int r - real_of_int l"
    using w t1 by simp
  moreover have "real_of_int l / 2 ^ k < y"
    using y2k pos by (simp add: pos_divide_less_eq)
  moreover have "y < real_of_int r / 2 ^ k"
    using y2k lt by (simp add: pos_less_divide_eq)
  ultimately show "y \<in> proots_within P0
      {y. real_of_int l / 2 ^ k < y \<and> y < real_of_int r / 2 ^ k}"
    by (simp add: proots_within_def)
qed



text \<open>\<^bold>\<open>The accept arm's fact.\<close> A cached count of one means \<open>P\<^sub>0\<close> has exactly one root, with multiplicity, strictly
  inside the node's box: the box isolates a root, which is what @{const hybrid_branch_one_monadic} pushes onto \<open>acc\<close> and
  what @{const defl_acc_isolates} asserts. \<open>square_free P\<^sub>0\<close> is a hypothesis, discharged by the caller's precondition.\<close>

lemma defl_node_box_one_root:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and cnt: "carried_descartes_count X = 1"
    and ne: "0 < length X"
    and sf: "square_free (of_int_poly (Poly rp) :: real poly)"
    and lr: "l < r"
  shows "roots_in (of_int_poly (Poly rp) :: real poly)
           (real_of_int l / 2 ^ k) (real_of_int r / 2 ^ k) = 1"
proof -
  have nzX: "(of_int_poly (Poly X) :: real poly) \<noteq> 0" by (rule defl_node_wrelD_nz[OF wrel])
  have r1: "roots_in (of_int_poly (Poly X) :: real poly) 0 1 = 1"
    by (rule defl_node_count_one_one_root[OF ne nzX cnt])
  have cX: "card (proots_within (of_int_poly (Poly X) :: real poly) {t. 0 < t \<and> t < 1}) = 1"
    by (rule defl_proots_count_1_card[OF nzX r1[unfolded roots_in_def]])
  have img: "proots_within (of_int_poly (Poly rp) :: real poly)
        {y. real_of_int l / 2 ^ k < y \<and> y < real_of_int r / 2 ^ k}
      = (\<lambda>t::real. (real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k)
          ` proots_within (of_int_poly (Poly X) :: real poly) {t. 0 < t \<and> t < 1}"
    by (rule defl_box_proots_image[OF lr]) (rule defl_node_local_to_global[OF wrel])
  have sub: "proots_within (of_int_poly (Poly X) :: real poly) {t. 0 < t \<and> t < 1}
      \<subseteq> {t. 0 < t \<and> t < 1}" by (auto simp: proots_within_def)
  have cP: "card (proots_within (of_int_poly (Poly rp) :: real poly)
        {y. real_of_int l / 2 ^ k < y \<and> y < real_of_int r / 2 ^ k}) = 1"
    unfolding img
    using card_image[OF inj_on_subset[OF defl_box_affine_inj[OF lr] sub]] cX by simp
  have rsf: "rsquarefree (of_int_poly (Poly rp) :: real poly)"
    using sf by (rule square_free_rsquarefree)
  show ?thesis
    unfolding roots_in_def
    using proots_count_eq_card_of_rsquarefree[OF rsf] cP by simp
qed

text \<open>\<^bold>\<open>And in the shape @{const defl_acc_isolates} reads\<close>: the non-degenerate branch of
  @{const dsc_pair_ok}. The degenerate branch is the MID-ROOT leaf the split arm pushes, and it
  is a different fact -- \<open>P\<^sub>0\<close> vanishing AT the midpoint -- so the two are kept apart.\<close>

lemma defl_node_box_pair_ok:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and cnt: "carried_descartes_count X = 1"
    and ne: "0 < length X"
    and sf: "square_free (of_int_poly (Poly rp) :: real poly)"
    and lr: "l < r"
  shows "dsc_pair_ok (of_int_poly (Poly rp) :: real poly)
           (real_of_int l / 2 ^ k, real_of_int r / 2 ^ k)"
proof -
  have box: "real_of_int l / 2 ^ k < real_of_int r / 2 ^ k"
    using lr by (simp add: divide_strict_right_mono)
  show ?thesis
    unfolding dsc_pair_ok_def
    using box defl_node_box_one_root[OF wrel cnt ne sf lr] by simp
qed



section \<open>The midpoint-root leaf the split arm accumulates\<close>

text \<open>\<^bold>\<open>The degenerate branch of @{const dsc_pair_ok}, and the one type conversion the chain needs.\<close>
  The child-build contract reports the fire as \<open>poly (of_int_poly (Poly X)) (1/2) = 0\<close> over \<open>\<rat>\<close>
  -- that is the frame the midpoint test lives in. Everything downstream of
  @{const defl_node_wrel} is over \<open>\<real>\<close>, because the coverage clause has to talk about irrational
  roots. The two meet at a RATIONAL point, so the conversion is pointwise and needs no polynomial
  identity: a hom applied to a root is a root of the mapped polynomial.\<close>

lemma defl_rat_root_to_real:
  fixes p :: "int poly" and x :: rat
  assumes "poly (map_poly rat_of_int p) x = 0"
  shows "poly (of_int_poly p :: real poly) (real_of_rat x) = 0"
proof -
  have "poly (of_int_poly p :: real poly) (real_of_rat x)
      = poly (map_poly real_of_rat (map_poly rat_of_int p)) (real_of_rat x)"
    by (simp add: defl_of_int_poly_via_rat)
  also have "\<dots> = real_of_rat (poly (map_poly rat_of_int p) x)"
    by (simp add: of_rat_hom.poly_map_poly)
  finally show ?thesis using assms by simp
qed

text \<open>\<^bold>\<open>And the mid root, in GLOBAL coordinates.\<close> The local \<open>1/2\<close> is the box midpoint
  \<open>(l + r) / 2\<^sup>k\<^sup>+\<^sup>1\<close>, which is exactly the pair @{const carried_push_mid_monadic} appends to
  \<open>acc\<close> -- so this is the fact that makes that push satisfy @{const defl_acc_isolates} through
  \<open>dsc_pair_ok\<close>'s degenerate branch.\<close>

lemma defl_mid_root_global:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and fire: "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0"
  shows "poly (of_int_poly (Poly rp) :: real poly)
           ((real_of_int l + real_of_int r) / 2 ^ Suc k) = 0"
proof -
  have h: "poly (of_int_poly (Poly X) :: real poly) (1 / 2) = 0"
    using defl_rat_root_to_real[OF fire] by (simp add: of_rat_divide)
  have iff: "(poly (of_int_poly (Poly X) :: real poly) (1 / 2) = 0)
      = (poly (of_int_poly (Poly rp) :: real poly)
           ((real_of_int l + (real_of_int r - real_of_int l) * (1 / 2)) / 2 ^ k) = 0)"
    by (rule defl_node_local_to_global[OF wrel]) auto
  have mid: "(real_of_int l + (real_of_int r - real_of_int l) * (1 / 2)) / 2 ^ k
      = (real_of_int l + real_of_int r) / 2 ^ Suc k"
    by (simp add: field_simps)
  show ?thesis using h iff mid by simp
qed

text \<open>\<^bold>\<open>The rational/real bridge, as an IFF.\<close> @{thm [source] defl_rat_root_to_real} is the
  direction the FIRING case needs; the NON-firing case needs the other one, and the split arm uses
  both in the same proof. Both follow from the same hom identity plus injectivity of
  \<open>real_of_rat\<close>, so state it once as an equivalence.\<close>

lemma defl_rat_root_iff_real:
  fixes p :: "int poly" and x :: rat
  shows "(poly (of_int_poly p :: real poly) (real_of_rat x) = 0)
       = (poly (map_poly rat_of_int p) x = 0)"
proof -
  have "poly (of_int_poly p :: real poly) (real_of_rat x)
      = poly (map_poly real_of_rat (map_poly rat_of_int p)) (real_of_rat x)"
    by (simp add: defl_of_int_poly_via_rat)
  also have "\<dots> = real_of_rat (poly (map_poly rat_of_int p) x)"
    by (simp add: of_rat_hom.poly_map_poly)
  finally show ?thesis by simp
qed

text \<open>\<^bold>\<open>And the midpoint is NOT a root of \<open>P\<^sub>0\<close> when the shed does not fire\<close> -- the fact
  \<open>defl_pending_covers_split_nofire\<close> takes, and the reason no root falls through a
  non-firing split.\<close>

lemma defl_mid_not_root_global:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and nofire: "poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0"
  shows "poly (of_int_poly (Poly rp) :: real poly)
           ((real_of_int l + real_of_int r) / 2 ^ Suc k) \<noteq> 0"
proof -
  have h: "poly (of_int_poly (Poly X) :: real poly) (1 / 2) \<noteq> 0"
    using nofire defl_rat_root_iff_real[of "Poly X" "1 / 2"] by (simp add: of_rat_divide)
  have iff: "(poly (of_int_poly (Poly X) :: real poly) (1 / 2) = 0)
      = (poly (of_int_poly (Poly rp) :: real poly)
           ((real_of_int l + (real_of_int r - real_of_int l) * (1 / 2)) / 2 ^ k) = 0)"
    by (rule defl_node_local_to_global[OF wrel]) auto
  have mid: "(real_of_int l + (real_of_int r - real_of_int l) * (1 / 2)) / 2 ^ k
      = (real_of_int l + real_of_int r) / 2 ^ Suc k"
    by (simp add: field_simps)
  show ?thesis using h iff mid by simp
qed

lemma defl_mid_pair_ok:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and fire: "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0"
  shows "dsc_pair_ok (of_int_poly (Poly rp) :: real poly)
           ((real_of_int l + real_of_int r) / 2 ^ Suc k,
            (real_of_int l + real_of_int r) / 2 ^ Suc k)"
  unfolding dsc_pair_ok_def using defl_mid_root_global[OF wrel fire] by simp



section \<open>What a push does to the accumulated windows\<close>

text \<open>\<^bold>\<open>@{const dyadic_interval_vec_triples} is a double \<open>zip\<close>\<close>, so appending one entry to each of
  the three columns appends exactly one triple -- provided the columns agree in length, which the
  vector's own invariant supplies. Stated separately because both places that grow \<open>acc\<close> (the
  ACCEPT arm's isolating box and the SPLIT arm's mid-root leaf) need it, and neither should have to
  unfold a \<open>zip\<close>.\<close>

lemma defl_acc_triples_push:
  assumes lal: "length al = length ar" and lak: "length ar = length ak"
  shows "dyadic_interval_vec_triples (al @ [A], ar @ [B], ak @ [m])
       = dyadic_interval_vec_triples (al, ar, ak) @ [((A, B), m)]"
proof -
  have z1: "zip (al @ [A]) (ar @ [B]) = zip al ar @ [(A, B)]"
    using lal by (simp add: zip_append)
  have lz: "length (zip al ar) = length ak" using lal lak by simp
  \<comment> \<open>@{thm [source] zip_append} is CONDITIONAL on the length agreement, and as a simp rule its
     premise is not discharged here even with \<open>lz\<close> in the simpset -- supply the instance.\<close>
  have z2: "zip (zip al ar @ [(A, B)]) (ak @ [m]) = zip (zip al ar) ak @ [((A, B), m)]"
    using zip_append[OF lz, of "[(A, B)]" "[m]"] by simp
  show ?thesis
    unfolding dyadic_interval_vec_triples_def
    by (simp add: z1 z2)
qed

lemma defl_acc_isolates_push:
  assumes iso: "defl_acc_isolates P0 (al, ar, ak)"
    and lal: "length al = length ar" and lak: "length ar = length ak"
    and ok: "dsc_pair_ok P0 (real_of_int A / 2 ^ m, real_of_int B / 2 ^ m)"
  shows "defl_acc_isolates P0 (al @ [A], ar @ [B], ak @ [m])"
  using iso ok
  unfolding defl_acc_isolates_def defl_acc_triples_push[OF lal lak]
  by (auto simp: nth_append less_Suc_eq)



section \<open>The geometry of the coverage clause, and its index bookkeeping\<close>

text \<open>\<^bold>\<open>The geometric half of coverage preservation, separated from the worklist bookkeeping.\<close> A bisection replaces
  one pending box by two, and the only point of the parent not handed to a child is the midpoint, which the split arm
  pushes onto \<open>acc\<close> when the shed fires and which is not a root of \<open>P\<^sub>0\<close> when it does not. So no root falls through the
  split. The child numerators are \<open>2l\<close> and \<open>2r\<close> at depth \<open>k+1\<close>, the same real endpoints as \<open>l\<close> and \<open>r\<close> at depth \<open>k\<close>; the two
  identities are stated explicitly because the outer bounds depend on them.\<close>

lemma defl_box_halves:
  fixes l :: int and k :: nat
  shows "real_of_int (2 * l) / 2 ^ Suc k = real_of_int l / 2 ^ k"
  by simp

lemma defl_box_split_cover:
  fixes l r :: int and k :: nat and y :: real
  assumes lo: "real_of_int l / 2 ^ k < y" and hi: "y < real_of_int r / 2 ^ k"
  shows "(real_of_int (2 * l) / 2 ^ Suc k < y \<and> y < real_of_int (l + r) / 2 ^ Suc k)
       \<or> y = real_of_int (l + r) / 2 ^ Suc k
       \<or> (real_of_int (l + r) / 2 ^ Suc k < y \<and> y < real_of_int (2 * r) / 2 ^ Suc k)"
proof -
  have e1: "real_of_int (2 * l) / 2 ^ Suc k = real_of_int l / 2 ^ k" by (rule defl_box_halves)
  have e2: "real_of_int (2 * r) / 2 ^ Suc k = real_of_int r / 2 ^ k" by (rule defl_box_halves)
  show ?thesis using lo hi unfolding e1 e2 by linarith
qed

text \<open>\<^bold>\<open>And the three index reads a two-entry push produces\<close>, so no consumer has to unfold
  @{const defl_todo_box} against an \<open>@\<close>.\<close>

lemma defl_todo_box_append_old:
  assumes i: "i < length lns"
    and l1: "length lns = length rns" and l2: "length rns = length ks"
  shows "defl_todo_box (lns @ [a1, a2], rns @ [b1, b2], ks @ [c1, c2]) i
       = defl_todo_box (lns, rns, ks) i"
  using assms unfolding defl_todo_box_def by (simp add: nth_append)

lemma defl_todo_box_append_fst:
  assumes l1: "length lns = n" and l2: "length rns = n" and l3: "length ks = n"
  shows "defl_todo_box (lns @ [a1, a2], rns @ [b1, b2], ks @ [c1, c2]) n
       = (real_of_int a1 / 2 ^ c1, real_of_int b1 / 2 ^ c1)"
  using assms unfolding defl_todo_box_def by (simp add: nth_append)

lemma defl_todo_box_append_snd:
  assumes l1: "length lns = n" and l2: "length rns = n" and l3: "length ks = n"
  shows "defl_todo_box (lns @ [a1, a2], rns @ [b1, b2], ks @ [c1, c2]) (Suc n)
       = (real_of_int a2 / 2 ^ c2, real_of_int b2 / 2 ^ c2)"
  using assms unfolding defl_todo_box_def by (simp add: nth_append)



section \<open>The node's init is nonzero, which the resolve step needs\<close>

text \<open>\<^bold>\<open>The resolve step on the deflating loop.\<close> On the ambiguous branch (\<open>c = 4\<close> and \<open>g < 2\<^sup>4\<^sup>2\<close>),
  @{const hybrid_resolve_count_monadic} calls @{const carried_escalate_keep_monadic}, which rebuilds the node exactly from
  the retained root \<open>rp\<close>, discarding the stored polynomial and returning the undeflated init at guard \<open>2\<^sup>4\<^sup>2\<close>. On that branch a
  deflating node loses its shed. For the proof this is a simplification: the node's exact object reverts to the init, and
  @{const defl_node_wrel} holds of it by reflexivity.

  Reflexivity still needs non-vanishing, which @{const defl_node_wrel} includes, and the coupling supplies non-vanishing
  only for the node's own polynomial. After a reset the witness is the init, so its non-vanishing comes from the root:
  \<open>P\<^sub>0 \<noteq> 0\<close> and a non-degenerate box. This section provides it, and it is why \<open>l < r\<close> is available per node.\<close>

lemma defl_carried_init_nz:
  assumes rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l < r"
  shows "(of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly) \<noteq> 0"
proof
  assume z: "(of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly) = 0"
  have d0: "(2::int) ^ k \<noteq> 0" by simp
  have w: "real_of_int r - real_of_int l \<noteq> 0" using lr by simp
  have all0: "\<And>y::real. poly (of_int_poly (Poly rp) :: real poly) y = 0"
  proof -
    fix y :: real
    define t where "t = (y * 2 ^ k - real_of_int l) / (real_of_int r - real_of_int l)"
    have phi: "(real_of_int l + (real_of_int r - real_of_int l) * t) / real_of_int (2 ^ k) = y"
      using w unfolding t_def by (simp add: field_simps)
    have "poly (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly) t = 0"
      using z by simp
    thus "poly (of_int_poly (Poly rp) :: real poly) y = 0"
      using defl_carried_init_zero_iff_real[OF d0, of l r rp t] phi by simp
  qed
  have "poly (of_int_poly (Poly rp) :: real poly) = poly 0" using all0 by auto
  hence "(of_int_poly (Poly rp) :: real poly) = 0" by (simp add: poly_eq_poly_eq_iff)
  thus False using rpnz by simp
qed

text \<open>\<^bold>\<open>And therefore the reset node satisfies the coupling's relation outright.\<close> This is the
  shape the loop-body step will feed after an escalating resolve.\<close>

lemma defl_node_wrel_init_refl:
  assumes rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l < r"
  shows "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp)
                        (carried_init_same_den l (2 ^ k) r rp)"
  by (rule defl_node_wrel_refl[OF defl_carried_init_nz[OF rpnz lr]])



section \<open>The resolve step, deflating version\<close>

text \<open>\<^bold>\<open>The non-deflating contract cannot be applied directly, but can be reused.\<close>
  @{thm [source] hybrid_resolve_count_monadic_classify} takes \<open>cache: hybrid_cs_ok g c (carried_descartes_count X)\<close> with \<open>X\<close>
  the node's init. On the deflating stack the cached class is against the node's deflated exact polynomial, so that
  hypothesis does not hold in general.

  On the branch where the lemma is needed, it does apply. The op rebuilds only when \<open>c = 4 \<and> g < 2\<^sup>4\<^sup>2\<close>, and
  \<open>hybrid_cs_ok g 4 cnt\<close> holds for any \<open>cnt\<close> under exactly that condition (the sentinel's own disjunct), so the hypothesis
  is available at \<open>X := init\<close> there; the other side condition, \<open>2\<^sup>4\<^sup>2 \<le> g \<longrightarrow> Q = X\<close>, is vacuous on the same branch. So the
  deflating version is a case split in which one branch reduces the op to a \<open>RETURN\<close> and the other uses the non-deflating
  lemma.

  \<^bold>\<open>The outputs of the two branches differ, and the existential absorbs the difference.\<close> On the pass-through branch the
  node keeps its deflated exact object; on the rebuild branch that object is replaced by the init. Both satisfy
  @{const defl_node_wrel} against the same init, the first by hypothesis and the second by reflexivity, which is why the
  coupling quantifies the exact object.\<close>

section \<open>The resolve carries the node's budget, payload and ceiling through\<close>

lemma defl_resolve_count_classify:
  assumes rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_pbound: "length (carried_init_same_den l_num (2 ^ k) r_num rp)
                     * nat_bitlen (length (carried_init_same_den l_num (2 ^ k) r_num rp))
                   < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length (carried_init_same_den l_num (2 ^ k) r_num rp)
                   < max_snat LENGTH(gmp_poly_len)"
    and frameD: "node_frame Xd Q g"
    and wrelD: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) Xd"
    and cacheD: "hybrid_cs_ok g c (carried_descartes_count Xd)"
    and cle: "4 < c \<longrightarrow> 4398046511104 \<le> g"
    and lockedD: "4398046511104 \<le> g \<longrightarrow> Q = Xd"
    \<comment> \<open>\<^bold>\<open>The rest of @{const defl_node_ok}, carried through the resolve.\<close> The dispatch arms need the budget, the payload
       and the ceiling at the resolved guard; the resolve either passes its input through or locks at the literal, in which
       case all three are degenerate.\<close>
    and budD: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and payD: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count Xd \<le> g - 4398046511104"
    and ceilD: "g \<le> 4398046511104 + length rp"
    and lenD: "length Xd \<le> length rp"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the input node's divisibility. Both branches keep it: the pass-through returns \<open>Xd\<close> itself, and the
       rebuild returns the node's own init, where it is \<open>dvd_refl\<close>. The arm case split is below the resolve, so the dispatch
       has no other source for it.\<close>
    and dvdD: "(of_int_poly (Poly Xd) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
  shows "hybrid_resolve_count_monadic Q g l_num r_num k rp c
       \<le> SPEC (\<lambda>(c', Q', g', rp'). rp' = rp
           \<and> (\<exists>X'. node_frame X' Q' g'
               \<and> defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X'
               \<and> dyadic_iv_cs_invar c' (carried_descartes_count X')
               \<and> length X' \<le> length rp
               \<and> (4398046511106 \<le> g'
                    \<longrightarrow> carried_descartes_count X' \<le> g' - 4398046511104)
               \<and> (4398046511104 \<le> g' \<longrightarrow> Q' = X')
               \<and> (of_int_poly (Poly X') :: real poly)
                   dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                         :: real poly))
           \<and> (g' \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g')
           \<and> g' \<le> 4398046511104 + length rp
           \<and> (4 < c' \<longrightarrow> 4398046511104 \<le> g')
           \<and> (g' < 4398046511104 \<longrightarrow> c' < 4))"
  \<comment> \<open>\<^bold>\<open>The last conjunct is the pop's whole contribution to the general-guard arms\<close>, and it
     is why @{const defl_node_ok} carries the class bound. It says: a node that survives the
     resolve at a guard BELOW the lock has a class the dispatch can read as a class --- never as
     a W1 window count. That is exactly what makes @{const hybrid_window_v_monadic} take its
     EXACT branch there, so the count the window is run with describes the polynomial the
     escalate just rebuilt rather than the deflated object the cache was about.

     Both branches supply it for a different reason: the rebuild branch LOCKS (\<open>g' = 2\<^sup>4\<^sup>2\<close>,
     so the implication is vacuous), and the pass-through branch has \<open>c \<noteq> 4\<close> from its own
     condition plus \<open>c \<le> 4\<close> from the coupling's bound.\<close>
proof (cases "c = 4 \<and> g < 4398046511104")
  case cond: False
  \<comment> \<open>\<open>if_not_P\<close>, not \<open>simp\<close> with \<open>cond\<close>: \<open>simp\<close> normalises \<open>\<not>(c = 4 \<and> g < 2\<^sup>4\<^sup>2)\<close> into an
     IMPLICATION and then no longer rewrites the \<open>if\<close>'s condition to \<open>False\<close>, leaving the whole
     rebuild branch in the goal.\<close>
  have red: "hybrid_resolve_count_monadic Q g l_num r_num k rp c = RETURN (c, Q, g, rp)"
    unfolding hybrid_resolve_count_monadic_def PR_CONST_def
    by (simp only: if_not_P[OF cond])
  have invc: "dyadic_iv_cs_invar c (carried_descartes_count Xd)"
    using cacheD cond by (auto simp: hybrid_cs_ok_def)
  have clt: "g < 4398046511104 \<longrightarrow> c < 4" using cond cle by force
  show ?thesis
    unfolding red using frameD wrelD invc lockedD cle clt budD payD ceilD lenD dvdD
    by simp blast
next
  case cond: True
  let ?X = "carried_init_same_den l_num (2 ^ k) r_num rp"
  \<comment> \<open>the sentinel's own disjunct -- available for ANY count, which is the whole trick\<close>
  have cache': "hybrid_cs_ok g c (carried_descartes_count ?X)"
    using cond by (simp add: hybrid_cs_ok_def)
  have lock': "4398046511104 \<le> g \<Longrightarrow> Q = ?X" using cond by simp
  have wrel': "defl_node_wrel ?X ?X" by (rule defl_node_wrel_init_refl[OF rpnz lr])
  \<comment> \<open>the rebuild returns the node's own init, so its divisibility is reflexivity.\<close>
  have dvd': "(of_int_poly (Poly ?X) :: real poly) dvd (of_int_poly (Poly ?X) :: real poly)"
    by (rule dvd_refl)
  have classic: "hybrid_resolve_count_monadic Q g l_num r_num k rp c
      \<le> SPEC (\<lambda>(c', Q', g', rp'). dyadic_iv_cs_invar c' (carried_descartes_count ?X)
          \<and> rp' = rp
          \<and> (4398046511104 \<le> g' \<longrightarrow> Q' = ?X)
          \<and> (g' < 4398046511104 \<longrightarrow> Q' = Q \<and> g' = g))"
    by (rule hybrid_resolve_count_monadic_classify[
          OF rp_len rp_bound k_bound Q_bound X_pbound X_gbound refl cache' lock'])
  \<comment> \<open>\<^bold>\<open>The rebuild branch always locks\<close>, which excludes the conclusion's \<open>g' < 2\<^sup>4\<^sup>2\<close> alternative; without it the two
     branches' exact objects could not be distinguished from the SPEC. \<open>\<le> SPEC\<close> carries a no-failure obligation, and the op's
     \<open>ASSERT\<close> is discharged by the escalation's length reasoning, which the non-deflating contract has done, so its no-failure
     fact is used.\<close>
  have nf: "nofail (hybrid_resolve_count_monadic Q g l_num r_num k rp c)"
    using classic by (auto simp: pw_le_iff)
  have glock: "hybrid_resolve_count_monadic Q g l_num r_num k rp c
      \<le> SPEC (\<lambda>(c', Q', g', rp'). g' = 4398046511104)"
    using cond nf
    unfolding hybrid_resolve_count_monadic_def PR_CONST_def
    \<comment> \<open>\<open>auto\<close>, not \<open>simp\<close>: the residue is \<open>\<forall>\<dots>. (\<exists>\<dots>. \<dots> \<and> ab = 2\<^sup>4\<^sup>2 \<dots>) \<longrightarrow> ab = 2\<^sup>4\<^sup>2\<close>, where the
       equation sits behind the escalate's own side conditions -- discharged from the borrowed
       nofail, but only by a tactic that will instantiate the existential.\<close>
    by (auto simp: pw_le_iff refine_pw_simps)
  show ?thesis
    apply (rule order_trans[OF defl_SPEC_conj[OF classic glock]])
    \<comment> \<open>\<^bold>\<open>No \<open>exI\<close> here, and that is worth a note.\<close> The conclusion's existential is PINNED by its
       own last conjunct: under \<open>glock\<close> the guard is the LOCK literal, so
       \<open>2\<^sup>4\<^sup>2 \<le> g' \<longrightarrow> Q' = X'\<close> forces \<open>X' = Q' = init\<close> and \<open>clarsimp\<close> eliminates the \<open>\<exists>\<close> by
       substitution before any witness has to be supplied. An \<open>exI\<close> after it has nothing left to
       apply to and fails.\<close>
    apply clarsimp
    apply (intro conjI)
    \<comment> \<open>the two class-bound conjuncts are vacuous on this branch --- \<open>glock\<close> has already pinned
       \<open>g' = 2\<^sup>4\<^sup>2\<close>, so \<open>simp\<close> closes them wherever \<open>clarsimp\<close> left them in the order.\<close>
    apply (all \<open>((rule node_frame_exact_any_g | rule wrel' | rule dvd' | simp); fail)?\<close>)
    \<comment> \<open>on the rebuild branch \<open>glock\<close> gives \<open>g' = 2\<^sup>4\<^sup>2\<close>, so the payload antecedent is false, the budget takes its second
       disjunct and the ceiling is immediate; none needs the input's own.\<close>
    apply (all \<open>(simp; fail)?\<close>)
    done
qed

lemma defl_resolve_bind:
  assumes rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_pbound: "length (carried_init_same_den l_num (2 ^ k) r_num rp)
                     * nat_bitlen (length (carried_init_same_den l_num (2 ^ k) r_num rp))
                   < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length (carried_init_same_den l_num (2 ^ k) r_num rp)
                   < max_snat LENGTH(gmp_poly_len)"
    and frameD: "node_frame Xd Q g"
    and wrelD: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) Xd"
    and cacheD: "hybrid_cs_ok g c (carried_descartes_count Xd)"
    and cle: "4 < c \<longrightarrow> 4398046511104 \<le> g"
    and lockedD: "4398046511104 \<le> g \<longrightarrow> Q = Xd"
    and budD: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and payD: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count Xd \<le> g - 4398046511104"
    and ceilD: "g \<le> 4398046511104 + length rp"
    and lenD: "length Xd \<le> length rp"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    \<comment> \<open>\<^bold>\<open>Last among the premises other than \<open>cont\<close>\<close>, passed to @{thm [source] defl_resolve_count_classify}, so no caller's
       \<open>[OF \<dots>]\<close> position moves.\<close>
    and dvdD: "(of_int_poly (Poly Xd) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
    and cont: "\<And>c' Q' g' rp' X'.
        \<lbrakk> rp' = rp;
          node_frame X' Q' g';
          defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X';
          dyadic_iv_cs_invar c' (carried_descartes_count X');
          4398046511104 \<le> g' \<longrightarrow> Q' = X';
          4 < c' \<longrightarrow> 4398046511104 \<le> g';
          g' < 4398046511104 \<longrightarrow> c' < 4;
          g' \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g';
          4398046511106 \<le> g' \<longrightarrow> carried_descartes_count X' \<le> g' - 4398046511104;
          g' \<le> 4398046511104 + length rp;
          length X' \<le> length rp;
          (of_int_poly (Poly X') :: real poly)
            dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                  :: real poly) \<rbrakk>
        \<Longrightarrow> f c' Q' g' rp' \<le> SPEC \<Phi>"
  shows "doN { (c', Q', g', rp') \<leftarrow> hybrid_resolve_count_monadic Q g l_num r_num k rp c;
               f c' Q' g' rp' }
       \<le> SPEC \<Phi>"
  apply (refine_vcg defl_resolve_count_classify[OF rp_len rp_bound k_bound Q_bound
        X_pbound X_gbound frameD wrelD cacheD cle lockedD budD payD ceilD lenD rpnz lr dvdD,
        THEN order_trans])
  apply clarsimp
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done



section \<open>The resolve in continuation form\<close>

text \<open>\<^bold>\<open>The deflating version of \<open>hybrid_resolve_bind\<close>.\<close> @{const defl_after_pop_monadic} binds the resolve and then
  dispatches, so the packed \<open>\<le> SPEC\<close> form of @{thm [source] defl_resolve_count_classify} has nothing to match
  (\<open>refine_vcg\<close> has already split the bind); hence the continuation form.

  \<^bold>\<open>The structural difference from the non-deflating version.\<close> \<open>hybrid_resolve_bind\<close>'s continuation receives
  \<open>dyadic_iv_cs_invar c' (count X)\<close> with \<open>X\<close> given by a formula (the node's init), so the arm selection can be placed above the
  resolve, splitting on \<open>count (carried_init_same_den (last lns) \<dots>)\<close> at the top (\<open>hybrid_step_all_cols\<close>). Here the exact
  object is existential, and the resolve may replace it, so the continuation receives an \<open>X'\<close> it introduces itself, and
  the arm case split happens below this bind.\<close>



section \<open>Coverage during a dispatch, and the reject arm's use of it\<close>

text \<open>\<^bold>\<open>The loop body pops before it dispatches, so the coverage clause does not hold in between and is restated.\<close>
  Between the pop and the push, the node being processed is in no column (it lives in the local variables \<open>l_num, r_num, k\<close>),
  so a root in its box is neither accumulated nor pending. @{const defl_pending_covers} is therefore not preserved step by
  step through the body; this three-way form, with the current box as a third alternative, is.

  Stated separately, it keeps each arm's obligation small: the reject arm discharges the third disjunct by showing that the
  box has no root, the accept arm by moving it into \<open>acc\<close>, and the split arm by handing it to the two children
  (@{thm [source] defl_box_split_cover}).\<close>

definition defl_dispatch_covers ::
  "real poly \<Rightarrow> real \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_dyadic_interval_vec
     \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool" where
  "defl_dispatch_covers P0 lo todo acc l r k \<longleftrightarrow>
     (\<forall>y::real. lo < y \<longrightarrow> poly P0 y = 0 \<longrightarrow>
        (\<exists>j A B m. j < length (dyadic_interval_vec_triples acc)
           \<and> dyadic_interval_vec_triples acc ! j = ((A, B), m)
           \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
              \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y)))
      \<or> (\<exists>i < length (fst (snd todo)). fst (defl_todo_box todo i) < y
             \<and> y < snd (defl_todo_box todo i))
      \<or> (real_of_int l / 2 ^ k < y \<and> y < real_of_int r / 2 ^ k))"

text \<open>\<^bold>\<open>The pop\<close>: the popped node's box becomes the third alternative, and every other pending
  box keeps its index under \<open>butlast\<close>.\<close>

lemma defl_dispatch_covers_pop:
  assumes cov: "defl_pending_covers P0 lo (lns, rns, ks) acc"
    and ne: "rns \<noteq> []"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
  shows "defl_dispatch_covers P0 lo (butlast lns, butlast rns, butlast ks) acc
           (last lns) (last rns) (last ks)"
  unfolding defl_dispatch_covers_def
proof (intro allI impI)
  fix y :: real
  assume yl: "lo < y" and yz: "poly P0 y = 0"
  \<comment> \<open>\<open>consider\<close>, not \<open>proof (cases D)\<close> on a disjunction FACT -- \<open>cases\<close> wants a datatype or a
     rule, and on a bare \<open>\<or>\<close> it fails at the \<open>proof\<close> itself with the untouched goal.\<close>
  \<comment> \<open>\<^bold>\<open>Two steps, not one.\<close> Unfolding must happen in the FACT (\<open>unfolding\<close> above rewrites the
     GOAL, and a chained opaque predicate is invisible to a closer); and INSTANTIATING the \<open>\<forall>y\<close>
     is a separate job from splitting the disjunction -- asking one \<open>auto\<close> to do both left the
     \<open>\<forall>\<close> untouched beside the two case rules.\<close>
  have D: "(\<exists>j A B m. j < length (dyadic_interval_vec_triples acc)
                 \<and> dyadic_interval_vec_triples acc ! j = ((A, B), m)
                 \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
                    \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y)))
          \<or> (\<exists>i < length rns. fst (defl_todo_box (lns, rns, ks) i) < y
                 \<and> y < snd (defl_todo_box (lns, rns, ks) i))"
    using cov[unfolded defl_pending_covers_def] yl yz by simp
  from D consider
      (inacc) "\<exists>j A B m. j < length (dyadic_interval_vec_triples acc)
                 \<and> dyadic_interval_vec_triples acc ! j = ((A, B), m)
                 \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
                    \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y))"
    | (inbox) "\<exists>i < length rns. fst (defl_todo_box (lns, rns, ks) i) < y
                 \<and> y < snd (defl_todo_box (lns, rns, ks) i)"
    by blast
  then show "(\<exists>j A B m. j < length (dyadic_interval_vec_triples acc)
           \<and> dyadic_interval_vec_triples acc ! j = ((A, B), m)
           \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
              \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y)))
      \<or> (\<exists>i < length (fst (snd (butlast lns, butlast rns, butlast ks))).
             fst (defl_todo_box (butlast lns, butlast rns, butlast ks) i) < y
             \<and> y < snd (defl_todo_box (butlast lns, butlast rns, butlast ks) i))
      \<or> (real_of_int (last lns) / 2 ^ last ks < y
             \<and> y < real_of_int (last rns) / 2 ^ last ks)"
  proof cases
    case inacc thus ?thesis by blast
  next
    case inbox
    then obtain i where i: "i < length rns"
      and box: "fst (defl_todo_box (lns, rns, ks) i) < y"
               "y < snd (defl_todo_box (lns, rns, ks) i)" by blast
    show ?thesis
    proof (cases "i < length rns - 1")
      case True
      hence ib: "i < length (butlast rns)" by simp
      have "defl_todo_box (butlast lns, butlast rns, butlast ks) i
          = defl_todo_box (lns, rns, ks) i"
        using True l1 l2 unfolding defl_todo_box_def by (simp add: nth_butlast)
      thus ?thesis using ib box by auto
    next
      case False
      hence ieq: "i = length rns - 1" using i by linarith
      have nesL: "lns \<noteq> []" and nesK: "ks \<noteq> []" using ne l1 l2 by auto
      \<comment> \<open>\<^bold>\<open>Componentwise, never as a PAIR equality.\<close> Proving
         \<open>defl_todo_box \<dots> i = (a/2\<^sup>k, b/2\<^sup>k)\<close> in one step makes \<open>simp\<close> attack the two divisions
         together and it splits into \<open>b = 0 \<or> k = k'\<close> nonsense. The two index reads are what is
         actually wanted.\<close>
      have bl: "lns ! i = last lns" using ieq l1 nesL by (simp add: last_conv_nth)
      have br: "rns ! i = last rns" using ieq ne by (simp add: last_conv_nth)
      have bk: "ks ! i = last ks" using ieq l2 nesK by (simp add: last_conv_nth)
      have "fst (defl_todo_box (lns, rns, ks) i) = real_of_int (last lns) / 2 ^ last ks"
        unfolding defl_todo_box_def using bl bk by simp
      moreover have "snd (defl_todo_box (lns, rns, ks) i)
          = real_of_int (last rns) / 2 ^ last ks"
        unfolding defl_todo_box_def using br bk by simp
      ultimately show ?thesis using box by simp
    qed
  qed
qed

text \<open>\<^bold>\<open>The REJECT arm\<close>: the third alternative is discharged outright, because the box holds no
  root of \<open>P\<^sub>0\<close> -- @{thm [source] defl_node_box_no_roots}, read off the zero cached count. The
  worklist and \<open>acc\<close> are untouched, so this is the whole of the arm's coverage obligation.\<close>

lemma defl_pending_covers_reject:
  assumes cov: "defl_dispatch_covers P0 lo todo acc l r k"
    and noroot: "\<And>y::real. real_of_int l / 2 ^ k < y \<Longrightarrow> y < real_of_int r / 2 ^ k
                   \<Longrightarrow> poly P0 y \<noteq> 0"
  shows "defl_pending_covers P0 lo todo acc"
  using cov noroot
  unfolding defl_dispatch_covers_def defl_pending_covers_def by blast



text \<open>\<^bold>\<open>The ACCEPT arm\<close>: the current box MOVES into \<open>acc\<close>, so the third alternative becomes the
  first. Old \<open>acc\<close> indices survive the append unchanged and the new entry sits at the end --
  @{thm [source] defl_acc_triples_push} is the only thing needed about the vector.\<close>

lemma defl_pending_covers_accept:
  assumes cov: "defl_dispatch_covers P0 lo todo (al, ar, ak) l r k"
    and lal: "length al = length ar" and lak: "length ar = length ak"
  shows "defl_pending_covers P0 lo todo (al @ [l], ar @ [r], ak @ [k])"
  unfolding defl_pending_covers_def
proof (intro allI impI)
  fix y :: real
  assume yl: "lo < y" and yz: "poly P0 y = 0"
  let ?T = "dyadic_interval_vec_triples (al, ar, ak)"
  have push: "dyadic_interval_vec_triples (al @ [l], ar @ [r], ak @ [k])
      = ?T @ [((l, r), k)]" by (rule defl_acc_triples_push[OF lal lak])
  from cov yl yz consider
      (inacc) "\<exists>j A B m. j < length ?T \<and> ?T ! j = ((A, B), m)
                 \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
                    \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y))"
    | (inbox) "\<exists>i < length (fst (snd todo)). fst (defl_todo_box todo i) < y
                 \<and> y < snd (defl_todo_box todo i)"
    | (cur) "real_of_int l / 2 ^ k < y \<and> y < real_of_int r / 2 ^ k"
    unfolding defl_dispatch_covers_def by blast
  then show "(\<exists>j A B m. j < length (dyadic_interval_vec_triples (al @ [l], ar @ [r], ak @ [k]))
           \<and> dyadic_interval_vec_triples (al @ [l], ar @ [r], ak @ [k]) ! j = ((A, B), m)
           \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
              \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y)))
      \<or> (\<exists>i < length (fst (snd todo)). fst (defl_todo_box todo i) < y
             \<and> y < snd (defl_todo_box todo i))"
  proof cases
    case inacc
    then obtain j A B m where j: "j < length ?T" and e: "?T ! j = ((A, B), m)"
      and b: "(real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
              \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y)" by blast
    have "j < length (?T @ [((l, r), k)])" using j by simp
    moreover have "(?T @ [((l, r), k)]) ! j = ((A, B), m)" using j e by (simp add: nth_append)
    ultimately show ?thesis unfolding push using b by blast
  next
    case inbox thus ?thesis by blast
  next
    case cur
    have "length ?T < length (?T @ [((l, r), k)])" by simp
    moreover have "(?T @ [((l, r), k)]) ! length ?T = ((l, r), k)" by (simp add: nth_append)
    ultimately show ?thesis unfolding push using cur by blast
  qed
qed

text \<open>\<^bold>\<open>The SPLIT arm, non-firing\<close>: the current box is handed to the two children, and the one
  point neither child gets -- the midpoint -- is not a root, which is exactly what the child-build
  contract reports when the shed does NOT fire.\<close>

lemma defl_pending_covers_split_nofire:
  assumes cov: "defl_dispatch_covers P0 lo (lns, rns, ks) acc l r k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and nomid: "poly P0 (real_of_int (l + r) / 2 ^ Suc k) \<noteq> 0"
  shows "defl_pending_covers P0 lo
           (lns @ [2 * l, l + r], rns @ [l + r, 2 * r], ks @ [Suc k, Suc k]) acc"
  unfolding defl_pending_covers_def
proof (intro allI impI)
  fix y :: real
  assume yl: "lo < y" and yz: "poly P0 y = 0"
  let ?T = "(lns @ [2 * l, l + r], rns @ [l + r, 2 * r], ks @ [Suc k, Suc k])"
  from cov yl yz consider
      (inacc) "\<exists>j A B m. j < length (dyadic_interval_vec_triples acc)
                 \<and> dyadic_interval_vec_triples acc ! j = ((A, B), m)
                 \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
                    \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y))"
    | (inbox) "\<exists>i < length rns. fst (defl_todo_box (lns, rns, ks) i) < y
                 \<and> y < snd (defl_todo_box (lns, rns, ks) i)"
    | (cur) "real_of_int l / 2 ^ k < y \<and> y < real_of_int r / 2 ^ k"
    \<comment> \<open>\<open>blast\<close>, not \<open>auto\<close>: the step instantiates the \<open>\<forall>y\<close> and splits a three-way disjunction onto the case rules, and \<open>auto\<close>
       stalls with the \<open>\<forall>\<close> untouched (as in @{thm [source] defl_dispatch_covers_pop}). \<open>fst_conv\<close>/\<open>snd_conv\<close> are unfolded too:
       the definition writes the pending column as \<open>fst (snd todo)\<close>, which at a concrete triple stays unreduced and does not
       match the case's \<open>length rns\<close>, and \<open>blast\<close> does no rewriting.\<close>
    unfolding defl_dispatch_covers_def fst_conv snd_conv by blast
  then show "(\<exists>j A B m. j < length (dyadic_interval_vec_triples acc)
           \<and> dyadic_interval_vec_triples acc ! j = ((A, B), m)
           \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
              \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y)))
      \<or> (\<exists>i < length (fst (snd ?T)). fst (defl_todo_box ?T i) < y
             \<and> y < snd (defl_todo_box ?T i))"
  proof cases
    case inacc thus ?thesis by blast
  next
    case inbox
    then obtain i where i: "i < length rns"
      and b: "fst (defl_todo_box (lns, rns, ks) i) < y"
             "y < snd (defl_todo_box (lns, rns, ks) i)" by blast
    have eq: "defl_todo_box ?T i = defl_todo_box (lns, rns, ks) i"
      by (rule defl_todo_box_append_old[OF _ l1 l2[symmetric]]) (use i l1 in simp)
    \<comment> \<open>\<^bold>\<open>Give the witness.\<close> The goal's second disjunct is a bounded \<open>\<exists>i\<close> over the EXTENDED
       column; \<open>auto\<close> negates it and then has to guess \<open>i\<close> back out of a \<open>\<forall>\<close>, which it does
       not. Supplying the index and the two bounds and finishing with \<open>blast\<close> is immediate.\<close>
    have lt: "i < length (fst (snd ?T))" using i by simp
    have "fst (defl_todo_box ?T i) < y \<and> y < snd (defl_todo_box ?T i)"
      using b eq by simp
    with lt show ?thesis by blast
  next
    case cur
    have tri: "(real_of_int (2 * l) / 2 ^ Suc k < y \<and> y < real_of_int (l + r) / 2 ^ Suc k)
         \<or> y = real_of_int (l + r) / 2 ^ Suc k
         \<or> (real_of_int (l + r) / 2 ^ Suc k < y \<and> y < real_of_int (2 * r) / 2 ^ Suc k)"
      using cur by (intro defl_box_split_cover) auto
    have notmid: "y \<noteq> real_of_int (l + r) / 2 ^ Suc k" using yz nomid by auto
    have f1: "defl_todo_box ?T (length rns)
        = (real_of_int (2 * l) / 2 ^ Suc k, real_of_int (l + r) / 2 ^ Suc k)"
      by (rule defl_todo_box_append_fst[OF l1 refl l2])
    have f2: "defl_todo_box ?T (Suc (length rns))
        = (real_of_int (l + r) / 2 ^ Suc k, real_of_int (2 * r) / 2 ^ Suc k)"
      by (rule defl_todo_box_append_snd[OF l1 refl l2])
    from tri show ?thesis
    proof (elim disjE)
      assume A: "real_of_int (2 * l) / 2 ^ Suc k < y
                 \<and> y < real_of_int (l + r) / 2 ^ Suc k"
      have lt: "length rns < length (fst (snd ?T))" by simp
      have "fst (defl_todo_box ?T (length rns)) < y
            \<and> y < snd (defl_todo_box ?T (length rns))" using A f1 by simp
      with lt show ?thesis by blast
    next
      assume "y = real_of_int (l + r) / 2 ^ Suc k"
      thus ?thesis using notmid by simp
    next
      assume A: "real_of_int (l + r) / 2 ^ Suc k < y
                 \<and> y < real_of_int (2 * r) / 2 ^ Suc k"
      have lt: "Suc (length rns) < length (fst (snd ?T))" by simp
      have "fst (defl_todo_box ?T (Suc (length rns))) < y
            \<and> y < snd (defl_todo_box ?T (Suc (length rns)))" using A f2 by simp
      with lt show ?thesis by blast
    qed
  qed
qed



text \<open>\<^bold>\<open>The SPLIT arm, FIRING\<close>: same trichotomy, but the midpoint is no longer excluded -- it IS
  a root, and it is accumulated as the degenerate pair @{term "((l + r, l + r), Suc k)"}. That is
  the one place @{const dsc_pair_ok}'s degenerate branch is used, and
  @{thm [source] defl_mid_pair_ok} is what makes it sound.\<close>

lemma defl_pending_covers_split_fire:
  assumes cov: "defl_dispatch_covers P0 lo (lns, rns, ks) (al, ar, ak) l r k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
  shows "defl_pending_covers P0 lo
           (lns @ [2 * l, l + r], rns @ [l + r, 2 * r], ks @ [Suc k, Suc k])
           (al @ [l + r], ar @ [l + r], ak @ [Suc k])"
  unfolding defl_pending_covers_def
proof (intro allI impI)
  fix y :: real
  assume yl: "lo < y" and yz: "poly P0 y = 0"
  let ?T = "(lns @ [2 * l, l + r], rns @ [l + r, 2 * r], ks @ [Suc k, Suc k])"
  let ?A = "dyadic_interval_vec_triples (al, ar, ak)"
  have push: "dyadic_interval_vec_triples (al @ [l + r], ar @ [l + r], ak @ [Suc k])
      = ?A @ [((l + r, l + r), Suc k)]" by (rule defl_acc_triples_push[OF lal lak])
  from cov yl yz consider
      (inacc) "\<exists>j A B m. j < length ?A \<and> ?A ! j = ((A, B), m)
                 \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
                    \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y))"
    | (inbox) "\<exists>i < length rns. fst (defl_todo_box (lns, rns, ks) i) < y
                 \<and> y < snd (defl_todo_box (lns, rns, ks) i)"
    | (cur) "real_of_int l / 2 ^ k < y \<and> y < real_of_int r / 2 ^ k"
    unfolding defl_dispatch_covers_def fst_conv snd_conv by blast
  then show "(\<exists>j A B m.
           j < length (dyadic_interval_vec_triples (al @ [l + r], ar @ [l + r], ak @ [Suc k]))
           \<and> dyadic_interval_vec_triples (al @ [l + r], ar @ [l + r], ak @ [Suc k]) ! j
                = ((A, B), m)
           \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
              \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y)))
      \<or> (\<exists>i < length (fst (snd ?T)). fst (defl_todo_box ?T i) < y
             \<and> y < snd (defl_todo_box ?T i))"
  proof cases
    case inacc
    then obtain j A B m where j: "j < length ?A" and e: "?A ! j = ((A, B), m)"
      and b: "(real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
              \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y)" by blast
    have "j < length (?A @ [((l + r, l + r), Suc k)])" using j by simp
    moreover have "(?A @ [((l + r, l + r), Suc k)]) ! j = ((A, B), m)"
      using j e by (simp add: nth_append)
    ultimately show ?thesis unfolding push using b by blast
  next
    case inbox
    then obtain i where i: "i < length rns"
      and b: "fst (defl_todo_box (lns, rns, ks) i) < y"
             "y < snd (defl_todo_box (lns, rns, ks) i)" by blast
    have eq: "defl_todo_box ?T i = defl_todo_box (lns, rns, ks) i"
      by (rule defl_todo_box_append_old[OF _ l1 l2[symmetric]]) (use i l1 in simp)
    have lt: "i < length (fst (snd ?T))" using i by simp
    have "fst (defl_todo_box ?T i) < y \<and> y < snd (defl_todo_box ?T i)"
      using b eq by simp
    with lt show ?thesis by blast
  next
    case cur
    have tri: "(real_of_int (2 * l) / 2 ^ Suc k < y \<and> y < real_of_int (l + r) / 2 ^ Suc k)
         \<or> y = real_of_int (l + r) / 2 ^ Suc k
         \<or> (real_of_int (l + r) / 2 ^ Suc k < y \<and> y < real_of_int (2 * r) / 2 ^ Suc k)"
      using cur by (intro defl_box_split_cover) auto
    have f1: "defl_todo_box ?T (length rns)
        = (real_of_int (2 * l) / 2 ^ Suc k, real_of_int (l + r) / 2 ^ Suc k)"
      by (rule defl_todo_box_append_fst[OF l1 refl l2])
    have f2: "defl_todo_box ?T (Suc (length rns))
        = (real_of_int (l + r) / 2 ^ Suc k, real_of_int (2 * r) / 2 ^ Suc k)"
      by (rule defl_todo_box_append_snd[OF l1 refl l2])
    from tri show ?thesis
    proof (elim disjE)
      assume A: "real_of_int (2 * l) / 2 ^ Suc k < y
                 \<and> y < real_of_int (l + r) / 2 ^ Suc k"
      have lt: "length rns < length (fst (snd ?T))" by simp
      have "fst (defl_todo_box ?T (length rns)) < y
            \<and> y < snd (defl_todo_box ?T (length rns))" using A f1 by simp
      with lt show ?thesis by blast
    next
      \<comment> \<open>the MID case, and the only one that differs from the non-firing twin: the point goes
         into \<open>acc\<close> as a degenerate pair, at the index the push just created.\<close>
      assume M: "y = real_of_int (l + r) / 2 ^ Suc k"
      have lt: "length ?A < length (?A @ [((l + r, l + r), Suc k)])" by simp
      have e: "(?A @ [((l + r, l + r), Suc k)]) ! length ?A = ((l + r, l + r), Suc k)"
        by (simp add: nth_append)
      have "real_of_int (l + r) / 2 ^ Suc k = y \<and> real_of_int (l + r) / 2 ^ Suc k = y"
        using M by simp
      with lt e show ?thesis unfolding push by blast
    next
      assume A: "real_of_int (l + r) / 2 ^ Suc k < y
                 \<and> y < real_of_int (2 * r) / 2 ^ Suc k"
      have lt: "Suc (length rns) < length (fst (snd ?T))" by simp
      have "fst (defl_todo_box ?T (Suc (length rns))) < y
            \<and> y < snd (defl_todo_box ?T (Suc (length rns)))" using A f2 by simp
      with lt show ?thesis by blast
    qed
  qed
qed
text \<open>\<^bold>\<open>The reject arm's fact, at an arbitrary point of the box.\<close> @{thm [source] defl_node_box_no_roots} is stated at
  \<open>(l + (r - l)\<cdot>t)/2\<^sup>k\<close> for \<open>t \<in> (0,1)\<close>, the form the local-to-global bridge produces. The reject arm and the left-only split
  ask for it at an arbitrary \<open>y\<close> strictly inside a box; one \<open>t\<close> closes the gap.\<close>

lemma defl_node_box_no_roots_y:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and cnt: "carried_descartes_count X = 0"
    and ne: "0 < length X"
    and lr: "l < r"
    and lo: "real_of_int l / 2 ^ k < y" and hi: "y < real_of_int r / 2 ^ k"
  shows "poly (of_int_poly (Poly rp) :: real poly) y \<noteq> 0"
proof -
  define t where "t = (y * 2 ^ k - real_of_int l) / (real_of_int r - real_of_int l)"
  have dpos: "(0::real) < real_of_int r - real_of_int l" using lr by simp
  have kpos: "(0::real) < 2 ^ k" by simp
  have y1: "real_of_int l < y * 2 ^ k" using lo kpos by (simp add: field_simps)
  have y2: "y * 2 ^ k < real_of_int r" using hi kpos by (simp add: field_simps)
  have t0: "0 < t" unfolding t_def using y1 dpos by simp
  have t1: "t < 1" unfolding t_def using y2 dpos by (simp add: field_simps)
  have yeq: "y = (real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k"
    unfolding t_def using dpos kpos by (simp add: field_simps)
  show ?thesis
    using defl_node_box_no_roots[OF wrel cnt ne t0 t1] yeq by simp
qed

text \<open>\<^bold>\<open>The split arm, left child only.\<close> The right half is root-free and the midpoint is not a root (on \<open>rz\<close> the shed
  provably did not fire), so the left child alone keeps every root of the current box pending. \<open>acc\<close> is unchanged.\<close>

lemma defl_pending_covers_split_left:
  assumes cov: "defl_dispatch_covers P0 lo (lns, rns, ks) acc l r k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and nomid: "poly P0 (real_of_int (l + r) / 2 ^ Suc k) \<noteq> 0"
    and noright: "\<And>y::real. real_of_int (l + r) / 2 ^ Suc k < y
                    \<Longrightarrow> y < real_of_int (2 * r) / 2 ^ Suc k \<Longrightarrow> poly P0 y \<noteq> 0"
  shows "defl_pending_covers P0 lo (lns @ [2 * l], rns @ [l + r], ks @ [Suc k]) acc"
  unfolding defl_pending_covers_def
proof (intro allI impI)
  fix y :: real
  assume yl: "lo < y" and yz: "poly P0 y = 0"
  let ?T = "(lns @ [2 * l], rns @ [l + r], ks @ [Suc k])"
  from cov yl yz consider
      (inacc) "\<exists>j A B m. j < length (dyadic_interval_vec_triples acc)
                 \<and> dyadic_interval_vec_triples acc ! j = ((A, B), m)
                 \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
                    \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y))"
    | (inbox) "\<exists>i < length rns. fst (defl_todo_box (lns, rns, ks) i) < y
                 \<and> y < snd (defl_todo_box (lns, rns, ks) i)"
    | (cur) "real_of_int l / 2 ^ k < y \<and> y < real_of_int r / 2 ^ k"
    unfolding defl_dispatch_covers_def fst_conv snd_conv by blast
  then show "(\<exists>j A B m. j < length (dyadic_interval_vec_triples acc)
           \<and> dyadic_interval_vec_triples acc ! j = ((A, B), m)
           \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
              \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y)))
      \<or> (\<exists>i < length (fst (snd ?T)). fst (defl_todo_box ?T i) < y
             \<and> y < snd (defl_todo_box ?T i))"
  proof cases
    case inacc thus ?thesis by blast
  next
    case inbox
    then obtain i where i: "i < length rns"
      and b: "fst (defl_todo_box (lns, rns, ks) i) < y"
             "y < snd (defl_todo_box (lns, rns, ks) i)" by blast
    have eq: "defl_todo_box ?T i = defl_todo_box (lns, rns, ks) i"
      using i l1 l2 unfolding defl_todo_box_def by (simp add: nth_append)
    have lt: "i < length (fst (snd ?T))" using i by simp
    have "fst (defl_todo_box ?T i) < y \<and> y < snd (defl_todo_box ?T i)"
      using b eq by simp
    with lt show ?thesis by blast
  next
    case cur
    have tri: "(real_of_int (2 * l) / 2 ^ Suc k < y \<and> y < real_of_int (l + r) / 2 ^ Suc k)
         \<or> y = real_of_int (l + r) / 2 ^ Suc k
         \<or> (real_of_int (l + r) / 2 ^ Suc k < y \<and> y < real_of_int (2 * r) / 2 ^ Suc k)"
      using cur by (intro defl_box_split_cover) auto
    have f1: "defl_todo_box ?T (length rns)
        = (real_of_int (2 * l) / 2 ^ Suc k, real_of_int (l + r) / 2 ^ Suc k)"
      using l1 l2 unfolding defl_todo_box_def by (simp add: nth_append)
    from tri show ?thesis
    proof (elim disjE)
      assume A: "real_of_int (2 * l) / 2 ^ Suc k < y
                 \<and> y < real_of_int (l + r) / 2 ^ Suc k"
      have lt: "length rns < length (fst (snd ?T))" by simp
      have "fst (defl_todo_box ?T (length rns)) < y
            \<and> y < snd (defl_todo_box ?T (length rns))" using A f1 by simp
      with lt show ?thesis by blast
    next
      assume "y = real_of_int (l + r) / 2 ^ Suc k"
      thus ?thesis using yz nomid by simp
    next
      \<comment> \<open>the skipped RIGHT half: no root lives there, so this case is vacuous.\<close>
      assume A: "real_of_int (l + r) / 2 ^ Suc k < y
                 \<and> y < real_of_int (2 * r) / 2 ^ Suc k"
      have "poly P0 y \<noteq> 0" by (rule noright) (use A in auto)
      thus ?thesis using yz by simp
    qed
  qed
qed




section \<open>The reject arm preserves the invariant\<close>

text \<open>\<^bold>\<open>The simplest arm.\<close> @{const hybrid_branch_zero_monadic} frees the popped node and returns the state unchanged, so
  two of the three clauses carry over directly and the only content is coverage: the discarded box must hold no root of
  \<open>P\<^sub>0\<close>, which @{thm [source] defl_node_box_no_roots} reads off the zero count and
  @{thm [source] defl_pending_covers_reject} turns into the clause. Without the cached-count clause of the coupling there
  would be no route to \<open>noroot\<close>.\<close>

lemma defl_branch_zero_invar:
  assumes coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates P0 acc"
    and cov: "defl_dispatch_covers P0 lo (lns, rns, ks) acc l_num r_num k"
    and noroot: "\<And>y::real. real_of_int l_num / 2 ^ k < y \<Longrightarrow> y < real_of_int r_num / 2 ^ k
                   \<Longrightarrow> poly P0 y \<noteq> 0"
  shows "hybrid_branch_zero_monadic (lns, rns, ks) qtodo es ss cs gs rp acc l_num r_num Q
       \<le> SPEC (defl_loop_invar P0 lo)"
proof -
  have cov': "defl_pending_covers P0 lo (lns, rns, ks) acc"
    by (rule defl_pending_covers_reject[OF cov noroot])
  have inv: "defl_loop_invar P0 lo ((((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc))"
    unfolding defl_loop_invar_def using iso cov' coup by simp
  \<comment> \<open>\<open>mpzb_discard_monadic\<close> is \<open>RETURN ()\<close>, so unfolding it collapses both binds; \<open>poly_free_monadic\<close> collapses via its
     \<open>= RETURN ()\<close> simp lemma. Left to \<open>refine_vcg\<close>, the two discards would become an unrelated \<open>RES UNIV\<close>/\<open>SUCCEED\<close> case
     split.\<close>
  show ?thesis
    unfolding hybrid_branch_zero_monadic_def PR_CONST_def mpzb_discard_monadic_def
    using inv by simp
qed



section \<open>The accept arm preserves the invariant\<close>

text \<open>\<^bold>\<open>The second arm, and the classic op needs no deflating twin.\<close>
  @{const hybrid_branch_one_monadic} is reused VERBATIM by the deflating dispatch, and
  @{thm [source] hybrid_branch_one_correct} already pins its result state exactly -- so the whole
  arm is: push the accepted box onto \<open>acc\<close>, and show the three clauses survive.

  Coupling is untouched (the worklist does not move). Coverage moves the current box from the
  third alternative into the first (@{thm [source] defl_pending_covers_accept}). Soundness is the
  only clause with real content, and it is @{thm [source] defl_node_box_pair_ok}: the cached count
  of ONE means the box isolates a root of \<open>P\<^sub>0\<close>, which is exactly what
  @{const defl_acc_isolates} asserts of everything in \<open>acc\<close>.\<close>

lemma defl_branch_one_invar:
  assumes coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates P0 (al, ar, ak)"
    and cov: "defl_dispatch_covers P0 lo (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and lal: "length al = length ar" and lak: "length ar = length ak"
    and push: "dyadic_interval_vec_pushable (al, ar, ak)"
    and pairok: "dsc_pair_ok P0 (real_of_int l_num / 2 ^ k, real_of_int r_num / 2 ^ k)"
  shows "hybrid_branch_one_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k Q
       \<le> SPEC (defl_loop_invar P0 lo)"
proof -
  have iso': "defl_acc_isolates P0 (al @ [l_num], ar @ [r_num], ak @ [k])"
    by (rule defl_acc_isolates_push[OF iso lal lak pairok])
  have cov': "defl_pending_covers P0 lo (lns, rns, ks) (al @ [l_num], ar @ [r_num], ak @ [k])"
    by (rule defl_pending_covers_accept[OF cov lal lak])
  have inv: "defl_loop_invar P0 lo
      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp),
       (al @ [l_num], ar @ [r_num], ak @ [k]))"
    unfolding defl_loop_invar_def using iso' cov' coup by simp
  show ?thesis
    by (rule order_trans[OF hybrid_branch_one_correct[OF push]]) (simp add: inv)
qed



section \<open>The split arm's state result\<close>

text \<open>\<^bold>\<open>The coupling clause does not depend on where the children went; the other two clauses do.\<close>
  \<open>defl_branch_split_exact_coupling\<close> needs only that the two pushed nodes are well formed. Coverage needs the pushed boxes by
  name, and soundness needs to know whether the midpoint leaf was appended to \<open>acc\<close>, so this second pass fixes the worklist and
  gives the \<open>acc\<close> dichotomy, as @{thm [source] hybrid_branch_split_exact_acc} does for the non-deflating arm. The two passes
  are joined by @{thm [source] defl_SPEC_conj}.

  \<^bold>\<open>The ghosts cannot be fixed to \<open>carried_left X\<close> here either.\<close> The non-deflating arm supplies
  @{thm [source] hybrid_split_pair_state_correct} with \<open>[where XL = "carried_left X"]\<close>, whose \<open>lockL\<close> side condition is then
  \<open>2\<^sup>4\<^sup>2 \<le> gl \<longrightarrow> carried_left X = ql\<close>. On a fired node that is false (the stored child is the deflated one), so the state pass
  has its own tail lemma with the children as ordinary variables, as the coupling pass does.\<close>

lemma defl_split_tail_state:
  assumes frameL: "node_frame XL ql gl" and frameR: "node_frame XR qr gr"
    and lockL: "4398046511104 \<le> gl \<longrightarrow> ql = XL"
    and lockR: "4398046511104 \<le> gr \<longrightarrow> qr = XR"
    and lenL: "length ql \<le> length rp" and lenR: "length qr \<le> length rp"
    \<comment> \<open>\<^bold>\<open>A direct word bound, NOT \<open>gl \<le> 2\<^sup>4\<^sup>2\<close>.\<close> The gate-open arm calls the split at the
       LOCK-WITH-PAYLOAD guard \<open>2\<^sup>4\<^sup>2 + v\<close>, which is strictly ABOVE \<open>2\<^sup>4\<^sup>2\<close> -- so a premise
       capping the child guard at the literal makes this lemma inapplicable there (the classic
       side hits the same thing and carries \<open>gcap_rp\<close>/\<open>gcap_lock\<close> as two separate instances).
       Bounding \<open>gl + length rp\<close> instead covers both call sites, and it is what
       @{thm [source] hybrid_split_pair_state_correct} actually needs.\<close>
    and glb: "gl + length rp < max_snat LENGTH(gmp_poly_len)"
    and grb: "gr + length rp < max_snat LENGTH(gmp_poly_len)"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kcap: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_split_pair_state_monadic (lns, rns, ks) qtodo es ss cs gs rp
             l_num r_num k e s mid ql gl qr gr
    \<comment> \<open>\<^bold>\<open>Stated with \<open>fst\<close>, not a 7-tuple PATTERN.\<close> The consumer's goal is \<open>fst wl = \<dots>\<close> after
       \<open>RETURN (wl, acc)\<close>; a \<open>case_prod\<close> postcondition has to be destructured before it can be
       used there, and the \<open>refine_vcg\<close> chain leaves the state only PARTLY split (\<open>x x1 x2\<close>),
       so the two never meet. Same shape as the \<open>gbind_decomp\<close> lesson: extensionally equal,
       different TERM.\<close>
       \<le> SPEC (\<lambda>st. fst st = (lns @ [2 * l_num, l_num + r_num],
                    rns @ [l_num + r_num, 2 * r_num], ks @ [Suc k, Suc k]))"
proof -
  have lXL: "length XL = length ql" by (rule cdlr_node_frame_len[OF frameL])
  have lXR: "length XR = length qr" by (rule cdlr_node_frame_len[OF frameR])
  have leL: "length XL \<le> length rp" using lXL lenL by simp
  have leR: "length XR \<le> length rp" using lXR lenR by simp
  have lbL: "length XL + 1 < max_snat LENGTH(gmp_poly_len)" using leL rpb by simp
  have lbR: "length XR + 1 < max_snat LENGTH(gmp_poly_len)" using leR rpb by simp
  have pbL: "length XL * nat_bitlen (length XL) < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_pb_mono[OF leL rp_pb])
  have pbR: "length XR * nat_bitlen (length XR) < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_pb_mono[OF leR rp_pb])
  have gbL: "gl + length XL < max_snat LENGTH(gmp_poly_len)" using glb leL by simp
  have gbR: "gr + length XR < max_snat LENGTH(gmp_poly_len)" using grb leR by simp
  have lockL': "4398046511104 \<le> gl \<longrightarrow> XL = ql" using lockL by simp
  have lockR': "4398046511104 \<le> gr \<longrightarrow> XR = qr" using lockR by simp
  show ?thesis
    by (rule order_trans[OF hybrid_split_pair_state_correct[where XL = XL and XR = XR,
        OF frameL frameR lockL' lockR' lbL lbR pbL pbR gbL gbR
           qcap gcap ecap sscap ccap push kcap scap1]]) auto
qed

text \<open>\<^bold>\<open>The left-only state tail\<close>: the one-push version of the lemma above, for the \<open>rz\<close> branch.\<close>

lemma defl_split_tail_state_left:
  assumes frameL: "node_frame XL ql gl"
    and lockL: "4398046511104 \<le> gl \<longrightarrow> ql = XL"
    and lenL: "length ql \<le> length rp"
    and glb: "gl + length rp < max_snat LENGTH(gmp_poly_len)"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kcap: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_split_pair_state_left_monadic (lns, rns, ks) qtodo es ss cs gs rp
             l_num r_num k e s mid ql gl
       \<le> SPEC (\<lambda>st. fst st = (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [Suc k]))"
proof -
  have lXL: "length XL = length ql" by (rule cdlr_node_frame_len[OF frameL])
  have leL: "length XL \<le> length rp" using lXL lenL by simp
  have lbL: "length XL + 1 < max_snat LENGTH(gmp_poly_len)" using leL rpb by simp
  have pbL: "length XL * nat_bitlen (length XL) < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_pb_mono[OF leL rp_pb])
  have gbL: "gl + length XL < max_snat LENGTH(gmp_poly_len)" using glb leL by simp
  have lockL': "4398046511104 \<le> gl \<longrightarrow> XL = ql" using lockL by simp
  show ?thesis
    by (rule order_trans[OF hybrid_split_pair_state_left_correct[where XL = XL,
        OF frameL lockL' lbL pbL gbL qcap gcap ecap sscap ccap push kcap scap1]]) auto
qed

text \<open>The worklist result is a dichotomy: two pushes, or, on \<open>rz\<close>, the left child alone, in which case the contract's
  interlock gives the two facts coverage needs: the exact right child counts \<open>0\<close>, and the shed did not fire (so the midpoint is
  not a root).\<close>

lemma defl_branch_split_exact_state:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qlen3: "3 \<le> length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and lenQrp: "length Q \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (\<lambda>(wl, acc').
           (fst wl = (lns @ [2 * l_num, l_num + r_num],
                      rns @ [l_num + r_num, 2 * r_num], ks @ [Suc k, Suc k])
            \<or> (fst wl = (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [Suc k])
               \<and> carried_descartes_count (carried_right X) = 0
               \<and> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0))
           \<and> (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0
               \<longrightarrow> acc' = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [Suc k]))
           \<and> (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0
               \<longrightarrow> acc' = (al, ar, ak)))"
proof -
  have Qne: "0 < length Q" using Qlen3 by linarith
  \<comment> \<open>the children contract's three word bounds, derived as in the coupling pass.\<close>
  have Qsmall: "length Q < 1099511627776" using lenQrp rp_small by linarith
  have Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)" by (rule small_len_b2[OF Qsmall])
  have dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)" by (rule small_len_dep[OF Qsmall])
  have kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    using gcap_rp lenQrp max.cobounded1[of g 4398046511104] by linarith
  have pm: "carried_push_mid_monadic (al, ar, ak) l_num r_num k
      \<le> SPEC (\<lambda>a. a = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1]))"
    by (simp add: cdlr_push_mid_eq[OF accpush])
  \<comment> \<open>closers without search, as in the coupling pass\<close>
  have gl_bound: "x \<le> max g 4398046511104 \<Longrightarrow> x + length rp < max_snat LENGTH(gmp_poly_len)"
    for x using gcap_rp by linarith
  have len_rp: "x \<le> length Q \<Longrightarrow> x \<le> length rp" for x using lenQrp by linarith
  show ?thesis
    unfolding defl_branch_split_monadic_def poly_length_monadic_def PR_CONST_def
    using gex Qlen3 Qne Qbound kcap rpne rpb krp accpush qcap gcap ecap sscap ccap push scap1
    apply (refine_vcg
        defl_split_children_gbind[OF frame lock gex Qlen3 Qbound Qbound2 dep kb]
        defl_split_children_gbind_decomp[OF frame lock gex Qlen3 Qbound Qbound2 dep kb]
        defl_split_tail_state[THEN order_trans]
        defl_split_tail_state_left[THEN order_trans]
        pm[THEN order_trans])
    apply (all \<open>(assumption; fail)?\<close>)
    \<comment> \<open>Unlike the coupling pass, this one does not depend on which exact child the ghost is: the conclusion fixes only
       the worklist, so \<open>refine_vcg\<close> may take \<open>XL := ql\<close>, and the frame goal becomes the reflexive \<open>node_frame ql ql gl\<close>.\<close>
    apply (all \<open>((rule node_frame_exact_any_g); fail)?\<close>)
    apply (all \<open>((rule gl_bound, assumption); fail)?\<close>)
    apply (all \<open>((rule len_rp, assumption); fail)?\<close>)
    apply (all \<open>((insert gex Qlen3, simp); fail)?\<close>)
    apply (all \<open>((insert rpb rp_small rp_pb kcap scap1, simp); fail)?\<close>)
    apply (all \<open>(simp; fail)?\<close>)
    done
qed


section \<open>The split arm preserves the invariant\<close>

text \<open>\<^bold>\<open>The arm with two \<open>refine_vcg\<close> passes.\<close> The coupling pass and the state pass are joined by
  @{thm [source] defl_SPEC_conj}, and the three clauses follow from the per-arm steps: coupling directly, soundness by
  @{thm [source] defl_acc_isolates_push} with @{thm [source] defl_mid_pair_ok}, and coverage by
  @{thm [source] defl_pending_covers_split_fire} or \<open>_nofire\<close> according to the shed. \<open>P\<^sub>0\<close> is the root polynomial's real
  image here, not an abstract parameter: every fact feeding this lemma is stated about \<open>rp\<close>, and fixing it avoids an
  equation under a \<open>refine_vcg\<close> postcondition.\<close>

theorem defl_branch_split_exact_invar:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    \<comment> \<open>in @{const defl_node_ok}'s own shape, so the assembly reads it off the popped node.\<close>
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    and gceil: "g \<le> 4398046511104 + length rp"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qlen3: "3 \<le> length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and lenQrp: "length Q \<le> length rp"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)"
    and cov: "defl_dispatch_covers (of_int_poly (Poly rp) :: real poly) lo
                (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
    \<comment> \<open>\<^bold>\<open>Last\<close>, immediately before \<open>shows\<close>, so that no existing \<open>[OF \<dots>]\<close> position in a caller moves.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
  shows "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo)"
proof -
  \<comment> \<open>the two payload clauses, for EITHER outcome of the shed, derived once so the final step
     is a substitution rather than a case analysis under a \<open>refine_vcg\<close> postcondition.\<close>
  \<comment> \<open>\<^bold>\<open>Stated COMPONENTWISE.\<close> \<open>clarsimp\<close> destructures the accumulator and splits the two
     dichotomy equations into three each, so a \<open>payload\<close> phrased about \<open>acc'\<close> as a TRIPLE no
     longer matches its own hypotheses at the call site.\<close>
  have payload: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (a1, a2, a3)
      \<and> defl_pending_covers (of_int_poly (Poly rp) :: real poly) lo
          (lns @ [2 * l_num, l_num + r_num],
           rns @ [l_num + r_num, 2 * r_num], ks @ [Suc k, Suc k]) (a1, a2, a3)"
    if F: "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0
             \<longrightarrow> a1 = al @ [l_num + r_num] \<and> a2 = ar @ [l_num + r_num]
                 \<and> a3 = ak @ [Suc k]"
      and N: "poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0
             \<longrightarrow> a1 = al \<and> a2 = ar \<and> a3 = ak"
    for a1 a2 a3
  proof (cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0")
    case fired: True
    have accd: "a1 = al @ [l_num + r_num]" "a2 = ar @ [l_num + r_num]" "a3 = ak @ [Suc k]"
      using F fired by simp_all
    \<comment> \<open>\<open>of_int_add\<close>: the mid fact says \<open>(real l + real r)/2\<^sup>k\<^sup>+\<^sup>1\<close> and the push lemma asks for
       \<open>real (l + r)/2\<^sup>k\<^sup>+\<^sup>1\<close> -- equal, different TERM.\<close>
    have pk: "dsc_pair_ok (of_int_poly (Poly rp) :: real poly)
          (real_of_int (l_num + r_num) / 2 ^ Suc k,
           real_of_int (l_num + r_num) / 2 ^ Suc k)"
      using defl_mid_pair_ok[OF wrel fired] by simp
    show ?thesis
      unfolding accd
      using defl_acc_isolates_push[OF iso lal lak pk]
            defl_pending_covers_split_fire[OF cov l1 l2 lal lak]
      by simp
  next
    case nofire: False
    have accd: "a1 = al" "a2 = ar" "a3 = ak" using N nofire by simp_all
    \<comment> \<open>\<open>of_int_add\<close> again, in the other direction: the coverage step asks for
       \<open>real (l + r)\<close> and the mid fact delivers \<open>real l + real r\<close>. Equal, different TERM, and
       \<open>OF\<close> reports \<open>no unifiers\<close>.\<close>
    have nomid: "poly (of_int_poly (Poly rp) :: real poly)
          (real_of_int (l_num + r_num) / 2 ^ Suc k) \<noteq> 0"
      using defl_mid_not_root_global[OF wrel nofire] by simp
    show ?thesis
      unfolding accd
      using iso defl_pending_covers_split_nofire[OF cov l1 l2 nomid] by simp
  qed
  \<comment> \<open>\<^bold>\<open>The left-only payload.\<close> On \<open>rz\<close> the shed did not fire, so \<open>acc\<close> is unchanged and the midpoint is not a root; and
     the exact right child counts \<open>0\<close>, so its box (the right half) holds no root of \<open>P\<^sub>0\<close>. Its \<open>l < r\<close> is not a premise: any \<open>y\<close>
     strictly inside the half makes the half non-empty, which is all @{thm [source] defl_node_box_no_roots_y} needs.\<close>
  have payload1: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)
      \<and> defl_pending_covers (of_int_poly (Poly rp) :: real poly) lo
          (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [Suc k]) (al, ar, ak)"
    if cnt0: "carried_descartes_count (carried_right X) = 0"
      and nofire: "poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0"
  proof -
    have nomid: "poly (of_int_poly (Poly rp) :: real poly)
          (real_of_int (l_num + r_num) / 2 ^ Suc k) \<noteq> 0"
      using defl_mid_not_root_global[OF wrel nofire] by simp
    have cong: "defl_node_wrel (carried_right (carried_init_same_den l_num (2 ^ k) r_num rp))
                               (carried_right X)"
      by (rule defl_node_wrel_carried_right[OF wrel])
    have ini: "carried_right (carried_init_same_den l_num (2 ^ k) r_num rp)
        = carried_init_same_den (l_num + r_num) (2 ^ Suc k) (2 * r_num) rp"
      using carried_init_child_right[of "2 ^ k" l_num r_num rp] by simp
    have wrelR: "defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k) (2 * r_num) rp)
                   (carried_right X)"
      using cong ini by simp
    have neX: "0 < length X" using cdlr_node_frame_len[OF frame] Qlen3 by linarith
    have neR: "0 < length (carried_right X)" using neX by simp
    have noright: "poly (of_int_poly (Poly rp) :: real poly) y \<noteq> 0"
      if lo': "real_of_int (l_num + r_num) / 2 ^ Suc k < y"
        and hi': "y < real_of_int (2 * r_num) / 2 ^ Suc k" for y
    proof -
      have "real_of_int (l_num + r_num) / 2 ^ Suc k < real_of_int (2 * r_num) / 2 ^ Suc k"
        using lo' hi' by linarith
      \<comment> \<open>cancel the common denominator FIRST: left to \<open>simp\<close>, \<open>2 ^ Suc k\<close> and \<open>2 * r\<close> are
         normalised and cancelled against each other before the division ever compares.\<close>
      hence "real_of_int (l_num + r_num) < real_of_int (2 * r_num)"
        unfolding divide_less_cancel by simp
      hence lr': "l_num + r_num < 2 * r_num" by (simp only: of_int_less_iff)
      show ?thesis by (rule defl_node_box_no_roots_y[OF wrelR cnt0 neR lr' lo' hi'])
    qed
    show ?thesis
      using iso defl_pending_covers_split_left[OF cov l1 l2 nomid noright] by simp
  qed
  \<comment> \<open>\<^bold>\<open>Let @{thm [source] defl_SPEC_conj} BUILD the conjoined postcondition\<close> rather than
     restating it: written out by hand it is a nested \<open>case\<close> over a pair inside a pair, and a
     single missing \<open>\<Rightarrow>\<close> is an inner-syntax error rather than a mismatch.\<close>
  show ?thesis
    apply (rule order_trans[OF defl_SPEC_conj[OF
          defl_branch_split_exact_coupling[OF frame lock gex pay gceil gcap_rp Qlen3 Qbound wrel lenQrp
            rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecap sscap ccap push scap1 coup dvdX]
          defl_branch_split_exact_state[OF frame lock gex gcap_rp Qlen3 Qbound lenQrp
            rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecap sscap ccap push scap1]]])
    apply (rule SPEC_rule)
    apply (clarsimp simp: defl_loop_invar_def)
    \<comment> \<open>the worklist is a dichotomy, so \<open>clarsimp\<close> cannot substitute it; it is split first, and a second \<open>clarsimp\<close>
       substitutes each side.\<close>
    apply (erule disjE)
     apply clarsimp
     apply (rule conjI)
      apply (rule conjunct1[OF payload]; assumption)
     apply (rule conjunct2[OF payload]; assumption)
    apply clarsimp
    apply (rule payload1; assumption)
    done
qed



section \<open>The non-deflating child build, strengthened for the deflating consumers\<close>

text \<open>\<^bold>\<open>What the existing contract lacks.\<close> @{thm [source] truncate_children_mid_agrees} gives the two child frames, the
  \<open>max g 2\<^sup>4\<^sup>2\<close> bound and the lock conjuncts, but not the guard trichotomy \<open>gl \<le> 1 \<or> 2\<^sup>4\<^sup>2 \<le> gl\<close>, which decides the deflating
  coupling's budget clause. It is derivable only under \<open>gex\<close>: at \<open>g = 0\<close> the child guards are \<open>0\<close> and the re-truncation can only
  raise them to \<open>1\<close>; at a lock guard they are returned unchanged. For a truncated node (\<open>0 < g < 2\<^sup>4\<^sup>2\<close>) neither holds, which is
  why the deflating stack gates its child build on \<open>gex\<close>.

  \<^bold>\<open>The escalating arm uses this.\<close> Under \<open>gex\<close> and \<open>len < 3\<close> the gate-open reject path reaches
  @{const defl_split_children_escalate_monadic}, whose \<open>code = 2\<close> rebuild cannot occur, so it reduces to this op, with the
  children undeflated and the node relation reflexive.\<close>

lemma defl_children_mid_gex_agrees:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_children_mid_monadic g Q
      \<le> SPEC (\<lambda>(ql, gl, qr, gr, mids, midbl).
          node_frame (carried_left X) ql gl \<and> node_frame (carried_right X) qr gr \<and>
          0 < length ql \<and> length ql \<le> length Q \<and>
          0 < length qr \<and> length qr \<le> length Q \<and>
          gl \<le> max g 4398046511104 \<and> gr \<le> max g 4398046511104 \<and>
          (gl \<le> 1 \<or> 4398046511104 \<le> gl) \<and> (gr \<le> 1 \<or> 4398046511104 \<le> gr) \<and>
          (4398046511104 \<le> gl \<longrightarrow> ql = carried_left X) \<and>
          (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X) \<and>
          mids = sgn (carried_right Q ! 0))"
proof -
  have QX: "Q = X"
  proof (cases "g = 0")
    case True
    have "X = Q" using frame True unfolding node_frame_def by simp
    thus ?thesis by (rule sym)
  next
    case False
    thus ?thesis using gex lock by simp
  qed
  have lb_l: "length (carried_left Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lb_r: "length (carried_right Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    using Qbound by simp_all
  have rne: "0 < length (carried_right Q)" using Qne by simp
  have lne: "0 < length (carried_left Q)" using Qne by simp
  have rneL: "carried_right Q \<noteq> []"
    using rne length_greater_0_conv[of "carried_right Q"] by blast
  have lneL: "carried_left Q \<noteq> []"
    using lne length_greater_0_conv[of "carried_left Q"] by blast
  have lr_step: "carried_left_right_monadic Q \<bind> f
      \<le> f (carried_left Q, carried_right Q)" for f
  proof -
    have "carried_left_right_monadic Q \<bind> f
        \<le> RETURN (carried_left Q, carried_right Q) \<bind> f"
      by (rule bind_mono(1)[OF carried_left_right_monadic_correct[OF Qne Qbound]]) simp
    also have "\<dots> = f (carried_left Q, carried_right Q)" by simp
    finally show ?thesis .
  qed
  have eqL: "carried_left Q = carried_left X" and eqR: "carried_right Q = carried_right X"
    using QX by simp_all
  \<comment> \<open>\<^bold>\<open>Unfold the guards op and split cases, rather than supplying an equation.\<close> Given
     \<open>truncate_child_guards_mop g len = RETURN (g, g)\<close> as a simp rule, the guards bind stays unreduced at the head and the
     \<open>lr_step\<close> collapse below has nothing to match. @{thm [source] truncate_children_mid_agrees} does the same: it unfolds
     \<open>truncate_child_guards_mop_def\<close> inside each guard case and lets \<open>simp\<close> resolve the cascade against that case's
     hypothesis.\<close>
  show ?thesis
  proof (cases "g = 0")
    case zero: True
    \<comment> \<open>\<open>simp add: zero\<close> substitutes \<open>g \<mapsto> 0\<close> into the guard, so the retrunc calls arrive at the
       LITERAL \<open>0\<close> and a rule fed at \<open>gin = g\<close> no longer matches. Instantiate the disjunct.\<close>
    have gz: "(0::nat) = 0 \<or> 4398046511104 \<le> (0::nat)" by simp
    show ?thesis
      unfolding truncate_children_mid_monadic_def PR_CONST_def poly_length_monadic_def
        truncate_child_guards_mop_def
        poly_coeff_sgn_monadic_def poly_coeff_bitlen2_monadic_def
      using Qne Qbound
      apply (simp add: zero)
      apply (rule order_trans[OF lr_step])
      apply (simp add: lb_l lb_r rne lne)
      apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
          defl_retrunc_frame_any[OF gz, THEN order_trans])
      \<comment> \<open>\<^bold>\<open>The destructuring step.\<close> Without it the remaining goals are \<open>x1b \<noteq> []\<close> over raw \<open>refine_vcg\<close> tuple variables,
         with the split present only as a chain of equations (\<open>x2c = (x1d, x2d)\<close>, \<open>x2b = (x1c, x2c)\<close>, \<dots>). \<open>clarsimp?\<close> is used
         separately because it closes some goals outright.\<close>
      apply (all \<open>clarsimp?\<close>)
      apply (all \<open>(assumption; fail)?\<close>)
      apply (all \<open>((insert Qne Qbound lb_l lb_r rne lne, simp); fail)?\<close>)
      \<comment> \<open>\<open>dest: cdlr_node_frame_len\<close>: the child LENGTH bounds are read off the frame the
         retruncation returns, and @{const node_frame} is opaque to \<open>simp\<close> without it.\<close>
      apply (all \<open>((insert zero eqL eqR lne rne,
                    auto simp: max_def dest: cdlr_node_frame_len); fail)?\<close>)
      apply (all \<open>((rule rneL | rule lneL); fail)?\<close>)
      done
  next
    case nz: False
    hence glock: "4398046511104 \<le> g" using gex by simp
    show ?thesis
      unfolding truncate_children_mid_monadic_def PR_CONST_def poly_length_monadic_def
        truncate_child_guards_mop_def
        poly_coeff_sgn_monadic_def poly_coeff_bitlen2_monadic_def
      using Qne Qbound
      apply (simp add: nz glock)
      apply (rule order_trans[OF lr_step])
      apply (simp add: lb_l lb_r rne lne)
      apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
          defl_retrunc_frame_any[OF gex, THEN order_trans])
      apply (all \<open>clarsimp?\<close>)
      apply (all \<open>(assumption; fail)?\<close>)
      apply (all \<open>((insert Qne Qbound lb_l lb_r rne lne, simp); fail)?\<close>)
      apply (all \<open>((insert glock eqL eqR lne rne,
                    auto simp: max_def dest: cdlr_node_frame_len); fail)?\<close>)
      apply (all \<open>((rule rneL | rule lneL); fail)?\<close>)
      done
  qed
qed



section \<open>The escalating arm's child build\<close>

text \<open>\<^bold>\<open>Smaller than its shape suggests.\<close> @{const defl_split_children_escalate_monadic} reads \<open>len0\<close>, builds children,
  decides, and on \<open>code = 2\<close> frees them, rebuilds from the root and re-enters the deflating build. Under \<open>gex\<close>,
  @{thm [source] defl_decide_fire_iff} gives \<open>code \<noteq> 2\<close>, so the ambiguous branch cannot occur, as on the main arm. What
  remains is the plain child build, with the children undeflated and the node relation reflexive. The conclusion is that of
  @{thm [source] defl_split_children_agrees}, so the arm lemmas of \<open>defl_branch_split_monadic\<close> can use either arm through one
  interface.\<close>

text \<open>\<^bold>\<open>The children build with the right-child decide, under \<open>gex\<close>\<close>: the counterpart of
  @{thm [source] defl_children_mid_gex_agrees} for @{const truncate_children_mid_skip_right_monadic}, which may prove the right
  child empty (\<open>rz\<close>) and then returns the singleton stub. @{thm [source] truncate_children_mid_skip_right_agrees} gives the
  frames and the interlock but not the guard trichotomy or the child lengths that decide the deflating coupling's budget;
  under \<open>gex\<close> both come from @{thm [source] defl_retrunc_frame_any}, as on the main arm.\<close>

lemma defl_children_mid_skip_right_gex_agrees:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_children_mid_skip_right_monadic g Q
      \<le> SPEC (\<lambda>(ql, gl, qr, gr, mids, midbl, rz).
          node_frame (carried_left X) ql gl \<and>
          (\<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X)) \<and>
          (rz \<longrightarrow> carried_descartes_count (carried_right X) = 0 \<and>
                  carried_right Q ! 0 \<noteq> 0) \<and>
          0 < length ql \<and> length ql \<le> length Q \<and>
          0 < length qr \<and> length qr \<le> length Q \<and>
          gl \<le> max g 4398046511104 \<and> gr \<le> max g 4398046511104 \<and>
          (gl \<le> 1 \<or> 4398046511104 \<le> gl) \<and> (gr \<le> 1 \<or> 4398046511104 \<le> gr) \<and>
          (4398046511104 \<le> gl \<longrightarrow> ql = carried_left X) \<and>
          mids = sgn (carried_right Q ! 0))"
proof -
  have QX: "Q = X"
  proof (cases "g = 0")
    case True
    have "X = Q" using frame True unfolding node_frame_def by simp
    thus ?thesis by (rule sym)
  next
    case False
    thus ?thesis using gex lock by simp
  qed
  have lb_l: "length (carried_left Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lb_r: "length (carried_right Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    using Qbound by simp_all
  have rne: "0 < length (carried_right Q)" using Qne by simp
  have gg: "truncate_child_guards_mop g n = RETURN (g, g)" for n
    unfolding truncate_child_guards_mop_def using gex by auto
  have eqL: "carried_left Q = carried_left X" and eqR: "carried_right Q = carried_right X"
    using QX by simp_all
  show ?thesis
    unfolding truncate_children_mid_skip_right_monadic_def PR_CONST_def poly_length_monadic_def
      poly_coeff_sgn_monadic_def poly_coeff_bitlen2_monadic_def
    using Qne Qbound Qbound2 dep
    apply (simp add: gg)
    apply (rule carried_left_right_skip_right_bind[OF Qne Qbound2 dep kb])
    subgoal for r rz
      apply (cases rz)
      \<comment> \<open>\<open>rz\<close>: the stub branch --- its frame is guarded away, only its length is claimed.\<close>
      subgoal
        apply (simp add: lb_l)
        apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
            defl_retrunc_frame_any[OF gex, THEN order_trans])
        apply (all \<open>clarsimp?\<close>)
        apply (all \<open>((insert Qne Qbound, simp); fail)?\<close>)
        apply (all \<open>((insert eqL gex QX, auto simp: max_def); fail)?\<close>)
        done
      subgoal
        apply (simp add: lb_l lb_r rne)
        apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
            defl_retrunc_frame_any[OF gex, THEN order_trans])
        apply (all \<open>clarsimp?\<close>)
        apply (all \<open>((insert Qne Qbound, simp); fail)?\<close>)
        apply (all \<open>((insert eqL eqR gex QX, auto simp: max_def); fail)?\<close>)
        done
      done
    done
qed

text \<open>The escalating contract has the main arm's six-tuple conclusion (\<open>rz\<close> last) and rests on the lemma above. The shed
  never fires on this arm (the ambiguous rebuild cannot occur under \<open>gex\<close>), so both witnesses are the undeflated children, and
  the interlock \<open>rz \<longrightarrow> \<not> fired\<close> is read off \<open>carried_right Q ! 0 \<noteq> 0\<close>.\<close>

lemma defl_split_children_escalate_agrees:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the children build's three word bounds.\<close>
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
  shows "defl_split_children_escalate_monadic l_num r_num k rp g len Q
      \<le> SPEC (\<lambda>(ql, gl, qr, gr, fired, rz).
          (\<exists>XL. node_frame XL ql gl \<and> defl_node_rel (carried_left X) XL
                \<and> (4398046511104 \<le> gl \<longrightarrow> ql = XL)) \<and>
          (\<not> rz \<longrightarrow> (\<exists>XR. node_frame XR qr gr \<and> defl_node_rel (carried_right X) XR
                \<and> (4398046511104 \<le> gr \<longrightarrow> qr = XR))) \<and>
          (rz \<longrightarrow> carried_descartes_count (carried_right X) = 0 \<and> \<not> fired) \<and>
          gl \<le> max g 4398046511104 \<and> gr \<le> max g 4398046511104 \<and>
          (gl \<le> 1 \<or> 4398046511104 \<le> gl) \<and>
          (gr \<le> 1 \<or> 4398046511104 \<le> gr) \<and>
          0 < length ql \<and> length ql \<le> length Q \<and>
          0 < length qr \<and> length qr \<le> length Q \<and>
          (fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0) \<and>
          (\<not> fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0))"
proof -
  have QX: "Q = X"
  proof (cases "g = 0")
    case True
    have "X = Q" using frame True unfolding node_frame_def by simp
    thus ?thesis by (rule sym)
  next
    case False
    thus ?thesis using gex lock by simp
  qed
  have midpoly: "(carried_right Q ! 0 = 0)
      = (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0)"
    using carried_right_nth0_zero_iff[OF Qne] QX by simp
  have nrL: "defl_node_rel (carried_left X) (carried_left X)"
    and nrR: "defl_node_rel (carried_right X) (carried_right X)"
    by (simp_all add: defl_node_rel_refl)
  show ?thesis
    unfolding defl_split_children_escalate_monadic_def PR_CONST_def poly_length_monadic_def
    using Qne Qbound Qbound2 dep rpne rpb krp
    \<comment> \<open>\<^bold>\<open>TWO stages with a \<open>clarsimp\<close> between\<close>: until the children contract's tuple is
       DESTRUCTURED the decide fact's \<open>mids_eq\<close> premise cannot match it -- so \<open>code \<noteq> 2\<close> never
       arrives and the ambiguous rebuild branch stays live in the goal.\<close>
    apply (refine_vcg
        defl_children_mid_skip_right_gex_agrees[OF frame lock gex Qne Qbound Qbound2 dep kb,
          THEN order_trans])
    apply (all \<open>clarsimp?\<close>)
    apply (refine_vcg
        defl_decide_fire_iff[where Q = Q, OF gex refl, THEN order_trans])
    apply (all \<open>clarsimp?\<close>)
    apply (all \<open>(assumption; fail)?\<close>)
    apply (all \<open>((insert midpoly nrL nrR Qne Qbound, auto); fail)?\<close>)
    done
qed


section \<open>The deflating worklist's word budget, linear in \<open>\<mu>\<close>\<close>

text \<open>\<^bold>\<open>Why this replaces @{const hybrid_budget_invar} here.\<close> That invariant charges every
  pending node \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 - 2\<close> future worklist entries and \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 - 1\<close> future accumulator entries ---
  the size of a complete binary tree below it --- so its seed needs \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 + 1 < 2\<^sup>6\<^sup>3\<close>, i.e.
  \<open>\<mu> \<le> 61\<close>, a floor on the root separation. The loop pops from the end, so its worklist is a
  depth-first stack, and @{const stack_ok} bounds it by \<open>\<mu>(0,1) + 1\<close> entries with the same
  preservation premises (pop, one child, two children, each strictly smaller).

  \<^bold>\<open>The accumulator half is not an invariant of this theory.\<close> No bound linear in \<open>\<mu>\<close>
  exists for it without roots: what bounds it is that the emitted windows are disjoint and each
  holds a root. That is the geometric invariant of \<open>Deflation_Loop_Geom\<close>, so here the accumulator
  capacity is a premise of the step (the second conjunct of \<open>defl_budget_invar\<close>), which the
  geometry-carrying loop supplies. These are proof-side predicates; the code is the same.\<close>

definition defl_stack_invar :: "real \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "defl_stack_invar \<delta> l0 r0 k0 todo \<longleftrightarrow>
     int (dyadic_iv_interval_mu \<delta> (0, 1)) + 3 < int (max_snat LENGTH(gmp_poly_len))
     \<and> length (fst todo) \<le> length (hybrid_alpha_views l0 r0 k0 todo)
     \<and> stack_ok (dyadic_iv_interval_mu \<delta> (0, 1))
         (map (dyadic_iv_interval_mu \<delta>) (hybrid_alpha_views l0 r0 k0 todo))"

definition defl_budget_invar ::
  "real \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "defl_budget_invar \<delta> l0 r0 k0 todo acc \<longleftrightarrow>
     defl_stack_invar \<delta> l0 r0 k0 todo
     \<and> int (length (fst acc)) + 2 < int (max_snat LENGTH(gmp_poly_len))"

lemma defl_budget_invarI:
  assumes "defl_stack_invar \<delta> l0 r0 k0 todo"
    and "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
  shows "defl_budget_invar \<delta> l0 r0 k0 todo (al, ar, ak)"
  using assms unfolding defl_budget_invar_def by simp

lemma defl_budget_invar_stack:
  "defl_budget_invar \<delta> l0 r0 k0 todo acc \<Longrightarrow> defl_stack_invar \<delta> l0 r0 k0 todo"
  unfolding defl_budget_invar_def by simp

lemma defl_stack_invar_todo_cap:
  assumes s: "defl_stack_invar \<delta> l0 r0 k0 (lns, rns, ks)"
  shows "length lns + 2 < max_snat LENGTH(gmp_poly_len)"
proof -
  let ?M = "dyadic_iv_interval_mu \<delta> (0, 1)"
  let ?vs = "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)"
  have M: "int ?M + 3 < int (max_snat LENGTH(gmp_poly_len))"
    and le: "length lns \<le> length ?vs"
    and st: "stack_ok ?M (map (dyadic_iv_interval_mu \<delta>) ?vs)"
    using s unfolding defl_stack_invar_def by simp_all
  have "length (map (dyadic_iv_interval_mu \<delta>) ?vs) \<le> Suc ?M"
    by (rule stack_ok_length[OF st]) (auto simp: dyadic_iv_interval_mu_def mu_def)
  then have "length lns \<le> Suc ?M" using le by simp
  then show ?thesis using M by linarith
qed

lemma defl_stack_invar_pop:
  assumes s: "defl_stack_invar \<delta> l0 r0 k0 (lns, rns, ks)"
    and vdec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
               = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks) @ [I]"
  shows "defl_stack_invar \<delta> l0 r0 k0 (butlast lns, butlast rns, butlast ks)"
proof -
  let ?M = "dyadic_iv_interval_mu \<delta> (0, 1)"
  let ?V = "hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)"
  have M: "int ?M + 3 < int (max_snat LENGTH(gmp_poly_len))"
    and le: "length lns \<le> length (?V @ [I])"
    and st: "stack_ok ?M (map (dyadic_iv_interval_mu \<delta>) ?V @ [dyadic_iv_interval_mu \<delta> I])"
    using s unfolding defl_stack_invar_def vdec by simp_all
  have "stack_ok ?M (map (dyadic_iv_interval_mu \<delta>) ?V)" by (rule stack_ok_pop[OF st])
  moreover have "length (butlast lns) \<le> length ?V" using le by simp
  ultimately show ?thesis using M unfolding defl_stack_invar_def by simp
qed

lemma defl_stack_invar_push1:
  assumes s: "defl_stack_invar \<delta> l0 r0 k0 (lns, rns, ks)"
    and vdec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks) = VS @ [I]"
    and vpush: "hybrid_alpha_views l0 r0 k0 (lns', rns', ks') = VS @ [J]"
    and len': "length lns' \<le> length lns"
    and muJ: "dyadic_iv_interval_mu \<delta> J < dyadic_iv_interval_mu \<delta> I"
  shows "defl_stack_invar \<delta> l0 r0 k0 (lns', rns', ks')"
proof -
  let ?M = "dyadic_iv_interval_mu \<delta> (0, 1)"
  have M: "int ?M + 3 < int (max_snat LENGTH(gmp_poly_len))"
    and le: "length lns \<le> length (VS @ [I])"
    and st: "stack_ok ?M (map (dyadic_iv_interval_mu \<delta>) VS @ [dyadic_iv_interval_mu \<delta> I])"
    using s unfolding defl_stack_invar_def vdec by simp_all
  have "stack_ok ?M (map (dyadic_iv_interval_mu \<delta>) VS @ [dyadic_iv_interval_mu \<delta> J])"
    by (rule stack_ok_replace[OF st]) (use muJ in simp)
  moreover have "length lns' \<le> length (VS @ [J])" using le len' by simp
  ultimately show ?thesis using M unfolding defl_stack_invar_def vpush by simp
qed

lemma defl_stack_invar_push2:
  assumes s: "defl_stack_invar \<delta> l0 r0 k0 (lns, rns, ks)"
    and vdec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks) = VS @ [I]"
    and vpush: "hybrid_alpha_views l0 r0 k0 (lns', rns', ks') = VS @ [IL, IR]"
    and len': "length lns' = length lns + 1"
    and muL: "dyadic_iv_interval_mu \<delta> IL < dyadic_iv_interval_mu \<delta> I"
    and muR: "dyadic_iv_interval_mu \<delta> IR < dyadic_iv_interval_mu \<delta> I"
  shows "defl_stack_invar \<delta> l0 r0 k0 (lns', rns', ks')"
proof -
  let ?M = "dyadic_iv_interval_mu \<delta> (0, 1)"
  have M: "int ?M + 3 < int (max_snat LENGTH(gmp_poly_len))"
    and le: "length lns \<le> length (VS @ [I])"
    and st: "stack_ok ?M (map (dyadic_iv_interval_mu \<delta>) VS @ [dyadic_iv_interval_mu \<delta> I])"
    using s unfolding defl_stack_invar_def vdec by simp_all
  have "stack_ok ?M (map (dyadic_iv_interval_mu \<delta>) VS
                       @ [dyadic_iv_interval_mu \<delta> IL, dyadic_iv_interval_mu \<delta> IR])"
    by (rule stack_ok_push2[OF st muL muR])
  moreover have "length lns' \<le> length (VS @ [IL, IR])" using le len' by simp
  ultimately show ?thesis using M unfolding defl_stack_invar_def vpush by simp
qed

lemma defl_stack_invar_seed:
  assumes mucap: "int (dyadic_iv_interval_mu \<delta> (0, 1)) + 3 < int (max_snat LENGTH(gmp_poly_len))"
    and vseed: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks) = [(0, 1)]"
    and lone: "length lns = 1"
  shows "defl_stack_invar \<delta> l0 r0 k0 (lns, rns, ks)"
  unfolding defl_stack_invar_def vseed using mucap lone by (simp add: stack_ok_seed)

text \<open>\<^bold>\<open>The budget-level interface\<close>: the names and premise lists of the
  \<open>hybrid_budget_invar_*\<close> lemmas the arms were written against, so each arm changes only the
  constant it cites. Every conclusion is the STACK half: the accumulator half is re-supplied at
  the next step by the caller.\<close>

lemma defl_budget_invar_todo_cap:
  assumes "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) acc"
  shows "length lns + 2 < max_snat LENGTH(gmp_poly_len)"
  by (rule defl_stack_invar_todo_cap[OF defl_budget_invar_stack[OF assms]])

lemma defl_budget_invar_acc_grown:
  assumes b: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and lne: "lns \<noteq> []" and lr: "length rns = length lns" and lk: "length ks = length lns"
  shows "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
  using b unfolding defl_budget_invar_def by simp

lemma defl_budget_invar_pop:
  assumes b0: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) acc"
    and vdec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
               = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks) @ [I]"
  shows "defl_stack_invar \<delta> l0 r0 k0 (butlast lns, butlast rns, butlast ks)"
  by (rule defl_stack_invar_pop[OF defl_budget_invar_stack[OF b0] vdec])

lemma defl_budget_invar_accept:
  assumes b: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and vdec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
               = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks) @ [I]"
    and accg: "length al' \<le> length al + 1"
  shows "defl_stack_invar \<delta> l0 r0 k0 (butlast lns, butlast rns, butlast ks)"
  by (rule defl_stack_invar_pop[OF defl_budget_invar_stack[OF b] vdec])

lemma defl_budget_invar_push2_branched:
  assumes b: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and vdec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks) = VS @ [I]"
    and vpush: "hybrid_alpha_views l0 r0 k0 (lns', rns', ks') = VS @ [IL, IR]"
    and len': "length lns' = length lns + 1"
    and muL: "dyadic_iv_interval_mu \<delta> IL < dyadic_iv_interval_mu \<delta> I"
    and muR: "dyadic_iv_interval_mu \<delta> IR < dyadic_iv_interval_mu \<delta> I"
    and grow: "Q \<longrightarrow> al' = al @ [x] \<and> ar' = ar @ [y] \<and> ak' = ak @ [z]"
    and keep: "\<not> Q \<longrightarrow> al' = al \<and> ar' = ar \<and> ak' = ak"
  shows "defl_stack_invar \<delta> l0 r0 k0 (lns', rns', ks')"
  by (rule defl_stack_invar_push2[OF defl_budget_invar_stack[OF b] vdec vpush len' muL muR])

lemma defl_budget_invar_push1:
  assumes b: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and vdec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks) = VS @ [I]"
    and vpush: "hybrid_alpha_views l0 r0 k0 (lns', rns', ks') = VS @ [J]"
    and len': "length lns' \<le> length lns"
    and muJ: "dyadic_iv_interval_mu \<delta> J < dyadic_iv_interval_mu \<delta> I"
    and accs: "length al' \<le> length al"
  shows "defl_stack_invar \<delta> l0 r0 k0 (lns', rns', ks')"
  by (rule defl_stack_invar_push1[OF defl_budget_invar_stack[OF b] vdec vpush len' muJ])


section \<open>The WHILEIT bundle\<close>

text \<open>The four arm lemmas above each conclude \<open>\<le> SPEC (defl_loop_invar P\<^sub>0 lo)\<close>, while the \<open>WHILEIT\<close> that
  @{const defl_loop_monadic} runs needs \<open>hybrid_loop_safe_invar \<and> cap \<and> budget \<and> pay \<and> P-eq \<and> defl_loop_invar\<close> and a variant
  decrease. The deflating loop uses @{const hybrid_loop_safe_invar} and @{const hybrid_loop_cond} unchanged
  (\<open>defl_loop_stateful_monadic\<close> in \<open>Hybrid_Solver_Pipeline\<close>), so the strengthening step, the well-founded measure and the loop
  capstone follow the non-deflating ones with @{const defl_loop_body_checked_monadic} substituted.

  \<^bold>\<open>What is not in the bundle\<close>: @{const hybrid_refine_invar}, the \<open>\<exists>pol\<close> machinery. The deflating loop proves no multiset
  equality, so the layers that build and maintain that witness have no counterpart; @{const defl_loop_invar} takes that slot.\<close>

definition defl_state_invar ::
  "real \<Rightarrow> int poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> real
     \<Rightarrow> hybrid_state \<Rightarrow> bool" where
  \<comment> \<open>\<^bold>\<open>@{const hybrid_pay_invar} is not in the bundle.\<close> Its atom bounds @{const carried_descartes_count} of the node's
     init, while the deflating window push stores \<open>2\<^sup>4\<^sup>2 + v\<close> with \<open>v\<close> the count of the possibly deflated object, and a Descartes
     count does not transport between the two. (A pop arm alone cannot reveal this, since every clause is preserved by
     restriction to a prefix; the push arms can.) The payload is stated in @{const defl_node_ok} about the exact object \<open>X\<close>,
     where it is provable (the split child's monotonicity becomes sub-box monotonicity within one polynomial,
     @{thm [source] defl_child_count_mono}), so the bundle provides it through @{const defl_loop_invar}'s coupling clause at
     every node.\<close>
  "defl_state_invar \<delta> P l0 r0 k0 P0 lo st \<longleftrightarrow>
     (case st of ((todo, qtodo, es, ss, cs, gs, rp), acc) \<Rightarrow>
        hybrid_cap_invar \<delta> l0 r0 k0 todo ss \<and>
        defl_stack_invar \<delta> l0 r0 k0 todo \<and>
        coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp \<and>
        defl_loop_invar P0 lo st)"

lemma defl_state_invar_simp[simp]:
  "defl_state_invar \<delta> P l0 r0 k0 P0 lo ((todo, qtodo, es, ss, cs, gs, rp), acc)
     \<longleftrightarrow> hybrid_cap_invar \<delta> l0 r0 k0 todo ss \<and>
         defl_stack_invar \<delta> l0 r0 k0 todo \<and>
         coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp \<and>
         defl_loop_invar P0 lo ((todo, qtodo, es, ss, cs, gs, rp), acc)"
  by (simp add: defl_state_invar_def)

text \<open>\<^bold>\<open>The exit, lifted through the bundle.\<close> The deflation-specific half is
  @{thm [source] defl_loop_invar_exit}; the bundle merely has to be projected first. This is the
  fact the loop capstone's \<open>exit\<close> obligation consumes, and the \<open>\<not> hybrid_loop_cond\<close> premise is
  turned into the empty-worklist premise here so that no later layer has to unfold
  @{const hybrid_loop_cond} again.\<close>

lemma defl_state_invar_exit:
  assumes inv: "defl_state_invar \<delta> P l0 r0 k0 P0 lo (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and ncond: "\<not> hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
  shows "defl_acc_isolates P0 acc" and "defl_acc_covers P0 lo acc"
proof -
  \<comment> \<open>\<^bold>\<open>The two predicates read DIFFERENT columns\<close>: @{const hybrid_loop_cond} tests \<open>lns\<close>
     while @{const defl_pending_covers} (and hence @{thm [source] defl_loop_invar_exit}) counts
     \<open>rns\<close>. The bridge is the column-length conjunct of @{const hybrid_loop_state_invar}, which
     is why that premise is here and not an oversight.\<close>
  have lnil: "lns = []" using ncond by (simp add: hybrid_loop_cond_def)
  have leq: "length rns = length lns"
    using stinv
    by (simp add: hybrid_loop_state_invar_def dyadic_interval_vec_invar_def)
  have empty: "fst (snd (lns, rns, ks)) = []" using lnil leq by simp
  have inv': "defl_loop_invar P0 lo (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    using inv by simp
  show "defl_acc_isolates P0 acc" by (rule defl_loop_invar_exit(1)[OF inv' empty])
  show "defl_acc_covers P0 lo acc" by (rule defl_loop_invar_exit(2)[OF inv' empty])
qed

subsection \<open>The loop as a bare \<open>WHILEIT\<close>, strengthened, with its measure\<close>

text \<open>Counterparts of @{thm [source] hybrid_loop_monadic_unfold} / @{thm [source] hybrid_loop_strengthened} /
  @{thm [source] hybrid_loop_correct}, with @{const defl_loop_body_checked_monadic} in place of the non-deflating body.
  \<open>WHILEIT_weaken\<close> is applied once, by an explicit \<open>rule\<close>: in a \<open>refine_vcg\<close> hint list its schematic \<open>?I'\<close> would apply it to
  its own output indefinitely.\<close>

lemma defl_loop_monadic_unfold:
  "defl_loop_monadic todo qtodo es ss cs gs rp acc
     = WHILEIT hybrid_loop_safe_invar hybrid_loop_cond
         defl_loop_body_checked_monadic ((todo, qtodo, es, ss, cs, gs, rp), acc)"
  unfolding defl_loop_monadic_def defl_loop_stateful_monadic_def PR_CONST_def
  by simp

lemma defl_loop_strengthened:
  "defl_loop_monadic todo qtodo es ss cs gs rp acc
     \<le> WHILEIT (\<lambda>st. hybrid_loop_safe_invar st \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo st)
         hybrid_loop_cond defl_loop_body_checked_monadic
         ((todo, qtodo, es, ss, cs, gs, rp), acc)"
  unfolding defl_loop_monadic_unfold
  by (rule WHILEIT_weaken) simp

text \<open>\<^bold>\<open>The measure is REUSED, not cloned\<close>: deflation sheds a root from a node's polynomial and
  never moves its box, so @{const hybrid_state_mu} --- which reads only the node columns
  (@{thm [source] hybrid_state_mu_simp}) --- is the deflating loop's variant unchanged, and
  @{thm [source] hybrid_state_mu_wf} is its well-foundedness.\<close>

lemma defl_loop_correct:
  assumes init: "hybrid_loop_safe_invar ((todo, qtodo, es, ss, cs, gs, rp), acc)
                 \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo
                     ((todo, qtodo, es, ss, cs, gs, rp), acc)"
    and step: "\<And>s. \<lbrakk> hybrid_loop_safe_invar s \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo s;
                      hybrid_loop_cond s \<rbrakk>
               \<Longrightarrow> defl_loop_body_checked_monadic s
                 \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s'
                                 \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo s')
                          \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                            < hybrid_state_mu \<delta> l0 r0 k0 s)"
    and exit: "\<And>s. \<lbrakk> hybrid_loop_safe_invar s \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo s;
                      \<not> hybrid_loop_cond s \<rbrakk> \<Longrightarrow> \<Phi> s"
  shows "defl_loop_monadic todo qtodo es ss cs gs rp acc \<le> SPEC \<Phi>"
  apply (rule order_trans[OF defl_loop_strengthened])
  \<comment> \<open>BARE \<open>apply\<close>, not \<open>subgoal by \<dots>\<close>, for the classic lemma's reason: the invariant's
     parameters are still SCHEMATIC and SHARED across the three subgoals, and a \<open>subgoal\<close>
     block would FIX them.\<close>
  apply (rule WHILEIT_rule[where
      R = "{(st', st). hybrid_state_mu \<delta> l0 r0 k0 st' < hybrid_state_mu \<delta> l0 r0 k0 st}"])
  apply (rule hybrid_state_mu_wf)
  apply (rule init)
  apply (simp only: mem_Collect_eq prod.case)
  apply (rule step, assumption+)
  apply (rule exit, assumption+)
  done

subsection \<open>Body-under-condition and the step's ARGS form\<close>

text \<open>Clones of @{thm [source] hybrid_loop_body_under_cond} /
  @{thm [source] hybrid_loop_step_unfold}: under the loop condition the checked body IS the
  step, and the step only destructures the flattened state. Together they turn the capstone's
  body obligation into an obligation on @{const defl_loop_step_args_monadic} --- the shape every
  arm lemma is already stated against.\<close>

lemma defl_loop_body_under_cond:
  assumes c: "hybrid_loop_cond st"
  shows "defl_loop_body_checked_monadic st = defl_loop_step_monadic st"
  unfolding defl_loop_body_checked_monadic_def PR_CONST_def using c by simp

lemma defl_loop_step_unfold:
  "defl_loop_step_monadic ((todo, qtodo, es, ss, cs, gs, rp), acc)
     = defl_loop_step_args_monadic todo qtodo es ss cs gs acc rp"
  unfolding defl_loop_step_monadic_def PR_CONST_def by simp

subsection \<open>The reject arm's body step, at the FULL bundle\<close>

text \<open>\<^bold>\<open>The de-risking step, and it passes.\<close> Same join as
  @{thm [source] hybrid_body_step_discard}, with the \<open>\<exists>pol\<close> step lemma
  (\<open>hybrid_refine_invar_discard_step\<close>) replaced by @{const defl_loop_invar} at the popped
  state --- which @{thm [source] defl_branch_zero_invar} already delivers --- and everything
  else identical. The three classic preservation lemmas fire unchanged:
  @{thm [source] hybrid_cap_invar_pop}, @{thm [source] hybrid_budget_invar_pop} and (for the
  reject arm, which pushes nothing) @{thm [source] hybrid_pay_invar_pop} via \<open>paypop\<close>.

  \<^bold>\<open>\<open>arm\<close> and \<open>invpop\<close> are separate hypotheses on purpose.\<close> The arm's result state is PINNED
  by \<open>arm\<close>, so carrying the invariant as a second fact about that pinned state is equivalent to
  conjoining it into the \<open>SPEC\<close> and avoids a pair-pattern that \<open>clarsimp\<close> would destructure.
  Step 3 of the completion path supplies \<open>arm\<close> (the pop-level state equation) and
  @{thm [source] defl_branch_zero_invar} supplies \<open>invpop\<close>.\<close>

lemma defl_body_step_discard:
  assumes cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [nd]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [I]"
    and safe': "hybrid_loop_safe_invar
                  (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                    butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) acc"
    and clr: "length lns = length ks" and crr: "length rns = length ks"
    and csk: "length ss = length ks"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and arm: "defl_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs acc rp
              \<le> SPEC (\<lambda>(wl, acc'). acc' = acc \<and>
                    wl = ((butlast lns, butlast rns, butlast ks), butlast qtodo,
                          butlast es, butlast ss, butlast cs, butlast gs, rp))"
    and invpop: "defl_loop_invar P0 lo
                   (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                     butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
  shows "defl_loop_body_checked_monadic (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s'
                       \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc))"
  apply (subst defl_loop_body_under_cond[OF cond])
  apply (subst defl_loop_step_unfold)
  apply (rule order_trans[OF arm])
  apply (rule SPEC_rule)
  \<comment> \<open>do NOT \<open>clarsimp\<close> first: it destructures \<open>acc\<close>, after which the facts stated at \<open>acc\<close>
     no longer match syntactically --- the classic lemma's own warning.\<close>
  using safe' invpop
        hybrid_state_mu_pop_less[OF nsplit]
        hybrid_cap_invar_pop[OF capinv clr crr csk]
        defl_budget_invar_pop[OF budinv vsplit]
        Pcoeffs
  by auto


section \<open>The window child's box holds every root of the node's box\<close>

text \<open>\<^bold>\<open>The chain for the window arm's coverage.\<close> The fact \<open>carried_repr_scalar X u v (newton_wcand e m X)\<close> at the node's
  own frame decomposes into existing facts:

  \<^item> @{thm [source] newton_wcand_repr_scalar_bl} (\<open>Bail_Loop_Refine\<close>) is the composition law, at an arbitrary anchor
    \<open>carried_repr_scalar P a b Q\<close>;
  \<^item> the anchor at the node's own frame is \<open>carried_repr_scalar X 0 1 X\<close>, and @{const local_poly_rat} at \<open>(0,1)\<close> is the
    identity, because @{thm [source] taylor_shift_list_zero} and @{thm [source] scale_poly_list_one} are \<open>[simp]\<close>
    (\<open>defl_repr_scalar_self\<close> below);
  \<^item> @{thm [source] newton_wcand_count_bl} turns that into a \<open>descartes_list_int\<close> equation on the node's unit box, and
    @{thm [source] newton_window_pick_bail_count} says the value is the parent's count \<open>v\<close>;
  \<^item> @{thm [source] carried_repr_count} at @{thm [source] carried_repr_init} says the parent's own count is
    \<open>descartes_list_int 0 1 X\<close>, so the two counts are equal;
  \<^item> @{thm [source] descartes_list_int_eq_Bernstein_changes} (\<open>Window_Mono\<close>) carries both sides into
    @{const Bernstein_changes}, the shape @{thm [source] Bernstein_window_no_roots_outside} consumes.

  What needs proving is a bound that the bail theory states only upwards (@{thm [source] newton_window_pick_bail_m_bound}):
  the grid index is non-negative, so the window's left endpoint does not leave the node's box. Everything here is in the
  node's local frame, over the unit box \<open>(0,1)\<close>, the frame of @{const defl_node_rel} and
  @{thm [source] defl_carried_init_zero_iff_real}.\<close>

lemma newton_window_pick_bail_m_nonneg:
  assumes "newton_window_pick_bail v e Q = Some (m, cand)"
  shows "0 \<le> m"
proof -
  \<comment> \<open>the counterpart of @{thm [source] newton_window_pick_bail_m_bound}, using the other half of the snap bracket:
     \<open>2 \<le> kn\<close> (@{thm [source] newton_snap_kn_ge2_bl}) and \<open>m = kn - 2\<close>. Every pick is a @{const newton_try_side} accept, so
     there is one case.\<close>
  have side: "\<And>loc. newton_try_side loc v e Q = Some (m, cand) \<Longrightarrow> 0 \<le> m"
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
    have "2 \<le> newton_snap_kn e num den" by (rule newton_snap_kn_ge2_bl)
    thus "0 \<le> m" using m_eq by simp
  qed
  show ?thesis
    using assms side by (auto simp: newton_window_pick_bail_def split: if_splits)
qed

lemma defl_local_poly_rat_unit: "local_poly_rat 0 1 X = map rat_of_int X"
  by (simp add: local_poly_rat_def)

lemma defl_repr_scalar_self: "carried_repr_scalar X 0 1 X"
  unfolding carried_repr_scalar_def
  by (rule exI[of _ 1]) (simp add: defl_local_poly_rat_unit smult_list_def rev_map)

text \<open>The node's own count, in the abstract form the Bernstein bridge reads.\<close>

lemma defl_count_unit_box: "carried_descartes_count X = descartes_list_int 0 1 X"
  by (rule carried_repr_count[OF carried_repr_init])

text \<open>\<^bold>\<open>The window arm's coverage fact.\<close> An ACCEPTED window child's grid cell contains, strictly,
  every root of the node's polynomial in the node's open unit box. Stated about \<open>X\<close> --- the node's
  own EXACT polynomial, which is what \<open>defl_gate_open_monadic\<close>'s \<open>qx\<close> is after
  @{const hybrid_cond_escalate_monadic} --- so nothing here mentions \<open>rp\<close>, the global frame, or
  the deflation. Carrying it to \<open>P\<^sub>0\<close>'s roots in the node's BOX is
  @{thm [source] defl_carried_init_zero_iff_real} plus @{const defl_node_rel}, both already proven.\<close>

theorem defl_window_no_roots_outside_local:
  fixes X :: "int list" and m :: int and e :: nat
  defines "s \<equiv> (2 :: int) ^ (2 ^ e + 2)"
  defines "u \<equiv> (of_int m / of_int s :: rat)"
    and "w \<equiv> (of_int (m + 4) / of_int s :: rat)"
  assumes lenX: "0 < length X"
    and pick: "newton_window_pick_bail v e X = Some (m, cand)"
    and vX: "carried_descartes_count X = v"
    and Xnz: "(map_poly of_int (Poly X) :: real poly) \<noteq> 0"
    and root: "poly (map_poly of_int (Poly X) :: real poly) x = 0"
    and x0: "0 < x" and x1: "x < 1"
  shows "real_of_int m / 2 ^ (2 ^ e + 2) < x
       \<and> x < real_of_int (m + 4) / 2 ^ (2 ^ e + 2)"
proof -
  have spos: "0 < s" unfolding s_def by simp
  have s4N: "s = int (4 * N_of e)" unfolding s_def using four_N_of_pow2 by simp
  have m0: "0 \<le> m" by (rule newton_window_pick_bail_m_nonneg[OF pick])
  have m4: "m + 4 \<le> s" using newton_window_pick_bail_m_bound[OF pick] s4N by simp
  \<comment> \<open>the grid cell sits inside the unit box\<close>
  have u0: "0 \<le> u" unfolding u_def using m0 spos by (simp add: zero_le_divide_iff)
  have w1: "w \<le> 1" unfolding w_def using m4 spos by (simp add: divide_le_eq_1)
  have uw: "u < w" unfolding u_def w_def using spos by (simp add: divide_strict_right_mono)
  have uwne: "u \<noteq> w" using uw by simp
  \<comment> \<open>\<^bold>\<open>the count equality\<close>, in \<open>descartes_list_int\<close> form on both sides\<close>
  have cand_eq: "cand = newton_wcand e m X" by (rule newton_window_pick_bail_cand[OF pick])
  have ne': "(0 :: rat) + (of_int m / of_int s) * (1 - 0)
           \<noteq> 0 + (of_int (m + 4) / of_int s) * (1 - 0)"
    using uwne unfolding u_def w_def by simp
  have wc: "carried_descartes_count (newton_wcand e m X)
          = descartes_list_int (0 + (of_int m / of_int s) * (1 - 0))
                               (0 + (of_int (m + 4) / of_int s) * (1 - 0)) X"
    unfolding s_def
    by (rule newton_wcand_count_bl[OF defl_repr_scalar_self lenX])
       (use ne' in \<open>simp add: s_def\<close>)
  have dwin: "descartes_list_int u w X = v"
    using wc cand_eq newton_window_pick_bail_count[OF pick]
    unfolding u_def w_def by simp
  have dunit: "descartes_list_int 0 1 X = v" using defl_count_unit_box vX by simp
  \<comment> \<open>\<^bold>\<open>the Bernstein bridge\<close>, once per box\<close>
  let ?P = "(map_poly of_int (Poly X) :: real poly)"
  let ?p = "length X - 1"
  have bwin: "int (descartes_list_int u w X)
            = Bernstein_changes ?p (of_rat u) (of_rat w) ?P"
    by (rule descartes_list_int_eq_Bernstein_changes[OF lenX uw])
  have bunit: "int (descartes_list_int 0 1 X)
             = Bernstein_changes ?p (of_rat (0::rat)) (of_rat (1::rat)) ?P"
    by (rule descartes_list_int_eq_Bernstein_changes[OF lenX]) simp
  have v_I: "Bernstein_changes ?p (real_of_rat u) (real_of_rat w) ?P
           = Bernstein_changes ?p 0 1 ?P"
    \<comment> \<open>do NOT feed \<open>zero_rat\<close>/\<open>one_rat\<close> here: they REWRITE \<open>0\<close> and \<open>1\<close> into
       \<open>Rat.Fract\<close> form, after which \<open>of_rat_0\<close>/\<open>of_rat_1\<close> no longer match and the goal
       survives with two un-normalised endpoints.\<close>
    using bwin bunit dwin dunit by simp
  \<comment> \<open>\<^bold>\<open>and the window-accept argument closes it\<close>\<close>
  have degX: "degree ?P \<le> ?p"
  proof -
    have "degree ?P \<le> degree (Poly X)" by (rule degree_map_poly_le)
    also have "\<dots> \<le> length X - 1"
      using lenX by (simp add: degree_le coeff_Poly nth_default_beyond)
    finally show ?thesis .
  qed
  have lo': "(0::real) \<le> fst (real_of_rat u, real_of_rat w)" using u0 by (simp add: of_rat_less_eq)
  have hi': "snd (real_of_rat u, real_of_rat w) \<le> (1::real)"
    \<comment> \<open>not \<open>simp add: of_rat_1[symmetric]\<close>: that orients \<open>1 = of_rat 1\<close> and rewrites the \<open>1\<close> it just produced
       indefinitely. The bound is coerced first, and then the \<open>[simp]\<close> rule \<open>of_rat_1\<close> fires in its own direction.\<close>
  proof -
    have "real_of_rat w \<le> real_of_rat 1" using w1 by (simp add: of_rat_less_eq)
    thus ?thesis by simp
  qed
  have sp': "fst (real_of_rat u, real_of_rat w) < snd (real_of_rat u, real_of_rat w)"
    using uw by (simp add: of_rat_less)
  have vI': "Bernstein_changes ?p (fst (real_of_rat u, real_of_rat w))
                (snd (real_of_rat u, real_of_rat w)) ?P
           = Bernstein_changes ?p 0 1 ?P"
    using v_I by simp
  \<comment> \<open>the coercion, at the two CONCRETE endpoints. A schematic \<open>\<And>i. real_of_rat (of_int i / \<dots>)\<close>
     does NOT serve: \<open>simp\<close> normalises \<open>of_int (m + 4) :: rat\<close> to \<open>rat_of_int m + 4\<close> in the goal,
     after which the schematic fact no longer matches at \<open>i := m + 4\<close>.\<close>
  \<comment> \<open>\<open>simp\<close> normalises \<open>2 ^ (2\<^sup>e + 2)\<close> to \<open>4 * 2 ^ 2\<^sup>e\<close> and \<open>of_int (m + 4)\<close> to
     \<open>rat_of_int m + 4\<close> on BOTH sides, so \<open>real_of_rat\<close> has to be pushed through a product, a
     power, a sum and a numeral --- not just through the division.\<close>
  note ofrat = of_rat_divide of_rat_power of_rat_mult of_rat_add of_rat_numeral_eq
  have coeL: "real_of_rat u = real_of_int m / 2 ^ (2 ^ e + 2)"
    unfolding u_def s_def by (simp add: ofrat)
  have coeR: "real_of_rat w = real_of_int (m + 4) / 2 ^ (2 ^ e + 2)"
    unfolding w_def s_def by (simp add: ofrat)
  show ?thesis
    using Bernstein_window_no_roots_outside[OF degX Xnz zero_less_one lo' sp' hi' vI'
            root x0 x1] coeL coeR
    by simp
qed


section \<open>The window child's box in global coordinates, and the coverage clause\<close>

text \<open>\<^bold>\<open>Three small pieces and one transfer.\<close> The previous section is stated in the node's local frame, where the box
  is \<open>(0,1)\<close> and the window is the grid cell \<open>(m/s, (m+4)/s)\<close>. The coverage clause is about \<open>P\<^sub>0\<close> on real boxes given by
  numerators over \<open>2\<^sup>k\<close>, and @{thm [source] hybrid_window_push_cols} says which numerators the push writes:
  \<open>l\<cdot>s + m(r-l)\<close> and \<open>l\<cdot>s + (m+4)(r-l)\<close> over \<open>2\<^sup>k\<^sup>+\<^sup>E\<close>, with \<open>s = 2\<^sup>E\<close>, \<open>E = 2\<^sup>e + 2\<close>. These describe the same box
  (\<open>defl_window_box_global\<close> below), the only place the push's integer numerators meet the local frame's rationals.

  \<open>l < r\<close> is not assumed, here or in the split arm: the coverage clause is only about a root already strictly inside the
  node's box, and that hypothesis gives the ordering, as in @{thm [source] defl_pending_covers_split_nofire}.\<close>

lemma defl_todo_box_append1_old:
  assumes i: "i < length lns"
    and l1: "length lns = length rns" and l2: "length rns = length ks"
  shows "defl_todo_box (lns @ [a1], rns @ [b1], ks @ [c1]) i
       = defl_todo_box (lns, rns, ks) i"
  using assms unfolding defl_todo_box_def by (simp add: nth_append)

lemma defl_todo_box_append1_new:
  assumes l1: "length lns = n" and l2: "length rns = n" and l3: "length ks = n"
  shows "defl_todo_box (lns @ [a1], rns @ [b1], ks @ [c1]) n
       = (real_of_int a1 / 2 ^ c1, real_of_int b1 / 2 ^ c1)"
  using assms unfolding defl_todo_box_def by (simp add: nth_append)

lemma defl_window_box_global:
  fixes l r m :: int and k E :: nat
  shows "real_of_int (l * 2 ^ E + m * (r - l)) / 2 ^ (k + E)
       = (real_of_int l + (real_of_int r - real_of_int l) * (real_of_int m / 2 ^ E)) / 2 ^ k"
proof -
  \<comment> \<open>split the power FIRST, then one \<open>field_simps\<close>: chaining the two rearrangements as
     separate \<open>also\<close> steps leaves an intermediate that neither \<open>simp\<close> nor \<open>field_simps\<close>
     normalises to the next step's LHS.\<close>
  have pw: "(2::real) ^ (k + E) = 2 ^ k * 2 ^ E" by (simp add: power_add)
  show ?thesis unfolding pw by (simp add: field_simps)
qed

text \<open>\<^bold>\<open>The transfer.\<close> Every root of \<open>P\<^sub>0\<close> strictly inside the node's box is strictly inside the accepted window
  child's box. The local statement is the previous section; here only the coordinates change, through
  @{thm [source] defl_node_local_to_global} in one direction and @{thm [source] defl_window_box_global} in the other.\<close>

lemma defl_node_box_window:
  fixes l r m :: int and k e :: nat
  defines "E \<equiv> 2 ^ e + 2"
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and lenX: "0 < length X"
    and pick: "newton_window_pick_bail v e X = Some (m, cand)"
    and vX: "carried_descartes_count X = v"
    and ylo: "real_of_int l / 2 ^ k < y" and yhi: "y < real_of_int r / 2 ^ k"
    and yz: "poly (of_int_poly (Poly rp) :: real poly) y = 0"
  shows "real_of_int (l * 2 ^ E + m * (r - l)) / 2 ^ (k + E) < y
       \<and> y < real_of_int (l * 2 ^ E + (m + 4) * (r - l)) / 2 ^ (k + E)"
proof -
  have kpos: "(0::real) < 2 ^ k" by simp
  have lr: "real_of_int l < real_of_int r"
  proof -
    have "real_of_int l < y * 2 ^ k" using ylo kpos by (simp add: pos_divide_less_eq)
    moreover have "y * 2 ^ k < real_of_int r" using yhi kpos by (simp add: pos_less_divide_eq)
    ultimately show ?thesis by linarith
  qed
  hence wpos: "0 < real_of_int r - real_of_int l" by simp
  define t where "t = (y * 2 ^ k - real_of_int l) / (real_of_int r - real_of_int l)"
  have t0: "0 < t" unfolding t_def using ylo kpos wpos by (simp add: field_simps)
  have t1: "t < 1" unfolding t_def using yhi kpos wpos by (simp add: field_simps)
  have yeq: "(real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k = y"
    unfolding t_def using wpos kpos by simp
  \<comment> \<open>into the node's LOCAL frame\<close>
  have rootX: "poly (of_int_poly (Poly X) :: real poly) t = 0"
    using defl_node_local_to_global[OF wrel t0 t1] yz yeq by simp
  have Xnz: "(of_int_poly (Poly X) :: real poly) \<noteq> 0" by (rule defl_node_wrelD_nz[OF wrel])
  \<comment> \<open>the local statement, at the node's own unit box\<close>
  have loc: "real_of_int m / 2 ^ E < t \<and> t < real_of_int (m + 4) / 2 ^ E"
    unfolding E_def
    by (rule defl_window_no_roots_outside_local[OF lenX pick vX Xnz rootX t0 t1])
  have lo': "real_of_int m / 2 ^ E < t" and hi': "t < real_of_int (m + 4) / 2 ^ E"
    using loc by simp_all
  \<comment> \<open>and back out, monotonically. \<^bold>\<open>Stated as two explicit \<open>rule\<close> chains\<close>: a bare
     \<open>simp add: divide_strict_right_mono\<close> does not fire here, because the goal needs the
     width multiplication and the shift by \<open>l\<close> BEFORE the division is compared.\<close>
  have mono1: "(real_of_int l + (real_of_int r - real_of_int l) * (real_of_int m / 2 ^ E)) / 2 ^ k
             < (real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k"
  proof -
    have "(real_of_int r - real_of_int l) * (real_of_int m / 2 ^ E)
          < (real_of_int r - real_of_int l) * t"
      by (rule mult_strict_left_mono[OF lo' wpos])
    hence "real_of_int l + (real_of_int r - real_of_int l) * (real_of_int m / 2 ^ E)
           < real_of_int l + (real_of_int r - real_of_int l) * t" by simp
    thus ?thesis using kpos by (rule divide_strict_right_mono)
  qed
  have mono2: "(real_of_int l + (real_of_int r - real_of_int l) * t) / 2 ^ k
             < (real_of_int l
                 + (real_of_int r - real_of_int l) * (real_of_int (m + 4) / 2 ^ E)) / 2 ^ k"
  proof -
    have "(real_of_int r - real_of_int l) * t
          < (real_of_int r - real_of_int l) * (real_of_int (m + 4) / 2 ^ E)"
      by (rule mult_strict_left_mono[OF hi' wpos])
    hence "real_of_int l + (real_of_int r - real_of_int l) * t
           < real_of_int l
             + (real_of_int r - real_of_int l) * (real_of_int (m + 4) / 2 ^ E)" by simp
    thus ?thesis using kpos by (rule divide_strict_right_mono)
  qed
  have L: "real_of_int (l * 2 ^ E + m * (r - l)) / 2 ^ (k + E) < y"
    using defl_window_box_global[of l E m r k] mono1 yeq by simp
  have R: "y < real_of_int (l * 2 ^ E + (m + 4) * (r - l)) / 2 ^ (k + E)"
    using defl_window_box_global[of l E "m + 4" r k] mono2 yeq by simp
  show ?thesis using L R by simp
qed

text \<open>\<^bold>\<open>The coverage clause for a ONE-child push.\<close> Same three-way case split as
  @{thm [source] defl_pending_covers_split_nofire}; the only difference is that the current box's
  roots go to a single new slot rather than to two halves, and that the slot is not the whole box
  --- so the \<open>cur\<close> case consumes \<open>inwin\<close> instead of a geometric trichotomy. \<^bold>\<open>There is no
  midpoint case\<close>: the window arm neither accepts nor discards a point.\<close>

lemma defl_pending_covers_window:
  assumes cov: "defl_dispatch_covers P0 lo (lns, rns, ks) acc l r k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and inwin: "\<And>y::real. real_of_int l / 2 ^ k < y \<Longrightarrow> y < real_of_int r / 2 ^ k
                  \<Longrightarrow> poly P0 y = 0
                  \<Longrightarrow> real_of_int L / 2 ^ K < y \<and> y < real_of_int R / 2 ^ K"
  shows "defl_pending_covers P0 lo (lns @ [L], rns @ [R], ks @ [K]) acc"
  unfolding defl_pending_covers_def
proof (intro allI impI)
  fix y :: real
  assume yl: "lo < y" and yz: "poly P0 y = 0"
  let ?T = "(lns @ [L], rns @ [R], ks @ [K])"
  from cov yl yz consider
      (inacc) "\<exists>j A B m. j < length (dyadic_interval_vec_triples acc)
                 \<and> dyadic_interval_vec_triples acc ! j = ((A, B), m)
                 \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
                    \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y))"
    | (inbox) "\<exists>i < length rns. fst (defl_todo_box (lns, rns, ks) i) < y
                 \<and> y < snd (defl_todo_box (lns, rns, ks) i)"
    | (cur) "real_of_int l / 2 ^ k < y \<and> y < real_of_int r / 2 ^ k"
    unfolding defl_dispatch_covers_def fst_conv snd_conv by blast
  then show "(\<exists>j A B m. j < length (dyadic_interval_vec_triples acc)
           \<and> dyadic_interval_vec_triples acc ! j = ((A, B), m)
           \<and> ((real_of_int A / 2 ^ m < y \<and> y < real_of_int B / 2 ^ m)
              \<or> (real_of_int A / 2 ^ m = y \<and> real_of_int B / 2 ^ m = y)))
      \<or> (\<exists>i < length (fst (snd ?T)). fst (defl_todo_box ?T i) < y
             \<and> y < snd (defl_todo_box ?T i))"
  proof cases
    case inacc thus ?thesis by blast
  next
    case inbox
    then obtain i where i: "i < length rns"
      and b: "fst (defl_todo_box (lns, rns, ks) i) < y"
             "y < snd (defl_todo_box (lns, rns, ks) i)" by blast
    have eq: "defl_todo_box ?T i = defl_todo_box (lns, rns, ks) i"
      by (rule defl_todo_box_append1_old[OF _ l1 l2[symmetric]]) (use i l1 in simp)
    have lt: "i < length (fst (snd ?T))" using i by simp
    have "fst (defl_todo_box ?T i) < y \<and> y < snd (defl_todo_box ?T i)" using b eq by simp
    with lt show ?thesis by blast
  next
    case cur
    have f1: "defl_todo_box ?T (length rns)
        = (real_of_int L / 2 ^ K, real_of_int R / 2 ^ K)"
      by (rule defl_todo_box_append1_new[OF l1 refl l2])
    have w: "real_of_int L / 2 ^ K < y \<and> y < real_of_int R / 2 ^ K"
      using inwin[OF _ _ yz] cur by simp
    have lt: "length rns < length (fst (snd ?T))" by simp
    have "fst (defl_todo_box ?T (length rns)) < y
          \<and> y < snd (defl_todo_box ?T (length rns))" using w f1 by simp
    with lt show ?thesis by blast
  qed
qed

section \<open>The window child stands in the node relation, and the coupling extends\<close>

text \<open>\<^bold>\<open>The window map preserves @{const defl_node_wrel}, for the same reason the two child maps do.\<close>
  @{const defl_node_wrel} says two polynomials are nonzero and have the same roots in the open local box \<open>(0,1)\<close>; the
  window child is @{const carried_init_same_den} at \<open>(m/2\<^sup>E, (m+4)/2\<^sup>E)\<close>, and @{thm [source] defl_carried_init_zero_iff_real}
  turns a root of the child at \<open>t\<close> into a root of the parent at \<open>(m + 4t)/2\<^sup>E\<close>. Under \<open>0 \<le> m\<close> and \<open>m + 4 \<le> 2\<^sup>E\<close>
  (@{thm [source] newton_window_pick_bail_m_nonneg} and @{thm [source] newton_window_pick_bail_m_bound}) that image lies
  strictly inside \<open>(0,1)\<close>, so the parent's relation applies there and transfers. Strictness at the left end comes from \<open>t\<close>,
  not from \<open>m\<close>: \<open>m\<close> may be \<open>0\<close>, and then the image is \<open>4t/2\<^sup>E\<close>, positive because \<open>t\<close> is.\<close>

lemma defl_node_wrel_window:
  fixes m :: int and E :: nat
  assumes rel: "defl_node_wrel A B"
    and m0: "0 \<le> m" and m4: "m + 4 \<le> 2 ^ E"
  shows "defl_node_wrel (carried_init_same_den m (2 ^ E) (m + 4) A)
                        (carried_init_same_den m (2 ^ E) (m + 4) B)"
  unfolding defl_node_wrel_def
proof (intro conjI allI impI)
  have Bnz: "(of_int_poly (Poly B) :: real poly) \<noteq> 0" by (rule defl_node_wrelD_nz[OF rel])
  show "(of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4) B)) :: real poly) \<noteq> 0"
    by (rule defl_carried_init_nz[OF Bnz]) simp
next
  fix t :: real assume t0: "0 < t" and t1: "t < 1"
  have d0: "(2::int) ^ E \<noteq> 0" by simp
  have dpos: "(0::real) < 2 ^ E" by simp
  define u where
    "u = (real_of_int m + (real_of_int (m + 4) - real_of_int m) * t) / real_of_int ((2::int) ^ E)"
  have ueq: "u = (real_of_int m + 4 * t) / 2 ^ E" unfolding u_def by simp
  have u0: "0 < u"
  proof -
    have "0 \<le> real_of_int m" using m0 by simp
    hence "0 < real_of_int m + 4 * t" using t0 by simp
    thus ?thesis unfolding ueq using dpos by (simp add: zero_less_divide_iff)
  qed
  have u1: "u < 1"
  proof -
    \<comment> \<open>coerce the INT bound in its own step: \<open>simp\<close> normalises \<open>real_of_int (m + 4)\<close> to
       \<open>real_of_int m + 4\<close>, after which an \<open>of_int_le_iff[symmetric]\<close> rewrite no longer has a
       \<open>real_of_int (m + 4)\<close> to fold back.\<close>
    have m4r: "real_of_int m + 4 \<le> 2 ^ E"
    proof -
      \<comment> \<open>\<open>simp only: of_int_le_iff\<close>, never plain \<open>simp\<close>: plain \<open>simp\<close> normalises
         \<open>real_of_int (m + 4)\<close> to \<open>real_of_int m + 4\<close> BEFORE the transfer rule can fire, and then
         there is no \<open>of_int _ \<le> of_int _\<close> left to transfer.\<close>
      have "(real_of_int (m + 4) :: real) \<le> real_of_int ((2::int) ^ E)"
        using m4 by (simp only: of_int_le_iff)
      thus ?thesis by simp
    qed
    have "real_of_int m + 4 * t < real_of_int m + 4" using t1 by simp
    also have "\<dots> \<le> 2 ^ E" using m4r by simp
    finally show ?thesis unfolding ueq using dpos by (simp add: divide_less_eq)
  qed
  show "(poly (of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4) A)) :: real poly) t = 0)
      = (poly (of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4) B)) :: real poly) t = 0)"
    using defl_carried_init_zero_iff_real[OF d0, of m "m + 4" A t]
          defl_carried_init_zero_iff_real[OF d0, of m "m + 4" B t]
          defl_node_wrelD_roots[OF rel u0 u1]
    unfolding u_def[symmetric] by simp
qed

text \<open>\<^bold>\<open>And the coupling extends by ONE slot.\<close> The two-child clone
  (@{thm [source] defl_trunc_coupling_push}) is the split arm's; the window arm pushes a single
  node, and with the per-node content factored into @{const defl_node_ok} this is the same
  three-line proof.\<close>

\<comment> \<open>\<open>defl_trunc_coupling_push1\<close> is next to its two-child counterpart (above), since the left-only split push uses
   it.\<close>

text \<open>\<^bold>\<open>The window child's own INIT, and why a composition identity is not needed.\<close> The coupling
  asks the window child to stand in @{const defl_node_wrel} to @{term "carried_init_same_den L
  (2 ^ (k + E)) R rp"} --- the init of its OWN box, built from \<open>rp\<close> in one step. What the window
  map produces is the TWO-step object: the node's init, then the grid cell of it. Those two lists
  are equal only up to a positive scalar, so a list identity is the wrong target; but
  @{const defl_node_wrel} is a statement about ROOTS, and a positive scalar moves none. So the
  bridge is proved by evaluating both sides through
  @{thm [source] defl_carried_init_zero_iff_real} and observing that the two affine maps land on
  the same point --- which is @{thm [source] defl_window_box_global}'s identity with \<open>m\<close> replaced
  by \<open>m + 4t\<close>.\<close>

lemma defl_window_point_compose:
  fixes l r m :: int and k E :: nat and t :: real
  shows "(real_of_int (l * 2 ^ E + m * (r - l))
           + (real_of_int (l * 2 ^ E + (m + 4) * (r - l))
              - real_of_int (l * 2 ^ E + m * (r - l))) * t)
         / real_of_int ((2::int) ^ (k + E))
       = (real_of_int l + (real_of_int r - real_of_int l)
            * ((real_of_int m + (real_of_int (m + 4) - real_of_int m) * t)
               / real_of_int ((2::int) ^ E)))
         / real_of_int ((2::int) ^ k)"
proof -
  have pw: "real_of_int ((2::int) ^ (k + E)) = real_of_int ((2::int) ^ k) * real_of_int ((2::int) ^ E)"
    by (simp add: power_add)
  show ?thesis unfolding pw by (simp add: field_simps)
qed

lemma defl_window_init_wrel:
  fixes l r m :: int and k E :: nat
  assumes rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l < r"
  shows "defl_node_wrel
           (carried_init_same_den (l * 2 ^ E + m * (r - l)) (2 ^ (k + E))
              (l * 2 ^ E + (m + 4) * (r - l)) rp)
           (carried_init_same_den m (2 ^ E) (m + 4)
              (carried_init_same_den l (2 ^ k) r rp))"
  unfolding defl_node_wrel_def
proof (intro conjI allI impI)
  have innz: "(of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly) \<noteq> 0"
    by (rule defl_carried_init_nz[OF rpnz lr])
  show "(of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4)
            (carried_init_same_den l (2 ^ k) r rp))) :: real poly) \<noteq> 0"
    by (rule defl_carried_init_nz[OF innz]) simp
next
  fix t :: real assume t0: "0 < t" and t1: "t < 1"
  have dE: "(2::int) ^ E \<noteq> 0" and dk: "(2::int) ^ k \<noteq> 0"
    and dkE: "(2::int) ^ (k + E) \<noteq> 0" by simp_all
  show "(poly (of_int_poly (Poly (carried_init_same_den (l * 2 ^ E + m * (r - l))
              (2 ^ (k + E)) (l * 2 ^ E + (m + 4) * (r - l)) rp)) :: real poly) t = 0)
      = (poly (of_int_poly (Poly (carried_init_same_den m (2 ^ E) (m + 4)
              (carried_init_same_den l (2 ^ k) r rp))) :: real poly) t = 0)"
    using defl_carried_init_zero_iff_real[OF dkE,
            of "l * 2 ^ E + m * (r - l)" "l * 2 ^ E + (m + 4) * (r - l)" rp t]
          defl_carried_init_zero_iff_real[OF dE, of m "m + 4"
            "carried_init_same_den l (2 ^ k) r rp" t]
          defl_carried_init_zero_iff_real[OF dk, of l r rp
            "(real_of_int m + (real_of_int (m + 4) - real_of_int m) * t)
               / real_of_int ((2::int) ^ E)"]
          \<comment> \<open>NAMED instantiation: \<open>of\<close> here follows the order the variables first occur in the
             STATEMENT (\<open>l, E, m, r, t, k\<close>), not the \<open>fixes\<close> order, and getting that wrong reports
             a \<open>Type unification failed: Clash of types\<close> \<open>real\<close>/\<open>nat\<close> with no hint of which
             slot moved.\<close>
          defl_window_point_compose[where l = l and E = E and m = m and r = r and k = k and t = t]
    by simp
qed

text \<open>\<^bold>\<open>The window child is a well-formed node.\<close> Everything the coupling asks of the pushed slot,
  at the guard and cache the gate-open arm actually writes: \<open>glock = 2\<^sup>4\<^sup>2 + v\<close> and \<open>c = v + 2\<close>.
  The witness is the child ITSELF -- a window child is exact by construction (the probe runs on
  \<open>qx\<close>, which under \<open>gex\<close> IS the node's own exact polynomial), so \<open>node_frame\<close> is the reflexive
  one and the lock clause is trivial.\<close>

lemma defl_window_child_node_ok:
  fixes l r m :: int and k e v :: nat
  defines "E \<equiv> 2 ^ e + 2"
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l < r"
    and m0: "0 \<le> m" and m4: "m + 4 \<le> 2 ^ E"
    and cand: "cand = carried_init_same_den m (2 ^ E) (m + 4) X"
    and cnt: "carried_descartes_count cand = v"
    and v2: "2 \<le> v"
    and lenX: "length X \<le> length rp"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the parent's divisibility, which \<open>defl_node_okE\<close> supplies at every call site.
       \<open>defl_window_child_dvd\<close> carries it across the window map, using the scalar identity rather than
       \<open>defl_window_init_wrel\<close>: a positive scalar moves no root but does stand between two lists.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)"
  shows "defl_node_ok rp (l * 2 ^ E + m * (r - l)) (l * 2 ^ E + (m + 4) * (r - l)) (k + E)
           cand (4398046511104 + v) (v + 2)"
proof (rule defl_node_okI)
  show "node_frame cand cand (4398046511104 + v)" by (rule node_frame_exact_any_g)
next
  have w1: "defl_node_wrel
              (carried_init_same_den (l * 2 ^ E + m * (r - l)) (2 ^ (k + E))
                 (l * 2 ^ E + (m + 4) * (r - l)) rp)
              (carried_init_same_den m (2 ^ E) (m + 4)
                 (carried_init_same_den l (2 ^ k) r rp))"
    by (rule defl_window_init_wrel[OF rpnz lr])
  have w2: "defl_node_wrel (carried_init_same_den m (2 ^ E) (m + 4)
                              (carried_init_same_den l (2 ^ k) r rp))
                           (carried_init_same_den m (2 ^ E) (m + 4) X)"
    by (rule defl_node_wrel_window[OF wrel m0 m4])
  show "defl_node_wrel
          (carried_init_same_den (l * 2 ^ E + m * (r - l)) (2 ^ (k + E))
             (l * 2 ^ E + (m + 4) * (r - l)) rp) cand"
    unfolding cand by (rule defl_node_wrel_trans[OF w1 w2])
next
  \<comment> \<open>the W1 decode: a LOCKED slot is always in @{const dyadic_iv_cs_invar}'s second disjunct,
     and \<open>c = v + 2\<close> with \<open>2 \<le> v\<close> reads the trichotomy and the \<open>c - 2\<close> decode at once.\<close>
  show "hybrid_cs_ok (4398046511104 + v) (v + 2) (carried_descartes_count cand)"
    unfolding hybrid_cs_ok_def dyadic_iv_cs_invar_def cnt using v2 by simp
next
  show "length cand \<le> length rp"
    unfolding cand using lenX by (simp add: truncate_length_carried_init_same_den)
next
  show "4398046511104 + v \<le> (k + E + 1) * length rp \<or> 4398046511104 \<le> 4398046511104 + v"
    by simp
next
  show "4398046511104 \<le> 4398046511104 + v \<longrightarrow> cand = cand" by simp
next
  \<comment> \<open>the window push is the ONE producer of a class above \<open>4\<close>, and it stores the LOCK guard
     in the same step --- so @{const defl_node_ok}'s last clause is immediate here.\<close>
  show "4 < v + 2 \<longrightarrow> 4398046511104 \<le> 4398046511104 + v" by simp
next
  \<comment> \<open>\<^bold>\<open>The payload holds with equality here\<close>, which is why the deflating form of the clause is provable where
     @{const hybrid_child_pay_ok} is not: the guard the window push stores is \<open>2\<^sup>4\<^sup>2 + v\<close>, and \<open>v\<close> is the accepted window's own
     count (@{thm [source] newton_window_pick_bail_count}, here \<open>cnt\<close>).\<close>
  show "4398046511106 \<le> 4398046511104 + v
          \<longrightarrow> carried_descartes_count cand \<le> 4398046511104 + v - 4398046511104"
    using cnt by simp
next
  \<comment> \<open>the ceiling: \<open>v = count cand\<close> and a Descartes count never exceeds the list's length
     (\<open>carried_descartes_count_le_length_cn\<close>), which \<open>lenX\<close> bounds by \<open>length rp\<close>.\<close>
  have vlen: "v \<le> length rp"
  proof -
    have "v \<le> length cand" using cnt carried_descartes_count_le_length_cn by metis
    also have "\<dots> \<le> length rp"
      unfolding cand using lenX by (simp add: truncate_length_carried_init_same_den)
    finally show ?thesis .
  qed
  show "4398046511104 + v \<le> 4398046511104 + length rp" using vlen by simp
next
  \<comment> \<open>\<^bold>\<open>Last\<close>, in the order \<open>defl_node_okI\<close> takes it.\<close>
  show "(of_int_poly (Poly cand) :: real poly)
          dvd (of_int_poly (Poly (carried_init_same_den (l * 2 ^ E + m * (r - l))
                 (2 ^ (k + E)) (l * 2 ^ E + (m + 4) * (r - l)) rp)) :: real poly)"
    unfolding cand by (rule defl_window_child_dvd[OF dvdX])
qed

section \<open>The gate-open accept sub-arm preserves the invariant\<close>

text \<open>\<^bold>\<open>Stated over the sub-program itself\<close>, as @{thm [source] hybrid_gate_open_accept_cols} is. The branch is chosen by
  \<open>wc\<close>, which the caller cannot see, so a lemma about the whole op would need a hypothesis about an op output. Over the
  \<open>else\<close> block there is no such problem, and the arm assembly only selects the branch.

  \<^bold>\<open>Three clauses, one with content.\<close> \<open>acc\<close> is returned unchanged, so isolation carries over (the window arm pushes a
  child and accepts no root). Coverage is @{thm [source] defl_pending_covers_window} fed by
  @{thm [source] defl_node_box_window}, and the coupling is @{thm [source] defl_trunc_coupling_push1} with
  @{thm [source] defl_window_child_node_ok} for the new slot.\<close>

lemma defl_gate_open_accept_invar:
  fixes l_num r_num m :: int and k e s v :: nat and rp :: gmp_poly
  \<comment> \<open>the \<open>(2::nat)\<close> annotation is load-bearing: \<open>E\<close> occurs in NO other part of the
     statement, and \<open>2 ^ e\<close> is polymorphic in its BASE, so without it \<open>E\<close> is fixed at a type
     variable and the first \<open>have\<close> mentioning \<open>2 ^ E\<close> fails with a coercion-inference error.\<close>
  defines "E \<equiv> (2 :: nat) ^ e + 2"
  defines "P0 \<equiv> (of_int_poly (Poly rp) :: real poly)"
  assumes ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and qlen1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)"
    and elen1: "length es + 1 < max_snat LENGTH(gmp_poly_len)"
    and slen1: "length ss + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the node\<close>
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and lenX: "0 < length X"
    \<comment> \<open>the accepted window\<close>
    and pick: "newton_window_pick_bail v e X = Some (m, cand)"
    and vX: "carried_descartes_count X = v"
    and v2: "2 \<le> v"
    \<comment> \<open>the invariant at the popped state\<close>
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates P0 (al, ar, ak)"
    and cov: "defl_dispatch_covers P0 lo (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
  \<comment> \<open>\<^bold>\<open>Stated AFTER the two column appends, and in \<open>Suc (Suc v)\<close> form\<close>: by the time the
     arm reaches this point \<open>refine_vcg\<close> has already performed \<open>mop_list_append\<close> twice and
     \<open>simp\<close> has normalised \<open>v + 2\<close>, so a lemma stated over the whole \<open>else\<close> block (or with
     \<open>v + 2\<close>) does not match the goal --- \<open>rule\<close> matches syntactically. This is the classic
     arm's shape too: it applies @{thm [source] hybrid_window_push_cols}, not the
     \<open>_accept_cols\<close> wrapper that also does the appends.\<close>
    \<comment> \<open>\<^bold>\<open>Last\<close>, immediately before \<open>shows\<close>, so that no existing \<open>[OF \<dots>]\<close> position in a caller moves.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
  shows "hybrid_window_push_monadic (lns, rns, ks) qtodo es ss
             (cs @ [Suc (Suc v)]) (gs @ [4398046511104 + v]) rp l_num r_num k e s m X cand
       \<le> SPEC (\<lambda>triple. defl_loop_invar P0 lo (triple, (al, ar, ak)))"
proof -
  have m0: "0 \<le> m" by (rule newton_window_pick_bail_m_nonneg[OF pick])
  have m4: "m + 4 \<le> 2 ^ E"
    unfolding E_def using newton_window_pick_bail_m_bound[OF pick] four_N_of_pow2 by simp
  have cand_eq: "cand = carried_init_same_den m (2 ^ E) (m + 4) X"
    using newton_window_pick_bail_cand[OF pick] unfolding newton_wcand_def E_def by simp
  have cnt: "carried_descartes_count cand = v" by (rule newton_window_pick_bail_count[OF pick])
  \<comment> \<open>the new slot is a well-formed node\<close>
  have ok1: "defl_node_ok rp (l_num * 2 ^ E + m * (r_num - l_num))
                (l_num * 2 ^ E + (m + 4) * (r_num - l_num)) (k + E)
                cand (4398046511104 + v) (v + 2)"
    unfolding E_def
    by (rule defl_window_child_node_ok[OF wrel rpnz lr m0 m4[unfolded E_def]
              cand_eq[unfolded E_def] cnt v2 lenXrp dvdX])
  have coup': "defl_trunc_coupling
      (lns @ [l_num * 2 ^ E + m * (r_num - l_num)],
       rns @ [l_num * 2 ^ E + (m + 4) * (r_num - l_num)], ks @ [k + E])
      (qtodo @ [cand]) (cs @ [v + 2]) (gs @ [4398046511104 + v]) rp"
    by (rule defl_trunc_coupling_push1[OF coup ok1])
  \<comment> \<open>coverage: every root of \<open>P\<^sub>0\<close> in the node's box is in the window child's box\<close>
  have Xnz: "(of_int_poly (Poly X) :: real poly) \<noteq> 0" by (rule defl_node_wrelD_nz[OF wrel])
  have inwin: "real_of_int (l_num * 2 ^ E + m * (r_num - l_num)) / 2 ^ (k + E) < y
             \<and> y < real_of_int (l_num * 2 ^ E + (m + 4) * (r_num - l_num)) / 2 ^ (k + E)"
    if "real_of_int l_num / 2 ^ k < y" and "y < real_of_int r_num / 2 ^ k"
       and "poly P0 y = 0" for y :: real
    unfolding E_def
    by (rule defl_node_box_window[OF wrel lenX pick vX that(1) that(2)
              that(3)[unfolded P0_def]])
  have cov': "defl_pending_covers P0 lo
      (lns @ [l_num * 2 ^ E + m * (r_num - l_num)],
       rns @ [l_num * 2 ^ E + (m + 4) * (r_num - l_num)], ks @ [k + E]) (al, ar, ak)"
    by (rule defl_pending_covers_window[OF cov l1 l2]) (use inwin in blast)
  \<comment> \<open>and the state result is the classic one, verbatim\<close>
  show ?thesis
    unfolding P0_def
    apply (rule order_trans[OF hybrid_window_push_cols[OF ecap ecap2 kcap2 ecap3
             push1 kslen qlen1 elen1 slen1]])
    apply (rule SPEC_rule)
    apply (clarsimp simp: defl_loop_invar_def)
    using iso cov' coup' unfolding P0_def E_def by simp
qed

section \<open>The gate-open arm preserves the invariant\<close>

text \<open>\<^bold>\<open>The fourth arm.\<close> @{const defl_gate_open_monadic} is the non-deflating op with one substitution (its reject
  sub-arm calls @{const defl_branch_split_monadic}), so the proof is @{thm [source] hybrid_gate_open_acc}'s with two
  callees replaced:

  \<^item> reject \<open>\<rightarrow>\<close> @{thm [source] defl_branch_split_exact_invar} at the lock guard \<open>2\<^sup>4\<^sup>2 + v\<close>, the instance the split lemmas are
    stated generally enough to cover;
  \<^item> accept \<open>\<rightarrow>\<close> @{thm [source] defl_gate_open_accept_invar}.

  \<^bold>\<open>The escalation is collapsed by \<open>gex\<close>, not by @{thm [source] hybrid_cond_escalate_gives_X}.\<close> That lemma takes
  \<open>X = carried_init_same_den l (2\<^sup>k) r rp\<close>, and a deflated node's witness is a divisor of its init, so it does not apply. Under
  \<open>gex\<close> the weaker @{thm [source] hybrid_cond_escalate_exact} suffices: the op is \<open>RETURN (Q, rp)\<close>, so \<open>qx = Q = X\<close> and no
  rebuild happens. So a \<open>2\<^sup>4\<^sup>2 + v\<close> payload recorded by a deflated ancestor never has to survive a rebuild on this arm.\<close>

theorem defl_gate_open_invar:
  fixes l_num r_num :: int and k e s cnt g v :: nat and rp :: gmp_poly
  defines "P0 \<equiv> (of_int_poly (Poly rp) :: real poly)"
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g"
    and frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and cnt2: "2 \<le> cnt"
    and inv: "dyadic_iv_cs_invar cnt (carried_descartes_count X)"
    and count2: "2 \<le> carried_descartes_count X"
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    \<comment> \<open>the node, in the DEFLATING shape: a witness related to the init, not equal to it\<close>
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and Qlen3: "3 \<le> length Q"
    \<comment> \<open>word bounds, all as in the classic arm\<close>
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne1: "1 < length X"
    and X_b2: "length X + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length X < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length X - 1) < max_snat LENGTH(gmp_poly_len)"
    and vcap1: "int (carried_descartes_count X) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count X < max_snat LENGTH(gmp_poly_len)"
    and gcap_lock: "4398046511104 + carried_descartes_count X + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the invariant at the popped state\<close>
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates P0 (al, ar, ak)"
    and cov: "defl_dispatch_covers P0 lo (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
    \<comment> \<open>\<^bold>\<open>Last\<close>, immediately before \<open>shows\<close>, so that no existing \<open>[OF \<dots>]\<close> position in a caller moves.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
  shows "defl_gate_open_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s cnt g Q
       \<le> SPEC (defl_loop_invar P0 lo)"
proof -
  have X_b1: "length X + 1 < max_snat LENGTH(gmp_poly_len)" using X_b2 by simp
  have X_ne0: "0 < length X" using X_ne1 by simp
  \<comment> \<open>\<^bold>\<open>the escalate is a no-op under \<open>gex\<close>\<close>\<close>
  have QX: "Q = X"
  proof (cases "g = 0")
    case True thus ?thesis using frame by (simp add: node_frame_def)
  next
    case False thus ?thesis using gex lock by simp
  qed
  \<comment> \<open>\<^bold>\<open>Stated at \<open>X\<close>, not at \<open>Q\<close>\<close>: every hint below (\<open>inv\<close>, \<open>pay\<close>, \<open>count2\<close>, the window
     choice) is about \<open>X\<close>, and a postcondition pinning the escalate's output to \<open>Q\<close> leaves the
     program saying \<open>Q\<close> after \<open>clarsimp\<close> --- at which point none of them fire. Same shape as the
     classic arm's @{thm [source] hybrid_cond_escalate_gives_X}, which is unavailable here
     because it takes \<open>X = carried_init_same_den \<dots>\<close> and a deflated node's witness is only a
     DIVISOR of its init.\<close>
  have esc: "hybrid_cond_escalate_monadic rp l_num r_num k Q g
           \<le> SPEC (\<lambda>(qx, rpx). qx = X \<and> rpx = rp)"
    using QX by (simp add: hybrid_cond_escalate_exact[OF gex])
  \<comment> \<open>\<^bold>\<open>the reject sub-arm's guard-shaped premises, at \<open>glock\<close>\<close>\<close>
  have fX: "node_frame X X (4398046511104 + carried_descartes_count X)"
    by (rule node_frame_exact_any_g)
  have lkX: "4398046511104 \<le> 4398046511104 + carried_descartes_count X \<longrightarrow> X = X" by simp
  have gexX: "4398046511104 + carried_descartes_count X = 0
              \<or> 4398046511104 \<le> 4398046511104 + carried_descartes_count X" by simp
  have gcap_lk: "max (4398046511104 + carried_descartes_count X) 4398046511104 + length rp
                   < max_snat LENGTH(gmp_poly_len)"
    using gcap_lock by simp
  \<comment> \<open>\<^bold>\<open>The reject instance's own payload atom.\<close> It is the lock guard with payload \<open>2\<^sup>4\<^sup>2 + count X\<close>, so the payload holds
     by construction, and the ceiling is the Descartes count's own length bound against \<open>lenXrp\<close>.\<close>
  have payX: "4398046511106 \<le> 4398046511104 + carried_descartes_count X
                \<longrightarrow> carried_descartes_count X
                      \<le> 4398046511104 + carried_descartes_count X - 4398046511104"
    by simp
  have ceilX: "4398046511104 + carried_descartes_count X \<le> 4398046511104 + length rp"
    using carried_descartes_count_le_length_cn[of "X"] lenXrp by simp
  have Xlen3: "3 \<le> length X" using QX Qlen3 by simp
  have qlen1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have elen1: "length es + 1 < max_snat LENGTH(gmp_poly_len)" using ecapl by simp
  have slen1: "length ss + 1 < max_snat LENGTH(gmp_poly_len)" using sscap by simp
  have clen1: "length cs + 1 < max_snat LENGTH(gmp_poly_len)" using ccap by simp
  have glen1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  show ?thesis
    unfolding defl_gate_open_monadic_def PR_CONST_def P0_def
    using rpne rpb krp X_ne1 X_b2 ecap ecap3 ecap2 kcap2 gate4
    apply (refine_vcg esc[THEN order_trans])
    apply (all \<open>((clarsimp; fail) | (linarith; fail))?\<close>)
    apply clarsimp
    apply (refine_vcg hybrid_window_v_exact[OF inv X_b1 pay count2, THEN order_trans])
    apply (all \<open>((clarsimp, insert vcap1 vcap2, simp); fail)?\<close>)
    apply clarsimp
    apply (refine_vcg blr_window_choice_refine_bl[OF X_ne0 X_b1 gate4 X_ne1 ecap2 X_b2
                        vcap1 count2 order_refl, THEN order_trans])
    \<comment> \<open>REJECT\<close>
    apply (rule defl_branch_split_exact_invar[OF fX lkX gexX payX ceilX gcap_lk Xlen3 X_b1
                 lenXrp wrel rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecapl
                 sscap ccap push2 scap1 coup iso[unfolded P0_def] cov[unfolded P0_def]
                 l1 l2 lal lak dvdX])
    \<comment> \<open>ACCEPT\<close>
    apply (all \<open>((insert push1 qlen1 elen1 slen1 clen1 glen1 vcap2, simp); fail)?\<close>)
    \<comment> \<open>ACCEPT: the push-level lemma, with \<open>pick\<close> left as a subgoal --- the context carries the
       window choice only as \<open>x = newton_window_pick_bail \<dots>\<close> plus \<open>the x = (x1, x2)\<close> plus
       \<open>\<exists>a b. x = Some (a, b)\<close>, which \<open>auto\<close> assembles.\<close>
    apply (rule order_trans[OF defl_gate_open_accept_invar[OF ecap ecap2 kcap2 ecap3 push1
                 kslen qlen1 elen1 slen1 wrel rpnz lr lenXrp X_ne0 _ refl count2
                 coup iso[unfolded P0_def] cov[unfolded P0_def] l1 l2 dvdX]])
      apply auto
    done
qed


section \<open>The general guard\<close>

text \<open>\<^bold>\<open>\<open>gex\<close> is a branch condition in the code, not a proof convenience.\<close> Each of the four arm lemmas here is stated at
  \<open>gex\<close> (\<open>g = 0 \<or> 2\<^sup>4\<^sup>2 \<le> g\<close>). @{const defl_branch_split_monadic} branches on that test: under \<open>gex \<and> 3 \<le> len\<close> it enters
  @{const defl_split_children_monadic}, and otherwise @{const defl_split_children_escalate_monadic}. So the deflating build is
  never reached at an intermediate guard; the escalating arm is.

  \<^bold>\<open>On the escalating arm, an intermediate guard makes the node exact.\<close> @{const truncate_mid_decide_monadic} at
  \<open>0 < g < 2\<^sup>4\<^sup>2\<close> returns \<open>2\<close> (ambiguous) or \<open>0\<close>, never \<open>1\<close>, because both of its \<open>RETURN (if \<dots> then 0 else 1)\<close> branches are
  guarded by \<open>g = 0\<close> and \<open>2\<^sup>4\<^sup>2 \<le> g\<close>. Hence:

  \<^item> \<open>code = 2\<close> \<open>\<rightarrow>\<close> the children are freed, \<open>qx\<close> is rebuilt exactly from the loop-carried root, and the deflating build is
    re-entered at guard \<open>0\<close>, i.e. within \<open>gex\<close>, with @{thm [source] defl_node_wrel_init_refl} giving the node relation by
    reflexivity;
  \<^item> \<open>code \<noteq> 2\<close> \<open>\<rightarrow>\<close> \<open>code = 0\<close>, so \<open>fired = False\<close>: no shed happens at an intermediate guard, the children are the non-deflated
    ones, and the node relation is the reflexive instance @{thm [source] defl_child_wrel_left} / \<open>_right\<close>.

  So the general-guard case needs no separate version of the split arm: the code does not deflate a truncated node.\<close>

lemma defl_decide_no_fire_of_ngex:
  assumes g0: "g \<noteq> 0" and glt: "g < 4398046511104"
  shows "truncate_mid_decide_monadic g len mids midbl
       \<le> SPEC (\<lambda>code. code = 0 \<or> code = 2)"
  \<comment> \<open>the two \<open>RETURN (if \<dots> then 0 else 1)\<close> arms are guarded by \<open>g = 0\<close> and \<open>2\<^sup>4\<^sup>2 \<le> g\<close>, so
     under \<open>ngex\<close> only the \<open>RETURN 2\<close> arm and the \<open>if tr then 0 else 2\<close> tail survive. The two
     inner \<open>mop\<close>s are \<open>RETURN\<close>-shaped with \<open>ASSERT\<close>s that their own branch guards discharge.\<close>
  unfolding truncate_mid_decide_monadic_def mid_guard_mop_def lead_trust_mop_def PR_CONST_def
  using g0 glt by (refine_vcg) (auto simp: max_snat_def)

text \<open>\<^bold>\<open>The two reflexive child instances\<close>, for the non-firing branch: a child that was not shed
  stands in @{const defl_node_rel} to itself, so @{thm [source] defl_child_wrel_left} /
  @{thm [source] defl_child_wrel_right} deliver the child's own init relation directly.\<close>

lemma defl_child_wrel_left_id:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
  shows "defl_node_wrel (carried_init_same_den (2 * l) (2 ^ Suc k) (l + r) rp) (carried_left X)"
  by (rule defl_child_wrel_left[OF wrel defl_node_rel_refl])

lemma defl_child_wrel_right_id:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
  shows "defl_node_wrel (carried_init_same_den (l + r) (2 ^ Suc k) (2 * r) rp) (carried_right X)"
  by (rule defl_child_wrel_right[OF wrel defl_node_rel_refl])


section \<open>What the escalating arm needs at a general guard\<close>

text \<open>@{const defl_split_children_escalate_monadic} is @{const hybrid_split_children_classic_monadic} with the deflating
  build spliced into its rebuild tail, so the proof skeleton is @{thm [source] hybrid_split_children_classic_gagrees}'s:
  @{thm [source] truncate_children_mid_decide_gbind} for the children-and-decide prefix, then a split on \<open>code = 2\<close>.

  \<^bold>\<open>Three places where the deflating conclusion is weaker, which is what @{const defl_node_ok} asks for.\<close>

  \<^item> \<^bold>\<open>The node relation is @{const defl_node_wrel} against the child's own init\<close>, not \<open>node_frame (carried_left X) ql gl\<close>:
    on the rebuild branch the children are the init's, not \<open>X\<close>'s. Both branches give the init form:
    @{thm [source] defl_child_wrel_left_id} on the decisive branch, and @{thm [source] defl_node_wrel_init_refl} composed
    with @{thm [source] defl_child_wrel_left} on the rebuild branch.
  \<^item> \<^bold>\<open>The guard clause is \<open>hybrid_child_gok \<dots> \<or> 2\<^sup>4\<^sup>2 \<le> gl\<close>\<close>: the rebuild re-enters @{const defl_split_children_monadic} at
    guard \<open>0\<close> with \<open>lockok = (len < len0)\<close>, so a shed there takes the lock and returns \<open>gl = 2\<^sup>4\<^sup>2\<close>, which exceeds \<open>g + length Q\<close>
    and is not an @{const hybrid_child_gok}. The disjunction is what the coupling's budget clause reads.
  \<^item> \<^bold>\<open>The length clause is \<open>\<le> length rp\<close>\<close>, not \<open>\<le> length Q\<close>: the rebuilt node is \<open>rp\<close>'s own init, which may be longer than the
    truncated \<open>Q\<close> that was popped.

  \<^bold>\<open>The \<open>fired\<close> clause\<close> is the lemma below: on the rebuild branch the shed is decided about the init, and the node
  relation carries that back to \<open>X\<close> because the midpoint \<open>1/2\<close> is an interior point of the local box, which is why
  @{const defl_node_wrel} is stated over the open \<open>(0,1)\<close>.\<close>

lemma defl_escalate_gen_fired_transfer:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and fired: "poly (map_poly rat_of_int (Poly (carried_init_same_den l (2 ^ k) r rp)))
                  (1 / 2) = 0"
  shows "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0"
proof -
  have h0: "(0::real) < 1 / 2" and h1: "(1::real) / 2 < 1" by simp_all
  \<comment> \<open>the rational/real bridge must be INSTANTIATED at \<open>1/2\<close> and the coercion done by
     \<open>of_rat_divide\<close> --- feeding it to \<open>simp\<close> bare leaves \<open>real_of_rat (1/2)\<close> unmatched against
     the goal's \<open>(1/2)::real\<close>. Same two-line shape as
     @{thm [source] defl_mid_not_root_global}.\<close>
  have hi: "poly (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)
              (1 / 2) = 0"
    using fired
      defl_rat_root_iff_real[of "Poly (carried_init_same_den l (2 ^ k) r rp)" "1 / 2"]
    by (simp add: of_rat_divide)
  have hx: "poly (of_int_poly (Poly X) :: real poly) (1 / 2) = 0"
    using hi defl_node_wrelD_roots[OF wrel h0 h1] by simp
  show ?thesis
    using hx defl_rat_root_iff_real[of "Poly X" "1 / 2"] by (simp add: of_rat_divide)
qed

text \<open>\<^bold>\<open>And the mirror\<close>, for the non-firing direction: the two are separate lemmas rather than an
  \<open>iff\<close> because the arms consume them at opposite polarities and an \<open>iff\<close> would have to be
  destructured at every use.\<close>

lemma defl_escalate_gen_nofire_transfer:
  assumes wrel: "defl_node_wrel (carried_init_same_den l (2 ^ k) r rp) X"
    and nofire: "poly (map_poly rat_of_int (Poly (carried_init_same_den l (2 ^ k) r rp)))
                   (1 / 2) \<noteq> 0"
  shows "poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0"
proof
  assume "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0"
  then have hx: "poly (of_int_poly (Poly X) :: real poly) (1 / 2) = 0"
    using defl_rat_root_iff_real[of "Poly X" "1 / 2"] by (simp add: of_rat_divide)
  have h0: "(0::real) < 1 / 2" and h1: "(1::real) / 2 < 1" by simp_all
  have "poly (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)
          (1 / 2) = 0"
    using hx defl_node_wrelD_roots[OF wrel h0 h1] by simp
  hence "poly (map_poly rat_of_int (Poly (carried_init_same_den l (2 ^ k) r rp))) (1 / 2) = 0"
    using defl_rat_root_iff_real[of "Poly (carried_init_same_den l (2 ^ k) r rp)" "1 / 2"]
    by (simp add: of_rat_divide)
  thus False using nofire by simp
qed


section \<open>The escalating arm's child build at a general guard\<close>

text \<open>The skeleton is @{thm [source] hybrid_split_children_classic_gagrees}'s:
  @{thm [source] truncate_children_mid_decide_gbind} for the children-and-decide prefix, a split on \<open>code = 2\<close>, and the shape of
  @{thm [source] hybrid_split_children_rebuild_tail} for the tail. The conclusion is weaker in the three places described
  above: the node relation is @{const defl_node_wrel} against the child's own init; the guard clause is the coupling's
  @{const hybrid_child_depth_ok} rather than @{const hybrid_child_gok} (the three branches produce guards of three
  different origins, and no single \<open>gok\<close> instance covers them); and the length bound is \<open>length rp\<close> rather than \<open>length Q\<close>.

  \<open>g_cpl\<close>, the popped node's budget conjunct carried by @{const defl_node_ok}, is needed: without it the decisive branch
  has no route to @{const hybrid_child_depth_ok}.

  Two proof notes: the \<open>doN\<close>-shaped \<open>gbind\<close> does not match once \<open>refine_vcg\<close> has split the outer bind (the \<open>_eta\<close> variant
  is used), and \<open>simp only: prod.case\<close> comes between \<open>RETURN_rule\<close> and \<open>intro conjI\<close>, since otherwise the postcondition is
  still a case-lambda applied to a tuple and \<open>intro conjI\<close> splits nothing.\<close>

text \<open>\<^bold>\<open>The decide returns \<open>1\<close> only on a zero sign\<close>, at every guard: both \<open>RETURN (if \<dots> then 0 else 1)\<close> arms test the
  sign, and the other two arms return only \<open>0\<close> or \<open>2\<close>. With the contract's \<open>rz \<longrightarrow> carried_right Q ! 0 \<noteq> 0\<close> this is the
  interlock \<open>rz \<longrightarrow> code \<noteq> 1\<close>, which the keystone's continuation does not carry and the deflating split arm needs (its \<open>rz\<close>
  branch tests \<open>mid\<close>).\<close>

lemma defl_decide_one_mids:
  "truncate_mid_decide_monadic g len mids midbl \<le> SPEC (\<lambda>code. code = 1 \<longrightarrow> mids = 0)"
  unfolding truncate_mid_decide_monadic_def mid_guard_mop_def lead_trust_mop_def PR_CONST_def
  by refine_vcg (auto simp: max_snat_def split: if_splits)

text \<open>\<^bold>\<open>The keystone's children-and-decide continuation, with the interlock.\<close> The two counterparts of
  @{thm [source] truncate_children_mid_skip_right_decide_gbind} / \<open>_eta\<close>, with one extra continuation premise,
  \<open>rz \<longrightarrow> code \<noteq> 1\<close>, placed last. The proof is the same, with @{thm [source] defl_decide_one_mids} joined to the decide's
  contract.\<close>

text \<open>The interlock as a closer without search, in the shape the two lemmas below leave it.\<close>
lemma defl_interlock_rule:
  "rz \<longrightarrow> D \<and> s \<noteq> (0::int) \<Longrightarrow> A \<and> (c = (1::nat) \<longrightarrow> sgn s = 0) \<Longrightarrow> rz \<longrightarrow> c \<noteq> 1"
  by (auto simp: sgn_if split: if_splits)

lemma defl_right_empty_decide_gbind:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and len_eq: "len = length Q"
    and cont: "\<And>ql gl qr gr code rz.
        \<lbrakk> node_frame (carried_left X) ql gl;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          hybrid_child_gok g (length Q) gl; hybrid_child_gok g (length Q) gr;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          \<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X);
          rz \<longrightarrow> carried_descartes_count (carried_right X) = 0;
          code = 1 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          code = 0 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0;
          g = 0 \<or> 4398046511104 \<le> g \<longrightarrow> code \<noteq> 2;
          code = 0 \<or> code = 1 \<or> code = 2;
          rz \<longrightarrow> code \<noteq> 1 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr code rz \<le> SPEC \<Phi>"
  shows "doN { (ql, gl, qr, gr, mids, midbl, rz) \<leftarrow> truncate_children_mid_skip_right_monadic g Q;
               code \<leftarrow> truncate_mid_decide_monadic g len mids midbl;
               f ql gl qr gr code rz }
       \<le> SPEC \<Phi>"
  apply (refine_vcg
      cdlr_SPEC_conj[OF
        truncate_children_mid_skip_right_agrees[OF frame lock g_tri Qne Qbound Qbound2 dep Q_small kb]
        truncate_children_mid_skip_right_gok[OF g_tri Qne Qbound Qbound2 dep Q_small kb],
        THEN order_trans])
  apply clarsimp
  apply (refine_vcg
      cdlr_SPEC_conj[OF
        truncate_mid_decide_agrees[OF frame lock len_eq Qne Q_small] defl_decide_one_mids,
        THEN order_trans])
  apply (all \<open>(((rule defl_interlock_rule, assumption, assumption) | simp); fail)?\<close>)
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  apply (all \<open>(((rule defl_interlock_rule, assumption, assumption) | simp); fail)?\<close>)
  done

lemma defl_right_empty_decide_gbind_eta:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and len_eq: "len = length Q"
    and cont: "\<And>ql gl qr gr code rz.
        \<lbrakk> node_frame (carried_left X) ql gl;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          hybrid_child_gok g (length Q) gl; hybrid_child_gok g (length Q) gr;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          \<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X);
          rz \<longrightarrow> carried_descartes_count (carried_right X) = 0;
          code = 1 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          code = 0 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0;
          g = 0 \<or> 4398046511104 \<le> g \<longrightarrow> code \<noteq> 2;
          code = 0 \<or> code = 1 \<or> code = 2;
          rz \<longrightarrow> code \<noteq> 1 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr code rz \<le> SPEC \<Phi>"
  shows "truncate_children_mid_skip_right_monadic g Q
       \<le> SPEC (\<lambda>x. (case x of (ql, gl, qr, gr, mids, midbl, rz) \<Rightarrow>
             truncate_mid_decide_monadic g len mids midbl \<bind> (\<lambda>code. f ql gl qr gr code rz))
           \<le> SPEC \<Phi>)"
  apply (refine_vcg
      cdlr_SPEC_conj[OF
        truncate_children_mid_skip_right_agrees[OF frame lock g_tri Qne Qbound Qbound2 dep Q_small kb]
        truncate_children_mid_skip_right_gok[OF g_tri Qne Qbound Qbound2 dep Q_small kb],
        THEN order_trans])
  apply clarsimp
  apply (refine_vcg
      cdlr_SPEC_conj[OF
        truncate_mid_decide_agrees[OF frame lock len_eq Qne Q_small] defl_decide_one_mids,
        THEN order_trans])
  apply (all \<open>(((rule defl_interlock_rule, assumption, assumption) | simp); fail)?\<close>)
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  apply (all \<open>(((rule defl_interlock_rule, assumption, assumption) | simp); fail)?\<close>)
  done

lemma defl_split_children_escalate_gagrees:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and len_eq: "len = length Q"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>The node's own divisibility, which the two children inherit.\<close> It is inside the existential below because it is
       about the witness: exporting it as a separate SPEC joined by @{thm [source] defl_SPEC_conj} does not work, since two
       \<open>\<exists>XL\<close> SPECs need not pick the same \<open>XL\<close>. This proof's witness-choosing closers fix the witness explicitly
       (\<open>rule exI[of _ \<dots>]\<close>) rather than searching.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the children build's three word bounds.\<close>
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
  \<comment> \<open>A six-tuple. The right witness is claimed on \<open>\<not> rz\<close> only; on \<open>rz\<close> the payload is a right child of count \<open>0\<close> in the
     child's own init relation (the shape @{thm [source] defl_node_box_no_roots_y} consumes) and the interlock \<open>\<not> fired\<close>. The
     witness depends on the path (\<open>carried_right X\<close> on the plain path, the init's own right child on the two rebuild paths),
     which is why it is existential.\<close>
  shows "defl_split_children_escalate_monadic l_num r_num k rp g len Q
      \<le> SPEC (\<lambda>(ql, gl, qr, gr, fired, rz).
          (\<exists>XL. node_frame XL ql gl
                \<and> defl_node_wrel (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                                    (l_num + r_num) rp) XL
                \<and> (4398046511104 \<le> gl \<longrightarrow> ql = XL)
                \<and> (of_int_poly (Poly XL) :: real poly)
                     dvd (of_int_poly (Poly (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                           (l_num + r_num) rp)) :: real poly)) \<and>
          (\<not> rz \<longrightarrow> (\<exists>XR. node_frame XR qr gr
                \<and> defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                    (2 * r_num) rp) XR
                \<and> (4398046511104 \<le> gr \<longrightarrow> qr = XR)
                \<and> (of_int_poly (Poly XR) :: real poly)
                     dvd (of_int_poly (Poly (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                           (2 * r_num) rp)) :: real poly))) \<and>
          (rz \<longrightarrow> (\<exists>XR. defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                          (2 * r_num) rp) XR
                       \<and> carried_descartes_count XR = 0 \<and> 0 < length XR) \<and> \<not> fired) \<and>
          gl \<le> max g 4398046511104 \<and> gr \<le> max g 4398046511104 \<and>
          hybrid_child_depth_ok (k + 1) (length rp) gl \<and>
          hybrid_child_depth_ok (k + 1) (length rp) gr \<and>
          0 < length ql \<and> length ql \<le> length rp \<and>
          (\<not> rz \<longrightarrow> 0 < length qr \<and> length qr \<le> length rp) \<and>
          (fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0))"
proof -
  \<comment> \<open>the node's INIT is written out rather than \<open>define\<close>d: the rebuild's ASSERTs arrive
     UNFOLDED from \<open>refine_vcg\<close>, and a \<open>define\<close>d abbreviation would have to be folded back at
     every one of them.\<close>
  have lenXQ: "length X = length Q" using cdlr_node_frame_len[OF frame] by simp
  have Xne: "0 < length X" using Qne lenXQ by simp
  have wrelXi: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp)
                               (carried_init_same_den l_num (2 ^ k) r_num rp)"
    by (rule defl_node_wrel_init_refl[OF rpnz lr])
  have lenXi: "length (carried_init_same_den l_num (2 ^ k) r_num rp) = length rp"
    by (simp add: truncate_length_carried_init_same_den)
  have Xib: "length (carried_init_same_den l_num (2 ^ k) r_num rp) + 1
               < max_snat LENGTH(gmp_poly_len)" using lenXi rpb by simp
  have Xine: "0 < length (carried_init_same_den l_num (2 ^ k) r_num rp)"
    using lenXi rpne by simp
  have one_le: "1 \<le> (k + 2) * length rp"
  proof -
    have "(1::nat) * 1 \<le> (k + 2) * length rp" using rpne by (intro mult_le_mono) auto
    thus ?thesis by simp
  qed
  \<comment> \<open>the classic conversion, once: a child guard bounded by \<open>g + length Q\<close> lands in the
     coupling's depth disjunct, because the parent's own budget bounds \<open>g\<close> and \<open>length Q\<close> is
     \<open>length X \<le> length rp\<close>.\<close>
  have depth_of_gok: "hybrid_child_depth_ok (k + 1) (length rp) gg"
    if gok: "hybrid_child_gok g (length Q) gg" for gg
  proof (cases "4398046511104 \<le> gg")
    case True thus ?thesis by (simp add: hybrid_child_depth_ok_def)
  next
    case False
    have le: "gg \<le> g + length Q" using gok by (simp add: hybrid_child_gok_def)
    have gq: "length Q \<le> length rp" using lenXQ lenXrp by simp
    have gle: "g \<le> (k + 1) * length rp" using g_cpl glt by simp
    have "gg \<le> (k + 1) * length rp + length rp" using le gq gle by simp
    also have "\<dots> = (k + 2) * length rp" by simp
    finally show ?thesis by (simp add: hybrid_child_depth_ok_def)
  qed
  have len_l: "length ql = length X" if "node_frame (carried_left X) ql gg" for ql gg
    using cdlr_node_frame_len[OF that] by simp
  have len_r: "length qr = length X" if "node_frame (carried_right X) qr gg" for qr gg
    using cdlr_node_frame_len[OF that] by simp
  \<comment> \<open>the two child conversions, PRE-NORMALISED to \<open>2 * 2 ^ k\<close>: \<open>clarsimp\<close> rewrites the goal's
     \<open>2 ^ Suc k\<close> that way, and an \<open>intro:\<close> rule matches syntactically.\<close>
  have dvdLrel: "(of_int_poly (Poly XL) :: real poly)
                   dvd (of_int_poly (Poly (carried_init_same_den (2 * l_num) (2 * 2 ^ k)
                         (l_num + r_num) rp)) :: real poly)"
    if "defl_node_rel (carried_left (carried_init_same_den l_num (2 ^ k) r_num rp)) XL" for XL
    using defl_node_relD_dvd_real[OF that] by (simp only: defl_child_left_init) simp
  have dvdRrel: "(of_int_poly (Poly XR) :: real poly)
                   dvd (of_int_poly (Poly (carried_init_same_den (l_num + r_num) (2 * 2 ^ k)
                         (2 * r_num) rp)) :: real poly)"
    if "defl_node_rel (carried_right (carried_init_same_den l_num (2 ^ k) r_num rp)) XR" for XR
    using defl_node_relD_dvd_real[OF that] by (simp only: defl_child_right_init) simp
  have wrelL: "defl_node_wrel (carried_init_same_den (2 * l_num) (2 * 2 ^ k)
                                 (l_num + r_num) rp) XL"
    if "defl_node_rel (carried_left (carried_init_same_den l_num (2 ^ k) r_num rp)) XL" for XL
    using defl_child_wrel_left[OF wrelXi that] by simp
  have wrelR: "defl_node_wrel (carried_init_same_den (l_num + r_num) (2 * 2 ^ k)
                                 (2 * r_num) rp) XR"
    if "defl_node_rel (carried_right (carried_init_same_den l_num (2 ^ k) r_num rp)) XR" for XR
    using defl_child_wrel_right[OF wrelXi that] by simp
  \<comment> \<open>and the SMALL-degree tail's conversion: there the guard is bounded by the REBUILT
     node's own length, i.e. by \<open>length rp\<close>, which is inside the budget for the same trivial
     reason \<open>one_le\<close> is.\<close>
  have depth_of_gok0: "hybrid_child_depth_ok (k + 1) (length rp) gg"
    if gok: "hybrid_child_gok 0 (length (carried_init_same_den l_num (2 ^ k) r_num rp)) gg"
    for gg
  proof (cases "4398046511104 \<le> gg")
    case True thus ?thesis by (simp add: hybrid_child_depth_ok_def)
  next
    case False
    have le: "gg \<le> length rp" using gok lenXi by (simp add: hybrid_child_gok_def)
    have "length rp \<le> (k + 2) * length rp" by simp
    thus ?thesis using le by (simp add: hybrid_child_depth_ok_def)
  qed
  \<comment> \<open>the small tail's rule needs all its premises PINNED: with \<open>_\<close> holes the higher-order
     unification has to guess \<open>X\<close>, \<open>Q\<close> and \<open>len\<close> at once and does not.\<close>
  have lock0: "4398046511104 \<le> (0::nat) \<longrightarrow>
      carried_init_same_den l_num (2 ^ k) r_num rp
        = carried_init_same_den l_num (2 ^ k) r_num rp" by simp
  have gtri0: "(0::nat) < 1099511627776 \<or> 4398046511104 \<le> (0::nat)" by simp
  have Xsm: "length (carried_init_same_den l_num (2 ^ k) r_num rp) < 1099511627776"
    using lenXi rp_small by simp
  \<comment> \<open>the rebuilt node's three word bounds, for both rebuild paths.\<close>
  have Xib2: "length (carried_init_same_den l_num (2 ^ k) r_num rp) + 2
                < max_snat LENGTH(gmp_poly_len)" by (rule small_len_b2[OF Xsm])
  have Xdep: "1 * (length (carried_init_same_den l_num (2 ^ k) r_num rp) - 1)
                < max_snat LENGTH(gmp_poly_len)" by (rule small_len_dep[OF Xsm])
  have Xkb: "0 + length (carried_init_same_den l_num (2 ^ k) r_num rp)
                < max_snat LENGTH(gmp_poly_len)" using Xib by simp
  \<comment> \<open>\<^bold>\<open>The two branches' divisibility, one line each.\<close>\<close>
  have dvdLS: "(of_int_poly (Poly (carried_left (carried_init_same_den l_num (2 ^ k) r_num rp)))
                  :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                       (l_num + r_num) rp)) :: real poly)"
    by (simp only: defl_child_left_init) (rule dvd_refl)
  have dvdRS: "(of_int_poly (Poly (carried_right (carried_init_same_den l_num (2 ^ k) r_num rp)))
                  :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                       (2 * r_num) rp)) :: real poly)"
    by (simp only: defl_child_right_init) (rule dvd_refl)
  have dvdLX: "(of_int_poly (Poly (carried_left X)) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                       (l_num + r_num) rp)) :: real poly)"
    using defl_carried_left_dvd_real[OF dvdX] by (simp only: defl_child_left_init)
  have dvdRX: "(of_int_poly (Poly (carried_right X)) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                       (2 * r_num) rp)) :: real poly)"
    using defl_carried_right_dvd_real[OF dvdX] by (simp only: defl_child_right_init)
  have wrelLS: "defl_node_wrel (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                                  (l_num + r_num) rp) XL"
    if "defl_node_rel (carried_left (carried_init_same_den l_num (2 ^ k) r_num rp)) XL" for XL
    by (rule defl_child_wrel_left[OF wrelXi that])
  have wrelRS: "defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                  (2 * r_num) rp) XR"
    if "defl_node_rel (carried_right (carried_init_same_den l_num (2 ^ k) r_num rp)) XR" for XR
    by (rule defl_child_wrel_right[OF wrelXi that])
  \<comment> \<open>the init's own right child in the child's init relation (the \<open>rz\<close> witness on both rebuild paths), in both
     normalisations, and non-empty.\<close>
  have wrelRi: "defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                  (2 * r_num) rp)
                  (carried_right (carried_init_same_den l_num (2 ^ k) r_num rp))"
    by (rule wrelRS[OF defl_node_rel_refl])
  have wrelRi': "defl_node_wrel (carried_init_same_den (l_num + r_num) (2 * 2 ^ k)
                                  (2 * r_num) rp)
                  (carried_right (carried_init_same_den l_num (2 ^ k) r_num rp))"
    by (rule wrelR[OF defl_node_rel_refl])
  have neRi: "0 < length (carried_right (carried_init_same_den l_num (2 ^ k) r_num rp))"
    using Xine by simp
  have wrelRX: "defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                  (2 * r_num) rp) (carried_right X)"
    by (rule defl_child_wrel_right_id[OF wrel])
  have neRX: "0 < length (carried_right X)" using Xne by simp
  \<comment> \<open>the same two in \<open>clarsimp\<close>'s normal form, which writes \<open>0 < length xs\<close> as \<open>xs \<noteq> []\<close>.\<close>
  have neRiL: "carried_right (carried_init_same_den l_num (2 ^ k) r_num rp) \<noteq> []"
    using neRi length_greater_0_conv[of "carried_right (carried_init_same_den l_num (2 ^ k) r_num rp)"]
    by blast
  have neRXL: "carried_right X \<noteq> []"
    using neRX length_greater_0_conv[of "carried_right X"] by blast
  \<comment> \<open>the rebuilt node's children are \<open>length rp\<close> long: the frame pins the child's length to
     the child map's, and the rebuilt node is \<open>rp\<close>'s own init.\<close>
  have lenqL: "length q = length rp"
    if "node_frame (carried_left (carried_init_same_den l_num (2 ^ k) r_num rp)) q gg"
    for q gg using cdlr_node_frame_len[OF that] lenXi by simp
  have lenqR: "length q = length rp"
    if "node_frame (carried_right (carried_init_same_den l_num (2 ^ k) r_num rp)) q gg"
    for q gg using cdlr_node_frame_len[OF that] lenXi by simp
  \<comment> \<open>\<^bold>\<open>The rebuild branch, packaged\<close>: the rebuilt node is the INIT, so the deflating build
     is re-entered at guard \<open>0\<close> --- inside \<open>gex\<close> --- and its own contract applies. The two
     conversions afterwards are @{thm [source] defl_child_wrel_left} at the reflexive init
     relation, and @{thm [source] defl_escalate_gen_fired_transfer} for the shed flag.\<close>
  have rebuild_deflate:
    "defl_split_children_monadic 0 lenx lockok (carried_init_same_den l_num (2 ^ k) r_num rp)
       \<le> SPEC (\<lambda>(ql, gl, qr, gr, fired, rz).
          (\<exists>XL. node_frame XL ql gl
                \<and> defl_node_wrel (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                                    (l_num + r_num) rp) XL
                \<and> (4398046511104 \<le> gl \<longrightarrow> ql = XL)
                \<and> (of_int_poly (Poly XL) :: real poly)
                     dvd (of_int_poly (Poly (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                           (l_num + r_num) rp)) :: real poly)) \<and>
          (\<not> rz \<longrightarrow> (\<exists>XR. node_frame XR qr gr
                \<and> defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                    (2 * r_num) rp) XR
                \<and> (4398046511104 \<le> gr \<longrightarrow> qr = XR)
                \<and> (of_int_poly (Poly XR) :: real poly)
                     dvd (of_int_poly (Poly (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                           (2 * r_num) rp)) :: real poly))) \<and>
          (rz \<longrightarrow> (\<exists>XR. defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                          (2 * r_num) rp) XR
                       \<and> carried_descartes_count XR = 0 \<and> 0 < length XR) \<and> \<not> fired) \<and>
          gl \<le> max g 4398046511104 \<and> gr \<le> max g 4398046511104 \<and>
          hybrid_child_depth_ok (k + 1) (length rp) gl \<and>
          hybrid_child_depth_ok (k + 1) (length rp) gr \<and>
          0 < length ql \<and> length ql \<le> length rp \<and>
          (\<not> rz \<longrightarrow> 0 < length qr \<and> length qr \<le> length rp) \<and>
          (fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0))"
    if L3: "3 \<le> length (carried_init_same_den l_num (2 ^ k) r_num rp)" for lenx lockok
  proof -
    have base: "defl_split_children_monadic 0 lenx lockok
                  (carried_init_same_den l_num (2 ^ k) r_num rp)
        \<le> SPEC (\<lambda>(ql, gl, qr, gr, fired, rz).
            (\<exists>XL. node_frame XL ql gl
                  \<and> defl_node_rel (carried_left (carried_init_same_den l_num (2 ^ k)
                                                     r_num rp)) XL
                  \<and> (4398046511104 \<le> gl \<longrightarrow> ql = XL)) \<and>
            (\<not> rz \<longrightarrow> (\<exists>XR. node_frame XR qr gr
                  \<and> defl_node_rel (carried_right (carried_init_same_den l_num (2 ^ k)
                                                      r_num rp)) XR
                  \<and> (4398046511104 \<le> gr \<longrightarrow> qr = XR))) \<and>
            (rz \<longrightarrow> carried_descartes_count
                      (carried_right (carried_init_same_den l_num (2 ^ k) r_num rp)) = 0
                    \<and> \<not> fired) \<and>
            gl \<le> max 0 4398046511104 \<and> gr \<le> max 0 4398046511104 \<and>
            (gl \<le> 1 \<or> 4398046511104 \<le> gl) \<and>
            (gr \<le> 1 \<or> 4398046511104 \<le> gr) \<and>
            0 < length ql
              \<and> length ql \<le> length (carried_init_same_den l_num (2 ^ k) r_num rp) \<and>
            0 < length qr
              \<and> length qr \<le> length (carried_init_same_den l_num (2 ^ k) r_num rp) \<and>
            (fired \<longrightarrow> poly (map_poly rat_of_int
                        (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))) (1 / 2) = 0) \<and>
            (\<not> fired \<longrightarrow> poly (map_poly rat_of_int
                        (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))) (1 / 2) \<noteq> 0))"
      by (rule defl_split_children_agrees[OF node_frame_exact _ _ L3 Xib Xib2 Xdep Xkb]) simp_all
    show ?thesis
      apply (rule weaken_SPEC[OF base])
      apply clarsimp
      apply (intro conjI impI)
      \<comment> \<open>release the \<open>rz\<close>-guarded facts against the branch's own flag.\<close>
      apply (all \<open>((drule (1) mp)+)?\<close>)
      apply (all \<open>(elim exE conjE)?\<close>)
      \<comment> \<open>the witnesses are the agrees contract's own \<open>XL\<close>/\<open>XR\<close>; only the RELATION changes,
         from \<open>defl_node_rel\<close> against the init's child to \<open>defl_node_wrel\<close> against the child's
         own init.\<close>
      apply (all \<open>((rule exI, intro conjI, assumption, rule wrelL, assumption, (assumption | simp),
                    rule dvdLrel, assumption); fail)?\<close>)
      apply (all \<open>((rule exI, intro conjI, assumption, rule wrelR, assumption, (assumption | simp),
                    rule dvdRrel, assumption); fail)?\<close>)
      \<comment> \<open>\<open>rz\<close>: the init's own right child counts \<open>0\<close>\<close>
      apply (all \<open>((rule exI[of _ "carried_right (carried_init_same_den l_num (2 ^ k) r_num rp)"],
                    intro conjI, (rule wrelRi' | rule wrelRi), (assumption | simp),
                    (rule neRi | rule neRiL)); fail)?\<close>)
      apply (all \<open>((simp); fail)?\<close>)
      apply (all \<open>(simp; fail)?\<close>)
      apply (all \<open>((insert one_le, auto simp: hybrid_child_depth_ok_def); fail)?\<close>)
      apply (all \<open>((auto dest: defl_escalate_gen_fired_transfer[OF wrel]); fail)?\<close>)
      done
  qed
  show ?thesis
    unfolding defl_split_children_escalate_monadic_def poly_length_monadic_def PR_CONST_def
    apply (rule ASSERT_leI[OF Qne], rule ASSERT_leI[OF Qbound], rule ASSERT_leI[OF Qbound2],
           rule ASSERT_leI[OF dep], rule ASSERT_leI[OF rpne],
           rule ASSERT_leI[OF rpb], rule ASSERT_leI[OF krp])
    apply (simp only: nres_monad1)
    apply (rule defl_right_empty_decide_gbind[
          OF frame lock g_tri Qne Qbound Qbound2 dep Q_small kb len_eq])
    apply (split if_split)
    apply (intro conjI impI)
    subgoal
      \<comment> \<open>\<open>code = 2\<close>: the AMBIGUOUS rebuild\<close>
      apply (refine_vcg
          carried_init_inplace_monadic_correct[OF rpne rpb krp, THEN order_trans])
      apply (all \<open>((insert Xine Xib Xib2 Xdep, simp); fail)?\<close>)
      \<comment> \<open>\<open>3 \<le> len2\<close>: the rebuilt node re-enters the deflating build at guard \<open>0\<close>\<close>
      apply (all \<open>((rule rebuild_deflate, assumption); fail)?\<close>)
      \<comment> \<open>\<open>len2 < 3\<close>: no deflating build, only the children of the rebuilt node at guard \<open>0\<close>, so the node relation is
         reflexive and the guard is bounded by the rebuilt node's length. The decomposed variant: \<open>refine_vcg\<close> has already
         split the outer bind, so the \<open>doN\<close>-shaped \<open>gbind\<close> does not match.\<close>
      apply (rule defl_right_empty_decide_gbind_eta[
            OF node_frame_exact lock0 gtri0 Xine Xib Xib2 Xdep Xsm Xkb refl])
      apply (rule RETURN_rule)
      \<comment> \<open>\<^bold>\<open>\<open>simp only: prod.case\<close> BEFORE \<open>intro conjI\<close>\<close>: without the beta-reduction the
         postcondition is still a case-lambda applied to a tuple.\<close>
      apply (simp only: prod.case)
      apply (intro conjI impI)
      apply (all \<open>((drule (1) mp)+)?\<close>)
      apply (all \<open>(elim conjE)?\<close>)
      apply (all \<open>((rule exI[of _ "carried_left (carried_init_same_den l_num (2 ^ k) r_num rp)"],
                     intro conjI, assumption,
                     rule wrelLS[OF defl_node_rel_refl], assumption, rule dvdLS); fail)?\<close>)
      apply (all \<open>((rule exI[of _ "carried_right (carried_init_same_den l_num (2 ^ k) r_num rp)"],
                     intro conjI, assumption,
                     rule wrelRS[OF defl_node_rel_refl], assumption, rule dvdRS); fail)?\<close>)
      apply (all \<open>((rule exI[of _ "carried_right (carried_init_same_den l_num (2 ^ k) r_num rp)"],
                     intro conjI, rule wrelRi, assumption, (rule neRi | rule neRiL)); fail)?\<close>)
      apply (all \<open>((rule depth_of_gok0, assumption); fail)?\<close>)
      \<comment> \<open>explicit \<open>frule\<close>, not \<open>auto dest:\<close>, which searches for a long time here.\<close>
      apply (all \<open>((frule lenqL, insert rpne, simp); fail)?\<close>)
      apply (all \<open>((frule lenqR, insert rpne, simp); fail)?\<close>)
      apply (all \<open>((rule defl_escalate_gen_fired_transfer[OF wrel], simp); fail)?\<close>)
      apply (all \<open>((assumption | simp); fail)?\<close>)
      done
    \<comment> \<open>\<open>code \<noteq> 2\<close>: the children frame \<open>carried_left X\<close> and (on \<open>\<not> rz\<close>) \<open>carried_right X\<close>, and the node relation is the
       reflexive instance.\<close>
    subgoal
      apply (rule RETURN_rule)
      apply (simp only: prod.case)
      apply (intro conjI impI)
      apply (all \<open>((drule (1) mp)+)?\<close>)
      apply (all \<open>(elim conjE)?\<close>)
      apply (all \<open>((rule exI[of _ "carried_left X"], intro conjI, assumption,
                     rule defl_child_wrel_left_id[OF wrel], assumption, rule dvdLX); fail)?\<close>)
      apply (all \<open>((rule exI[of _ "carried_right X"], intro conjI, assumption,
                     rule defl_child_wrel_right_id[OF wrel], assumption, rule dvdRX); fail)?\<close>)
      apply (all \<open>((rule exI[of _ "carried_right X"], intro conjI, rule wrelRX, assumption,
                     (rule neRX | rule neRXL)); fail)?\<close>)
      apply (all \<open>((rule depth_of_gok, assumption); fail)?\<close>)
      apply (all \<open>((frule len_l, insert Xne lenXrp, simp); fail)?\<close>)
      apply (all \<open>((frule len_r, insert Xne lenXrp, simp); fail)?\<close>)
      apply (all \<open>((assumption | simp); fail)?\<close>)
      done
    done
qed


section \<open>The general-guard escalating contract in continuation form\<close>

text \<open>\<^bold>\<open>Why the packed \<open>\<le> SPEC\<close> form is not enough.\<close> @{thm [source] defl_split_children_escalate_gagrees} gives its facts
  packed, with the two exact children under an \<open>\<exists>\<close>. Given directly to \<open>refine_vcg\<close> in the split arm, the existentials land
  in the hypotheses and the tail's ghost children are instantiated to the stored children instead, leaving goals of the
  form \<open>node_frame a a aa\<close> (the ghost-instantiation problem described at @{thm [source] defl_split_tail_coupling}). Both
  shapes are supplied, as for @{thm [source] defl_split_children_gbind_decomp}: \<open>refine_vcg\<close> produces the decomposed goal
  whenever the op is under an outer bind, and a rule that does not match fails silently.\<close>

lemma defl_split_children_escalate_ggbind:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and len_eq: "len = length Q"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>passed to the contract.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
    \<comment> \<open>the contract's three word bounds, passed through.\<close>
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the right witness and its facts are guarded by \<open>\<not> rz\<close> (the continuation still receives a named \<open>XR\<close>, via
       @{thm [source] defl_ex_right_cases}); on \<open>rz\<close> the continuation receives the zero-count right child and the interlock
       instead.\<close>
    and cont: "\<And>XL XR ql gl qr gr fired rz.
        \<lbrakk> node_frame XL ql gl;
          defl_node_wrel (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                            (l_num + r_num) rp) XL;
          4398046511104 \<le> gl \<longrightarrow> ql = XL;
          \<not> rz \<longrightarrow> node_frame XR qr gr
                  \<and> defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                      (2 * r_num) rp) XR
                  \<and> (4398046511104 \<le> gr \<longrightarrow> qr = XR)
                  \<and> (of_int_poly (Poly XR) :: real poly)
                       dvd (of_int_poly (Poly (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                             (2 * r_num) rp)) :: real poly);
          rz \<longrightarrow> (\<exists>XR'. defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                             (2 * r_num) rp) XR'
                          \<and> carried_descartes_count XR' = 0 \<and> 0 < length XR') \<and> \<not> fired;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          hybrid_child_depth_ok (k + 1) (length rp) gl;
          hybrid_child_depth_ok (k + 1) (length rp) gr;
          0 < length ql; length ql \<le> length rp;
          \<not> rz \<longrightarrow> 0 < length qr \<and> length qr \<le> length rp;
          fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          (of_int_poly (Poly XL) :: real poly)
            dvd (of_int_poly (Poly (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                  (l_num + r_num) rp)) :: real poly) \<rbrakk>
        \<Longrightarrow> f ql gl qr gr fired rz \<le> SPEC \<Phi>"
  shows "(doN { (ql, gl, qr, gr, fired, rz)
                  \<leftarrow> defl_split_children_escalate_monadic l_num r_num k rp g len Q;
               f ql gl qr gr fired rz })
       \<le> SPEC \<Phi>"
  apply (refine_vcg defl_split_children_escalate_gagrees[
        OF frame lock g0 glt g_tri g_cpl Qne Qbound Q_small len_eq wrel rpnz lr lenXrp
           rpne rpb rp_small krp dvdX Qbound2 dep kb, THEN order_trans])
  apply clarsimp
  apply (erule defl_ex_right_cases)
  \<comment> \<open>\<^bold>\<open>Pin BOTH witnesses by name.\<close> \<open>clarsimp\<close> normalises the contract's \<open>2 ^ Suc k\<close> to
     \<open>2 * 2 ^ k\<close>, so a schematic \<open>?XR\<close> in \<open>cont\<close>'s \<open>\<not> rz\<close>-guarded premise never unifies
     with the named witness by \<open>assumption\<close>; fixed, the premise is closed by \<open>simp\<close>.\<close>
  subgoal for ql gl qr gr fired rz XL XR
    apply (rule cont[where XL = XL and XR = XR])
    apply (all \<open>((assumption | simp); fail)?\<close>)
    done
  done

lemma defl_split_children_escalate_ggbind_decomp:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and len_eq: "len = length Q"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>passed to the contract.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and cont: "\<And>XL XR ql gl qr gr fired rz.
        \<lbrakk> node_frame XL ql gl;
          defl_node_wrel (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                            (l_num + r_num) rp) XL;
          4398046511104 \<le> gl \<longrightarrow> ql = XL;
          \<not> rz \<longrightarrow> node_frame XR qr gr
                  \<and> defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                      (2 * r_num) rp) XR
                  \<and> (4398046511104 \<le> gr \<longrightarrow> qr = XR)
                  \<and> (of_int_poly (Poly XR) :: real poly)
                       dvd (of_int_poly (Poly (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                             (2 * r_num) rp)) :: real poly);
          rz \<longrightarrow> (\<exists>XR'. defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                             (2 * r_num) rp) XR'
                          \<and> carried_descartes_count XR' = 0 \<and> 0 < length XR') \<and> \<not> fired;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          hybrid_child_depth_ok (k + 1) (length rp) gl;
          hybrid_child_depth_ok (k + 1) (length rp) gr;
          0 < length ql; length ql \<le> length rp;
          \<not> rz \<longrightarrow> 0 < length qr \<and> length qr \<le> length rp;
          fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          (of_int_poly (Poly XL) :: real poly)
            dvd (of_int_poly (Poly (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                  (l_num + r_num) rp)) :: real poly) \<rbrakk>
        \<Longrightarrow> f ql gl qr gr fired rz \<le> SPEC \<Phi>"
  shows "defl_split_children_escalate_monadic l_num r_num k rp g len Q
       \<le> SPEC (\<lambda>x. (case x of (ql, gl, qr, gr, fired, rz) \<Rightarrow> f ql gl qr gr fired rz)
             \<le> SPEC \<Phi>)"
  apply (refine_vcg defl_split_children_escalate_gagrees[
        OF frame lock g0 glt g_tri g_cpl Qne Qbound Q_small len_eq wrel rpnz lr lenXrp
           rpne rpb rp_small krp dvdX Qbound2 dep kb, THEN order_trans])
  apply clarsimp
  apply (erule defl_ex_right_cases)
  \<comment> \<open>\<^bold>\<open>Pin BOTH witnesses by name.\<close> \<open>clarsimp\<close> normalises the contract's \<open>2 ^ Suc k\<close> to
     \<open>2 * 2 ^ k\<close>, so a schematic \<open>?XR\<close> in \<open>cont\<close>'s \<open>\<not> rz\<close>-guarded premise never unifies
     with the named witness by \<open>assumption\<close>; fixed, the premise is closed by \<open>simp\<close>.\<close>
  subgoal for ql gl qr gr fired rz XL XR
    apply (rule cont[where XL = XL and XR = XR])
    apply (all \<open>((assumption | simp); fail)?\<close>)
    done
  done



section \<open>The split arm at a general guard\<close>

lemma defl_branch_split_gen_coupling:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    \<comment> \<open>\<^bold>\<open>Last\<close>, immediately before \<open>shows\<close>, so that no existing \<open>[OF \<dots>]\<close> position in a caller moves.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
  shows "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (\<lambda>(wl, acc').
           case wl of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
             defl_trunc_coupling todo' qtodo' cs' gs' rp')"
proof -
  have pm: "carried_push_mid_monadic (al, ar, ak) l_num r_num k
      \<le> SPEC (\<lambda>a. a = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1]))"
    by (simp add: cdlr_push_mid_eq[OF accpush])
  have notgex: "\<not> ((g = 0 \<or> 4398046511104 \<le> g) \<and> 3 \<le> length Q)" using g0 glt by simp
  \<comment> \<open>\<^bold>\<open>At a general guard the child payload holds trivially.\<close> \<open>g < 2\<^sup>4\<^sup>2\<close> reduces the contract's \<open>gl \<le> max g 2\<^sup>4\<^sup>2\<close> to
     \<open>gl \<le> 2\<^sup>4\<^sup>2\<close>, so the payload antecedent \<open>2\<^sup>4\<^sup>2 + 2 \<le> gl\<close> is false and the ceiling is immediate.\<close>
  have gmax: "max g 4398046511104 = 4398046511104" using glt by simp
  \<comment> \<open>the children contract's three word bounds, from what the arm carries.\<close>
  have lXQ: "length X = length Q" using cdlr_node_frame_len[OF frame] by simp
  have Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)" by (rule small_len_b2[OF Q_small])
  have dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)" by (rule small_len_dep[OF Q_small])
  have kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    using gcap_rp lenXrp lXQ max.cobounded1[of g 4398046511104] by linarith
  \<comment> \<open>closers without search: the release stage below puts the whole contract into every goal.\<close>
  have gl_bound: "x \<le> max g 4398046511104 \<Longrightarrow> x + length rp < max_snat LENGTH(gmp_poly_len)"
    for x using gcap_rp by linarith
  have gl_ceil: "x \<le> max g 4398046511104 \<Longrightarrow> x \<le> 4398046511104 + length rp" for x
    using gmax by simp
  have gl_pay: "x \<le> max g 4398046511104 \<Longrightarrow> 4398046511106 \<le> x \<longrightarrow> R" for x R
    using gmax by simp
  show ?thesis
    unfolding defl_branch_split_monadic_def poly_length_monadic_def PR_CONST_def
    using Qne Qbound kcap rpne rpb krp accpush qcap gcap ecap sscap ccap push scap1
    apply (simp only: nres_monad1)
    \<comment> \<open>\<^bold>\<open>The CONT-style twins, not the packed contract\<close> --- the ghost-instantiation trap
       @{thm [source] defl_split_tail_coupling} exists to avoid.\<close>
    apply (refine_vcg
        defl_split_children_escalate_ggbind[OF frame lock g0 glt g_tri g_cpl Qne Qbound
          Q_small refl wrel rpnz lr lenXrp rpne rpb rp_small krp dvdX Qbound2 dep kb]
        defl_split_children_escalate_ggbind_decomp[OF frame lock g0 glt g_tri g_cpl Qne Qbound
          Q_small refl wrel rpnz lr lenXrp rpne rpb rp_small krp dvdX Qbound2 dep kb]
        pm[THEN order_trans])
    \<comment> \<open>goal 1 is \<open>True\<close>; the \<open>gex\<close> branch is unreachable here; and the \<open>rz \<and> mid\<close> branch is excluded by the interlock
       (\<open>rz \<longrightarrow> \<not> fired\<close>)\<close>
    apply (all \<open>((insert notgex, simp); fail)?\<close>)
    \<comment> \<open>\<^bold>\<open>The tails, with the ghosts fixed by \<open>subgoal for\<close>\<close>: left schematic, \<open>?XL\<close>/\<open>?XR\<close> would unify with the stored
       children. The \<open>\<not> rz\<close>-guarded right facts are released first, and then the tail matching the goal's op is used: the
       one-child tail on \<open>rz\<close>, the two-child tail otherwise.\<close>
    subgoal for XL XR ql gl qr gr fired rz
      apply ((drule (1) mp)+)?
      apply (elim conjE)?
      apply (rule order_trans[OF defl_split_tail_coupling_left[where XL = XL, OF coup]]
             | rule order_trans[OF defl_split_tail_coupling[where XL = XL and XR = XR, OF coup]])
      apply (all \<open>(assumption; fail)?\<close>)
      apply (all \<open>((simp add: hybrid_child_depth_ok_def); fail)?\<close>)
      apply (all \<open>((rule gl_bound, assumption); fail)?\<close>)
      apply (all \<open>((rule gl_ceil, assumption); fail)?\<close>)
      apply (all \<open>((rule gl_pay, assumption); fail)?\<close>)
      apply (all \<open>((insert rpb rp_small rp_pb kcap scap1, simp); fail)?\<close>)
      apply (all \<open>(simp; fail)?\<close>)
      done
    subgoal for XL XR ql gl qr gr fired rz
      apply ((drule (1) mp)+)?
      apply (elim conjE)?
      apply (rule order_trans[OF defl_split_tail_coupling_left[where XL = XL, OF coup]]
             | rule order_trans[OF defl_split_tail_coupling[where XL = XL and XR = XR, OF coup]])
      apply (all \<open>(assumption; fail)?\<close>)
      apply (all \<open>((simp add: hybrid_child_depth_ok_def); fail)?\<close>)
      apply (all \<open>((rule gl_bound, assumption); fail)?\<close>)
      apply (all \<open>((rule gl_ceil, assumption); fail)?\<close>)
      apply (all \<open>((rule gl_pay, assumption); fail)?\<close>)
      apply (all \<open>((insert rpb rp_small rp_pb kcap scap1, simp); fail)?\<close>)
      apply (all \<open>(simp; fail)?\<close>)
      done
    subgoal for XL XR ql gl qr gr fired rz
      apply ((drule (1) mp)+)?
      apply (elim conjE)?
      apply (rule order_trans[OF defl_split_tail_coupling_left[where XL = XL, OF coup]]
             | rule order_trans[OF defl_split_tail_coupling[where XL = XL and XR = XR, OF coup]])
      apply (all \<open>(assumption; fail)?\<close>)
      apply (all \<open>((simp add: hybrid_child_depth_ok_def); fail)?\<close>)
      apply (all \<open>((rule gl_bound, assumption); fail)?\<close>)
      apply (all \<open>((rule gl_ceil, assumption); fail)?\<close>)
      apply (all \<open>((rule gl_pay, assumption); fail)?\<close>)
      apply (all \<open>((insert rpb rp_small rp_pb kcap scap1, simp); fail)?\<close>)
      apply (all \<open>(simp; fail)?\<close>)
      done
    done
qed


text \<open>\<^bold>\<open>The no-fire half of the general-guard escalating contract.\<close> @{thm [source] defl_split_children_escalate_gagrees}
  states only \<open>fired \<longrightarrow>\<close> the midpoint is a root, which the coupling needs. The state half needs the converse: the split arm
  pushes the two open half-boxes, so the midpoint is covered only if it is emitted, and
  @{thm [source] defl_pending_covers_split_nofire} asks that the midpoint not be a root on the branch where nothing was
  emitted.

  It holds at a general guard for a reason unrelated to \<open>gex\<close>: the decisive branch returns \<open>fired = (code = 1)\<close>, and
  @{thm [source] truncate_mid_decide_agrees} gives \<open>code = 0 \<longrightarrow> \<not> root\<close> with the trichotomy, so \<open>\<not> fired\<close> and \<open>code \<noteq> 2\<close> force
  \<open>code = 0\<close>. It is a separate \<open>\<le> SPEC\<close>, joined by @{thm [source] defl_SPEC_conj}, so that the closers of \<open>_gagrees\<close> are not
  reordered.\<close>

lemma defl_split_children_escalate_gnofire:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and len_eq: "len = length Q"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the children build's three word bounds.\<close>
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
  shows "defl_split_children_escalate_monadic l_num r_num k rp g len Q
      \<le> SPEC (\<lambda>(ql, gl, qr, gr, fired, rz).
          \<not> fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0)"
proof -
  have lenXi: "length (carried_init_same_den l_num (2 ^ k) r_num rp) = length rp"
    by (simp add: truncate_length_carried_init_same_den)
  have Xib: "length (carried_init_same_den l_num (2 ^ k) r_num rp) + 1
               < max_snat LENGTH(gmp_poly_len)" using lenXi rpb by simp
  have Xine: "0 < length (carried_init_same_den l_num (2 ^ k) r_num rp)"
    using lenXi rpne by simp
  have Xsm: "length (carried_init_same_den l_num (2 ^ k) r_num rp) < 1099511627776"
    using lenXi rp_small by simp
  have Xib2: "length (carried_init_same_den l_num (2 ^ k) r_num rp) + 2
                < max_snat LENGTH(gmp_poly_len)" by (rule small_len_b2[OF Xsm])
  have Xdep: "1 * (length (carried_init_same_den l_num (2 ^ k) r_num rp) - 1)
                < max_snat LENGTH(gmp_poly_len)" by (rule small_len_dep[OF Xsm])
  have Xkb: "0 + length (carried_init_same_den l_num (2 ^ k) r_num rp)
                < max_snat LENGTH(gmp_poly_len)" using Xib by simp
  have lock0: "4398046511104 \<le> (0::nat) \<longrightarrow>
      carried_init_same_den l_num (2 ^ k) r_num rp
        = carried_init_same_den l_num (2 ^ k) r_num rp" by simp
  have gtri0: "(0::nat) < 1099511627776 \<or> 4398046511104 \<le> (0::nat)" by simp
  have rebuild_nofire:
    "defl_split_children_monadic 0 lenx lockok (carried_init_same_den l_num (2 ^ k) r_num rp)
       \<le> SPEC (\<lambda>(ql, gl, qr, gr, fired, rz).
          \<not> fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0)"
    if L3: "3 \<le> length (carried_init_same_den l_num (2 ^ k) r_num rp)" for lenx lockok
  proof -
    have base: "defl_split_children_monadic 0 lenx lockok
                  (carried_init_same_den l_num (2 ^ k) r_num rp)
        \<le> SPEC (\<lambda>(ql, gl, qr, gr, fired, rz).
            (\<not> fired \<longrightarrow> poly (map_poly rat_of_int
                        (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))) (1 / 2) \<noteq> 0))"
      by (rule weaken_SPEC[OF defl_split_children_agrees[OF node_frame_exact _ _ L3 Xib Xib2 Xdep
            Xkb]]) auto
    show ?thesis
      apply (rule weaken_SPEC[OF base])
      \<comment> \<open>\<open>auto dest:\<close>, not \<open>rule\<close>: \<open>clarsimp\<close> folds \<open>map_poly rat_of_int\<close> into \<open>of_int_poly\<close>
         and the transfer lemma is stated in the unfolded form, so a syntactic \<open>rule\<close> misses.\<close>
      apply (auto dest: defl_escalate_gen_nofire_transfer[OF wrel])
      done
  qed
  show ?thesis
    unfolding defl_split_children_escalate_monadic_def poly_length_monadic_def PR_CONST_def
    apply (rule ASSERT_leI[OF Qne], rule ASSERT_leI[OF Qbound], rule ASSERT_leI[OF Qbound2],
           rule ASSERT_leI[OF dep], rule ASSERT_leI[OF rpne],
           rule ASSERT_leI[OF rpb], rule ASSERT_leI[OF krp])
    apply (simp only: nres_monad1)
    apply (rule defl_right_empty_decide_gbind[
          OF frame lock g_tri Qne Qbound Qbound2 dep Q_small kb len_eq])
    apply (split if_split)
    apply (intro conjI impI)
    subgoal
      apply (refine_vcg
          carried_init_inplace_monadic_correct[OF rpne rpb krp, THEN order_trans])
      apply (all \<open>((insert Xine Xib Xib2 Xdep, simp); fail)?\<close>)
      apply (all \<open>((rule rebuild_nofire, assumption); fail)?\<close>)
      apply (rule defl_right_empty_decide_gbind_eta[
            OF node_frame_exact lock0 gtri0 Xine Xib Xib2 Xdep Xsm Xkb refl])
      apply (rule RETURN_rule)
      apply (simp only: prod.case)
      apply (auto dest: defl_escalate_gen_nofire_transfer[OF wrel])
      done
    subgoal
      apply (rule RETURN_rule)
      apply (simp only: prod.case)
      \<comment> \<open>the decisive branch: the contract's trichotomy plus \<open>code \<noteq> 2\<close> and \<open>\<not> fired\<close>
         (i.e. \<open>code \<noteq> 1\<close>) leaves \<open>code = 0\<close>, whose own clause IS the conclusion\<close>
      apply auto
      done
    done
qed


text \<open>\<^bold>\<open>The general-guard escalating contract in continuation form, with the no-fire clause.\<close> The plain
  @{thm [source] defl_split_children_escalate_ggbind} is what the coupling pass uses; the state pass needs the shed flag in
  both directions, because its conclusion is a dichotomy on \<open>poly X (1/2) = 0\<close> and the accumulator changes on exactly one
  side. It is a separate pair so that @{thm [source] defl_branch_split_gen_coupling}, which consumes the existing
  continuation, is unaffected.\<close>

lemma defl_split_children_escalate_ggbind_nf:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and len_eq: "len = length Q"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>passed to @{thm [source] defl_split_children_escalate_gagrees}.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
    \<comment> \<open>the two contracts' three word bounds, passed through.\<close>
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the \<open>_ggbind\<close> continuation (guarded right witness, \<open>rz\<close> payload), with the no-fire clause last.\<close>
    and cont: "\<And>XL XR ql gl qr gr fired rz.
        \<lbrakk> node_frame XL ql gl;
          defl_node_wrel (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                            (l_num + r_num) rp) XL;
          4398046511104 \<le> gl \<longrightarrow> ql = XL;
          \<not> rz \<longrightarrow> node_frame XR qr gr
                  \<and> defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                      (2 * r_num) rp) XR
                  \<and> (4398046511104 \<le> gr \<longrightarrow> qr = XR)
                  \<and> (of_int_poly (Poly XR) :: real poly)
                       dvd (of_int_poly (Poly (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                             (2 * r_num) rp)) :: real poly);
          rz \<longrightarrow> (\<exists>XR'. defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                             (2 * r_num) rp) XR'
                          \<and> carried_descartes_count XR' = 0 \<and> 0 < length XR') \<and> \<not> fired;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          hybrid_child_depth_ok (k + 1) (length rp) gl;
          hybrid_child_depth_ok (k + 1) (length rp) gr;
          0 < length ql; length ql \<le> length rp;
          \<not> rz \<longrightarrow> 0 < length qr \<and> length qr \<le> length rp;
          fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          (of_int_poly (Poly XL) :: real poly)
            dvd (of_int_poly (Poly (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                  (l_num + r_num) rp)) :: real poly);
          \<not> fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr fired rz \<le> SPEC \<Phi>"
  shows "(doN { (ql, gl, qr, gr, fired, rz)
                  \<leftarrow> defl_split_children_escalate_monadic l_num r_num k rp g len Q;
               f ql gl qr gr fired rz })
       \<le> SPEC \<Phi>"
  apply (refine_vcg defl_SPEC_conj[OF
        defl_split_children_escalate_gagrees[
          OF frame lock g0 glt g_tri g_cpl Qne Qbound Q_small len_eq wrel rpnz lr lenXrp
             rpne rpb rp_small krp dvdX Qbound2 dep kb]
        defl_split_children_escalate_gnofire[
          OF frame lock g_tri Qne Qbound Q_small len_eq wrel rpne rpb rp_small krp
             Qbound2 dep kb],
        THEN order_trans])
  apply clarsimp
  apply (erule defl_ex_right_cases)
  \<comment> \<open>\<^bold>\<open>Pin BOTH witnesses by name.\<close> \<open>clarsimp\<close> normalises the contract's \<open>2 ^ Suc k\<close> to
     \<open>2 * 2 ^ k\<close>, so a schematic \<open>?XR\<close> in \<open>cont\<close>'s \<open>\<not> rz\<close>-guarded premise never unifies
     with the named witness by \<open>assumption\<close>; fixed, the premise is closed by \<open>simp\<close>.\<close>
  subgoal for ql gl qr gr fired rz XL XR
    apply (rule cont[where XL = XL and XR = XR])
    apply (all \<open>((assumption | simp); fail)?\<close>)
    done
  done

lemma defl_split_children_escalate_ggbind_decomp_nf:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and len_eq: "len = length Q"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and cont: "\<And>XL XR ql gl qr gr fired rz.
        \<lbrakk> node_frame XL ql gl;
          defl_node_wrel (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                            (l_num + r_num) rp) XL;
          4398046511104 \<le> gl \<longrightarrow> ql = XL;
          \<not> rz \<longrightarrow> node_frame XR qr gr
                  \<and> defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                      (2 * r_num) rp) XR
                  \<and> (4398046511104 \<le> gr \<longrightarrow> qr = XR)
                  \<and> (of_int_poly (Poly XR) :: real poly)
                       dvd (of_int_poly (Poly (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                             (2 * r_num) rp)) :: real poly);
          rz \<longrightarrow> (\<exists>XR'. defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                             (2 * r_num) rp) XR'
                          \<and> carried_descartes_count XR' = 0 \<and> 0 < length XR') \<and> \<not> fired;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          hybrid_child_depth_ok (k + 1) (length rp) gl;
          hybrid_child_depth_ok (k + 1) (length rp) gr;
          0 < length ql; length ql \<le> length rp;
          \<not> rz \<longrightarrow> 0 < length qr \<and> length qr \<le> length rp;
          fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          (of_int_poly (Poly XL) :: real poly)
            dvd (of_int_poly (Poly (carried_init_same_den (2 * l_num) (2 ^ Suc k)
                  (l_num + r_num) rp)) :: real poly);
          \<not> fired \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr fired rz \<le> SPEC \<Phi>"
  shows "defl_split_children_escalate_monadic l_num r_num k rp g len Q
       \<le> SPEC (\<lambda>x. (case x of (ql, gl, qr, gr, fired, rz) \<Rightarrow> f ql gl qr gr fired rz)
             \<le> SPEC \<Phi>)"
  apply (refine_vcg defl_SPEC_conj[OF
        defl_split_children_escalate_gagrees[
          OF frame lock g0 glt g_tri g_cpl Qne Qbound Q_small len_eq wrel rpnz lr lenXrp
             rpne rpb rp_small krp dvdX Qbound2 dep kb]
        defl_split_children_escalate_gnofire[
          OF frame lock g_tri Qne Qbound Q_small len_eq wrel rpne rpb rp_small krp
             Qbound2 dep kb],
        THEN order_trans])
  apply clarsimp
  apply (erule defl_ex_right_cases)
  \<comment> \<open>\<^bold>\<open>Pin BOTH witnesses by name.\<close> \<open>clarsimp\<close> normalises the contract's \<open>2 ^ Suc k\<close> to
     \<open>2 * 2 ^ k\<close>, so a schematic \<open>?XR\<close> in \<open>cont\<close>'s \<open>\<not> rz\<close>-guarded premise never unifies
     with the named witness by \<open>assumption\<close>; fixed, the premise is closed by \<open>simp\<close>.\<close>
  subgoal for ql gl qr gr fired rz XL XR
    apply (rule cont[where XL = XL and XR = XR])
    apply (all \<open>((assumption | simp); fail)?\<close>)
    done
  done


text \<open>\<^bold>\<open>The general-guard split arm's state half\<close>, the counterpart of @{thm [source] defl_branch_split_exact_state}: the
  worklist receives the two children, and the accumulator changes exactly when the midpoint is a root of \<open>X\<close>. Unlike the
  coupling pass, this one does not depend on which exact child the ghost is (the conclusion fixes only the worklist and
  the accumulator), so \<open>assumption\<close> may take the contract's own \<open>XL\<close>.\<close>

lemma defl_branch_split_gen_state:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>Last\<close>: passed to @{thm [source] defl_split_children_escalate_gagrees}, whose existentials carry the two
       children's divisibility.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
  \<comment> \<open>the worklist is a dichotomy, as on the exact arm. On the one-push side the right half's payload is a zero-count
     right child in the child's own init relation (existential, because it depends on the escalation path), and the shed did
     not fire.\<close>
  shows "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (\<lambda>(wl, acc').
           (fst wl = (lns @ [2 * l_num, l_num + r_num],
                      rns @ [l_num + r_num, 2 * r_num], ks @ [Suc k, Suc k])
            \<or> (fst wl = (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [Suc k])
               \<and> (\<exists>XR'. defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                          (2 * r_num) rp) XR'
                        \<and> carried_descartes_count XR' = 0 \<and> 0 < length XR')
               \<and> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0))
           \<and> (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0
               \<longrightarrow> acc' = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [Suc k]))
           \<and> (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0
               \<longrightarrow> acc' = (al, ar, ak)))"
proof -
  have pm: "carried_push_mid_monadic (al, ar, ak) l_num r_num k
      \<le> SPEC (\<lambda>a. a = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1]))"
    by (simp add: cdlr_push_mid_eq[OF accpush])
  have notgex: "\<not> ((g = 0 \<or> 4398046511104 \<le> g) \<and> 3 \<le> length Q)" using g0 glt by simp
  \<comment> \<open>the children contract's three word bounds, as in the coupling pass.\<close>
  have lXQ: "length X = length Q" using cdlr_node_frame_len[OF frame] by simp
  have Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)" by (rule small_len_b2[OF Q_small])
  have dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)" by (rule small_len_dep[OF Q_small])
  have kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    using gcap_rp lenXrp lXQ max.cobounded1[of g 4398046511104] by linarith
  have gl_bound: "x \<le> max g 4398046511104 \<Longrightarrow> x + length rp < max_snat LENGTH(gmp_poly_len)"
    for x using gcap_rp by linarith
  show ?thesis
    unfolding defl_branch_split_monadic_def poly_length_monadic_def PR_CONST_def
    using Qne Qbound kcap rpne rpb krp accpush qcap gcap ecap sscap ccap push scap1
    apply (simp only: nres_monad1)
    apply (refine_vcg
        defl_split_children_escalate_ggbind_nf[OF frame lock g0 glt g_tri g_cpl Qne Qbound
          Q_small refl wrel rpnz lr lenXrp rpne rpb rp_small krp dvdX Qbound2 dep kb]
        defl_split_children_escalate_ggbind_decomp_nf[OF frame lock g0 glt g_tri g_cpl Qne
          Qbound Q_small refl wrel rpnz lr lenXrp rpne rpb rp_small krp dvdX Qbound2 dep kb]
        defl_split_tail_state[THEN order_trans]
        defl_split_tail_state_left[THEN order_trans]
        pm[THEN order_trans])
    apply (all \<open>(assumption; fail)?\<close>)
    \<comment> \<open>the state pass does not care which exact child the ghost is: \<open>XL := ql\<close> is fine\<close>
    apply (all \<open>((rule node_frame_exact_any_g); fail)?\<close>)
    apply (all \<open>((rule gl_bound, assumption); fail)?\<close>)
    apply (all \<open>((insert notgex, simp); fail)?\<close>)
    apply (all \<open>((insert rpb rp_small rp_pb kcap scap1, simp); fail)?\<close>)
    apply (all \<open>(simp; fail)?\<close>)
    done
qed


text \<open>\<^bold>\<open>The general-guard split arm\<close>, assembled as @{thm [source] defl_branch_split_exact_invar}: the coupling pass and
  the state pass joined by @{thm [source] defl_SPEC_conj}, and the three invariant clauses read off. The payload step is
  the exact arm's: it depends only on the two dichotomy implications, not on how the children were built, which is why the
  state half is a dichotomy on \<open>poly X (1/2) = 0\<close> rather than on the op's \<open>fired\<close> flag.\<close>

theorem defl_branch_split_gen_invar:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)"
    and cov: "defl_dispatch_covers (of_int_poly (Poly rp) :: real poly) lo
                (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
    \<comment> \<open>\<^bold>\<open>Last\<close>, immediately before \<open>shows\<close>, so that no existing \<open>[OF \<dots>]\<close> position in a caller moves.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
  shows "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo)"
proof -
  have payload: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (a1, a2, a3)
      \<and> defl_pending_covers (of_int_poly (Poly rp) :: real poly) lo
          (lns @ [2 * l_num, l_num + r_num],
           rns @ [l_num + r_num, 2 * r_num], ks @ [Suc k, Suc k]) (a1, a2, a3)"
    if F: "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0
             \<longrightarrow> a1 = al @ [l_num + r_num] \<and> a2 = ar @ [l_num + r_num]
                 \<and> a3 = ak @ [Suc k]"
      and N: "poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0
             \<longrightarrow> a1 = al \<and> a2 = ar \<and> a3 = ak"
    for a1 a2 a3
  proof (cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0")
    case fired: True
    have accd: "a1 = al @ [l_num + r_num]" "a2 = ar @ [l_num + r_num]" "a3 = ak @ [Suc k]"
      using F fired by simp_all
    have pk: "dsc_pair_ok (of_int_poly (Poly rp) :: real poly)
          (real_of_int (l_num + r_num) / 2 ^ Suc k,
           real_of_int (l_num + r_num) / 2 ^ Suc k)"
      using defl_mid_pair_ok[OF wrel fired] by simp
    show ?thesis
      unfolding accd
      using defl_acc_isolates_push[OF iso lal lak pk]
            defl_pending_covers_split_fire[OF cov l1 l2 lal lak]
      by simp
  next
    case nofire: False
    have accd: "a1 = al" "a2 = ar" "a3 = ak" using N nofire by simp_all
    have nomid: "poly (of_int_poly (Poly rp) :: real poly)
          (real_of_int (l_num + r_num) / 2 ^ Suc k) \<noteq> 0"
      using defl_mid_not_root_global[OF wrel nofire] by simp
    show ?thesis
      unfolding accd
      using iso defl_pending_covers_split_nofire[OF cov l1 l2 nomid] by simp
  qed
  \<comment> \<open>\<^bold>\<open>The left-only payload\<close> at a general guard: \<open>acc\<close> unchanged, the midpoint not a root, and the right half
     root-free, read off a zero-count right child in the child's own init relation, whichever escalation path produced it.\<close>
  have payload1: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)
      \<and> defl_pending_covers (of_int_poly (Poly rp) :: real poly) lo
          (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [Suc k]) (al, ar, ak)"
    if ex: "\<exists>XR'. defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                    (2 * r_num) rp) XR'
                 \<and> carried_descartes_count XR' = 0 \<and> 0 < length XR'"
      and nofire: "poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0"
  proof -
    from ex obtain XR' where
        wrelR: "defl_node_wrel (carried_init_same_den (l_num + r_num) (2 ^ Suc k)
                                  (2 * r_num) rp) XR'"
      and cnt0: "carried_descartes_count XR' = 0" and neR: "0 < length XR'" by blast
    have nomid: "poly (of_int_poly (Poly rp) :: real poly)
          (real_of_int (l_num + r_num) / 2 ^ Suc k) \<noteq> 0"
      using defl_mid_not_root_global[OF wrel nofire] by simp
    have noright: "poly (of_int_poly (Poly rp) :: real poly) y \<noteq> 0"
      if lo': "real_of_int (l_num + r_num) / 2 ^ Suc k < y"
        and hi': "y < real_of_int (2 * r_num) / 2 ^ Suc k" for y
    proof -
      have "real_of_int (l_num + r_num) / 2 ^ Suc k < real_of_int (2 * r_num) / 2 ^ Suc k"
        using lo' hi' by linarith
      hence "real_of_int (l_num + r_num) < real_of_int (2 * r_num)"
        unfolding divide_less_cancel by simp
      hence lr': "l_num + r_num < 2 * r_num" by (simp only: of_int_less_iff)
      show ?thesis by (rule defl_node_box_no_roots_y[OF wrelR cnt0 neR lr' lo' hi'])
    qed
    show ?thesis
      using iso defl_pending_covers_split_left[OF cov l1 l2 nomid noright] by simp
  qed
  show ?thesis
    apply (rule order_trans[OF defl_SPEC_conj[OF
          defl_branch_split_gen_coupling[OF frame lock g0 glt g_tri g_cpl gcap_rp Qne Qbound
            Q_small wrel rpnz lr lenXrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap
            ecap sscap ccap push scap1 coup dvdX]
          defl_branch_split_gen_state[OF frame lock g0 glt g_tri g_cpl gcap_rp Qne Qbound
            Q_small wrel rpnz lr lenXrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap
            ecap sscap ccap push scap1 dvdX]]])
    apply (rule SPEC_rule)
    apply (clarsimp simp: defl_loop_invar_def)
    \<comment> \<open>split the worklist dichotomy first, then let \<open>clarsimp\<close> substitute each side.\<close>
    apply (erule disjE)
     apply clarsimp
     apply (rule conjI)
      apply (rule conjunct1[OF payload]; assumption)
     apply (rule conjunct2[OF payload]; assumption)
    apply clarsimp
    \<comment> \<open>the existential arrives in \<open>clarsimp\<close>'s normal form (\<open>2 * 2 ^ k\<close>, \<open>xs \<noteq> []\<close>)\<close>
    apply (rule payload1)
     apply (all \<open>(assumption; fail)?\<close>)
     apply (all \<open>(blast; fail)?\<close>)
    apply (all \<open>(auto; fail)?\<close>)
    done
qed

subsection \<open>The general-guard \<open>v\<close> read is exact\<close>

text \<open>\<^bold>\<open>At a general guard the window's count is never the cache.\<close> Both non-exact branches of
  @{const hybrid_window_v_monadic} are unreachable there: the W1 branch needs \<open>4 \<le> cnt\<close>, which
  @{thm [source] defl_resolve_count_classify} has just excluded (\<open>g < 2\<^sup>4\<^sup>2 \<longrightarrow> c' < 4\<close>, itself
  read off @{const defl_node_ok}'s class bound), and the capped branch needs the payload guard
  \<open>2\<^sup>4\<^sup>2 + 2 \<le> g\<close>. What is left is the exact kernel on the polynomial the escalate just
  rebuilt --- which is the whole point: the count then describes \<^emph>\<open>that\<close> polynomial and not the
  deflated object the cache was about.\<close>

lemma defl_window_v_exact_gen:
  assumes cnt4: "cnt < 4"
    and glt: "g < 4398046511106"
    and Qb: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_window_v_monadic cnt g Q \<le> SPEC (\<lambda>v. v = carried_descartes_count Q)"
  unfolding hybrid_window_v_monadic_def PR_CONST_def
  using cnt4 glt
  apply simp
  apply (rule order_trans[OF carried_descartes_count_exact_monadic_correct[OF Qb]])
  apply simp
  done

section \<open>The gate-open arm at a general guard\<close>

text \<open>\<^bold>\<open>The remaining case of the fourth arm.\<close> Under \<open>gex\<close> the escalation is a no-op and everything concerns the node's
  own (possibly deflated) exact object \<open>X\<close>. At \<open>0 < g < 2\<^sup>4\<^sup>2\<close> it rebuilds, and the rest of the arm runs on the node's init,
  so this lemma does not mention \<open>X\<close>: the coupling's witness is the init (@{thm [source] defl_node_wrel_init_refl},
  reflexivity), as in @{thm [source] defl_resolve_count_classify}'s rebuild branch.

  \<^bold>\<open>The \<open>2 \<le> v\<close> case split is the code's own test.\<close> \<open>blr_window_choice_refine_bl\<close>, the contract of the concrete window
  cascade, takes \<open>2 \<le> v\<close>, and at a general guard the cached class does not bound \<open>v\<close>, because a Descartes count does not
  transport from the deflated object to the init. Below the gate the op returns \<open>None\<close> and the arm bisects, which is this
  proof's second case.\<close>

theorem defl_gate_open_gen_invar:
  fixes l_num r_num :: int and k e s cnt g :: nat and rp :: gmp_poly
  defines "P0 \<equiv> (of_int_poly (Poly rp) :: real poly)"
  defines "Xi \<equiv> carried_init_same_den l_num (2 ^ k) r_num rp"
  assumes g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    \<comment> \<open>from @{thm [source] defl_resolve_count_classify}'s last conjunct\<close>
    and cnt4: "cnt < 4"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length Xi \<le> length rp"
    and Xlen3: "3 \<le> length Xi"
    \<comment> \<open>word bounds, all as in the \<open>gex\<close> arm but read off the INIT\<close>
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_b2: "length Xi + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length Xi < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length Xi - 1) < max_snat LENGTH(gmp_poly_len)"
    and vcap1: "int (carried_descartes_count Xi) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count Xi < max_snat LENGTH(gmp_poly_len)"
    and gcap_lock: "4398046511104 + carried_descartes_count Xi + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates P0 (al, ar, ak)"
    and cov: "defl_dispatch_covers P0 lo (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
  shows "defl_gate_open_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s cnt g Q
       \<le> SPEC (defl_loop_invar P0 lo)"
proof -
  have X_b1: "length Xi + 1 < max_snat LENGTH(gmp_poly_len)" using X_b2 by simp
  \<comment> \<open>\<open>linarith\<close>, not \<open>simp\<close>: \<open>0 < length xs\<close> is rewritten by simp to \<open>xs \<noteq> []\<close>, which then no longer follows from an
     arithmetic bound.\<close>
  have X_ne0: "0 < length Xi" using Xlen3 by linarith
  have X_ne1: "1 < length Xi" using Xlen3 by linarith
  have qlen1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have elen1: "length es + 1 < max_snat LENGTH(gmp_poly_len)" using ecapl by simp
  have slen1: "length ss + 1 < max_snat LENGTH(gmp_poly_len)" using sscap by simp
  have clen1: "length cs + 1 < max_snat LENGTH(gmp_poly_len)" using ccap by simp
  have glen1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  \<comment> \<open>\<^bold>\<open>the escalate REBUILDS here\<close>, which is the whole difference from the \<open>gex\<close> arm\<close>
  have esc: "hybrid_cond_escalate_monadic rp l_num r_num k Q g
           \<le> SPEC (\<lambda>(qx, rpx). qx = Xi \<and> rpx = rp)"
    unfolding Xi_def by (rule hybrid_cond_escalate_trunc[OF g0 glt refl rpne rpb krp])
  \<comment> \<open>and the coupling's witness moves with it: the init stands in the node relation to
     ITSELF, so no fact about the deflated object is needed downstream\<close>
  have wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) Xi"
    unfolding Xi_def by (rule defl_node_wrel_init_refl[OF rpnz lr])
  have vex: "hybrid_window_v_monadic cnt g Xi
           \<le> SPEC (\<lambda>v. v = carried_descartes_count Xi)"
    by (rule defl_window_v_exact_gen[OF cnt4 _ X_b1]) (use glt in simp)
  \<comment> \<open>\<^bold>\<open>the reject sub-arm's guard-shaped premises, at \<open>glock\<close>\<close> --- identical to the \<open>gex\<close>
     arm's, with the init in place of \<open>X\<close>\<close>
  have fX: "node_frame Xi Xi (4398046511104 + carried_descartes_count Xi)"
    by (rule node_frame_exact_any_g)
  have lkX: "4398046511104 \<le> 4398046511104 + carried_descartes_count Xi \<longrightarrow> Xi = Xi" by simp
  have gexX: "4398046511104 + carried_descartes_count Xi = 0
              \<or> 4398046511104 \<le> 4398046511104 + carried_descartes_count Xi" by simp
  have gcap_lk: "max (4398046511104 + carried_descartes_count Xi) 4398046511104 + length rp
                   < max_snat LENGTH(gmp_poly_len)"
    using gcap_lock by simp
  \<comment> \<open>\<^bold>\<open>The reject instance's own payload atom.\<close> It is the lock guard with payload \<open>2\<^sup>4\<^sup>2 + count Xi\<close>, so the payload holds
     by construction, and the ceiling is the Descartes count's length bound against \<open>lenXrp\<close>.\<close>
  have payX: "4398046511106 \<le> 4398046511104 + carried_descartes_count Xi
                \<longrightarrow> carried_descartes_count Xi
                      \<le> 4398046511104 + carried_descartes_count Xi - 4398046511104"
    by simp
  have ceilX: "4398046511104 + carried_descartes_count Xi \<le> 4398046511104 + length rp"
    using carried_descartes_count_le_length_cn[of "Xi"] lenXrp by simp
  \<comment> \<open>\<^bold>\<open>The reject arm, stated once and used twice\<close>: it is reached when the window choice returns \<open>None\<close>, and when the
     \<open>2 \<le> v\<close> gate declines to run the choice. Both reach the same call at the same guard, so naming the instance avoids
     repeating a long \<open>OF\<close> list and keeps the two branches identical.\<close>
  \<comment> \<open>\<^bold>\<open>This arm runs on the node's init\<close>: the general guard rebuilds, which is why the theorem is stated at \<open>Xi\<close> and
     does not mention a deflated \<open>X\<close>. So its divisibility is reflexivity; a \<open>dvdX\<close> premise here would be about a variable the
     statement does not otherwise constrain.\<close>
  have dvdXi: "(of_int_poly (Poly Xi) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
    unfolding Xi_def by (rule dvd_refl)
  have rej: "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
                 l_num r_num k e s (4398046511104 + carried_descartes_count Xi) Xi
           \<le> SPEC (defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo)"
    by (rule defl_branch_split_exact_invar[OF fX lkX gexX payX ceilX gcap_lk Xlen3 X_b1
              lenXrp wrel rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecapl
              sscap ccap push2 scap1 coup iso[unfolded P0_def] cov[unfolded P0_def]
              l1 l2 lal lak dvdXi])
  show ?thesis
    unfolding defl_gate_open_monadic_def PR_CONST_def P0_def
    using rpne rpb krp X_ne1 X_b2 ecap ecap3 ecap2 kcap2 gate4
    apply (refine_vcg esc[THEN order_trans])
    apply (all \<open>((clarsimp; fail) | (linarith; fail))?\<close>)
    apply clarsimp
    apply (refine_vcg vex[THEN order_trans])
    apply (all \<open>((clarsimp, insert vcap1 vcap2, simp); fail)?\<close>)
    apply clarsimp
    apply (refine_vcg blr_window_choice_refine_bl[OF X_ne0 X_b1 gate4 X_ne1 ecap2 X_b2
                        vcap1 _ order_refl, THEN order_trans])
    \<comment> \<open>REJECT: the window choice ran and declined\<close>
    apply (rule rej)
    \<comment> \<open>ACCEPT\<close>
    apply (all \<open>((insert push1 qlen1 elen1 slen1 clen1 glen1 vcap2, simp); fail)?\<close>)
    apply (rule order_trans[OF defl_gate_open_accept_invar[OF ecap ecap2 kcap2 ecap3 push1
                 kslen qlen1 elen1 slen1 wrel rpnz lr lenXrp X_ne0 _ refl _
                 coup iso[unfolded P0_def] cov[unfolded P0_def] l1 l2 dvdXi]])
      apply auto
    \<comment> \<open>and the arm BELOW the gate: the choice never ran, \<open>wc = None\<close> by construction, so the
       same reject instance closes it\<close>
    apply (rule rej)
    done
qed


section \<open>The two \<open>safe'\<close> lemmas, with the child length premise weakened\<close>

text \<open>\<^bold>\<open>The assumption of the non-deflating \<open>safe'\<close> lemmas that fails on this stack.\<close>
  @{thm [source] hybrid_loop_safe_invar_push2_all} and its one-child counterpart take \<open>length qr = length rp\<close>, true there
  because every child holds its parent's init; a deflated child is one shorter. The equation is used only for three
  consequences, \<open>qr \<noteq> []\<close>, \<open>0 < length qr\<close> and \<open>length qr + 1 < max_snat\<close>, all of which follow from \<open>0 < length qr\<close> and
  \<open>length qr \<le> length rp\<close>, the pair @{const defl_node_ok} carries for every node. So the loop body reads them off the coupling
  at the pushed slot.\<close>

lemma defl_loop_safe_invar_push2_all:
  assumes stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and budinv: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and capinv': "hybrid_cap_invar \<delta> l0 r0 k0
                    (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [j1, j2])
                    (butlast ss @ [sv1, sv2])"
    \<comment> \<open>\<^bold>\<open>Weakened from \<open>length qr = length rp\<close>\<close>: a deflated child is one shorter than its parent's init, and the equation
       was used only for non-emptiness and the word cap, which follow from the two bounds @{const defl_node_ok} carries.\<close>
    and qpos: "0 < length qr" and qle: "length qr \<le> length rp"
    \<comment> \<open>\<^bold>\<open>The accumulator may have GROWN by the midpoint root\<close> -- the split and window arms
       both branch on it, and \<open>\<le> \<dots> + 1\<close> covers the unchanged branch too, so one shape serves
       both. The extra slot is paid by @{thm [source] hybrid_budget_invar_acc_grown}.\<close>
    and accg: "length al' \<le> length al + 1"
    and accinv: "dyadic_interval_vec_invar (al', ar', ak')"
    and dpos: "0 < \<delta>"
    and rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_loop_safe_invar
           (((butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [j1, j2]),
             butlast qtodo @ [ql, qr], butlast es @ [e1, e2],
             butlast ss @ [sv1, sv2], butlast cs @ [c1, c2], butlast gs @ [g1, g2], rp),
            (al', ar', ak'))"
proof -
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have lne: "lns \<noteq> []" using pre unfolding hybrid_loop_step_pre_def by simp
  have tcap: "length lns + 2 < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_budget_invar_todo_cap[OF budinv])
  \<comment> \<open>the accumulator's own cap, for the branch that grew it. \<open>ar'\<close>/\<open>ak'\<close> ride on \<open>al'\<close>
     through \<open>accinv\<close>, which is why the three columns need only ONE length premise.\<close>
  have acap: "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
    by (rule defl_budget_invar_acc_grown[OF budinv lne VL(1) VL(2)])
  have apush: "dyadic_interval_vec_pushable (al', ar', ak')"
    using acap accg accinv
    unfolding dyadic_interval_vec_pushable_def dyadic_interval_vec_invar_def by simp
  \<comment> \<open>the two column-VALUE facts at the index that IS last after the push. \<^bold>\<open>Stated at
     \<open>Suc (length ks - Suc 0)\<close>, the form \<open>simp\<close> PRODUCES\<close>, not at the \<open>length (butlast ks) + 1\<close>
     the push writes: instantiated the other way the \<open>nth\<close> rewrite stops firing on the cited
     fact -- this file's iron rule, paid for again here.\<close>
  have kidx: "Suc (length ks - Suc 0) < length (butlast ks @ [j1, j2])" by simp
  have knth: "(butlast ks @ [j1, j2]) ! Suc (length ks - Suc 0) = j2"
    by (simp add: nth_append)
  have sidx: "Suc (length ks - Suc 0) < length (butlast ss @ [sv1, sv2])"
    using SL VL by simp
  have snth: "(butlast ss @ [sv1, sv2]) ! Suc (length ks - Suc 0) = sv2"
    using SL VL by (simp add: nth_append)
  have kb1: "int j2 + 1 \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_depth_succ_le[OF capinv' kidx dpos] by (simp add: knth)
  have kb2: "int j2 \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_depth_le[OF capinv' kidx] by (simp add: knth)
  have sb: "sv2 \<le> j2"
    using hybrid_cap_invar_sigma_nth[OF capinv' sidx] by (simp add: knth snth)
  have kbn: "j2 + 1 < max_snat LENGTH(gmp_poly_len)" using kb1 kcap by linarith
  have kbp: "j2 * (length rp - 1) < max_snat LENGTH(gmp_poly_len)" by (rule kdepth[OF kb2])
  have sbn: "sv2 + 1 < max_snat LENGTH(gmp_poly_len)" using sb kbn by simp
  \<comment> \<open>\<open>Qne\<close> goes in the \<open>add:\<close> list, not the \<open>use\<close> list.\<close>
  have Qne2: "0 < length qr" by (rule qpos)
  have Qne: "qr \<noteq> []" using qpos length_greater_0_conv[of "qr"] by blast
  have Qcap: "length qr + 1 < max_snat LENGTH(gmp_poly_len)" using qle rp_bound by simp
  note Pu = pre[unfolded hybrid_loop_step_pre_def]
  show ?thesis
    unfolding hybrid_loop_safe_invar_def hybrid_loop_step_pre_def
  proof (intro conjI impI)
    show "hybrid_loop_state_invar
            (((butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [j1, j2]),
              butlast qtodo @ [ql, qr], butlast es @ [e1, e2],
              butlast ss @ [sv1, sv2], butlast cs @ [c1, c2], butlast gs @ [g1, g2], rp),
             (al', ar', ak'))"
      using stinv accinv
      by (auto simp: hybrid_loop_state_invar_def dyadic_interval_vec_invar_def Let_def)
  qed (use Pu tcap VL SL kbn kbp sbn Qcap rp_len rp_bound apush in
         \<open>simp_all add: dyadic_interval_vec_pushable2_def dyadic_interval_vec_pushable_def
                        Qne Qne2\<close>)
qed

lemma defl_loop_safe_invar_push1_all:
  assumes stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and capinv': "hybrid_cap_invar \<delta> l0 r0 k0
                    (butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [j1])
                    (butlast ss @ [sv1])"
    \<comment> \<open>\<^bold>\<open>Weakened\<close>, as in the two-child lemma.\<close>
    and qpos: "0 < length q1" and qle: "length q1 \<le> length rp"
    and dpos: "0 < \<delta>"
    and rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_loop_safe_invar
           (((butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [j1]),
             butlast qtodo @ [q1], butlast es @ [e1],
             butlast ss @ [sv1], butlast cs @ [c1], butlast gs @ [g1], rp), acc)"
proof -
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have kidx: "length ks - Suc 0 < length (butlast ks @ [j1])" by simp
  have knth: "(butlast ks @ [j1]) ! (length ks - Suc 0) = j1"
    by (simp add: nth_append)
  have sidx: "length ks - Suc 0 < length (butlast ss @ [sv1])"
    using SL VL by simp
  have snth: "(butlast ss @ [sv1]) ! (length ks - Suc 0) = sv1"
    using SL VL by (simp add: nth_append)
  have kb1: "int j1 + 1 \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_depth_succ_le[OF capinv' kidx dpos] by (simp add: knth)
  have kb2: "int j1 \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_depth_le[OF capinv' kidx] by (simp add: knth)
  have sb: "sv1 \<le> j1"
    using hybrid_cap_invar_sigma_nth[OF capinv' sidx] by (simp add: knth snth)
  have kbn: "j1 + 1 < max_snat LENGTH(gmp_poly_len)" using kb1 kcap by linarith
  have kbp: "j1 * (length rp - 1) < max_snat LENGTH(gmp_poly_len)" by (rule kdepth[OF kb2])
  have sbn: "sv1 + 1 < max_snat LENGTH(gmp_poly_len)" using sb kbn by simp
  have Qne2: "0 < length q1" by (rule qpos)
  have Qne: "q1 \<noteq> []" using qpos length_greater_0_conv[of "q1"] by blast
  have Qcap: "length q1 + 1 < max_snat LENGTH(gmp_poly_len)" using qle rp_bound by simp
  \<comment> \<open>\<^bold>\<open>\<open>lfix\<close> is what makes the column caps MATCH.\<close> The one-child push leaves the vector the
     same length, so \<open>step_pre\<close>'s own cap already covers it -- but the goal normalises to
     \<open>Suc (length lns)\<close> while the hypothesis stays at \<open>Suc (Suc (length lns - Suc 0))\<close>, and
     \<open>lns \<noteq> []\<close> sits inside a premise CONJUNCTION where \<open>simp\<close> will not mine it. As a simp rule
     \<open>lfix\<close> rewrites both sides to the same form.\<close>
  have lne: "lns \<noteq> []" using pre unfolding hybrid_loop_step_pre_def by simp
  have lfix: "Suc (length lns - Suc 0) = length lns" using lne by simp
  note Pu = pre[unfolded hybrid_loop_step_pre_def]
  show ?thesis
    unfolding hybrid_loop_safe_invar_def hybrid_loop_step_pre_def
  proof (intro conjI impI)
    show "hybrid_loop_state_invar
            (((butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [j1]),
              butlast qtodo @ [q1], butlast es @ [e1],
              butlast ss @ [sv1], butlast cs @ [c1], butlast gs @ [g1], rp), acc)"
      using stinv
      by (auto simp: hybrid_loop_state_invar_def dyadic_interval_vec_invar_def Let_def)
  qed (use Pu VL SL kbn kbp sbn Qcap rp_len rp_bound in
         \<open>simp_all add: dyadic_interval_vec_pushable2_def dyadic_interval_vec_pushable_def
                        lfix Qne Qne2\<close>)
qed

section \<open>The split arm's full column shape\<close>

text \<open>\<^bold>\<open>Why the existing state lemmas are not enough.\<close>
  @{thm [source] defl_branch_split_exact_state} pins only \<open>fst wl\<close> --- the interval columns ---
  because the coupling and the two payload clauses were all it had to feed. The body step needs
  more: @{const hybrid_cap_invar} reads \<open>ss\<close>, \<open>safe'\<close> reads the pushed polynomial's slot, and
  @{const hybrid_state_mu} reads the node columns. So the same chain is run once more with the
  full column conclusion, exactly as @{thm [source] hybrid_loop_step_args_split} states it on
  the classic side --- and \<open>sv \<le> s + 1\<close> comes free from
  @{thm [source] hybrid_split_run_len_le}.\<close>

lemma defl_split_tail_cols:
  assumes frameL: "node_frame XL ql gl" and frameR: "node_frame XR qr gr"
    and lockL: "4398046511104 \<le> gl \<longrightarrow> ql = XL"
    and lockR: "4398046511104 \<le> gr \<longrightarrow> qr = XR"
    and lenL: "length ql \<le> length rp" and lenR: "length qr \<le> length rp"
    \<comment> \<open>\<^bold>\<open>A direct word bound, NOT \<open>gl \<le> 2\<^sup>4\<^sup>2\<close>.\<close> The gate-open arm calls the split at the
       LOCK-WITH-PAYLOAD guard \<open>2\<^sup>4\<^sup>2 + v\<close>, which is strictly ABOVE \<open>2\<^sup>4\<^sup>2\<close> -- so a premise
       capping the child guard at the literal makes this lemma inapplicable there (the classic
       side hits the same thing and carries \<open>gcap_rp\<close>/\<open>gcap_lock\<close> as two separate instances).
       Bounding \<open>gl + length rp\<close> instead covers both call sites, and it is what
       @{thm [source] hybrid_split_pair_state_correct} actually needs.\<close>
    and glb: "gl + length rp < max_snat LENGTH(gmp_poly_len)"
    and grb: "gr + length rp < max_snat LENGTH(gmp_poly_len)"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kcap: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_split_pair_state_monadic (lns, rns, ks) qtodo es ss cs gs rp
             l_num r_num k e s mid ql gl qr gr
    \<comment> \<open>\<^bold>\<open>Stated with \<open>fst\<close>, not a 7-tuple PATTERN.\<close> The consumer's goal is \<open>fst wl = \<dots>\<close> after
       \<open>RETURN (wl, acc)\<close>; a \<open>case_prod\<close> postcondition has to be destructured before it can be
       used there, and the \<open>refine_vcg\<close> chain leaves the state only PARTLY split (\<open>x x1 x2\<close>),
       so the two never meet. Same shape as the \<open>gbind_decomp\<close> lesson: extensionally equal,
       different TERM.\<close>
       \<le> SPEC (\<lambda>st. case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
             todo' = (lns @ [2 * l_num, l_num + r_num],
                      rns @ [l_num + r_num, 2 * r_num], ks @ [Suc k, Suc k])
           \<and> rp' = rp
           \<and> (\<exists>ql' qr' cl cr gl' gr' sv.
                qtodo' = qtodo @ [ql', qr']
              \<and> es' = es @ [newton_child_exp e, newton_child_exp e]
              \<and> ss' = ss @ [sv, sv] \<and> cs' = cs @ [cl, cr] \<and> gs' = gs @ [gl', gr']
              \<and> sv \<le> s + 1))"
proof -
  have lXL: "length XL = length ql" by (rule cdlr_node_frame_len[OF frameL])
  have lXR: "length XR = length qr" by (rule cdlr_node_frame_len[OF frameR])
  have leL: "length XL \<le> length rp" using lXL lenL by simp
  have leR: "length XR \<le> length rp" using lXR lenR by simp
  have lbL: "length XL + 1 < max_snat LENGTH(gmp_poly_len)" using leL rpb by simp
  have lbR: "length XR + 1 < max_snat LENGTH(gmp_poly_len)" using leR rpb by simp
  have pbL: "length XL * nat_bitlen (length XL) < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_pb_mono[OF leL rp_pb])
  have pbR: "length XR * nat_bitlen (length XR) < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_pb_mono[OF leR rp_pb])
  have gbL: "gl + length XL < max_snat LENGTH(gmp_poly_len)" using glb leL by simp
  have gbR: "gr + length XR < max_snat LENGTH(gmp_poly_len)" using grb leR by simp
  have lockL': "4398046511104 \<le> gl \<longrightarrow> XL = ql" using lockL by simp
  have lockR': "4398046511104 \<le> gr \<longrightarrow> XR = qr" using lockR by simp
  show ?thesis
    by (rule order_trans[OF hybrid_split_pair_state_correct[where XL = XL and XR = XR,
        OF frameL frameR lockL' lockR' lbL lbR pbL pbR gbL gbR
           qcap gcap ecap sscap ccap push kcap scap1]])
       (use hybrid_split_run_len_le in auto)
qed

text \<open>\<^bold>\<open>The split arm's column outcome, as a named predicate\<close>: two children pushed, or (the right child proved empty)
  the left child alone. The clause is carried by both split arms, the reject halves of both gate-open arms and the two
  arm-shape bridges; as an opaque atom it passes through them unchanged, and only its producers (the two tails, below) and
  consumers (the arm-shape bridges) unfold it, as with the keystone's @{const hybrid_split_wl}.\<close>

definition defl_split_cols ::
  "int list \<Rightarrow> int list \<Rightarrow> nat list \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
     nat list \<Rightarrow> nat list \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
     hybrid_worklist \<Rightarrow> bool" where
  "defl_split_cols lns rns ks qtodo es ss cs gs rp l_num r_num k e s st \<longleftrightarrow>
     (case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow> rp' = rp \<and>
        ((todo' = (lns @ [2 * l_num, l_num + r_num],
                   rns @ [l_num + r_num, 2 * r_num], ks @ [Suc k, Suc k])
          \<and> (\<exists>ql' qr' cl cr gl' gr' sv.
                qtodo' = qtodo @ [ql', qr']
              \<and> es' = es @ [newton_child_exp e, newton_child_exp e]
              \<and> ss' = ss @ [sv, sv] \<and> cs' = cs @ [cl, cr] \<and> gs' = gs @ [gl', gr']
              \<and> sv \<le> s + 1))
         \<or> (todo' = (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [Suc k])
          \<and> (\<exists>ql' cl gl' sv.
                qtodo' = qtodo @ [ql'] \<and> es' = es @ [newton_child_exp e]
              \<and> ss' = ss @ [sv] \<and> cs' = cs @ [cl] \<and> gs' = gs @ [gl']
              \<and> sv \<le> s + 1))))"

text \<open>\<^bold>\<open>The one-child tail's columns\<close>: the counterpart of @{thm [source] defl_split_tail_cols} through
  @{thm [source] hybrid_split_pair_state_left_correct}; \<open>sv \<le> s + 1\<close> is again @{thm [source] hybrid_split_run_len_le}.\<close>

lemma defl_split_tail_cols_left:
  assumes frameL: "node_frame XL ql gl"
    and lockL: "4398046511104 \<le> gl \<longrightarrow> ql = XL"
    and lenL: "length ql \<le> length rp"
    and glb: "gl + length rp < max_snat LENGTH(gmp_poly_len)"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kcap: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_split_pair_state_left_monadic (lns, rns, ks) qtodo es ss cs gs rp
             l_num r_num k e s mid ql gl
       \<le> SPEC (\<lambda>st. case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
             todo' = (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [Suc k])
           \<and> rp' = rp
           \<and> (\<exists>ql' cl gl' sv.
                qtodo' = qtodo @ [ql'] \<and> es' = es @ [newton_child_exp e]
              \<and> ss' = ss @ [sv] \<and> cs' = cs @ [cl] \<and> gs' = gs @ [gl']
              \<and> sv \<le> s + 1))"
proof -
  have lXL: "length XL = length ql" by (rule cdlr_node_frame_len[OF frameL])
  have leL: "length XL \<le> length rp" using lXL lenL by simp
  have lbL: "length XL + 1 < max_snat LENGTH(gmp_poly_len)" using leL rpb by simp
  have pbL: "length XL * nat_bitlen (length XL) < max_snat LENGTH(gmp_poly_len)"
    by (rule defl_pb_mono[OF leL rp_pb])
  have gbL: "gl + length XL < max_snat LENGTH(gmp_poly_len)" using glb leL by simp
  have lockL': "4398046511104 \<le> gl \<longrightarrow> XL = ql" using lockL by simp
  show ?thesis
    by (rule order_trans[OF hybrid_split_pair_state_left_correct[where XL = XL,
        OF frameL lockL' lbL pbL gbL qcap gcap ecap sscap ccap push kcap scap1]])
       (use hybrid_split_run_len_le in auto)
qed

text \<open>\<^bold>\<open>The two tails into the named outcome\<close>, proved once here in a small context (a blanket
  \<open>auto simp: defl_split_cols_def\<close> over the arm's goals, each carrying the arm's full premise set, is slow), in both the
  introduction form and the \<open>SPEC \<le> SPEC\<close> form \<open>refine_vcg\<close> leaves after a tail's \<open>order_trans\<close>.\<close>

lemma defl_split_colsI2:
  assumes "case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
             todo' = (lns @ [2 * l_num, l_num + r_num],
                      rns @ [l_num + r_num, 2 * r_num], ks @ [Suc k, Suc k])
           \<and> rp' = rp
           \<and> (\<exists>ql' qr' cl cr gl' gr' sv.
                qtodo' = qtodo @ [ql', qr']
              \<and> es' = es @ [newton_child_exp e, newton_child_exp e]
              \<and> ss' = ss @ [sv, sv] \<and> cs' = cs @ [cl, cr] \<and> gs' = gs @ [gl', gr']
              \<and> sv \<le> s + 1)"
  shows "defl_split_cols lns rns ks qtodo es ss cs gs rp l_num r_num k e s st"
  using assms by (cases st) (simp add: defl_split_cols_def)

lemma defl_split_colsI1:
  assumes "case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
             todo' = (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [Suc k])
           \<and> rp' = rp
           \<and> (\<exists>ql' cl gl' sv.
                qtodo' = qtodo @ [ql'] \<and> es' = es @ [newton_child_exp e]
              \<and> ss' = ss @ [sv] \<and> cs' = cs @ [cl] \<and> gs' = gs @ [gl']
              \<and> sv \<le> s + 1)"
  shows "defl_split_cols lns rns ks qtodo es ss cs gs rp l_num r_num k e s st"
  using assms by (cases st) (simp add: defl_split_cols_def)

lemma defl_split_cols_tail2:
  "SPEC (\<lambda>st. case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
             todo' = (lns @ [2 * l_num, l_num + r_num],
                      rns @ [l_num + r_num, 2 * r_num], ks @ [Suc k, Suc k])
           \<and> rp' = rp
           \<and> (\<exists>ql' qr' cl cr gl' gr' sv.
                qtodo' = qtodo @ [ql', qr']
              \<and> es' = es @ [newton_child_exp e, newton_child_exp e]
              \<and> ss' = ss @ [sv, sv] \<and> cs' = cs @ [cl, cr] \<and> gs' = gs @ [gl', gr']
              \<and> sv \<le> s + 1))
     \<le> SPEC (\<lambda>wl'. RETURN (wl', acc)
            \<le> SPEC (\<lambda>(st, acc'). defl_split_cols lns rns ks qtodo es ss cs gs rp l_num r_num k e s st))"
  by (rule SPEC_rule) (auto intro: defl_split_colsI2)

lemma defl_split_cols_tail1:
  "SPEC (\<lambda>st. case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
             todo' = (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [Suc k])
           \<and> rp' = rp
           \<and> (\<exists>ql' cl gl' sv.
                qtodo' = qtodo @ [ql'] \<and> es' = es @ [newton_child_exp e]
              \<and> ss' = ss @ [sv] \<and> cs' = cs @ [cl] \<and> gs' = gs @ [gl']
              \<and> sv \<le> s + 1))
     \<le> SPEC (\<lambda>wl'. RETURN (wl', acc)
            \<le> SPEC (\<lambda>(st, acc'). defl_split_cols lns rns ks qtodo es ss cs gs rp l_num r_num k e s st))"
  by (rule SPEC_rule) (auto intro: defl_split_colsI1)

lemma defl_branch_split_exact_cols:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qlen3: "3 \<le> length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and lenQrp: "length Q \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  \<comment> \<open>the named column outcome: two pushes or left only.\<close>
  shows "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (\<lambda>(st, acc'). defl_split_cols lns rns ks qtodo es ss cs gs rp l_num r_num k e s st)"
proof -
  have Qne: "0 < length Q" using Qlen3 by linarith
  have Qsmall: "length Q < 1099511627776" using lenQrp rp_small by linarith
  have Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)" by (rule small_len_b2[OF Qsmall])
  have dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)" by (rule small_len_dep[OF Qsmall])
  have kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    using gcap_rp lenQrp max.cobounded1[of g 4398046511104] by linarith
  have pm: "carried_push_mid_monadic (al, ar, ak) l_num r_num k
      \<le> SPEC (\<lambda>a. a = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1]))"
    by (simp add: cdlr_push_mid_eq[OF accpush])
  have gl_bound: "x \<le> max g 4398046511104 \<Longrightarrow> x + length rp < max_snat LENGTH(gmp_poly_len)"
    for x using gcap_rp by linarith
  have len_rp: "x \<le> length Q \<Longrightarrow> x \<le> length rp" for x using lenQrp by linarith
  show ?thesis
    unfolding defl_branch_split_monadic_def poly_length_monadic_def PR_CONST_def
    using gex Qlen3 Qne Qbound kcap rpne rpb krp accpush qcap gcap ecap sscap ccap push scap1
    apply (refine_vcg
        defl_split_children_gbind[OF frame lock gex Qlen3 Qbound Qbound2 dep kb]
        defl_split_children_gbind_decomp[OF frame lock gex Qlen3 Qbound Qbound2 dep kb]
        defl_split_tail_cols[THEN order_trans]
        defl_split_tail_cols_left[THEN order_trans]
        pm[THEN order_trans])
    apply (all \<open>(assumption; fail)?\<close>)
    \<comment> \<open>the column pass does not care which exact child the ghost is: \<open>XL := ql\<close> is fine\<close>
    apply (all \<open>((rule node_frame_exact_any_g); fail)?\<close>)
    apply (all \<open>((rule gl_bound, assumption); fail)?\<close>)
    apply (all \<open>((rule len_rp, assumption); fail)?\<close>)
    apply (all \<open>((insert gex Qlen3, simp); fail)?\<close>)
    apply (all \<open>((insert rpb rp_small rp_pb kcap scap1, simp); fail)?\<close>)
    \<comment> \<open>the two tails' postconditions are exactly the two disjuncts of the named outcome\<close>
    apply (all \<open>((simp add: defl_split_cols_def); fail)?\<close>)
    apply (all \<open>((rule defl_split_cols_tail2 | rule defl_split_cols_tail1
                    | (rule defl_split_colsI2, assumption) | (rule defl_split_colsI1, assumption)
                    | (elim Pair_inject, hypsubst, ((rule defl_split_colsI2, assumption) | (rule defl_split_colsI1, assumption)))); fail)?\<close>)
    done
qed

lemma defl_branch_split_gen_cols:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>Last\<close>: passed to @{thm [source] defl_split_children_escalate_gagrees}, whose existentials carry the two
       children's divisibility.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
  \<comment> \<open>the named column outcome: two pushes or left only.\<close>
  shows "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (\<lambda>(st, acc'). defl_split_cols lns rns ks qtodo es ss cs gs rp l_num r_num k e s st)"
proof -
  have pm: "carried_push_mid_monadic (al, ar, ak) l_num r_num k
      \<le> SPEC (\<lambda>a. a = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1]))"
    by (simp add: cdlr_push_mid_eq[OF accpush])
  have notgex: "\<not> ((g = 0 \<or> 4398046511104 \<le> g) \<and> 3 \<le> length Q)" using g0 glt by simp
  have lXQ: "length X = length Q" using cdlr_node_frame_len[OF frame] by simp
  have Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)" by (rule small_len_b2[OF Q_small])
  have dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)" by (rule small_len_dep[OF Q_small])
  have kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    using gcap_rp lenXrp lXQ max.cobounded1[of g 4398046511104] by linarith
  have gl_bound: "x \<le> max g 4398046511104 \<Longrightarrow> x + length rp < max_snat LENGTH(gmp_poly_len)"
    for x using gcap_rp by linarith
  show ?thesis
    unfolding defl_branch_split_monadic_def poly_length_monadic_def PR_CONST_def
    using Qne Qbound kcap rpne rpb krp accpush qcap gcap ecap sscap ccap push scap1
    apply (simp only: nres_monad1)
    apply (refine_vcg
        defl_split_children_escalate_ggbind[OF frame lock g0 glt g_tri g_cpl Qne Qbound
          Q_small refl wrel rpnz lr lenXrp rpne rpb rp_small krp dvdX Qbound2 dep kb]
        defl_split_children_escalate_ggbind_decomp[OF frame lock g0 glt g_tri g_cpl Qne Qbound
          Q_small refl wrel rpnz lr lenXrp rpne rpb rp_small krp dvdX Qbound2 dep kb]
        defl_split_tail_cols[THEN order_trans]
        defl_split_tail_cols_left[THEN order_trans]
        pm[THEN order_trans])
    apply (all \<open>(assumption; fail)?\<close>)
    apply (all \<open>((rule node_frame_exact_any_g); fail)?\<close>)
    apply (all \<open>((rule gl_bound, assumption); fail)?\<close>)
    apply (all \<open>((insert notgex, simp); fail)?\<close>)
    apply (all \<open>((insert rpb rp_small rp_pb kcap scap1, simp); fail)?\<close>)
    apply (all \<open>((simp add: defl_split_cols_def); fail)?\<close>)
    apply (all \<open>((rule defl_split_cols_tail2 | rule defl_split_cols_tail1
                    | (rule defl_split_colsI2, assumption) | (rule defl_split_colsI1, assumption)
                    | (elim Pair_inject, hypsubst, ((rule defl_split_colsI2, assumption) | (rule defl_split_colsI1, assumption)))); fail)?\<close>)
    done
qed

section \<open>The gate-open arm's column shape, in both guard bands\<close>

text \<open>\<^bold>\<open>A DISJUNCTION, because the arm has two outcomes.\<close> The window choice either declines ---
  in which case the arm IS the two-child split at the lock-with-payload guard, and the columns
  are the split arm's --- or it accepts, and the arm pushes ONE child whose box, exponent, cache
  and lock guard are all fixed by @{thm [source] hybrid_gate_open_accept_cols}. This is the
  same shape @{thm [source] hybrid_loop_step_args_window} states on the classic side.\<close>

lemma defl_gate_open_cols:
  fixes l_num r_num :: int and k e s cnt g v :: nat and rp :: gmp_poly
  defines "P0 \<equiv> (of_int_poly (Poly rp) :: real poly)"
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g"
    and frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and cnt2: "2 \<le> cnt"
    and inv: "dyadic_iv_cs_invar cnt (carried_descartes_count X)"
    and count2: "2 \<le> carried_descartes_count X"
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    \<comment> \<open>the node, in the DEFLATING shape: a witness related to the init, not equal to it\<close>
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and Qlen3: "3 \<le> length Q"
    \<comment> \<open>word bounds, all as in the classic arm\<close>
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne1: "1 < length X"
    and X_b2: "length X + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length X < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length X - 1) < max_snat LENGTH(gmp_poly_len)"
    and vcap1: "int (carried_descartes_count X) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count X < max_snat LENGTH(gmp_poly_len)"
    and gcap_lock: "4398046511104 + carried_descartes_count X + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the invariant at the popped state\<close>
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates P0 (al, ar, ak)"
    and cov: "defl_dispatch_covers P0 lo (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
  shows "defl_gate_open_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s cnt g Q
       \<le> SPEC (\<lambda>(st, acc'). defl_split_cols lns rns ks qtodo es ss cs gs rp l_num r_num k e s st
             \<or> (case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
                (\<exists>m cand.
                   newton_window_pick_bail (carried_descartes_count X) e X = Some (m, cand)
                 \<and> carried_descartes_count cand = carried_descartes_count X
                 \<and> todo' = (lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                            rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                            ks @ [k + (2 ^ e + 2)])
                 \<and> qtodo' = qtodo @ [cand] \<and> es' = es @ [e + 1] \<and> ss' = ss @ [s]
                 \<and> cs' = cs @ [carried_descartes_count X + 2]
                 \<and> gs' = gs @ [4398046511104 + carried_descartes_count X]
                 \<and> rp' = rp)))"
proof -
  have X_b1: "length X + 1 < max_snat LENGTH(gmp_poly_len)" using X_b2 by simp
  have X_ne0: "0 < length X" using X_ne1 by simp
  have QX: "Q = X"
  proof (cases "g = 0")
    case True thus ?thesis using frame by (simp add: node_frame_def)
  next
    case False thus ?thesis using gex lock by simp
  qed
  have esc: "hybrid_cond_escalate_monadic rp l_num r_num k Q g
           \<le> SPEC (\<lambda>(qx, rpx). qx = X \<and> rpx = rp)"
    using QX by (simp add: hybrid_cond_escalate_exact[OF gex])
  have fX: "node_frame X X (4398046511104 + carried_descartes_count X)"
    by (rule node_frame_exact_any_g)
  have lkX: "4398046511104 \<le> 4398046511104 + carried_descartes_count X \<longrightarrow> X = X" by simp
  have gexX: "4398046511104 + carried_descartes_count X = 0
              \<or> 4398046511104 \<le> 4398046511104 + carried_descartes_count X" by simp
  have gcap_lk: "max (4398046511104 + carried_descartes_count X) 4398046511104 + length rp
                   < max_snat LENGTH(gmp_poly_len)"
    using gcap_lock by simp
  have Xlen3: "3 \<le> length X" using QX Qlen3 by simp
  have qlen1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have elen1: "length es + 1 < max_snat LENGTH(gmp_poly_len)" using ecapl by simp
  have slen1: "length ss + 1 < max_snat LENGTH(gmp_poly_len)" using sscap by simp
  have clen1: "length cs + 1 < max_snat LENGTH(gmp_poly_len)" using ccap by simp
  have glen1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  show ?thesis
    unfolding defl_gate_open_monadic_def PR_CONST_def
    using rpne rpb krp X_ne1 X_b2 ecap ecap3 ecap2 kcap2 gate4
    apply (refine_vcg esc[THEN order_trans])
    apply (all \<open>((clarsimp; fail) | (linarith; fail))?\<close>)
    apply clarsimp
    apply (refine_vcg hybrid_window_v_exact[OF inv X_b1 pay count2, THEN order_trans])
    apply (all \<open>((clarsimp, insert vcap1 vcap2, simp); fail)?\<close>)
    apply clarsimp
    apply (refine_vcg blr_window_choice_refine_bl[OF X_ne0 X_b1 gate4 X_ne1 ecap2 X_b2
                        vcap1 count2 order_refl, THEN order_trans])
    \<comment> \<open>REJECT --- the LEFT disjunct, the ordinary two-child split shape\<close>
    apply (rule order_trans[OF defl_branch_split_exact_cols[OF fX lkX gexX gcap_lk Xlen3 X_b1
                 lenXrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecapl
                 sscap ccap push2 scap1]])
    apply (rule SPEC_rule)
    \<comment> \<open>\<open>clarsimp\<close> FIRST: the postcondition is a \<open>case\<close> on a bound tuple variable, and
       \<open>blast\<close> cannot see inside one. \<open>;\<close> rather than a second \<open>apply\<close> so that a \<open>clarsimp\<close>
       which happens to close the goal outright does not make the next step fail on
       \<open>no subgoals\<close> --- this file's closer trap.\<close>
    apply (clarsimp; blast)
    \<comment> \<open>ACCEPT\<close>
    apply (all \<open>((insert push1 qlen1 elen1 slen1 clen1 glen1 vcap2, simp); fail)?\<close>)
    \<comment> \<open>\<^bold>\<open>@{thm [source] hybrid_window_push_cols}, not the \<open>_accept_cols\<close> wrapper.\<close> By
       this point \<open>refine_vcg\<close> has already performed both \<open>mop_list_append\<close>s, so the goal is
       about the push op at the ALREADY-appended \<open>cs\<close>/\<open>gs\<close> --- the wrapper, which covers the
       appends too, has nothing to match. Same lesson as
       @{thm [source] defl_gate_open_accept_invar}'s own banner.\<close>
    apply (rule order_trans[OF hybrid_window_push_cols[OF ecap ecap2 kcap2 ecap3 push1
                 kslen qlen1 elen1 slen1]])
    apply (rule SPEC_rule)
    apply auto
    \<comment> \<open>the accepted window PRESERVES the parent's count --- the one goal \<open>auto\<close> leaves\<close>
    apply (all \<open>((rule newton_window_pick_bail_count, assumption) | (drule newton_window_pick_bail_count, simp); fail)?\<close>)
    done
qed


lemma defl_gate_open_gen_cols:
  fixes l_num r_num :: int and k e s cnt g :: nat and rp :: gmp_poly
  defines "P0 \<equiv> (of_int_poly (Poly rp) :: real poly)"
  defines "Xi \<equiv> carried_init_same_den l_num (2 ^ k) r_num rp"
  assumes g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    \<comment> \<open>from @{thm [source] defl_resolve_count_classify}'s last conjunct\<close>
    and cnt4: "cnt < 4"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length Xi \<le> length rp"
    and Xlen3: "3 \<le> length Xi"
    \<comment> \<open>word bounds, all as in the \<open>gex\<close> arm but read off the INIT\<close>
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_b2: "length Xi + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length Xi < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length Xi - 1) < max_snat LENGTH(gmp_poly_len)"
    and vcap1: "int (carried_descartes_count Xi) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count Xi < max_snat LENGTH(gmp_poly_len)"
    and gcap_lock: "4398046511104 + carried_descartes_count Xi + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates P0 (al, ar, ak)"
    and cov: "defl_dispatch_covers P0 lo (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
  shows "defl_gate_open_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s cnt g Q
       \<le> SPEC (\<lambda>(st, acc'). defl_split_cols lns rns ks qtodo es ss cs gs rp l_num r_num k e s st
             \<or> (case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
                (\<exists>m cand.
                   newton_window_pick_bail (carried_descartes_count Xi) e Xi = Some (m, cand)
                 \<and> carried_descartes_count cand = carried_descartes_count Xi
                 \<and> todo' = (lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                            rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                            ks @ [k + (2 ^ e + 2)])
                 \<and> qtodo' = qtodo @ [cand] \<and> es' = es @ [e + 1] \<and> ss' = ss @ [s]
                 \<and> cs' = cs @ [carried_descartes_count Xi + 2]
                 \<and> gs' = gs @ [4398046511104 + carried_descartes_count Xi]
                 \<and> rp' = rp)))"
proof -
  have X_b1: "length Xi + 1 < max_snat LENGTH(gmp_poly_len)" using X_b2 by simp
  have X_ne0: "0 < length Xi" using Xlen3 by linarith
  have X_ne1: "1 < length Xi" using Xlen3 by linarith
  have qlen1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have elen1: "length es + 1 < max_snat LENGTH(gmp_poly_len)" using ecapl by simp
  have slen1: "length ss + 1 < max_snat LENGTH(gmp_poly_len)" using sscap by simp
  have clen1: "length cs + 1 < max_snat LENGTH(gmp_poly_len)" using ccap by simp
  have glen1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  have esc: "hybrid_cond_escalate_monadic rp l_num r_num k Q g
           \<le> SPEC (\<lambda>(qx, rpx). qx = Xi \<and> rpx = rp)"
    unfolding Xi_def by (rule hybrid_cond_escalate_trunc[OF g0 glt refl rpne rpb krp])
  have vex: "hybrid_window_v_monadic cnt g Xi
           \<le> SPEC (\<lambda>v. v = carried_descartes_count Xi)"
    by (rule defl_window_v_exact_gen[OF cnt4 _ X_b1]) (use glt in simp)
  have fX: "node_frame Xi Xi (4398046511104 + carried_descartes_count Xi)"
    by (rule node_frame_exact_any_g)
  have lkX: "4398046511104 \<le> 4398046511104 + carried_descartes_count Xi \<longrightarrow> Xi = Xi" by simp
  have gexX: "4398046511104 + carried_descartes_count Xi = 0
              \<or> 4398046511104 \<le> 4398046511104 + carried_descartes_count Xi" by simp
  have gcap_lk: "max (4398046511104 + carried_descartes_count Xi) 4398046511104 + length rp
                   < max_snat LENGTH(gmp_poly_len)"
    using gcap_lock by simp
  have rej: "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
                 l_num r_num k e s (4398046511104 + carried_descartes_count Xi) Xi
           \<le> SPEC (\<lambda>(st, acc'). defl_split_cols lns rns ks qtodo es ss cs gs rp l_num r_num k e s st
                          \<or> (case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
                             (\<exists>m cand.
                                newton_window_pick_bail (carried_descartes_count Xi) e Xi = Some (m, cand)
                              \<and> carried_descartes_count cand = carried_descartes_count Xi
                              \<and> todo' = (lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                                         rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                                         ks @ [k + (2 ^ e + 2)])
                              \<and> qtodo' = qtodo @ [cand] \<and> es' = es @ [e + 1] \<and> ss' = ss @ [s]
                              \<and> cs' = cs @ [carried_descartes_count Xi + 2]
                              \<and> gs' = gs @ [4398046511104 + carried_descartes_count Xi]
                              \<and> rp' = rp)))"
    apply (rule order_trans[OF defl_branch_split_exact_cols[OF fX lkX gexX gcap_lk Xlen3 X_b1
              lenXrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecapl
              sscap ccap push2 scap1]])
    apply (rule SPEC_rule)
    apply (clarsimp; blast)
    done
  show ?thesis
    unfolding defl_gate_open_monadic_def PR_CONST_def
    using rpne rpb krp X_ne1 X_b2 ecap ecap3 ecap2 kcap2 gate4
    apply (refine_vcg esc[THEN order_trans])
    apply (all \<open>((clarsimp; fail) | (linarith; fail))?\<close>)
    apply clarsimp
    apply (refine_vcg vex[THEN order_trans])
    apply (all \<open>((clarsimp, insert vcap1 vcap2, simp); fail)?\<close>)
    apply clarsimp
    apply (refine_vcg blr_window_choice_refine_bl[OF X_ne0 X_b1 gate4 X_ne1 ecap2 X_b2
                        vcap1 _ order_refl, THEN order_trans])
    \<comment> \<open>REJECT: the window choice ran and declined. \<^bold>\<open>Through \<open>order_trans\<close>, not a
       bare \<open>rule\<close>\<close>: by this point \<open>refine_vcg\<close> has SIMP-NORMALISED the postcondition
       (\<open>Suc s\<close> for \<open>s + 1\<close>, \<open>4 * 2 ^ 2 ^ e\<close> for \<open>2 ^ (2 ^ e + 2)\<close>, and the whole
       \<open>case\<close> into a \<open>\<forall> \<dots> \<longrightarrow>\<close>), so a bare \<open>rule\<close> --- which matches
       syntactically --- fails on a fact that is logically the same statement.\<close>
    apply (rule order_trans[OF rej])
    apply (rule SPEC_rule)
    \<comment> \<open>\<open>clarsimp\<close> FIRST: the postcondition is a \<open>case\<close> on a bound tuple variable, and
       \<open>blast\<close> cannot see inside one. \<open>;\<close> rather than a second \<open>apply\<close> so that a \<open>clarsimp\<close>
       which happens to close the goal outright does not make the next step fail on
       \<open>no subgoals\<close> --- this file's closer trap.\<close>
    apply (clarsimp; blast)
    \<comment> \<open>ACCEPT\<close>
    apply (all \<open>((insert push1 qlen1 elen1 slen1 clen1 glen1 vcap2, simp); fail)?\<close>)
    \<comment> \<open>\<^bold>\<open>@{thm [source] hybrid_window_push_cols}, not the \<open>_accept_cols\<close> wrapper.\<close> By
       this point \<open>refine_vcg\<close> has already performed both \<open>mop_list_append\<close>s, so the goal is
       about the push op at the ALREADY-appended \<open>cs\<close>/\<open>gs\<close> --- the wrapper, which covers the
       appends too, has nothing to match. Same lesson as
       @{thm [source] defl_gate_open_accept_invar}'s own banner.\<close>
    apply (rule order_trans[OF hybrid_window_push_cols[OF ecap ecap2 kcap2 ecap3 push1
                 kslen qlen1 elen1 slen1]])
    apply (rule SPEC_rule)
    apply auto
    \<comment> \<open>the accepted window PRESERVES the parent's count --- the one goal \<open>auto\<close> leaves\<close>
    apply (all \<open>((rule newton_window_pick_bail_count, assumption) | (drule newton_window_pick_bail_count, simp); fail)?\<close>)
    \<comment> \<open>and the arm BELOW the \<open>2 \<le> v\<close> gate: the choice never ran\<close>
    apply (rule order_trans[OF rej])
    apply (rule SPEC_rule)
    \<comment> \<open>\<open>clarsimp\<close> FIRST: the postcondition is a \<open>case\<close> on a bound tuple variable, and
       \<open>blast\<close> cannot see inside one. \<open>;\<close> rather than a second \<open>apply\<close> so that a \<open>clarsimp\<close>
       which happens to close the goal outright does not make the next step fail on
       \<open>no subgoals\<close> --- this file's closer trap.\<close>
    apply (clarsimp; blast)
    done
qed


section \<open>The accumulator shape, which \<open>safe'\<close> and the budget need\<close>

text \<open>\<^bold>\<open>The split arm's full outcome, as a named predicate\<close>: the column outcome with its accumulator. On the two-push
  side \<open>acc\<close> may have grown by the midpoint leaf; on the left-only side it cannot have (the shed did not fire). This is
  \<open>defl_arm_shape\<close>'s two-push and left-only pair without the push witness, which \<open>defl_arm_shape_of_split_cols\<close> adds.\<close>

definition defl_split_shape ::
  "int list \<Rightarrow> int list \<Rightarrow> nat list \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
     nat list \<Rightarrow> nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
     nat \<Rightarrow> nat \<Rightarrow> hybrid_state \<Rightarrow> bool" where
  "defl_split_shape lns rns ks qtodo es ss cs gs acc rp l_num r_num k e s x \<longleftrightarrow>
     (case x of (st, acc') \<Rightarrow>
        defl_split_cols lns rns ks qtodo es ss cs gs rp l_num r_num k e s st
        \<and> (acc' = acc
           \<or> acc' = (case acc of (al, ar, ak) \<Rightarrow>
                        (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [Suc k])))
        \<and> (fst st = (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [Suc k]) \<longrightarrow> acc' = acc))"

lemma defl_branch_split_exact_cols_acc:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qlen3: "3 \<le> length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and lenQrp: "length Q \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  \<comment> \<open>the named outcome; the dispatch step passes it to \<open>defl_arm_shape_of_split_cols\<close>.\<close>
  shows "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (defl_split_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp l_num r_num k e s)"
proof -
  show ?thesis
    apply (rule order_trans[OF defl_SPEC_conj[OF
          defl_branch_split_exact_cols[OF frame lock gex gcap_rp Qlen3 Qbound lenQrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecap sscap ccap push scap1]
          defl_branch_split_exact_state[OF frame lock gex gcap_rp Qlen3 Qbound lenQrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecap sscap ccap push scap1]]])
    apply (rule SPEC_rule)
    \<comment> \<open>unfold ONLY the new atom: the columns stay packed in @{const defl_split_cols}, and the
       accumulator is settled by the one fact that decides it, whether the midpoint is a root\<close>
    apply (clarsimp simp: defl_split_shape_def)
    apply (all \<open>(cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0"; auto)\<close>)
    done
qed

lemma defl_branch_split_gen_cols_acc:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>Last\<close>: passed down to the two no-fire continuation lemmas, which pass it to
       @{thm [source] defl_split_children_escalate_gagrees}.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
  \<comment> \<open>the named outcome, as on the exact arm.\<close>
  shows "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (defl_split_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp l_num r_num k e s)"
proof -
  show ?thesis
    apply (rule order_trans[OF defl_SPEC_conj[OF
          defl_branch_split_gen_cols[OF frame lock g0 glt g_tri g_cpl gcap_rp Qne Qbound Q_small wrel rpnz lr lenXrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecap sscap ccap push scap1 dvdX]
          defl_branch_split_gen_state[OF frame lock g0 glt g_tri g_cpl gcap_rp Qne Qbound Q_small wrel rpnz lr lenXrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecap sscap ccap push scap1 dvdX]]])
    apply (rule SPEC_rule)
    apply (clarsimp simp: defl_split_shape_def)
    apply (all \<open>(cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0"; auto)\<close>)
    done
qed


lemma defl_gate_open_cols_:
  fixes l_num r_num :: int and k e s cnt g v :: nat and rp :: gmp_poly
  defines "P0 \<equiv> (of_int_poly (Poly rp) :: real poly)"
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g"
    and frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and cnt2: "2 \<le> cnt"
    and inv: "dyadic_iv_cs_invar cnt (carried_descartes_count X)"
    and count2: "2 \<le> carried_descartes_count X"
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    \<comment> \<open>the node, in the DEFLATING shape: a witness related to the init, not equal to it\<close>
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and Qlen3: "3 \<le> length Q"
    \<comment> \<open>word bounds, all as in the classic arm\<close>
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne1: "1 < length X"
    and X_b2: "length X + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length X < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length X - 1) < max_snat LENGTH(gmp_poly_len)"
    and vcap1: "int (carried_descartes_count X) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count X < max_snat LENGTH(gmp_poly_len)"
    and gcap_lock: "4398046511104 + carried_descartes_count X + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the invariant at the popped state\<close>
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates P0 (al, ar, ak)"
    and cov: "defl_dispatch_covers P0 lo (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
  shows "defl_gate_open_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s cnt g Q
       \<le> SPEC (\<lambda>(st, acc'). defl_split_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp l_num r_num k e s (st, acc')
             \<or> (case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
                (\<exists>m cand.
                   newton_window_pick_bail (carried_descartes_count X) e X = Some (m, cand)
                 \<and> carried_descartes_count cand = carried_descartes_count X
                 \<and> todo' = (lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                            rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                            ks @ [k + (2 ^ e + 2)])
                 \<and> qtodo' = qtodo @ [cand] \<and> es' = es @ [e + 1] \<and> ss' = ss @ [s]
                 \<and> cs' = cs @ [carried_descartes_count X + 2]
                 \<and> gs' = gs @ [4398046511104 + carried_descartes_count X]
                 \<and> rp' = rp)
            \<and> acc' = (al, ar, ak)))"
proof -
  have X_b1: "length X + 1 < max_snat LENGTH(gmp_poly_len)" using X_b2 by simp
  have X_ne0: "0 < length X" using X_ne1 by simp
  have QX: "Q = X"
  proof (cases "g = 0")
    case True thus ?thesis using frame by (simp add: node_frame_def)
  next
    case False thus ?thesis using gex lock by simp
  qed
  have esc: "hybrid_cond_escalate_monadic rp l_num r_num k Q g
           \<le> SPEC (\<lambda>(qx, rpx). qx = X \<and> rpx = rp)"
    using QX by (simp add: hybrid_cond_escalate_exact[OF gex])
  have fX: "node_frame X X (4398046511104 + carried_descartes_count X)"
    by (rule node_frame_exact_any_g)
  have lkX: "4398046511104 \<le> 4398046511104 + carried_descartes_count X \<longrightarrow> X = X" by simp
  have gexX: "4398046511104 + carried_descartes_count X = 0
              \<or> 4398046511104 \<le> 4398046511104 + carried_descartes_count X" by simp
  have gcap_lk: "max (4398046511104 + carried_descartes_count X) 4398046511104 + length rp
                   < max_snat LENGTH(gmp_poly_len)"
    using gcap_lock by simp
  have Xlen3: "3 \<le> length X" using QX Qlen3 by simp
  have qlen1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have elen1: "length es + 1 < max_snat LENGTH(gmp_poly_len)" using ecapl by simp
  have slen1: "length ss + 1 < max_snat LENGTH(gmp_poly_len)" using sscap by simp
  have clen1: "length cs + 1 < max_snat LENGTH(gmp_poly_len)" using ccap by simp
  have glen1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  show ?thesis
    unfolding defl_gate_open_monadic_def PR_CONST_def
    using rpne rpb krp X_ne1 X_b2 ecap ecap3 ecap2 kcap2 gate4
    apply (refine_vcg esc[THEN order_trans])
    apply (all \<open>((clarsimp; fail) | (linarith; fail))?\<close>)
    apply clarsimp
    apply (refine_vcg hybrid_window_v_exact[OF inv X_b1 pay count2, THEN order_trans])
    apply (all \<open>((clarsimp, insert vcap1 vcap2, simp); fail)?\<close>)
    apply clarsimp
    apply (refine_vcg blr_window_choice_refine_bl[OF X_ne0 X_b1 gate4 X_ne1 ecap2 X_b2
                        vcap1 count2 order_refl, THEN order_trans])
    \<comment> \<open>REJECT --- the LEFT disjunct, the ordinary two-child split shape\<close>
    apply (rule order_trans[OF defl_branch_split_exact_cols_acc[OF fX lkX gexX gcap_lk Xlen3 X_b1
                 lenXrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecapl
                 sscap ccap push2 scap1]])
    apply (rule SPEC_rule)
    \<comment> \<open>\<open>clarsimp\<close> FIRST: the postcondition is a \<open>case\<close> on a bound tuple variable, and
       \<open>blast\<close> cannot see inside one. \<open>;\<close> rather than a second \<open>apply\<close> so that a \<open>clarsimp\<close>
       which happens to close the goal outright does not make the next step fail on
       \<open>no subgoals\<close> --- this file's closer trap.\<close>
    apply (clarsimp; blast)
    \<comment> \<open>ACCEPT\<close>
    apply (all \<open>((insert push1 qlen1 elen1 slen1 clen1 glen1 vcap2, simp); fail)?\<close>)
    \<comment> \<open>\<^bold>\<open>@{thm [source] hybrid_window_push_cols}, not the \<open>_accept_cols\<close> wrapper.\<close> By
       this point \<open>refine_vcg\<close> has already performed both \<open>mop_list_append\<close>s, so the goal is
       about the push op at the ALREADY-appended \<open>cs\<close>/\<open>gs\<close> --- the wrapper, which covers the
       appends too, has nothing to match. Same lesson as
       @{thm [source] defl_gate_open_accept_invar}'s own banner.\<close>
    apply (rule order_trans[OF hybrid_window_push_cols[OF ecap ecap2 kcap2 ecap3 push1
                 kslen qlen1 elen1 slen1]])
    apply (rule SPEC_rule)
    apply auto
    \<comment> \<open>the accepted window PRESERVES the parent's count --- the one goal \<open>auto\<close> leaves\<close>
    apply (all \<open>((rule newton_window_pick_bail_count, assumption) | (drule newton_window_pick_bail_count, simp); fail)?\<close>)
    done
qed


lemma defl_gate_open_gen_cols_:
  fixes l_num r_num :: int and k e s cnt g :: nat and rp :: gmp_poly
  defines "P0 \<equiv> (of_int_poly (Poly rp) :: real poly)"
  defines "Xi \<equiv> carried_init_same_den l_num (2 ^ k) r_num rp"
  assumes g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    \<comment> \<open>from @{thm [source] defl_resolve_count_classify}'s last conjunct\<close>
    and cnt4: "cnt < 4"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length Xi \<le> length rp"
    and Xlen3: "3 \<le> length Xi"
    \<comment> \<open>word bounds, all as in the \<open>gex\<close> arm but read off the INIT\<close>
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_b2: "length Xi + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length Xi < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length Xi - 1) < max_snat LENGTH(gmp_poly_len)"
    and vcap1: "int (carried_descartes_count Xi) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count Xi < max_snat LENGTH(gmp_poly_len)"
    and gcap_lock: "4398046511104 + carried_descartes_count Xi + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates P0 (al, ar, ak)"
    and cov: "defl_dispatch_covers P0 lo (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
  shows "defl_gate_open_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s cnt g Q
       \<le> SPEC (\<lambda>(st, acc'). defl_split_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp l_num r_num k e s (st, acc')
             \<or> (case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
                (\<exists>m cand.
                   newton_window_pick_bail (carried_descartes_count Xi) e Xi = Some (m, cand)
                 \<and> carried_descartes_count cand = carried_descartes_count Xi
                 \<and> todo' = (lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                            rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                            ks @ [k + (2 ^ e + 2)])
                 \<and> qtodo' = qtodo @ [cand] \<and> es' = es @ [e + 1] \<and> ss' = ss @ [s]
                 \<and> cs' = cs @ [carried_descartes_count Xi + 2]
                 \<and> gs' = gs @ [4398046511104 + carried_descartes_count Xi]
                 \<and> rp' = rp)
            \<and> acc' = (al, ar, ak)))"
proof -
  have X_b1: "length Xi + 1 < max_snat LENGTH(gmp_poly_len)" using X_b2 by simp
  have X_ne0: "0 < length Xi" using Xlen3 by linarith
  have X_ne1: "1 < length Xi" using Xlen3 by linarith
  have qlen1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have elen1: "length es + 1 < max_snat LENGTH(gmp_poly_len)" using ecapl by simp
  have slen1: "length ss + 1 < max_snat LENGTH(gmp_poly_len)" using sscap by simp
  have clen1: "length cs + 1 < max_snat LENGTH(gmp_poly_len)" using ccap by simp
  have glen1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  have esc: "hybrid_cond_escalate_monadic rp l_num r_num k Q g
           \<le> SPEC (\<lambda>(qx, rpx). qx = Xi \<and> rpx = rp)"
    unfolding Xi_def by (rule hybrid_cond_escalate_trunc[OF g0 glt refl rpne rpb krp])
  have vex: "hybrid_window_v_monadic cnt g Xi
           \<le> SPEC (\<lambda>v. v = carried_descartes_count Xi)"
    by (rule defl_window_v_exact_gen[OF cnt4 _ X_b1]) (use glt in simp)
  have fX: "node_frame Xi Xi (4398046511104 + carried_descartes_count Xi)"
    by (rule node_frame_exact_any_g)
  have lkX: "4398046511104 \<le> 4398046511104 + carried_descartes_count Xi \<longrightarrow> Xi = Xi" by simp
  have gexX: "4398046511104 + carried_descartes_count Xi = 0
              \<or> 4398046511104 \<le> 4398046511104 + carried_descartes_count Xi" by simp
  have gcap_lk: "max (4398046511104 + carried_descartes_count Xi) 4398046511104 + length rp
                   < max_snat LENGTH(gmp_poly_len)"
    using gcap_lock by simp
  have rej: "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
                 l_num r_num k e s (4398046511104 + carried_descartes_count Xi) Xi
           \<le> SPEC (defl_split_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp l_num r_num k e s)"
    by (rule defl_branch_split_exact_cols_acc[OF fX lkX gexX gcap_lk Xlen3 X_b1
              lenXrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecapl
              sscap ccap push2 scap1])
  show ?thesis
    unfolding defl_gate_open_monadic_def PR_CONST_def
    using rpne rpb krp X_ne1 X_b2 ecap ecap3 ecap2 kcap2 gate4
    apply (refine_vcg esc[THEN order_trans])
    apply (all \<open>((clarsimp; fail) | (linarith; fail))?\<close>)
    apply clarsimp
    apply (refine_vcg vex[THEN order_trans])
    apply (all \<open>((clarsimp, insert vcap1 vcap2, simp); fail)?\<close>)
    apply clarsimp
    apply (refine_vcg blr_window_choice_refine_bl[OF X_ne0 X_b1 gate4 X_ne1 ecap2 X_b2
                        vcap1 _ order_refl, THEN order_trans])
    \<comment> \<open>REJECT: the window choice ran and declined. \<^bold>\<open>Through \<open>order_trans\<close>, not a
       bare \<open>rule\<close>\<close>: by this point \<open>refine_vcg\<close> has SIMP-NORMALISED the postcondition
       (\<open>Suc s\<close> for \<open>s + 1\<close>, \<open>4 * 2 ^ 2 ^ e\<close> for \<open>2 ^ (2 ^ e + 2)\<close>, and the whole
       \<open>case\<close> into a \<open>\<forall> \<dots> \<longrightarrow>\<close>), so a bare \<open>rule\<close> --- which matches
       syntactically --- fails on a fact that is logically the same statement.\<close>
    apply (rule order_trans[OF rej])
    apply (rule SPEC_rule)
    \<comment> \<open>\<open>clarsimp\<close> FIRST: the postcondition is a \<open>case\<close> on a bound tuple variable, and
       \<open>blast\<close> cannot see inside one. \<open>;\<close> rather than a second \<open>apply\<close> so that a \<open>clarsimp\<close>
       which happens to close the goal outright does not make the next step fail on
       \<open>no subgoals\<close> --- this file's closer trap.\<close>
    apply (clarsimp; blast)
    \<comment> \<open>ACCEPT\<close>
    apply (all \<open>((insert push1 qlen1 elen1 slen1 clen1 glen1 vcap2, simp); fail)?\<close>)
    \<comment> \<open>\<^bold>\<open>@{thm [source] hybrid_window_push_cols}, not the \<open>_accept_cols\<close> wrapper.\<close> By
       this point \<open>refine_vcg\<close> has already performed both \<open>mop_list_append\<close>s, so the goal is
       about the push op at the ALREADY-appended \<open>cs\<close>/\<open>gs\<close> --- the wrapper, which covers the
       appends too, has nothing to match. Same lesson as
       @{thm [source] defl_gate_open_accept_invar}'s own banner.\<close>
    apply (rule order_trans[OF hybrid_window_push_cols[OF ecap ecap2 kcap2 ecap3 push1
                 kslen qlen1 elen1 slen1]])
    apply (rule SPEC_rule)
    apply auto
    \<comment> \<open>the accepted window PRESERVES the parent's count --- the one goal \<open>auto\<close> leaves\<close>
    apply (all \<open>((rule newton_window_pick_bail_count, assumption) | (drule newton_window_pick_bail_count, simp); fail)?\<close>)
    \<comment> \<open>and the arm BELOW the \<open>2 \<le> v\<close> gate: the choice never ran\<close>
    apply (rule order_trans[OF rej])
    apply (rule SPEC_rule)
    \<comment> \<open>\<open>clarsimp\<close> FIRST: the postcondition is a \<open>case\<close> on a bound tuple variable, and
       \<open>blast\<close> cannot see inside one. \<open>;\<close> rather than a second \<open>apply\<close> so that a \<open>clarsimp\<close>
       which happens to close the goal outright does not make the next step fail on
       \<open>no subgoals\<close> --- this file's closer trap.\<close>
    apply (clarsimp; blast)
    done
qed


section \<open>One opaque shape for all six arms\<close>

text \<open>\<^bold>\<open>Why this is a definition and not an inline postcondition.\<close> Every arm lemma is applied inside the dispatch's own
  \<open>refine_vcg\<close> chain, after \<open>simp\<close> and \<open>clarsimp\<close> have normalised the goal (\<open>Suc s\<close> for \<open>s + 1\<close>, \<open>4 * 2\<^sup>2\<^sup>^\<^sup>e\<close> for \<open>2\<^sup>(\<^sup>2\<^sup>^\<^sup>e\<^sup>+\<^sup>2\<^sup>)\<close>, a
  7-tuple \<open>case\<close> re-split as \<open>(todo', a)\<close>). Written inline, the arm's fact and the goal would be the same statement in two
  normal forms, which \<open>rule\<close> and \<open>order_refl\<close> do not bridge and \<open>blast\<close>/\<open>force\<close> do not find quickly. An opaque constant has
  no interior for \<open>simp\<close> to normalise, so the goal stays what the arm proves, and its arguments are plain variables. All six
  arms conclude the same predicate, so the dispatch level is a case split without assembling a disjunction.

  \<^bold>\<open>The window disjunct carries the two \<open>m\<close> bounds, not the \<open>pick\<close> fact\<close>: the bounds are what the measure decrease needs,
  and \<open>pick\<close> mentions the node's exact object, which the loop body has no name for.\<close>

section \<open>The push witness, and why the arm shape carries it\<close>

text \<open>\<^bold>\<open>The \<open>wide\<close> premise of \<open>defl_body_step\<close> (\<open>\<delta> < b - a\<close> at the popped node) is derived from the count, and is false
  for a narrow popped node\<close>: a narrow child of a wide parent is pushed, popped and discarded. It is used only inside the push
  joins of that lemma, never in the pop branches, so it is derived from \<open>2 \<le> count\<close> where the node splits.

  \<^bold>\<open>The non-deflating derivation is unavailable here.\<close> It goes \<open>2 \<le> carried_descartes_count Q\<close> \<open>\<rightarrow>\<close>
  @{thm [source] hybrid_count_bridge} (which needs @{const carried_repr_scalar}) \<open>\<rightarrow>\<close> \<open>2 \<le> descartes_list_int a b (coeffs P)\<close> \<open>\<rightarrow>\<close>
  the contrapositive of \<open>small_fast\<close>. A deflated node is not a carried representation of anything (it is a divisor of one),
  and a Descartes count does not transport across @{const defl_node_wrel}. Divisibility is the hypothesis that reaches the
  count, which is why @{const defl_node_ok} carries it.

  \<^bold>\<open>Why an opaque predicate on the arm shape.\<close> The witness is what each push arm knows and the body step cannot
  recover: the arms have the node's divisibility and count, while the body step, above the resolve, sees only the shape.
  Carrying it costs each arm one premise and lets the \<open>\<delta>\<close> derivation be done once.\<close>

definition defl_push_wit :: "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool" where
  "defl_push_wit rp l r k \<longleftrightarrow>
     (\<exists>X. (of_int_poly (Poly X) :: real poly)
             dvd (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)
        \<and> 2 \<le> carried_descartes_count X)"

lemma defl_push_witI:
  assumes dvd: "(of_int_poly (Poly X) :: real poly)
                  dvd (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)"
    and cnt2: "2 \<le> carried_descartes_count X"
  shows "defl_push_wit rp l r k"
  using assms unfolding defl_push_wit_def by blast

lemma defl_push_witE:
  assumes "defl_push_wit rp l r k"
  obtains X where "(of_int_poly (Poly X) :: real poly)
                     dvd (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)"
    and "2 \<le> carried_descartes_count X"
  using assms unfolding defl_push_wit_def by blast

definition defl_arm_shape ::
  "int list \<Rightarrow> int list \<Rightarrow> nat list \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list
     \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly
     \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> hybrid_state \<Rightarrow> bool" where
  "defl_arm_shape lns rns ks qtodo es ss cs gs acc rp l_num r_num k e s st \<longleftrightarrow>
     (case st of ((todo', qtodo', es', ss', cs', gs', rp'), acc') \<Rightarrow> rp' = rp \<and>
        (\<comment> \<open>POP: the reject arm, and the accept arm which also grows \<open>acc\<close>\<close>
         (todo' = (lns, rns, ks) \<and> qtodo' = qtodo \<and> es' = es \<and> ss' = ss
            \<and> cs' = cs \<and> gs' = gs
            \<and> (acc' = acc
               \<or> acc' = (case acc of (al, ar, ak) \<Rightarrow> (al @ [l_num], ar @ [r_num], ak @ [k]))))
         \<or> \<comment> \<open>PUSH2: both split arms, and the gate-open arms' reject half\<close>
         (todo' = (lns @ [2 * l_num, l_num + r_num],
                   rns @ [l_num + r_num, 2 * r_num], ks @ [Suc k, Suc k])
            \<and> (\<exists>ql qr cl cr gl gr sv. qtodo' = qtodo @ [ql, qr]
                 \<and> es' = es @ [newton_child_exp e, newton_child_exp e]
                 \<and> ss' = ss @ [sv, sv] \<and> cs' = cs @ [cl, cr] \<and> gs' = gs @ [gl, gr]
                 \<and> sv \<le> s + 1)
            \<and> (acc' = acc
               \<or> acc' = (case acc of (al, ar, ak) \<Rightarrow>
                            (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [Suc k])))
            \<and> defl_push_wit rp l_num r_num k)
         \<or> \<comment> \<open>PUSH1: the gate-open arms' accept half. \<^bold>\<open>It carries the window CHOICE, not the
              two \<open>m\<close> bounds\<close> --- the bounds follow from it by
              @{thm [source] newton_window_pick_bail_m_nonneg} /
              @{thm [source] newton_window_pick_bail_m_bound}, and deriving them HERE would
              make the bridge out of the column contract a search instead of a \<open>blast\<close>.\<close>
         (\<exists>m cand v QQ. newton_window_pick_bail v e QQ = Some (m, cand)
            \<and> todo' = (lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                       rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                       ks @ [k + (2 ^ e + 2)])
            \<and> qtodo' = qtodo @ [cand] \<and> es' = es @ [e + 1] \<and> ss' = ss @ [s]
            \<and> cs' = cs @ [v + 2] \<and> gs' = gs @ [4398046511104 + v]
            \<and> acc' = acc
            \<and> e \<le> newton_pol_ecap
            \<and> defl_push_wit rp l_num r_num k)
         \<or> \<comment> \<open>\<^bold>\<open>Left only\<close>: the split arms' push of the left child alone. The right child was proved empty and not built, and
              \<open>acc\<close> is unchanged (on \<open>rz\<close> the shed provably did not fire).\<close>
         (todo' = (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [Suc k])
            \<and> (\<exists>ql cl gl sv. qtodo' = qtodo @ [ql] \<and> es' = es @ [newton_child_exp e]
                 \<and> ss' = ss @ [sv] \<and> cs' = cs @ [cl] \<and> gs' = gs @ [gl]
                 \<and> sv \<le> s + 1)
            \<and> acc' = acc
            \<and> defl_push_wit rp l_num r_num k)))"


lemma defl_gate_open_cols_accd:
  fixes l_num r_num :: int and k e s cnt g v :: nat and rp :: gmp_poly
  defines "P0 \<equiv> (of_int_poly (Poly rp) :: real poly)"
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g"
    and frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and cnt2: "2 \<le> cnt"
    and inv: "dyadic_iv_cs_invar cnt (carried_descartes_count X)"
    and count2: "2 \<le> carried_descartes_count X"
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    \<comment> \<open>the node, in the DEFLATING shape: a witness related to the init, not equal to it\<close>
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and Qlen3: "3 \<le> length Q"
    \<comment> \<open>word bounds, all as in the classic arm\<close>
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne1: "1 < length X"
    and X_b2: "length X + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length X < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length X - 1) < max_snat LENGTH(gmp_poly_len)"
    and vcap1: "int (carried_descartes_count X) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count X < max_snat LENGTH(gmp_poly_len)"
    and gcap_lock: "4398046511104 + carried_descartes_count X + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the invariant at the popped state\<close>
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates P0 (al, ar, ak)"
    and cov: "defl_dispatch_covers P0 lo (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
  shows "defl_gate_open_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s cnt g Q
       \<le> SPEC (\<lambda>(st, acc'). defl_split_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp l_num r_num k e s (st, acc')
             \<or> (case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
                (\<exists>m cand.
                   newton_window_pick_bail (carried_descartes_count X) e X = Some (m, cand)
                 \<and> carried_descartes_count cand = carried_descartes_count X
                 \<and> todo' = (lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                            rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                            ks @ [k + (2 ^ e + 2)])
                 \<and> qtodo' = qtodo @ [cand] \<and> es' = es @ [e + 1] \<and> ss' = ss @ [s]
                 \<and> cs' = cs @ [carried_descartes_count X + 2]
                 \<and> gs' = gs @ [4398046511104 + carried_descartes_count X]
                 \<and> rp' = rp)
            \<and> acc' = (al, ar, ak)))"
proof -
  have X_b1: "length X + 1 < max_snat LENGTH(gmp_poly_len)" using X_b2 by simp
  have X_ne0: "0 < length X" using X_ne1 by simp
  have QX: "Q = X"
  proof (cases "g = 0")
    case True thus ?thesis using frame by (simp add: node_frame_def)
  next
    case False thus ?thesis using gex lock by simp
  qed
  have esc: "hybrid_cond_escalate_monadic rp l_num r_num k Q g
           \<le> SPEC (\<lambda>(qx, rpx). qx = X \<and> rpx = rp)"
    using QX by (simp add: hybrid_cond_escalate_exact[OF gex])
  have fX: "node_frame X X (4398046511104 + carried_descartes_count X)"
    by (rule node_frame_exact_any_g)
  have lkX: "4398046511104 \<le> 4398046511104 + carried_descartes_count X \<longrightarrow> X = X" by simp
  have gexX: "4398046511104 + carried_descartes_count X = 0
              \<or> 4398046511104 \<le> 4398046511104 + carried_descartes_count X" by simp
  have gcap_lk: "max (4398046511104 + carried_descartes_count X) 4398046511104 + length rp
                   < max_snat LENGTH(gmp_poly_len)"
    using gcap_lock by simp
  have Xlen3: "3 \<le> length X" using QX Qlen3 by simp
  have qlen1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have elen1: "length es + 1 < max_snat LENGTH(gmp_poly_len)" using ecapl by simp
  have slen1: "length ss + 1 < max_snat LENGTH(gmp_poly_len)" using sscap by simp
  have clen1: "length cs + 1 < max_snat LENGTH(gmp_poly_len)" using ccap by simp
  have glen1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  show ?thesis
    unfolding defl_gate_open_monadic_def PR_CONST_def
    using rpne rpb krp X_ne1 X_b2 ecap ecap3 ecap2 kcap2 gate4
    apply (refine_vcg esc[THEN order_trans])
    apply (all \<open>((clarsimp; fail) | (linarith; fail))?\<close>)
    apply clarsimp
    apply (refine_vcg hybrid_window_v_exact[OF inv X_b1 pay count2, THEN order_trans])
    apply (all \<open>((clarsimp, insert vcap1 vcap2, simp); fail)?\<close>)
    apply clarsimp
    apply (refine_vcg blr_window_choice_refine_bl[OF X_ne0 X_b1 gate4 X_ne1 ecap2 X_b2
                        vcap1 count2 order_refl, THEN order_trans])
    \<comment> \<open>REJECT --- the LEFT disjunct, the ordinary two-child split shape\<close>
    apply (rule order_trans[OF defl_branch_split_exact_cols_acc[OF fX lkX gexX gcap_lk Xlen3 X_b1
                 lenXrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecapl
                 sscap ccap push2 scap1]])
    apply (rule SPEC_rule)
    \<comment> \<open>\<open>clarsimp\<close> FIRST: the postcondition is a \<open>case\<close> on a bound tuple variable, and
       \<open>blast\<close> cannot see inside one. \<open>;\<close> rather than a second \<open>apply\<close> so that a \<open>clarsimp\<close>
       which happens to close the goal outright does not make the next step fail on
       \<open>no subgoals\<close> --- this file's closer trap.\<close>
    apply (clarsimp; blast)
    \<comment> \<open>ACCEPT\<close>
    apply (all \<open>((insert push1 qlen1 elen1 slen1 clen1 glen1 vcap2, simp); fail)?\<close>)
    \<comment> \<open>\<^bold>\<open>@{thm [source] hybrid_window_push_cols}, not the \<open>_accept_cols\<close> wrapper.\<close> By
       this point \<open>refine_vcg\<close> has already performed both \<open>mop_list_append\<close>s, so the goal is
       about the push op at the ALREADY-appended \<open>cs\<close>/\<open>gs\<close> --- the wrapper, which covers the
       appends too, has nothing to match. Same lesson as
       @{thm [source] defl_gate_open_accept_invar}'s own banner.\<close>
    apply (rule order_trans[OF hybrid_window_push_cols[OF ecap ecap2 kcap2 ecap3 push1
                 kslen qlen1 elen1 slen1]])
    apply (rule SPEC_rule)
    apply auto
    \<comment> \<open>the accepted window PRESERVES the parent's count --- the one goal \<open>auto\<close> leaves\<close>
    apply (all \<open>((rule newton_window_pick_bail_count, assumption) | (drule newton_window_pick_bail_count, simp); fail)?\<close>)
    done
qed

lemma defl_gate_open_gen_cols_accd:
  fixes l_num r_num :: int and k e s cnt g :: nat and rp :: gmp_poly
  defines "P0 \<equiv> (of_int_poly (Poly rp) :: real poly)"
  defines "Xi \<equiv> carried_init_same_den l_num (2 ^ k) r_num rp"
  assumes g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    \<comment> \<open>from @{thm [source] defl_resolve_count_classify}'s last conjunct\<close>
    and cnt4: "cnt < 4"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length Xi \<le> length rp"
    and Xlen3: "3 \<le> length Xi"
    \<comment> \<open>word bounds, all as in the \<open>gex\<close> arm but read off the INIT\<close>
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_b2: "length Xi + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length Xi < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length Xi - 1) < max_snat LENGTH(gmp_poly_len)"
    and vcap1: "int (carried_descartes_count Xi) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count Xi < max_snat LENGTH(gmp_poly_len)"
    and gcap_lock: "4398046511104 + carried_descartes_count Xi + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates P0 (al, ar, ak)"
    and cov: "defl_dispatch_covers P0 lo (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
  shows "defl_gate_open_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s cnt g Q
       \<le> SPEC (\<lambda>(st, acc'). defl_split_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp l_num r_num k e s (st, acc')
             \<or> (case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
                (\<exists>m cand.
                   newton_window_pick_bail (carried_descartes_count Xi) e Xi = Some (m, cand)
                 \<and> carried_descartes_count cand = carried_descartes_count Xi
                 \<and> todo' = (lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                            rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                            ks @ [k + (2 ^ e + 2)])
                 \<and> qtodo' = qtodo @ [cand] \<and> es' = es @ [e + 1] \<and> ss' = ss @ [s]
                 \<and> cs' = cs @ [carried_descartes_count Xi + 2]
                 \<and> gs' = gs @ [4398046511104 + carried_descartes_count Xi]
                 \<and> rp' = rp)
            \<and> acc' = (al, ar, ak)))"
proof -
  have X_b1: "length Xi + 1 < max_snat LENGTH(gmp_poly_len)" using X_b2 by simp
  have X_ne0: "0 < length Xi" using Xlen3 by linarith
  have X_ne1: "1 < length Xi" using Xlen3 by linarith
  have qlen1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have elen1: "length es + 1 < max_snat LENGTH(gmp_poly_len)" using ecapl by simp
  have slen1: "length ss + 1 < max_snat LENGTH(gmp_poly_len)" using sscap by simp
  have clen1: "length cs + 1 < max_snat LENGTH(gmp_poly_len)" using ccap by simp
  have glen1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  have esc: "hybrid_cond_escalate_monadic rp l_num r_num k Q g
           \<le> SPEC (\<lambda>(qx, rpx). qx = Xi \<and> rpx = rp)"
    unfolding Xi_def by (rule hybrid_cond_escalate_trunc[OF g0 glt refl rpne rpb krp])
  have vex: "hybrid_window_v_monadic cnt g Xi
           \<le> SPEC (\<lambda>v. v = carried_descartes_count Xi)"
    by (rule defl_window_v_exact_gen[OF cnt4 _ X_b1]) (use glt in simp)
  have fX: "node_frame Xi Xi (4398046511104 + carried_descartes_count Xi)"
    by (rule node_frame_exact_any_g)
  have lkX: "4398046511104 \<le> 4398046511104 + carried_descartes_count Xi \<longrightarrow> Xi = Xi" by simp
  have gexX: "4398046511104 + carried_descartes_count Xi = 0
              \<or> 4398046511104 \<le> 4398046511104 + carried_descartes_count Xi" by simp
  have gcap_lk: "max (4398046511104 + carried_descartes_count Xi) 4398046511104 + length rp
                   < max_snat LENGTH(gmp_poly_len)"
    using gcap_lock by simp
  have rej: "defl_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
                 l_num r_num k e s (4398046511104 + carried_descartes_count Xi) Xi
           \<le> SPEC (defl_split_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp l_num r_num k e s)"
    by (rule defl_branch_split_exact_cols_acc[OF fX lkX gexX gcap_lk Xlen3 X_b1
              lenXrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecapl
              sscap ccap push2 scap1])
  show ?thesis
    unfolding defl_gate_open_monadic_def PR_CONST_def
    using rpne rpb krp X_ne1 X_b2 ecap ecap3 ecap2 kcap2 gate4
    apply (refine_vcg esc[THEN order_trans])
    apply (all \<open>((clarsimp; fail) | (linarith; fail))?\<close>)
    apply clarsimp
    apply (refine_vcg vex[THEN order_trans])
    apply (all \<open>((clarsimp, insert vcap1 vcap2, simp); fail)?\<close>)
    apply clarsimp
    apply (refine_vcg blr_window_choice_refine_bl[OF X_ne0 X_b1 gate4 X_ne1 ecap2 X_b2
                        vcap1 _ order_refl, THEN order_trans])
    \<comment> \<open>REJECT: the window choice ran and declined. \<^bold>\<open>Through \<open>order_trans\<close>, not a
       bare \<open>rule\<close>\<close>: by this point \<open>refine_vcg\<close> has SIMP-NORMALISED the postcondition
       (\<open>Suc s\<close> for \<open>s + 1\<close>, \<open>4 * 2 ^ 2 ^ e\<close> for \<open>2 ^ (2 ^ e + 2)\<close>, and the whole
       \<open>case\<close> into a \<open>\<forall> \<dots> \<longrightarrow>\<close>), so a bare \<open>rule\<close> --- which matches
       syntactically --- fails on a fact that is logically the same statement.\<close>
    apply (rule order_trans[OF rej])
    apply (rule SPEC_rule)
    \<comment> \<open>\<open>clarsimp\<close> FIRST: the postcondition is a \<open>case\<close> on a bound tuple variable, and
       \<open>blast\<close> cannot see inside one. \<open>;\<close> rather than a second \<open>apply\<close> so that a \<open>clarsimp\<close>
       which happens to close the goal outright does not make the next step fail on
       \<open>no subgoals\<close> --- this file's closer trap.\<close>
    apply (clarsimp; blast)
    \<comment> \<open>ACCEPT\<close>
    apply (all \<open>((insert push1 qlen1 elen1 slen1 clen1 glen1 vcap2, simp); fail)?\<close>)
    \<comment> \<open>\<^bold>\<open>@{thm [source] hybrid_window_push_cols}, not the \<open>_accept_cols\<close> wrapper.\<close> By
       this point \<open>refine_vcg\<close> has already performed both \<open>mop_list_append\<close>s, so the goal is
       about the push op at the ALREADY-appended \<open>cs\<close>/\<open>gs\<close> --- the wrapper, which covers the
       appends too, has nothing to match. Same lesson as
       @{thm [source] defl_gate_open_accept_invar}'s own banner.\<close>
    apply (rule order_trans[OF hybrid_window_push_cols[OF ecap ecap2 kcap2 ecap3 push1
                 kslen qlen1 elen1 slen1]])
    apply (rule SPEC_rule)
    apply auto
    \<comment> \<open>the accepted window PRESERVES the parent's count --- the one goal \<open>auto\<close> leaves\<close>
    apply (all \<open>((rule newton_window_pick_bail_count, assumption) | (drule newton_window_pick_bail_count, simp); fail)?\<close>)
    \<comment> \<open>and the arm BELOW the \<open>2 \<le> v\<close> gate: the choice never ran\<close>
    apply (rule order_trans[OF rej])
    apply (rule SPEC_rule)
    \<comment> \<open>\<open>clarsimp\<close> FIRST: the postcondition is a \<open>case\<close> on a bound tuple variable, and
       \<open>blast\<close> cannot see inside one. \<open>;\<close> rather than a second \<open>apply\<close> so that a \<open>clarsimp\<close>
       which happens to close the goal outright does not make the next step fail on
       \<open>no subgoals\<close> --- this file's closer trap.\<close>
    apply (clarsimp; blast)
    done
qed

text \<open>\<^bold>\<open>Three small BRIDGES, so no closer ever searches the whole postcondition.\<close> Each takes
  one arm's column contract at a state and produces @{const defl_arm_shape} there; the disjunct
  choice happens here, on a goal small enough for \<open>blast\<close> to see, and the arm proofs are then
  \<open>rule\<close> plus \<open>assumption\<close>. Unfolding @{thm [source] defl_arm_shape_def} inside the ARM instead
  would put the three-way disjunction and the column disjunction in front of one search.\<close>

lemma defl_arm_shape_of_split_cols:
  assumes "defl_split_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp l_num r_num k e s x"
    \<comment> \<open>passed to the arm shape's push disjuncts, where \<open>defl_body_step\<close> opens it to derive \<open>wide\<close>; the arms do not look
       inside it.\<close>
    and wit: "defl_push_wit rp l_num r_num k"
  shows "defl_arm_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp l_num r_num k e s x"
  using assms unfolding defl_arm_shape_def defl_split_shape_def defl_split_cols_def
  by (cases x) (clarsimp; blast)

lemma defl_arm_shape_of_window_cols:
  fixes XX :: gmp_poly
  assumes "(\<lambda>(st, acc'). defl_split_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp l_num r_num k e s (st, acc')
             \<or> (case st of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
                (\<exists>m cand.
                   newton_window_pick_bail (carried_descartes_count XX) e XX = Some (m, cand)
                 \<and> carried_descartes_count cand = carried_descartes_count XX
                 \<and> todo' = (lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                            rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                            ks @ [k + (2 ^ e + 2)])
                 \<and> qtodo' = qtodo @ [cand] \<and> es' = es @ [e + 1] \<and> ss' = ss @ [s]
                 \<and> cs' = cs @ [carried_descartes_count XX + 2]
                 \<and> gs' = gs @ [4398046511104 + carried_descartes_count XX]
                 \<and> rp' = rp)
            \<and> acc' = (al, ar, ak))) x"
    \<comment> \<open>passed to the arm shape's push disjuncts, where \<open>defl_body_step\<close> opens it to derive \<open>wide\<close>; the arms do not look
       inside it.\<close>
    and wit: "defl_push_wit rp l_num r_num k"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the gate's \<open>e \<le> newton_pol_ecap\<close> conjunct. It is carried by the window disjunct because \<open>defl_body_step\<close>
       needs it for the window push's \<open>k\<close>-budget and there is no other channel; it is not a loop invariant, since this push
       stores \<open>e + 1\<close> while the gate caps only \<open>e\<close>.\<close>
    and eecap: "e \<le> newton_pol_ecap"
  shows "defl_arm_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp l_num r_num k e s x"
  \<comment> \<open>\<^bold>\<open>DECOMPOSED, not searched.\<close> Splitting the column contract's disjunction first leaves
     each side a goal small enough to close outright; one \<open>blast\<close> over both does not finish.\<close>
  \<comment> \<open>\<^bold>\<open>The reject half is the split outcome\<close>, so it goes through the split bridge by \<open>rule\<close> with the named atoms kept
     folded. Unfolding them too would put a two-level disjunction under one \<open>blast\<close>. Only the window half unfolds the arm
     shape.\<close>
  using assms
  apply (cases x)
  apply clarsimp
  apply (elim disjE)
   apply (rule defl_arm_shape_of_split_cols[OF _ wit], assumption)
  apply (clarsimp simp: defl_arm_shape_def)
  apply blast
  done

section \<open>The box parametrisation, and the two scalar dispatch arms\<close>


text \<open>\<^bold>\<open>The \<open>cnt = 0\<close> and \<open>cnt = 1\<close> dispatch arms, invariant AND columns.\<close> Both are the
  classic op verbatim, so the column half is @{thm [source] hybrid_branch_zero_correct} /
  @{thm [source] hybrid_branch_one_correct} and the invariant half is the arm lemma. The
  arm-selection premise is on \<open>cnt\<close> --- the RESOLVED class --- because on this stack that is
  the only place it can be (\<open>defl_resolve_bind\<close>'s banner).\<close>

lemma defl_dispatch_zero_step:
  assumes cnt0: "cnt = 0"
    and inv: "dyadic_iv_cs_invar cnt (carried_descartes_count X)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) acc"
    and cov: "defl_dispatch_covers (of_int_poly (Poly rp) :: real poly) lo
                (lns, rns, ks) acc l_num r_num k"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and ne: "0 < length X" and lr: "l_num < r_num"
  shows "defl_dispatch_monadic (lns, rns, ks) qtodo es ss cs gs acc rp
             l_num r_num k e s g1 Q1 cnt
       \<le> SPEC (\<lambda>x.
             defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo x
           \<and> defl_arm_shape lns rns ks qtodo es ss cs gs acc rp
               l_num r_num k e s x)"
proof -
  have cnt0X: "carried_descartes_count X = 0"
    using inv cnt0 by (simp add: dyadic_iv_cs_invar_def)
  have noroot: "poly (of_int_poly (Poly rp) :: real poly) y \<noteq> 0"
    if "real_of_int l_num / 2 ^ k < y" and "y < real_of_int r_num / 2 ^ k" for y
    by (rule defl_node_box_no_roots_y[OF wrel cnt0X ne lr that])
  \<comment> \<open>\<^bold>\<open>The column half is a \<open>\<le> RETURN\<close>, and @{thm [source] defl_SPEC_conj} needs two
     \<open>\<le> SPEC\<close>s.\<close> \<open>RETURN x \<le> SPEC P\<close> is \<open>P x\<close>, so one \<open>order_trans\<close> converts it; feeding the
     \<open>\<le> RETURN\<close> form straight to the conjunction rule reports a bare \<open>OF: no unifiers\<close>.\<close>
  have st0: "hybrid_branch_zero_monadic (lns, rns, ks) qtodo es ss cs gs rp acc
                 l_num r_num Q1
           \<le> SPEC (\<lambda>r. r = (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc))"
    by (rule order_trans[OF hybrid_branch_zero_correct]) simp
  show ?thesis
    unfolding defl_dispatch_monadic_def PR_CONST_def
    apply (simp add: cnt0)
    apply (rule order_trans[OF defl_SPEC_conj[OF
          defl_branch_zero_invar[OF coup iso cov noroot] st0]])
    \<comment> \<open>\<open>noroot\<close> is a \<open>\<And>y\<close>-fact whose own two premises \<open>OF\<close> leaves OPEN, in the trivial
       \<open>\<lbrakk>A; B\<rbrakk> \<Longrightarrow> A\<close> shape --- they come FIRST, so they have to be cleared before the
       postcondition goal is reachable.\<close>
    apply (all \<open>(assumption; fail)?\<close>)
    apply (rule SPEC_rule)
    apply (clarsimp simp: defl_arm_shape_def)
    apply (all \<open>(blast; fail)?\<close>)
    done
qed


lemma defl_dispatch_one_step:
  assumes cnt1: "cnt = 1"
    and inv: "dyadic_iv_cs_invar cnt (carried_descartes_count X)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)"
    and cov: "defl_dispatch_covers (of_int_poly (Poly rp) :: real poly) lo
                (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and ne: "0 < length X" and lr: "l_num < r_num"
    and sf: "square_free (of_int_poly (Poly rp) :: real poly)"
    and lal: "length al = length ar" and lak: "length ar = length ak"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
  shows "defl_dispatch_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s g1 Q1 cnt
       \<le> SPEC (\<lambda>x.
             defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo x
           \<and> defl_arm_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp
               l_num r_num k e s x)"
proof -
  have cnt1X: "carried_descartes_count X = 1"
    using inv cnt1 by (simp add: dyadic_iv_cs_invar_def)
  have pairok: "dsc_pair_ok (of_int_poly (Poly rp) :: real poly)
      (real_of_int l_num / 2 ^ k, real_of_int r_num / 2 ^ k)"
    by (rule defl_node_box_pair_ok[OF wrel cnt1X ne sf lr])
  have st1: "hybrid_branch_one_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
                 l_num r_num k Q1
           \<le> SPEC (\<lambda>r. r = (((lns, rns, ks), qtodo, es, ss, cs, gs, rp),
                             al @ [l_num], ar @ [r_num], ak @ [k]))"
    by (rule order_trans[OF hybrid_branch_one_correct[OF accpush]]) simp
  show ?thesis
    unfolding defl_dispatch_monadic_def PR_CONST_def
    apply (simp add: cnt1)
    apply (rule order_trans[OF defl_SPEC_conj[OF
          defl_branch_one_invar[OF coup iso cov lal lak accpush pairok] st1]])
    apply (rule SPEC_rule)
    apply (clarsimp simp: defl_arm_shape_def)
    apply (all \<open>(blast; fail)?\<close>)
    done
qed


section \<open>The four dispatch arms with \<open>2 \<le> cnt\<close>\<close>

text \<open>\<^bold>\<open>Each is its arm's INVARIANT lemma and its COLUMN lemma, joined by
  @{thm [source] defl_SPEC_conj}\<close>, with the gate taken as a \<open>\<le> SPEC\<close> hypothesis so the caller
  can supply it from @{thm [source] newton_pol_gate_mop_correct} without this layer having to
  know what @{const newton_pol_gate} evaluates to. Four rather than two because every arm below
  the dispatch is stated at one of the two guard bands (\<^emph>\<open>exact-or-locked\<close> vs \<^emph>\<open>general\<close>) ---
  that split is a branch condition in the code, not a proof convenience.\<close>

lemma defl_dispatch_split_exact_step:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    \<comment> \<open>in @{const defl_node_ok}'s own shape, so the assembly reads it off the popped node.\<close>
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    and gceil: "g \<le> 4398046511104 + length rp"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qlen3: "3 \<le> length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and lenQrp: "length Q \<le> length rp"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)"
    and cov: "defl_dispatch_covers (of_int_poly (Poly rp) :: real poly) lo
                (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
    and cnt2: "2 \<le> cnt"
    and gate: "newton_pol_gate_mop Q e k s \<le> SPEC (\<lambda>gt. \<not> gt)"
    \<comment> \<open>\<^bold>\<open>Last\<close>, immediately before \<open>shows\<close>, so that no existing \<open>[OF \<dots>]\<close> position in a caller moves.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the push witness, built once by \<open>defl_dispatch_step\<close> and passed to the arm-shape bridge. It is opaque
       here; the dispatch already knows its content.\<close>
    and wit: "defl_push_wit rp l_num r_num k"
  shows "defl_dispatch_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s g Q cnt
       \<le> SPEC (\<lambda>x.
             defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo x
           \<and> defl_arm_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp
               l_num r_num k e s x)"
proof -
  have n0: "cnt \<noteq> 0" and n1: "cnt \<noteq> Suc 0" using cnt2 by auto
  show ?thesis
    unfolding defl_dispatch_monadic_def PR_CONST_def
    apply (simp add: n0 n1)
    apply (refine_vcg gate[THEN order_trans])
    \<comment> \<open>the DEAD \<open>if\<close> branch first --- the gate cannot be both open and closed, so that
       goal carries \<open>x\<close> and \<open>\<not> x\<close> together. \<open>(clarsimp; fail)?\<close> keeps the step only
       when \<open>clarsimp\<close> CLOSES the goal, so it cannot mangle the live branch.\<close>
    apply (all \<open>((clarsimp; fail))?\<close>)
    apply clarsimp
    apply (rule order_trans[OF defl_SPEC_conj[OF
          defl_branch_split_exact_invar[OF frame lock gex pay gceil gcap_rp Qlen3 Qbound lenQrp wrel rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecap sscap ccap push scap1 coup iso cov l1 l2 lal lak dvdX]
          defl_branch_split_exact_cols_acc[OF frame lock gex gcap_rp Qlen3 Qbound lenQrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecap sscap ccap push scap1]]])
    apply (rule SPEC_rule)
    apply (elim conjE)
    apply (rule conjI)
     apply assumption
    apply (rule defl_arm_shape_of_split_cols[OF _ wit])
    apply assumption
    done
qed


lemma defl_dispatch_split_gen_step:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)"
    and cov: "defl_dispatch_covers (of_int_poly (Poly rp) :: real poly) lo
                (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
    and cnt2: "2 \<le> cnt"
    and gate: "newton_pol_gate_mop Q e k s \<le> SPEC (\<lambda>gt. \<not> gt)"
    \<comment> \<open>\<^bold>\<open>Last\<close>, immediately before \<open>shows\<close>, so that no existing \<open>[OF \<dots>]\<close> position in a caller moves.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the push witness, built once by \<open>defl_dispatch_step\<close> and passed to the arm-shape bridge. It is opaque
       here; the dispatch already knows its content.\<close>
    and wit: "defl_push_wit rp l_num r_num k"
  shows "defl_dispatch_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s g Q cnt
       \<le> SPEC (\<lambda>x.
             defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo x
           \<and> defl_arm_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp
               l_num r_num k e s x)"
proof -
  have n0: "cnt \<noteq> 0" and n1: "cnt \<noteq> Suc 0" using cnt2 by auto
  show ?thesis
    unfolding defl_dispatch_monadic_def PR_CONST_def
    apply (simp add: n0 n1)
    apply (refine_vcg gate[THEN order_trans])
    \<comment> \<open>the DEAD \<open>if\<close> branch first --- the gate cannot be both open and closed, so that
       goal carries \<open>x\<close> and \<open>\<not> x\<close> together. \<open>(clarsimp; fail)?\<close> keeps the step only
       when \<open>clarsimp\<close> CLOSES the goal, so it cannot mangle the live branch.\<close>
    apply (all \<open>((clarsimp; fail))?\<close>)
    apply clarsimp
    apply (rule order_trans[OF defl_SPEC_conj[OF
          defl_branch_split_gen_invar[OF frame lock g0 glt g_tri g_cpl gcap_rp Qne Qbound Q_small wrel rpnz lr lenXrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecap sscap ccap push scap1 coup iso cov l1 l2 lal lak dvdX]
          defl_branch_split_gen_cols_acc[OF frame lock g0 glt g_tri g_cpl gcap_rp Qne Qbound Q_small wrel rpnz lr lenXrp rpne rpb rp_small rp_pb krp kcap accpush qcap gcap ecap sscap ccap push scap1 dvdX]]])
    apply (rule SPEC_rule)
    apply (elim conjE)
    apply (rule conjI)
     apply assumption
    apply (rule defl_arm_shape_of_split_cols[OF _ wit])
    apply assumption
    done
qed


lemma defl_dispatch_window_exact_step:
  fixes l_num r_num :: int and k e s cnt g v :: nat and rp :: gmp_poly
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g"
    and frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and cnt2: "2 \<le> cnt"
    and inv: "dyadic_iv_cs_invar cnt (carried_descartes_count X)"
    and count2: "2 \<le> carried_descartes_count X"
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    \<comment> \<open>the node, in the DEFLATING shape: a witness related to the init, not equal to it\<close>
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length X \<le> length rp"
    and Qlen3: "3 \<le> length Q"
    \<comment> \<open>word bounds, all as in the classic arm\<close>
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne1: "1 < length X"
    and X_b2: "length X + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length X < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length X - 1) < max_snat LENGTH(gmp_poly_len)"
    and vcap1: "int (carried_descartes_count X) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count X < max_snat LENGTH(gmp_poly_len)"
    and gcap_lock: "4398046511104 + carried_descartes_count X + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the invariant at the popped state\<close>
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)"
    and cov: "defl_dispatch_covers (of_int_poly (Poly rp) :: real poly) lo (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
    and cnt2: "2 \<le> cnt"
    and gate: "newton_pol_gate_mop Q e k s \<le> SPEC (\<lambda>gt. gt)"
    \<comment> \<open>\<^bold>\<open>Last\<close>, immediately before \<open>shows\<close>, so that no existing \<open>[OF \<dots>]\<close> position in a caller moves.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the push witness, built once by \<open>defl_dispatch_step\<close> and passed to the arm-shape bridge. It is opaque
       here; the dispatch already knows its content.\<close>
    and wit: "defl_push_wit rp l_num r_num k"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the gate's \<open>e \<le> newton_pol_ecap\<close> conjunct, passed to the arm-shape bridge. The dispatch reads it off
       \<open>gopen\<close>.\<close>
    and eecap: "e \<le> newton_pol_ecap"
  shows "defl_dispatch_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s g Q cnt
       \<le> SPEC (\<lambda>x.
             defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo x
           \<and> defl_arm_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp
               l_num r_num k e s x)"
proof -
  have n0: "cnt \<noteq> 0" and n1: "cnt \<noteq> Suc 0" using cnt2 by auto
  show ?thesis
    unfolding defl_dispatch_monadic_def PR_CONST_def
    apply (simp add: n0 n1)
    apply (refine_vcg gate[THEN order_trans])
    \<comment> \<open>the DEAD \<open>if\<close> branch first --- the gate cannot be both open and closed, so that
       goal carries \<open>x\<close> and \<open>\<not> x\<close> together. \<open>(clarsimp; fail)?\<close> keeps the step only
       when \<open>clarsimp\<close> CLOSES the goal, so it cannot mangle the live branch.\<close>
    apply (all \<open>((clarsimp; fail))?\<close>)
    apply clarsimp
    apply (rule order_trans[OF defl_SPEC_conj[OF
          defl_gate_open_invar[OF gex frame lock cnt2 inv count2 pay wrel rpnz lr lenXrp Qlen3 rpne rpb rp_small rp_pb krp kcap Qne Qbound X_ne1 X_b2 X_small ecap ecap2 ecap3 kcap2 gate4 vcap1 vcap2 gcap_lock accpush qcap gcap ecapl sscap ccap push2 push1 kslen scap1 coup iso cov l1 l2 lal lak dvdX]
          defl_gate_open_cols_accd[OF gex frame lock cnt2 inv count2 pay wrel rpnz lr lenXrp Qlen3 rpne rpb rp_small rp_pb krp kcap Qne Qbound X_ne1 X_b2 X_small ecap ecap2 ecap3 kcap2 gate4 vcap1 vcap2 gcap_lock accpush qcap gcap ecapl sscap ccap push2 push1 kslen scap1 coup iso cov l1 l2 lal lak]]])
    apply (rule SPEC_rule)
    apply (elim conjE)
    apply (rule conjI)
     apply assumption
    apply (rule defl_arm_shape_of_window_cols[OF _ wit eecap])
    apply assumption
    done
qed


lemma defl_dispatch_window_gen_step:
  fixes l_num r_num :: int and k e s cnt g :: nat and rp :: gmp_poly
  assumes g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    \<comment> \<open>from @{thm [source] defl_resolve_count_classify}'s last conjunct\<close>
    and cnt4: "cnt < 4"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and lr: "l_num < r_num"
    and lenXrp: "length (carried_init_same_den l_num (2 ^ k) r_num rp) \<le> length rp"
    and Xlen3: "3 \<le> length (carried_init_same_den l_num (2 ^ k) r_num rp)"
    \<comment> \<open>word bounds, all as in the \<open>gex\<close> arm but read off the INIT\<close>
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_b2: "length (carried_init_same_den l_num (2 ^ k) r_num rp) + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length (carried_init_same_den l_num (2 ^ k) r_num rp) < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length (carried_init_same_den l_num (2 ^ k) r_num rp) - 1) < max_snat LENGTH(gmp_poly_len)"
    and vcap1: "int (carried_descartes_count (carried_init_same_den l_num (2 ^ k) r_num rp)) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count (carried_init_same_den l_num (2 ^ k) r_num rp) < max_snat LENGTH(gmp_poly_len)"
    and gcap_lock: "4398046511104 + carried_descartes_count (carried_init_same_den l_num (2 ^ k) r_num rp) + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)"
    and cov: "defl_dispatch_covers (of_int_poly (Poly rp) :: real poly) lo (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
    and cnt2: "2 \<le> cnt"
    and gate: "newton_pol_gate_mop Q e k s \<le> SPEC (\<lambda>gt. gt)"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the push witness, built once by \<open>defl_dispatch_step\<close> and passed to the arm-shape bridge. It is opaque
       here; the dispatch already knows its content.\<close>
    and wit: "defl_push_wit rp l_num r_num k"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the gate's \<open>e \<le> newton_pol_ecap\<close> conjunct, passed to the arm-shape bridge. The dispatch reads it off
       \<open>gopen\<close>.\<close>
    and eecap: "e \<le> newton_pol_ecap"
  shows "defl_dispatch_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s g Q cnt
       \<le> SPEC (\<lambda>x.
             defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo x
           \<and> defl_arm_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp
               l_num r_num k e s x)"
proof -
  have n0: "cnt \<noteq> 0" and n1: "cnt \<noteq> Suc 0" using cnt2 by auto
  show ?thesis
    unfolding defl_dispatch_monadic_def PR_CONST_def
    apply (simp add: n0 n1)
    apply (refine_vcg gate[THEN order_trans])
    \<comment> \<open>the DEAD \<open>if\<close> branch first --- the gate cannot be both open and closed, so that
       goal carries \<open>x\<close> and \<open>\<not> x\<close> together. \<open>(clarsimp; fail)?\<close> keeps the step only
       when \<open>clarsimp\<close> CLOSES the goal, so it cannot mangle the live branch.\<close>
    apply (all \<open>((clarsimp; fail))?\<close>)
    apply clarsimp
    apply (rule order_trans[OF defl_SPEC_conj[OF
          defl_gate_open_gen_invar[OF g0 glt cnt4 rpnz lr lenXrp Xlen3 rpne rpb rp_small rp_pb krp kcap X_b2 X_small ecap ecap2 ecap3 kcap2 gate4 vcap1 vcap2 gcap_lock accpush qcap gcap ecapl sscap ccap push2 push1 kslen scap1 coup iso cov l1 l2 lal lak]
          defl_gate_open_gen_cols_accd[OF g0 glt cnt4 rpnz lr lenXrp Xlen3 rpne rpb rp_small rp_pb krp kcap X_b2 X_small ecap ecap2 ecap3 kcap2 gate4 vcap1 vcap2 gcap_lock accpush qcap gcap ecapl sscap ccap push2 push1 kslen scap1 coup iso cov l1 l2 lal lak]]])
    apply (rule SPEC_rule)
    apply (elim conjE)
    apply (rule conjI)
     apply assumption
    apply (rule defl_arm_shape_of_window_cols[OF _ wit eecap])
    apply assumption
    done
qed


section \<open>The sharp Descartes bound, and why no fifth arm is needed\<close>

text \<open>\<^bold>\<open>The case this closes.\<close> @{const defl_branch_split_monadic} takes its deflating build only when
  \<open>(g = 0 \<or> 2\<^sup>4\<^sup>2 \<le> g) \<and> 3 \<le> len\<close>, so @{thm [source] defl_branch_split_exact_invar} carries \<open>3 \<le> length Q\<close>, a branch condition of the
  code. At an exact or locked guard with \<open>len < 3\<close> the op takes the escalating route instead, and no arm lemma covers that.

  \<^bold>\<open>That case cannot occur.\<close> The dispatch reaches the split only at \<open>2 \<le> cnt\<close>, hence \<open>2 \<le> carried_descartes_count X\<close>; and a
  sign-variation count over a list of length \<open>n\<close> is at most \<open>n - 1\<close>, not \<open>n\<close>. So \<open>length X \<ge> 3\<close>.

  @{thm [source] carried_descartes_count_le_length_cn} gives only \<open>\<le> length Q\<close>, because
  @{thm [source] fold_sign_step_snd_le_cn} is stated for an arbitrary starting sign \<open>s\<close>. The sharper bound uses the start
  \<open>s = 0\<close>: by @{const sign_step_from_sgn}, a step out of the zero state resets the counter rather than incrementing it, so the
  first element contributes nothing.\<close>

lemma defl_sign_step_zero_le:
  fixes x :: int
  shows "snd (sign_step x (0, n)) \<le> n"
  using sign_step_from_sgn_correct[of x "(0, n)"]
  by (simp add: sign_step_from_sgn_def)

lemma defl_fold_sign_step_zero:
  fixes xs :: "int list"
  shows "snd (fold sign_step xs (0, 0)) \<le> length xs - 1"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case (Cons x ys)
  obtain s' n' where sn': "sign_step x (0, 0) = (s', n')"
    by (cases "sign_step x (0, 0)")
  have "n' \<le> 0" using defl_sign_step_zero_le[of x 0] sn' by simp
  hence n0: "n' = 0" by simp
  have "snd (fold sign_step ys (s', n')) \<le> n' + length ys"
    by (rule fold_sign_step_snd_le_cn)
  thus ?thesis using Cons sn' n0 by simp
qed

lemma defl_cdc_le_length_1: "carried_descartes_count Q \<le> length Q - 1"
  using defl_fold_sign_step_zero[of "taylor_shift_list 1 (rev Q)"]
  by (simp add: carried_descartes_count_def sign_changes_fold_def)

lemma defl_count2_len3: "2 \<le> carried_descartes_count Q \<Longrightarrow> 3 \<le> length Q"
  using defl_cdc_le_length_1[of Q] by linarith


section \<open>The dispatch: all six arms under one case split\<close>

text \<open>\<^bold>\<open>The arm selection is here, not above the resolve\<close>, the one structural difference from the non-deflating
  assembly (see \<open>defl_resolve_bind\<close>): there the exact object is given by a formula, while here it is existential and may be
  replaced by the resolve. So the case split is on the resolved class \<open>cnt\<close>, the Newton gate, and the guard band: six
  leaves, each one of the arm lemmas.

  \<^bold>\<open>\<open>3 \<le> length Q\<close> is derived, not assumed\<close>: the split arm's deflating build is gated on it in the code, and \<open>2 \<le> cnt\<close>
  gives it through the sharp Descartes bound.\<close>

lemma defl_dispatch_step:
  fixes l_num r_num :: int and k e s cnt g :: nat and rp :: gmp_poly
  assumes frame: "node_frame X Q g"
    and wrel: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and inv: "dyadic_iv_cs_invar cnt (carried_descartes_count X)"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    and gceil: "g \<le> 4398046511104 + length rp"
    and bud: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and clt: "g < 4398046511104 \<longrightarrow> cnt < 4"
    and lenX: "length X \<le> length rp"
    \<comment> \<open>the keystone premise that makes the saturation band unreachable\<close>
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    \<comment> \<open>the node, and the root\<close>
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and sf: "square_free (of_int_poly (Poly rp) :: real poly)"
    and lr: "l_num < r_num"
    and rpne: "0 < length rp"
    and rp_gb: "4398046511104 + length rp + length rp < max_snat LENGTH(gmp_poly_len)"
    and rp_sint: "int (length rp) < max_sint LENGTH(gmp_long_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>The Newton gate's five word bounds are derived, not assumed.\<close> Each rests on \<open>e \<le> newton_pol_ecap\<close>, which is
       the gate's own conjunct and not a property of the \<open>es\<close> column (the window push stores \<open>e + 1\<close>). They are read off
       \<open>gopen\<close> below, as @{thm [source] hybrid_step_discharge_window} reads its \<open>eecap\<close>. The premise that remains is what
       the gate cannot give: the node's depth headroom.\<close>
    and kroom258: "k + 258 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the columns\<close>
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the invariant at the popped state\<close>
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)"
    and cov: "defl_dispatch_covers (of_int_poly (Poly rp) :: real poly) lo
                (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the node's divisibility at the resolved object, from @{thm [source] defl_resolve_bind}'s continuation;
       the arm case split is below the resolve, so there is no other source.\<close>
    and dvdX: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
  shows "defl_dispatch_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s g Q cnt
       \<le> SPEC (\<lambda>x.
             defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo x
           \<and> defl_arm_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp
               l_num r_num k e s x)"
proof -
  have lenQ: "length X = length Q" by (rule cdlr_node_frame_len[OF frame])
  \<comment> \<open>the node's polynomial is non-empty because @{const defl_node_wrel} bundles
     non-vanishing, and \<open>Poly [] = 0\<close>\<close>
  have Xnz: "(of_int_poly (Poly X) :: real poly) \<noteq> 0" by (rule defl_node_wrelD_nz[OF wrel])
  have Xne: "0 < length X" using Xnz by (cases X) auto
  have lenQrp: "length Q \<le> length rp" using lenQ lenX by simp
  have rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)" using rp_gb rpne by simp
  have Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)" using lenQrp rpb by simp
  have Q_small: "length Q < 1099511627776" using lenQrp rp_small by simp
  have X_small: "length X < 1099511627776" using lenX rp_small by simp
  have X_b2: "length X + 2 < max_snat LENGTH(gmp_poly_len)" using lenX rp_gb by simp
  have cX: "carried_descartes_count X \<le> length rp"
    using carried_descartes_count_le_length_cn[of X] lenX by simp
  have vcap1: "int (carried_descartes_count X) < max_sint LENGTH(gmp_long_len)"
    using cX rp_sint by simp
  have vcap2: "4398046511104 + carried_descartes_count X < max_snat LENGTH(gmp_poly_len)"
    using cX rp_gb by simp
  have gcap_lock: "4398046511104 + carried_descartes_count X + length rp
                     < max_snat LENGTH(gmp_poly_len)"
    using cX rp_gb by simp
  have gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    using gceil rp_gb by (simp add: max_def)
  show ?thesis
  proof (cases "cnt = 0")
    case True
    show ?thesis
      by (rule defl_dispatch_zero_step[OF True inv coup iso cov wrel Xne lr])
  next
    case c0: False
    show ?thesis
    proof (cases "cnt = 1")
      case True
      show ?thesis
        by (rule defl_dispatch_one_step[OF True inv coup iso cov wrel Xne lr sf lal lak accpush])
    next
      case c1: False
      have cnt2: "2 \<le> cnt" using c0 c1 by simp
      have count2: "2 \<le> carried_descartes_count X"
        using inv cnt2 by (simp add: dyadic_iv_cs_invar_def)
      have Xlen3: "3 \<le> length X" by (rule defl_count2_len3[OF count2])
      \<comment> \<open>\<^bold>\<open>The push witness, built once here.\<close> This is the only point with both halves, the node's divisibility and its
         count, and every arm below pushes, so the four arms take it as an opaque premise.\<close>
      have wit: "defl_push_wit rp l_num r_num k" by (rule defl_push_witI[OF dvdX count2])
      have Qlen3: "3 \<le> length Q" using Xlen3 lenQ by simp
      have Qne: "0 < length Q" using Qlen3 by linarith
      have X_ne1: "1 < length X" using Xlen3 by linarith
      have gm: "newton_pol_gate_mop Q e k s
              \<le> RETURN (newton_pol_gate (length Q - 1) e k s)"
        by (rule newton_pol_gate_mop_correct[OF Qne]) (use Qbound in simp)
      show ?thesis
      proof (cases "newton_pol_gate (length Q - 1) e k s")
        case gopen: True
        have gate: "newton_pol_gate_mop Q e k s \<le> SPEC (\<lambda>gt. gt)"
          by (rule order_trans[OF gm]) (use gopen in simp)
        \<comment> \<open>\<^bold>\<open>The five window word bounds, from the gate\<close>, as \<open>Newton_Solver\<close> derives \<open>2\<^sup>e + 2 \<le> 258\<close> from a
           @{const newton_pol_gate}, and as @{thm [source] hybrid_step_discharge_window} derives \<open>eecap\<close>.\<close>
        have eecap: "e \<le> newton_pol_ecap"
          using gopen by (simp add: newton_pol_gate_def)
        have ew: "(2::nat) ^ e + 2 \<le> 258" by (rule newton_pol_ecap_width[OF eecap])
        have ecap: "e < LENGTH(gmp_poly_len)"
          using eecap by (simp add: newton_pol_ecap_def)
        have ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
          using ew by (simp add: max_snat_def)
        have ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
          using eecap by (simp add: newton_pol_ecap_def max_snat_def)
        \<comment> \<open>\<^bold>\<open>The one bound the gate cannot give\<close> --- the window child sinks
           \<open>2\<^sup>e + 2 \<le> 258\<close> below THIS node, so the depth headroom is a
           caller obligation and stays a premise.\<close>
        have kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
          using ew kroom258 by simp
        \<comment> \<open>a PRODUCT of two variables, so no linear closer finds it --- chained through
           the two constants instead\<close>
        have gate4rp: "(2 ^ e + 2) * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
        proof -
          have "(2 ^ e + 2) * (length rp - 1) \<le> 258 * (length rp - 1)" using ew by simp
          also have "\<dots> < 258 * 1099511627776" using rp_small rpne by simp
          also have "\<dots> < max_snat LENGTH(gmp_poly_len)" by (simp add: max_snat_def)
          finally show ?thesis .
        qed
        have gate4: "(2 ^ e + 2) * (length X - 1) < max_snat LENGTH(gmp_poly_len)"
        proof -
          have "(2 ^ e + 2) * (length X - 1) \<le> (2 ^ e + 2) * (length rp - 1)"
            using lenX by (intro mult_le_mono) auto
          thus ?thesis using gate4rp by linarith
        qed
        show ?thesis
        proof (cases "g = 0 \<or> 4398046511104 \<le> g")
          case gex: True
          show ?thesis
            by (rule defl_dispatch_window_exact_step[OF gex frame lock cnt2 inv count2 pay
                  wrel rpnz lr lenX Qlen3 rpne rpb rp_small rp_pb krp kcap Qne Qbound X_ne1
                  X_b2 X_small ecap ecap2 ecap3 kcap2 gate4 vcap1 vcap2 gcap_lock accpush
                  qcap gcap ecapl sscap ccap push2 push1 kslen scap1 coup iso cov l1 l2
                  lal lak cnt2 gate dvdX wit eecap])
        next
          case ngex: False
          have g0: "g \<noteq> 0" and glt: "g < 4398046511104" using ngex by auto
          have cnt4: "cnt < 4" using clt glt by simp
          have XiL: "length (carried_init_same_den l_num (2 ^ k) r_num rp) = length rp"
            by (simp add: truncate_length_carried_init_same_den)
          have Xilen3: "3 \<le> length (carried_init_same_den l_num (2 ^ k) r_num rp)"
            using XiL Xlen3 lenX by simp
          have cXi: "carried_descartes_count (carried_init_same_den l_num (2 ^ k) r_num rp)
                       \<le> length rp"
            using carried_descartes_count_le_length_cn
                    [of "carried_init_same_den l_num (2 ^ k) r_num rp"] XiL by simp
          show ?thesis
            by (rule defl_dispatch_window_gen_step[OF g0 glt cnt4 rpnz lr
                  _ Xilen3 rpne rpb rp_small rp_pb krp kcap _ _ ecap ecap2 ecap3 kcap2 _
                  _ _ _ accpush qcap gcap ecapl sscap ccap push2 push1 kslen scap1
                  coup iso cov l1 l2 lal lak cnt2 gate wit eecap])
               (use XiL rp_gb rp_small rp_sint gate4rp cXi in simp_all)
        qed
      next
        case gclosed: False
        have gate: "newton_pol_gate_mop Q e k s \<le> SPEC (\<lambda>gt. \<not> gt)"
          by (rule order_trans[OF gm]) (use gclosed in simp)
        show ?thesis
        proof (cases "g = 0 \<or> 4398046511104 \<le> g")
          case gex: True
          show ?thesis
            by (rule defl_dispatch_split_exact_step[OF frame lock gex pay gceil gcap_rp
                  Qlen3 Qbound lenQrp wrel rpne rpb rp_small rp_pb krp kcap accpush qcap
                  gcap ecapl sscap ccap push2 scap1 coup iso cov l1 l2 lal lak cnt2 gate dvdX wit])
        next
          case ngex: False
          have g0: "g \<noteq> 0" and glt: "g < 4398046511104" using ngex by auto
          show ?thesis
            by (rule defl_dispatch_split_gen_step[OF frame lock g0 glt g_tri bud gcap_rp
                  Qne Qbound Q_small wrel rpnz lr lenX rpne rpb rp_small rp_pb krp kcap
                  accpush qcap gcap ecapl sscap ccap push2 scap1 coup iso cov l1 l2
                  lal lak cnt2 gate dvdX wit])
        qed
      qed
    qed
  qed
qed

text \<open>\<^bold>\<open>The two product-shape bridges, supplied once and BY NAME\<close> ---
  @{thm [source] defl_branch_split_exact_coupling}'s banner, one level up. The resolve states
  the node's budget as \<open>g \<le> length rp + k \<cdot> length rp\<close>; the dispatch asks for
  \<open>(k + 1) \<cdot> length rp\<close>. To \<open>linarith\<close> a product is an ATOM, so it crosses neither the
  distribution nor --- once distributed --- the summand ORDER, and a closer that tries costs a
  cycle each time. Hoisted out into named lemmas exactly as that banner hoists \<open>one_le\<close>.\<close>

lemma defl_bud_form:
  assumes "g \<le> length rp + k * length rp \<or> 4398046511104 \<le> g"
  shows "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
  using assms by (simp add: algebra_simps)

lemma defl_gtri_of_room:
  assumes room: "(k + 1) * length rp < 1099511627776"
    and bud: "g \<le> length rp + k * length rp \<or> 4398046511104 \<le> g"
  shows "g < 1099511627776 \<or> 4398046511104 \<le> g"
  \<comment> \<open>\<open>auto\<close>, not \<open>simp\<close>: the hypothesis is a DISJUNCTION and simp does not case-split
     one. The arithmetic in each branch is trivial once \<open>algebra_simps\<close> has put the two
     product forms into one.\<close>
  using room bud by (auto simp: algebra_simps)

section \<open>After-pop: resolve, then dispatch\<close>

text \<open>\<^bold>\<open>\<open>g_tri\<close> is derived here, from the resolve's budget disjunct and \<open>g_room\<close>\<close>: it is a
  PREMISE of the body step, not a conjunct of any invariant, and the classic chain derives it at
  exactly this point for exactly this reason.\<close>

lemma defl_after_pop_step:
  fixes l_num r_num :: int and k e s c g :: nat and rp :: gmp_poly
  assumes node: "defl_node_ok rp l_num r_num k Q g c"
    and g_room: "(k + 1) * length rp < 1099511627776"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and sf: "square_free (of_int_poly (Poly rp) :: real poly)"
    and lr: "l_num < r_num"
    and rpne: "0 < length rp"
    and rp_gb: "4398046511104 + length rp + length rp < max_snat LENGTH(gmp_poly_len)"
    and rp_sint: "int (length rp) < max_sint LENGTH(gmp_long_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>passed on, in place of the five caps derived from the gate.\<close>
    and kroom258: "k + 258 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and iso: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)"
    and cov: "defl_dispatch_covers (of_int_poly (Poly rp) :: real poly) lo
                (lns, rns, ks) (al, ar, ak) l_num r_num k"
    and l1: "length lns = length rns" and l2: "length ks = length rns"
    and lal: "length al = length ar" and lak: "length ar = length ak"
  shows "defl_after_pop_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s c g Q
       \<le> SPEC (\<lambda>x.
             defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo x
           \<and> defl_arm_shape lns rns ks qtodo es ss cs gs (al, ar, ak) rp
               l_num r_num k e s x)"
proof -
  obtain X where frameD: "node_frame X Q g"
    and wrelD: "defl_node_wrel (carried_init_same_den l_num (2 ^ k) r_num rp) X"
    and cacheD: "hybrid_cs_ok g c (carried_descartes_count X)"
    and lenD: "length X \<le> length rp"
    and budD: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and payD: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    and lockedD: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and cle: "4 < c \<longrightarrow> 4398046511104 \<le> g"
    and ceilD: "g \<le> 4398046511104 + length rp"
    and dvdD: "(of_int_poly (Poly X) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den l_num (2 ^ k) r_num rp))
                       :: real poly)"
    by (rule defl_node_okE[OF node])
  have rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)" using rp_gb rpne by simp
  have lenQ: "length X = length Q" by (rule cdlr_node_frame_len[OF frameD])
  have Xnz: "(of_int_poly (Poly X) :: real poly) \<noteq> 0" by (rule defl_node_wrelD_nz[OF wrelD])
  have Qne: "0 < length Q" using Xnz lenQ by (cases X) auto
  have Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)" using lenQ lenD rpb by simp
  have XiL: "length (carried_init_same_den l_num (2 ^ k) r_num rp) = length rp"
    by (simp add: truncate_length_carried_init_same_den)
  have X_pbound: "length (carried_init_same_den l_num (2 ^ k) r_num rp)
                    * nat_bitlen (length (carried_init_same_den l_num (2 ^ k) r_num rp))
                  < max_snat LENGTH(gmp_poly_len)" using XiL rp_pb by simp
  have X_gbound: "4398046511104 + length (carried_init_same_den l_num (2 ^ k) r_num rp)
                  < max_snat LENGTH(gmp_poly_len)" using XiL rp_gb by simp
  \<comment> \<open>the children build's two word bounds on the resolved node, in the simp-normal form the goals have, from its frame,
     its length bound and \<open>rp_small\<close>.\<close>
  have q_b2: "Suc (Suc (length q)) < max_snat 64"
    if "node_frame Xq q gq" and "length Xq \<le> length rp" for Xq q gq
  proof -
    have "length q < 1099511627776"
      using cdlr_node_frame_len[OF that(1)] that(2) rp_small by linarith
    from small_len_b2[OF this] show ?thesis by simp
  qed
  have q_dep: "length q - Suc 0 < max_snat 64"
    if "node_frame Xq q gq" and "length Xq \<le> length rp" for Xq q gq
  proof -
    have "length q < 1099511627776"
      using cdlr_node_frame_len[OF that(1)] that(2) rp_small by linarith
    from small_len_dep[OF this] show ?thesis by simp
  qed
  show ?thesis
    unfolding defl_after_pop_monadic_def PR_CONST_def
    using Qne Qbound kcap rpne rpb krp
    apply (refine_vcg defl_resolve_bind[OF rpne rpb krp Qbound X_pbound X_gbound
          frameD wrelD cacheD cle lockedD budD payD ceilD lenD rpnz lr dvdD])
    \<comment> \<open>the five ASSERTs after the resolve. \<open>rp1 = rp\<close> settles three of them; the other two
       are about the RESOLVED polynomial, whose length is the node relation's non-vanishing
       plus the frame's length equation.\<close>
    apply (all \<open>((insert rpne rpb krp, simp); fail)?\<close>)
    apply (all \<open>((clarsimp, frule cdlr_node_frame_len,
                  frule defl_node_wrelD_nz, insert rpne rpb krp, simp);
                 fail)?\<close>)
    \<comment> \<open>and the dispatch, at the RESOLVED node\<close>
    apply (all \<open>clarsimp?\<close>)
    \<comment> \<open>the two word-bound side goals precede the dispatch goal; they are closed by name so that \<open>subgoal\<close> below lands on
       the dispatch goal.\<close>
    apply (all \<open>((rule q_b2 q_dep, assumption+); fail)?\<close>)
    subgoal for cnt Q1 g1 X1
      apply (rule defl_dispatch_step[where X = X1, OF _ _ _ _ _ _ _ _ _ _ rpnz sf lr rpne
                rp_gb rp_sint rp_small rp_pb krp kcap kroom258
                accpush qcap gcap ecapl sscap ccap push2 push1 kslen scap1
                coup iso cov l1 l2 lal lak])
      apply (all \<open>(assumption; fail)?\<close>)
      \<comment> \<open>the budget disjunct, and \<open>g_tri\<close> from it against \<open>g_room\<close> --- both
         through the NAMED product bridges, never through a closer\<close>
      apply (all \<open>((erule defl_bud_form); fail)?\<close>)
      apply (all \<open>((erule defl_gtri_of_room[OF g_room]); fail)?\<close>)
      done
    done
qed

section \<open>The arguments level: pop, then after-pop\<close>

text \<open>A clone of @{thm [source] hybrid_loop_step_args_pop} with the deflating after-pop
  substituted --- the two ops perform the same six pops and the same fourteen ASSERTs.\<close>

lemma defl_loop_step_args_pop:
  assumes tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and lne: "lns \<noteq> []" and lr: "length rns = length lns" and lk: "length ks = length lns"
    and qne: "qtodo \<noteq> []" and ene: "es \<noteq> []" and sne: "ss \<noteq> []"
    and cne: "cs \<noteq> []" and gne: "gs \<noteq> []"
  shows "defl_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs acc rp
       \<le> doN {
            ASSERT (0 < length (last qtodo));
            ASSERT (length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len));
            ASSERT (length (last qtodo) + 2 < max_snat LENGTH(gmp_poly_len));
            ASSERT (1 * (length (last qtodo) - 1) < max_snat LENGTH(gmp_poly_len));
            ASSERT (last ks + 1 < max_snat LENGTH(gmp_poly_len));
            ASSERT (last ss + 1 < max_snat LENGTH(gmp_poly_len));
            ASSERT (0 < length rp);
            ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
            ASSERT (last ks * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
            ASSERT (dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks));
            ASSERT (dyadic_interval_vec_pushable acc);
            ASSERT (length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len));
            ASSERT (length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len));
            ASSERT (length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len));
            ASSERT (length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len));
            ASSERT (length (butlast gs) + 2 < max_snat LENGTH(gmp_poly_len));
            defl_after_pop_monadic
              (butlast lns, butlast rns, butlast ks) (butlast qtodo)
              (butlast es) (butlast ss) (butlast cs) (butlast gs) acc rp
              (last lns) (last rns) (last ks) (last es) (last ss) (last cs) (last gs)
              (last qtodo)
          }"
  unfolding defl_loop_step_args_monadic_def PR_CONST_def
  using tinv lne qne ene sne cne gne
  by (simp add: cdlr_todo_pop_eq[OF lne lr lk] cdlr_poly_vec_pop_eq[OF qne]
                cdlr_exp_pop_eq[OF ene] cdlr_exp_pop_eq[OF sne]
                cdlr_exp_pop_eq[OF cne] cdlr_exp_pop_eq[OF gne])

lemma defl_loop_step_args_step:
  fixes rp :: gmp_poly
  assumes tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and lne: "lns \<noteq> []" and lrl: "length rns = length lns" and lk: "length ks = length lns"
    and qne: "qtodo \<noteq> []" and ene: "es \<noteq> []" and sne: "ss \<noteq> []"
    and cne: "cs \<noteq> []" and gne: "gs \<noteq> []"
    and node: "defl_node_ok rp (last lns) (last rns) (last ks)
                 (last qtodo) (last gs) (last cs)"
    and g_room: "(last ks + 1) * length rp < 1099511627776"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and sf: "square_free (of_int_poly (Poly rp) :: real poly)"
    and lrne: "last lns < last rns"
    and rpne: "0 < length rp"
    and rp_gb: "4398046511104 + length rp + length rp < max_snat LENGTH(gmp_poly_len)"
    and rp_sint: "int (length rp) < max_sint LENGTH(gmp_long_len)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and krp: "last ks * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "last ks + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>passed on, in place of the five caps derived from the gate.\<close>
    and kroom258: "last ks + 258 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length (butlast gs) + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
    and push1: "dyadic_interval_vec_pushable (butlast lns, butlast rns, butlast ks)"
    and kslen: "length (butlast ks) + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "last ss + 1 < max_snat LENGTH(gmp_poly_len)"
    and coup: "defl_trunc_coupling (butlast lns, butlast rns, butlast ks)
                 (butlast qtodo) (butlast cs) (butlast gs) rp"
    and iso: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)"
    and cov: "defl_dispatch_covers (of_int_poly (Poly rp) :: real poly) lo
                (butlast lns, butlast rns, butlast ks) (al, ar, ak)
                (last lns) (last rns) (last ks)"
    and l1: "length (butlast lns) = length (butlast rns)"
    and l2: "length (butlast ks) = length (butlast rns)"
    and lal: "length al = length ar" and lak: "length ar = length ak"
  shows "defl_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
       \<le> SPEC (\<lambda>x.
             defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo x
           \<and> defl_arm_shape (butlast lns) (butlast rns) (butlast ks) (butlast qtodo)
               (butlast es) (butlast ss) (butlast cs) (butlast gs) (al, ar, ak) rp
               (last lns) (last rns) (last ks) (last es) (last ss) x)"
proof -
  \<comment> \<open>the popped node's two length facts, derived ONCE, rather than handing
     @{thm [source] defl_node_okE} to a blanket \<open>auto\<close> over the fourteen ASSERTs.\<close>
  obtain XN where fr: "node_frame XN (last qtodo) (last gs)"
    and wr: "defl_node_wrel
               (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp) XN"
    and ok3: "hybrid_cs_ok (last gs) (last cs) (carried_descartes_count XN)"
    and le: "length XN \<le> length rp"
    and ok5: "last gs \<le> (last ks + 1) * length rp \<or> 4398046511104 \<le> last gs"
    and ok6: "4398046511106 \<le> last gs
                \<longrightarrow> carried_descartes_count XN \<le> last gs - 4398046511104"
    and ok7: "4398046511104 \<le> last gs \<longrightarrow> last qtodo = XN"
    and ok8: "4 < last cs \<longrightarrow> 4398046511104 \<le> last gs"
    and ok9: "last gs \<le> 4398046511104 + length rp"
    by (rule defl_node_okE[OF node])
  have lenQ: "length XN = length (last qtodo)" by (rule cdlr_node_frame_len[OF fr])
  have Xnz: "(of_int_poly (Poly XN) :: real poly) \<noteq> 0" by (rule defl_node_wrelD_nz[OF wr])
  have Qne: "0 < length (last qtodo)" using Xnz lenQ by (cases XN) auto
  have rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)" using rp_gb rpne by simp
  have Qbound: "length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len)"
    using lenQ le rpb by simp
  \<comment> \<open>the pop's two word bounds (@{thm [source] small_len_b2} / @{thm [source] small_len_dep}), from the popped node's
     length and \<open>rp_small\<close>.\<close>
  have Qsm: "length (last qtodo) < 1099511627776" using lenQ le rp_small by linarith
  have Qb2: "length (last qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
    by (rule small_len_b2[OF Qsm])
  have Qdep: "1 * (length (last qtodo) - 1) < max_snat LENGTH(gmp_poly_len)"
    by (rule small_len_dep[OF Qsm])
  show ?thesis
    apply (rule order_trans[OF defl_loop_step_args_pop[OF tinv lne lrl lk qne ene sne cne gne]])
    apply (refine_vcg defl_after_pop_step[OF node g_room rpnz sf lrne rpne rp_gb rp_sint
          rp_small rp_pb krp kcap kroom258 accpush qcap gcap ecapl
          sscap ccap push2 push1 kslen scap1 coup iso cov l1 l2 lal lak, THEN order_trans])
    \<comment> \<open>the fourteen ASSERTs, each by NAME. \<open>assumption\<close> cannot see them --- they are the
       lemma's own assumptions, not the goal's premises --- and a blanket \<open>simp\<close> with them
       inserted does not terminate in reasonable time.\<close>
    apply (all \<open>((rule Qne Qbound Qb2 Qdep kcap scap1 rpne rpb krp push2 accpush qcap ecapl
                       sscap ccap gcap); fail)?\<close>)
    \<comment> \<open>and the two projections of the after-pop's own conjunction\<close>
    apply (all \<open>((elim conjE, assumption); fail)?\<close>)
    done
qed


section \<open>The body step's three joins, one per shape\<close>

text \<open>\<^bold>\<open>Pure implications, no monadic reasoning.\<close> @{thm [source] defl_loop_step_args_step}
  delivers \<open>defl_loop_invar\<close> and @{const defl_arm_shape} at the result state; what remains is
  to turn the shape into the other four conjuncts of @{const defl_state_invar} plus the measure
  drop. That is the classic preservation machinery verbatim, minus the \<open>\<exists>pol\<close> subgoal ---
  so each join is stated as an ordinary implication and the body step is three \<open>rule\<close>s under an
  \<open>elim disjE\<close>.\<close>

lemma defl_body_join_pop:
  fixes rp :: gmp_poly
  assumes safe': "hybrid_loop_safe_invar
                    (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                      butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) acc"
    and clr: "length lns = length ks" and crr: "length rns = length ks"
    and csk: "length ss = length ks"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [nd]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [I]"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and inv: "defl_loop_invar P0 lo
                (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                  butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
  shows "(hybrid_loop_safe_invar
            (((butlast lns, butlast rns, butlast ks), butlast qtodo,
              butlast es, butlast ss, butlast cs, butlast gs, rp), acc)
          \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo
              (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                butlast es, butlast ss, butlast cs, butlast gs, rp), acc))
       \<and> hybrid_state_mu \<delta> l0 r0 k0
            (((butlast lns, butlast rns, butlast ks), butlast qtodo,
              butlast es, butlast ss, butlast cs, butlast gs, rp), acc)
         < hybrid_state_mu \<delta> l0 r0 k0
            (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
  using safe' inv
        hybrid_state_mu_pop_less[OF nsplit]
        hybrid_cap_invar_pop[OF capinv clr crr csk]
        defl_budget_invar_pop[OF budinv vsplit]
        Pcoeffs
  by simp

lemma defl_body_join_push2:
  fixes rp :: gmp_poly
  assumes stinv: "hybrid_loop_state_invar
                    (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and pre: "hybrid_loop_step_pre
                (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and clr: "length lns = length ks" and crr: "length rns = length ks"
    and csk: "length ss = length ks" and kne: "ks \<noteq> []"
    and lr0: "l0 < r0" and dpos: "0 < \<delta>"
    and ab: "a < b" and wide: "\<delta> < real_of_rat b - real_of_rat a"
    and abnode: "dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks) = (a, b)"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [nd]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, b)]"
    and npush: "hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [Suc (last ks), Suc (last ks)])
                   (butlast es @ [newton_child_exp (last es), newton_child_exp (last es)])
                   (butlast ss @ [sv, sv])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, (a + b) / 2, ec, dk + 1, sv), ((a + b) / 2, b, ec, dk + 1, sv)]"
    and nd_eq: "nd = (a, b, e', dk, sv0)"
    and vpush: "hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [Suc (last ks), Suc (last ks)])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, (a + b) / 2), ((a + b) / 2, b)]"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and svb: "sv \<le> last ss + 1"
    and accd: "(al', ar', ak') = (al, ar, ak)
               \<or> (al', ar', ak') = (al @ [last lns + last rns], ar @ [last lns + last rns],
                         ak @ [Suc (last ks)])"
    and inv: "defl_loop_invar P0 lo
                (((butlast lns @ [2 * last lns, last lns + last rns],
                   butlast rns @ [last lns + last rns, 2 * last rns],
                   butlast ks @ [Suc (last ks), Suc (last ks)]),
                  butlast qtodo @ [ql, qr],
                  butlast es @ [newton_child_exp (last es), newton_child_exp (last es)],
                  butlast ss @ [sv, sv], butlast cs @ [cl, cr],
                  butlast gs @ [gl, gr], rp), (al', ar', ak'))"
  shows "hybrid_loop_safe_invar
            (((butlast lns @ [2 * last lns, last lns + last rns],
               butlast rns @ [last lns + last rns, 2 * last rns],
               butlast ks @ [Suc (last ks), Suc (last ks)]),
              butlast qtodo @ [ql, qr],
              butlast es @ [newton_child_exp (last es), newton_child_exp (last es)],
              butlast ss @ [sv, sv], butlast cs @ [cl, cr], butlast gs @ [gl, gr], rp), (al', ar', ak'))
          \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo
              (((butlast lns @ [2 * last lns, last lns + last rns],
                 butlast rns @ [last lns + last rns, 2 * last rns],
                 butlast ks @ [Suc (last ks), Suc (last ks)]),
                butlast qtodo @ [ql, qr],
                butlast es @ [newton_child_exp (last es), newton_child_exp (last es)],
                butlast ss @ [sv, sv], butlast cs @ [cl, cr], butlast gs @ [gl, gr], rp), (al', ar', ak'))
       \<and> hybrid_state_mu \<delta> l0 r0 k0
            (((butlast lns @ [2 * last lns, last lns + last rns],
               butlast rns @ [last lns + last rns, 2 * last rns],
               butlast ks @ [Suc (last ks), Suc (last ks)]),
              butlast qtodo @ [ql, qr],
              butlast es @ [newton_child_exp (last es), newton_child_exp (last es)],
              butlast ss @ [sv, sv], butlast cs @ [cl, cr], butlast gs @ [gl, gr], rp), (al', ar', ak'))
         < hybrid_state_mu \<delta> l0 r0 k0 (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
proof -
  have lne: "lns \<noteq> []" using kne clr by auto
  have rp_len: "0 < length rp" and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    using pre unfolding hybrid_loop_step_pre_def by simp_all
  have mu1: "dyadic_iv_interval_mu \<delta> (a, (a + b) / 2) < dyadic_iv_interval_mu \<delta> (a, b)"
    and mu2: "dyadic_iv_interval_mu \<delta> ((a + b) / 2, b) < dyadic_iv_interval_mu \<delta> (a, b)"
    by (rule hybrid_mu_halve[OF dpos ab wide])+
  have muL: "dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0
                  ((2 * last lns, last lns + last rns), Suc (last ks)))
             < dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using mu1 by (simp add: hybrid_node_iv_split_children(1)[OF lr0] abnode)
  have muR: "dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0
                  ((last lns + last rns, 2 * last rns), Suc (last ks)))
             < dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using mu2 by (simp add: hybrid_node_iv_split_children(2)[OF lr0] abnode)
  have ndL: "fst (dyadic_iv_node_iv_of l0 r0 k0
                    ((2 * last lns, last lns + last rns), Suc (last ks)))
             < snd (dyadic_iv_node_iv_of l0 r0 k0
                    ((2 * last lns, last lns + last rns), Suc (last ks)))"
    using ab by (simp add: hybrid_node_iv_split_children(1)[OF lr0] abnode)
  have ndR: "fst (dyadic_iv_node_iv_of l0 r0 k0
                    ((last lns + last rns, 2 * last rns), Suc (last ks)))
             < snd (dyadic_iv_node_iv_of l0 r0 k0
                    ((last lns + last rns, 2 * last rns), Suc (last ks)))"
    using ab by (simp add: hybrid_node_iv_split_children(2)[OF lr0] abnode)
  have capinv': "hybrid_cap_invar \<delta> l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [Suc (last ks), Suc (last ks)])
                   (butlast ss @ [sv, sv])"
    \<comment> \<open>\<open>by simp\<close>, not \<open>by rule\<close>: the classic lemma states the pushed depth as
       \<open>last ks + 1\<close> and the shape carries \<open>Suc (last ks)\<close> --- the same term, a different
       FORM, and \<open>rule\<close> matches syntactically.\<close>
    using hybrid_cap_invar_push2[OF capinv clr crr csk kne muL muR svb ndL ndR] by simp
  \<comment> \<open>\<^bold>\<open>The pushed polynomial's two length facts come from the coupling\<close>, not from the arm's SPEC, which is what the
     weakened \<open>safe'\<close> lemma is for: a deflated child is one shorter than its parent's init.\<close>
  have coup': "defl_trunc_coupling
                 (butlast lns @ [2 * last lns, last lns + last rns],
                  butlast rns @ [last lns + last rns, 2 * last rns],
                  butlast ks @ [Suc (last ks), Suc (last ks)])
                 (butlast qtodo @ [ql, qr]) (butlast cs @ [cl, cr])
                 (butlast gs @ [gl, gr]) rp"
    using inv unfolding defl_loop_invar_def by simp
  have nodeR: "defl_node_ok rp (last (butlast lns @ [2 * last lns, last lns + last rns]))
                 (last (butlast rns @ [last lns + last rns, 2 * last rns]))
                 (last (butlast ks @ [Suc (last ks), Suc (last ks)]))
                 (last (butlast qtodo @ [ql, qr]))
                 (last (butlast gs @ [gl, gr])) (last (butlast cs @ [cl, cr]))"
    by (rule defl_trunc_coupling_last[OF coup']) simp
  obtain XR where frR: "node_frame XR qr gr"
    and wrR: "defl_node_wrel (carried_init_same_den (last lns + last rns)
                 (2 ^ Suc (last ks)) (2 * last rns) rp) XR"
    and o3: "hybrid_cs_ok gr cr (carried_descartes_count XR)"
    and leR: "length XR \<le> length rp"
    and o5: "gr \<le> (Suc (last ks) + 1) * length rp \<or> 4398046511104 \<le> gr"
    and o6: "4398046511106 \<le> gr \<longrightarrow> carried_descartes_count XR \<le> gr - 4398046511104"
    and o7: "4398046511104 \<le> gr \<longrightarrow> qr = XR"
    and o8: "4 < cr \<longrightarrow> 4398046511104 \<le> gr"
    and o9: "gr \<le> 4398046511104 + length rp"
    using nodeR by (auto simp: nth_append elim!: defl_node_okE)
  have lenqr: "length XR = length qr" by (rule cdlr_node_frame_len[OF frR])
  have XRnz: "(of_int_poly (Poly XR) :: real poly) \<noteq> 0" by (rule defl_node_wrelD_nz[OF wrR])
  have qpos: "0 < length qr" using XRnz lenqr by (cases XR) auto
  have qle: "length qr \<le> length rp" using lenqr leR by simp
  have accg: "length al' \<le> length al + 1" using accd by auto
  have accinv0: "dyadic_interval_vec_invar (al, ar, ak)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have accinv: "dyadic_interval_vec_invar (al', ar', ak')"
    using accd accinv0 by (auto simp: dyadic_interval_vec_invar_def)
  have lpush: "length (butlast lns @ [2 * last lns, last lns + last rns]) = length lns + 1"
    using lne by simp
  have safe': "hybrid_loop_safe_invar
                 (((butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [Suc (last ks), Suc (last ks)]),
                   butlast qtodo @ [ql, qr],
                   butlast es @ [newton_child_exp (last es), newton_child_exp (last es)],
                   butlast ss @ [sv, sv], butlast cs @ [cl, cr], butlast gs @ [gl, gr], rp),
                  (al', ar', ak'))"
    by (rule defl_loop_safe_invar_push2_all[OF stinv pre budinv capinv' qpos qle
              accg accinv dpos rp_len rp_bound kcap kdepth])
  have budinv': "defl_stack_invar \<delta> l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [Suc (last ks), Suc (last ks)])"
    by (rule defl_budget_invar_push2_branched[where Q = "(al', ar', ak') \<noteq> (al, ar, ak)"
              and al' = al' and ar' = ar' and ak' = ak',
          OF budinv vsplit vpush lpush mu1 mu2]) (use accd in auto)
  have mud: "hybrid_state_mu \<delta> l0 r0 k0
               (((butlast lns @ [2 * last lns, last lns + last rns],
                  butlast rns @ [last lns + last rns, 2 * last rns],
                  butlast ks @ [Suc (last ks), Suc (last ks)]),
                 butlast qtodo @ [ql, qr],
                 butlast es @ [newton_child_exp (last es), newton_child_exp (last es)],
                 butlast ss @ [sv, sv], butlast cs @ [cl, cr], butlast gs @ [gl, gr], rp), (al', ar', ak'))
             < hybrid_state_mu \<delta> l0 r0 k0
               (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    \<comment> \<open>the two drops are \<open>mu1\<close>/\<open>mu2\<close> once \<open>npush\<close> has pinned the children's intervals ---
       the classic arm's own step\<close>
    by (simp only: hybrid_state_mu_simp nsplit npush)
       (rule hybrid_mu_mset_push2_less; use mu1 mu2 nd_eq in simp)
  show ?thesis
    using safe' capinv' budinv' Pcoeffs inv mud by simp
qed
text \<open>\<^bold>\<open>The join for the left-only split push\<close>: the split arm proved the right child empty and pushed the left child
  alone. As in \<open>hybrid_body_step_split\<close>: the cap and budget halves go through the two-push columns of a phantom push
  (\<open>npush\<close>/\<open>vpush\<close> are pure geometry, so no right-child polynomial is needed) and then pop the phantom; safety is
  @{thm [source] defl_loop_safe_invar_push1_all}, with the left child's length facts read off the one-push state's coupling;
  and the measure decreases by @{thm [source] hybrid_mu_mset_push1_less}. \<open>acc\<close> is unchanged, since on \<open>rz\<close> the shed did not
  fire.\<close>

lemma defl_body_join_push1l:
  fixes rp :: gmp_poly
  assumes stinv: "hybrid_loop_state_invar
                    (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and pre: "hybrid_loop_step_pre
                (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and clr: "length lns = length ks" and crr: "length rns = length ks"
    and csk: "length ss = length ks" and kne: "ks \<noteq> []"
    and lr0: "l0 < r0" and dpos: "0 < \<delta>"
    and ab: "a < b" and wide: "\<delta> < real_of_rat b - real_of_rat a"
    and abnode: "dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks) = (a, b)"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [nd]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, b)]"
    \<comment> \<open>the PHANTOM two-push columns: geometry only, no right-child polynomial\<close>
    and npush: "hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [Suc (last ks), Suc (last ks)])
                   (butlast es @ [newton_child_exp (last es), newton_child_exp (last es)])
                   (butlast ss @ [sv, sv])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, (a + b) / 2, ec, dk + 1, sv), ((a + b) / 2, b, ec, dk + 1, sv)]"
    and nd_eq: "nd = (a, b, e', dk, sv0)"
    and vpush: "hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [Suc (last ks), Suc (last ks)])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, (a + b) / 2), ((a + b) / 2, b)]"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and svb: "sv \<le> last ss + 1"
    and inv: "defl_loop_invar P0 lo
                (((butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                   butlast ks @ [Suc (last ks)]),
                  butlast qtodo @ [ql], butlast es @ [newton_child_exp (last es)],
                  butlast ss @ [sv], butlast cs @ [cl], butlast gs @ [gl], rp), (al, ar, ak))"
  shows "hybrid_loop_safe_invar
            (((butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
               butlast ks @ [Suc (last ks)]),
              butlast qtodo @ [ql], butlast es @ [newton_child_exp (last es)],
              butlast ss @ [sv], butlast cs @ [cl], butlast gs @ [gl], rp), (al, ar, ak))
          \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo
              (((butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                 butlast ks @ [Suc (last ks)]),
                butlast qtodo @ [ql], butlast es @ [newton_child_exp (last es)],
                butlast ss @ [sv], butlast cs @ [cl], butlast gs @ [gl], rp), (al, ar, ak))
       \<and> hybrid_state_mu \<delta> l0 r0 k0
            (((butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
               butlast ks @ [Suc (last ks)]),
              butlast qtodo @ [ql], butlast es @ [newton_child_exp (last es)],
              butlast ss @ [sv], butlast cs @ [cl], butlast gs @ [gl], rp), (al, ar, ak))
         < hybrid_state_mu \<delta> l0 r0 k0 (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
proof -
  have lne: "lns \<noteq> []" using kne clr by auto
  have rp_len: "0 < length rp" and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    using pre unfolding hybrid_loop_step_pre_def by simp_all
  have mu1: "dyadic_iv_interval_mu \<delta> (a, (a + b) / 2) < dyadic_iv_interval_mu \<delta> (a, b)"
    and mu2: "dyadic_iv_interval_mu \<delta> ((a + b) / 2, b) < dyadic_iv_interval_mu \<delta> (a, b)"
    by (rule hybrid_mu_halve[OF dpos ab wide])+
  have muL: "dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0
                  ((2 * last lns, last lns + last rns), Suc (last ks)))
             < dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using mu1 by (simp add: hybrid_node_iv_split_children(1)[OF lr0] abnode)
  have muR: "dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0
                  ((last lns + last rns, 2 * last rns), Suc (last ks)))
             < dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using mu2 by (simp add: hybrid_node_iv_split_children(2)[OF lr0] abnode)
  have ndL: "fst (dyadic_iv_node_iv_of l0 r0 k0
                    ((2 * last lns, last lns + last rns), Suc (last ks)))
             < snd (dyadic_iv_node_iv_of l0 r0 k0
                    ((2 * last lns, last lns + last rns), Suc (last ks)))"
    using ab by (simp add: hybrid_node_iv_split_children(1)[OF lr0] abnode)
  have ndR: "fst (dyadic_iv_node_iv_of l0 r0 k0
                    ((last lns + last rns, 2 * last rns), Suc (last ks)))
             < snd (dyadic_iv_node_iv_of l0 r0 k0
                    ((last lns + last rns, 2 * last rns), Suc (last ks)))"
    using ab by (simp add: hybrid_node_iv_split_children(2)[OF lr0] abnode)
  have VL: "length rns = length lns" "length ks = length lns" using clr crr by simp_all
  have SLg: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have BL: "length (butlast lns) = length (butlast rns)"
     "length (butlast rns) = length (butlast ks)"
     "length (butlast es) = length (butlast ks)" "length (butlast ss) = length (butlast ks)"
    using VL SLg by simp_all
  \<comment> \<open>cap: the phantom two-push, then POP the phantom\<close>
  have capG: "hybrid_cap_invar \<delta> l0 r0 k0
                (butlast lns @ [2 * last lns, last lns + last rns],
                 butlast rns @ [last lns + last rns, 2 * last rns],
                 butlast ks @ [Suc (last ks), Suc (last ks)])
                (butlast ss @ [sv, sv])"
    using hybrid_cap_invar_push2[OF capinv clr crr csk kne muL muR svb ndL ndR] by simp
  have cap1: "hybrid_cap_invar \<delta> l0 r0 k0
                (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                 butlast ks @ [Suc (last ks)])
                (butlast ss @ [sv])"
    using hybrid_cap_invar_pop[OF capG] clr crr csk by (simp add: butlast_append)
  \<comment> \<open>the pushed child's two length facts from the one-push state's COUPLING\<close>
  have coup': "defl_trunc_coupling
                 (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                  butlast ks @ [Suc (last ks)])
                 (butlast qtodo @ [ql]) (butlast cs @ [cl]) (butlast gs @ [gl]) rp"
    using inv unfolding defl_loop_invar_def by simp
  have nodeL: "defl_node_ok rp (last (butlast lns @ [2 * last lns]))
                 (last (butlast rns @ [last lns + last rns]))
                 (last (butlast ks @ [Suc (last ks)]))
                 (last (butlast qtodo @ [ql]))
                 (last (butlast gs @ [gl])) (last (butlast cs @ [cl]))"
    by (rule defl_trunc_coupling_last[OF coup']) simp
  obtain XL where frL: "node_frame XL ql gl"
    and wrL: "defl_node_wrel (carried_init_same_den (2 * last lns)
                 (2 ^ Suc (last ks)) (last lns + last rns) rp) XL"
    and leL: "length XL \<le> length rp"
    using nodeL by (auto simp: nth_append elim!: defl_node_okE)
  have lenql: "length XL = length ql" by (rule cdlr_node_frame_len[OF frL])
  have XLnz: "(of_int_poly (Poly XL) :: real poly) \<noteq> 0" by (rule defl_node_wrelD_nz[OF wrL])
  have qpos: "0 < length ql" using XLnz lenql by (cases XL) auto
  have qle: "length ql \<le> length rp" using lenql leL by simp
  have safe1: "hybrid_loop_safe_invar
                 (((butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                    butlast ks @ [Suc (last ks)]),
                   butlast qtodo @ [ql], butlast es @ [newton_child_exp (last es)],
                   butlast ss @ [sv], butlast cs @ [cl], butlast gs @ [gl], rp), (al, ar, ak))"
    by (rule defl_loop_safe_invar_push1_all[OF stinv pre cap1 qpos qle dpos rp_len rp_bound
              kcap kdepth])
  \<comment> \<open>budget: the phantom two-push with an UNCHANGED accumulator, then POP the phantom\<close>
  have lpush: "length (butlast lns @ [2 * last lns, last lns + last rns]) = length lns + 1"
    using lne by simp
  have budG: "defl_stack_invar \<delta> l0 r0 k0
                (butlast lns @ [2 * last lns, last lns + last rns],
                 butlast rns @ [last lns + last rns, 2 * last rns],
                 butlast ks @ [Suc (last ks), Suc (last ks)])"
    by (rule defl_budget_invar_push2_branched[where Q = False
              and al' = al and ar' = ar and ak' = ak,
          OF budinv vsplit vpush lpush mu1 mu2]) auto
  note VD = hybrid_alpha_views_push2_drop(2)[OF BL(1) BL(2) vpush]
  have bud1: "defl_stack_invar \<delta> l0 r0 k0
                (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                 butlast ks @ [Suc (last ks)])"
    using defl_stack_invar_pop[OF budG, where I = "((a + b) / 2, b)"] VD
    by (simp add: butlast_append)
  \<comment> \<open>measure: the one-push nodes are the phantom's minus the right slot\<close>
  have ND1: "hybrid_alpha_nodes l0 r0 k0
               (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                butlast ks @ [Suc (last ks)])
               (butlast es @ [newton_child_exp (last es)]) (butlast ss @ [sv])
             = hybrid_alpha_nodes l0 r0 k0
                 (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
               @ [(a, (a + b) / 2, ec, dk + 1, sv)]"
    by (rule hybrid_alpha_nodes_push2_drop(1)[OF BL npush])
  have mud: "hybrid_state_mu \<delta> l0 r0 k0
               (((butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                  butlast ks @ [Suc (last ks)]),
                 butlast qtodo @ [ql], butlast es @ [newton_child_exp (last es)],
                 butlast ss @ [sv], butlast cs @ [cl], butlast gs @ [gl], rp), (al, ar, ak))
             < hybrid_state_mu \<delta> l0 r0 k0
               (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    by (simp only: hybrid_state_mu_simp nsplit ND1)
       (rule hybrid_mu_mset_push1_less; use mu1 nd_eq in simp)
  show ?thesis
    using safe1 cap1 bud1 Pcoeffs inv mud by simp
qed


text \<open>\<^bold>\<open>The window child's geometry, without the polynomial.\<close> @{thm [source] hybrid_window_geometry_node} goes through
  \<open>try_window_bail_int\<close> and so needs @{thm [source] hybrid_window_pick_abs_node}, whose \<open>X = carried_init_same_den \<dots>\<close> fixes
  the node to its init, which is false on this stack under \<open>gex\<close>, where the window runs on the possibly deflated object.
  The box facts follow instead from @{thm [source] node_iv_window_child_bl}, which mentions no polynomial, and the two \<open>m\<close>
  bounds the shape carries.\<close>

lemma defl_window_geometry_node:
  fixes l r :: int and k e k0 :: nat and m :: int
  assumes lr0: "l0 < r0" and dpos: "0 < \<delta>"
    and ab: "a < b" and wide: "\<delta> < real_of_rat b - real_of_rat a"
    and abnode: "dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k) = (a, b)"
    and m0: "0 \<le> m" and m4: "m + 4 \<le> 2 ^ (2 ^ e + 2)"
  shows "dyadic_iv_interval_mu \<delta>
           (dyadic_iv_node_iv_of l0 r0 k0
              ((l * 2 ^ (2 ^ e + 2) + m * (r - l),
                l * 2 ^ (2 ^ e + 2) + (m + 4) * (r - l)), k + (2 ^ e + 2)))
         < dyadic_iv_interval_mu \<delta> (a, b)"
    and "fst (dyadic_iv_node_iv_of l0 r0 k0
                ((l * 2 ^ (2 ^ e + 2) + m * (r - l),
                  l * 2 ^ (2 ^ e + 2) + (m + 4) * (r - l)), k + (2 ^ e + 2)))
         < snd (dyadic_iv_node_iv_of l0 r0 k0
                ((l * 2 ^ (2 ^ e + 2) + m * (r - l),
                  l * 2 ^ (2 ^ e + 2) + (m + 4) * (r - l)), k + (2 ^ e + 2)))"
proof -
  let ?W = "dyadic_iv_node_iv_of l0 r0 k0
              ((l * 2 ^ (2 ^ e + 2) + m * (r - l),
                l * 2 ^ (2 ^ e + 2) + (m + 4) * (r - l)), k + (2 ^ e + 2))"
  have Nge: "2 \<le> N_of e" by (rule N_of_ge_2)
  have Nne: "(of_nat (4 * N_of e) :: rat) \<noteq> 0" using Nge by simp
  have m4': "m + 4 \<le> int (4 * N_of e)" using m4 by (simp add: four_N_of_pow2)
  have chl: "newton_window_child l r k e m
             = (l * 2 ^ (2 ^ e + 2) + m * (r - l),
                l * 2 ^ (2 ^ e + 2) + (m + 4) * (r - l), k + (2 ^ e + 2))"
    by (simp add: newton_window_child_def Let_def)
  have box: "?W = (a + of_int m * (b - a) / of_nat (4 * N_of e),
                   a + of_int (m + 4) * (b - a) / of_nat (4 * N_of e))"
    using node_iv_window_child_bl[where l = l and r = r and k = k and e = e and m = m
                              and k0 = k0, OF lr0 m4'] chl abnode
    by (simp add: dyadic_iv_node_iv_of_def)
  have abd: "(0 :: rat) < b - a" using ab by simp
  show "fst ?W < snd ?W"
    unfolding box using abd Nne Nge by (simp add: divide_strict_right_mono)
  have widq: "snd ?W - fst ?W = (b - a) / of_nat (N_of e)"
    unfolding box using Nne Nge by (simp add: field_simps)
  have wid: "real_of_rat (snd ?W) - real_of_rat (fst ?W)
           = (real_of_rat b - real_of_rat a) / real (N_of e)"
  proof -
    have "real_of_rat (snd ?W) - real_of_rat (fst ?W) = real_of_rat (snd ?W - fst ?W)"
      by (simp add: of_rat_diff)
    also have "\<dots> = real_of_rat ((b - a) / of_nat (N_of e))" using widq by simp
    also have "\<dots> = (real_of_rat b - real_of_rat a) / real (N_of e)"
      by (simp add: of_rat_divide of_rat_diff)
    finally show ?thesis .
  qed
  have abr: "real_of_rat a < real_of_rat b" using ab by (simp add: of_rat_less)
  show "dyadic_iv_interval_mu \<delta> ?W < dyadic_iv_interval_mu \<delta> (a, b)"
    unfolding dyadic_iv_interval_mu_def
    using mu_subinterval_factor_strict[OF dpos abr wide N_of_ge_2 wid] by simp
qed


section \<open>The body step's single-push join\<close>

lemma defl_body_join_push1:
  fixes rp :: gmp_poly and m :: int
    and lns rns :: "int list" and ks es ss cs gs :: "nat list"
  defines "lw \<equiv> last lns * 2 ^ (2 ^ last es + 2) + m * (last rns - last lns)"
  defines "rw \<equiv> last lns * 2 ^ (2 ^ last es + 2) + (m + 4) * (last rns - last lns)"
  defines "kw \<equiv> last ks + (2 ^ last es + 2)"
  assumes stinv: "hybrid_loop_state_invar
                    (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and pre: "hybrid_loop_step_pre
                (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and clr: "length lns = length ks" and crr: "length rns = length ks"
    and csk: "length ss = length ks" and kne: "ks \<noteq> []"
    and lr0: "l0 < r0" and dpos: "0 < \<delta>"
    and ab: "a < b" and wide: "\<delta> < real_of_rat b - real_of_rat a"
    and abnode: "dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks) = (a, b)"
    and m0: "0 \<le> m" and m4: "m + 4 \<le> 2 ^ (2 ^ last es + 2)"
    and jle: "int (2 ^ last es + 2) \<le> int (2 ^ newton_pol_ecap + 2)"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [nd]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, b)]"
    and npush: "hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [lw], butlast rns @ [rw], butlast ks @ [kw])
                   (butlast es @ [last es + 1]) (butlast ss @ [last ss])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((lw, rw), kw)),
                       snd (dyadic_iv_node_iv_of l0 r0 k0 ((lw, rw), kw)),
                       ecw, dkw, last ss)]"
    and nd_eq: "nd = (a, b, e', dk, sv0)"
    and vpush: "hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [lw], butlast rns @ [rw], butlast ks @ [kw])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [dyadic_iv_node_iv_of l0 r0 k0 ((lw, rw), kw)]"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and inv: "defl_loop_invar P0 lo
                (((butlast lns @ [lw], butlast rns @ [rw], butlast ks @ [kw]),
                  butlast qtodo @ [cand], butlast es @ [last es + 1],
                  butlast ss @ [last ss], butlast cs @ [cwv], butlast gs @ [gwv], rp),
                 (al, ar, ak))"
  shows "hybrid_loop_safe_invar
            (((butlast lns @ [lw], butlast rns @ [rw], butlast ks @ [kw]),
              butlast qtodo @ [cand], butlast es @ [last es + 1],
              butlast ss @ [last ss], butlast cs @ [cwv], butlast gs @ [gwv], rp),
             (al, ar, ak))
          \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo
              (((butlast lns @ [lw], butlast rns @ [rw], butlast ks @ [kw]),
                butlast qtodo @ [cand], butlast es @ [last es + 1],
                butlast ss @ [last ss], butlast cs @ [cwv], butlast gs @ [gwv], rp),
               (al, ar, ak))
       \<and> hybrid_state_mu \<delta> l0 r0 k0
            (((butlast lns @ [lw], butlast rns @ [rw], butlast ks @ [kw]),
              butlast qtodo @ [cand], butlast es @ [last es + 1],
              butlast ss @ [last ss], butlast cs @ [cwv], butlast gs @ [gwv], rp),
             (al, ar, ak))
         < hybrid_state_mu \<delta> l0 r0 k0 (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
proof -
  have lne: "lns \<noteq> []" using kne clr by auto
  have rp_len: "0 < length rp" and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    using pre unfolding hybrid_loop_step_pre_def by simp_all
  have muW: "dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv_of l0 r0 k0 ((lw, rw), kw))
             < dyadic_iv_interval_mu \<delta>
                 (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    and ndW: "fst (dyadic_iv_node_iv_of l0 r0 k0 ((lw, rw), kw))
              < snd (dyadic_iv_node_iv_of l0 r0 k0 ((lw, rw), kw))"
    unfolding lw_def rw_def kw_def
    using defl_window_geometry_node[OF lr0 dpos ab wide abnode m0 m4] abnode by simp_all
  have capinv': "hybrid_cap_invar \<delta> l0 r0 k0
                   (butlast lns @ [lw], butlast rns @ [rw], butlast ks @ [kw])
                   (butlast ss @ [last ss])"
    by (rule hybrid_cap_invar_push1[OF capinv clr crr csk kne muW _ jle ndW])
       (simp add: kw_def)
  have coup': "defl_trunc_coupling
                 (butlast lns @ [lw], butlast rns @ [rw], butlast ks @ [kw])
                 (butlast qtodo @ [cand]) (butlast cs @ [cwv]) (butlast gs @ [gwv]) rp"
    using inv unfolding defl_loop_invar_def by simp
  have nodeW: "defl_node_ok rp (last (butlast lns @ [lw])) (last (butlast rns @ [rw]))
                 (last (butlast ks @ [kw])) (last (butlast qtodo @ [cand]))
                 (last (butlast gs @ [gwv])) (last (butlast cs @ [cwv]))"
    by (rule defl_trunc_coupling_last[OF coup']) simp
  obtain XW where frW: "node_frame XW cand gwv"
    and wrW: "defl_node_wrel (carried_init_same_den lw (2 ^ kw) rw rp) XW"
    and w3: "hybrid_cs_ok gwv cwv (carried_descartes_count XW)"
    and leW: "length XW \<le> length rp"
    and w5: "gwv \<le> (kw + 1) * length rp \<or> 4398046511104 \<le> gwv"
    and w6: "4398046511106 \<le> gwv \<longrightarrow> carried_descartes_count XW \<le> gwv - 4398046511104"
    and w7: "4398046511104 \<le> gwv \<longrightarrow> cand = XW"
    and w8: "4 < cwv \<longrightarrow> 4398046511104 \<le> gwv"
    and w9: "gwv \<le> 4398046511104 + length rp"
    using nodeW by (auto simp: nth_append elim!: defl_node_okE)
  have lenc: "length XW = length cand" by (rule cdlr_node_frame_len[OF frW])
  have XWnz: "(of_int_poly (Poly XW) :: real poly) \<noteq> 0" by (rule defl_node_wrelD_nz[OF wrW])
  have qpos: "0 < length cand" using XWnz lenc by (cases XW) auto
  have qle: "length cand \<le> length rp" using lenc leW by simp
  have safe': "hybrid_loop_safe_invar
                 (((butlast lns @ [lw], butlast rns @ [rw], butlast ks @ [kw]),
                   butlast qtodo @ [cand], butlast es @ [last es + 1],
                   butlast ss @ [last ss], butlast cs @ [cwv], butlast gs @ [gwv], rp),
                  (al, ar, ak))"
    by (rule defl_loop_safe_invar_push1_all[OF stinv pre capinv' qpos qle dpos
              rp_len rp_bound kcap kdepth])
  have lpush: "length (butlast lns @ [lw]) \<le> length lns" using lne by simp
  have budinv': "defl_stack_invar \<delta> l0 r0 k0
                   (butlast lns @ [lw], butlast rns @ [rw], butlast ks @ [kw])"
    by (rule defl_budget_invar_push1[OF budinv vsplit vpush lpush _ order_refl])
       (use muW abnode in simp)
  have mud: "hybrid_state_mu \<delta> l0 r0 k0
               (((butlast lns @ [lw], butlast rns @ [rw], butlast ks @ [kw]),
                 butlast qtodo @ [cand], butlast es @ [last es + 1],
                 butlast ss @ [last ss], butlast cs @ [cwv], butlast gs @ [gwv], rp),
                (al, ar, ak))
             < hybrid_state_mu \<delta> l0 r0 k0
               (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    by (simp only: hybrid_state_mu_simp nsplit npush)
       (rule hybrid_mu_mset_push1_less; use muW abnode nd_eq in simp)
  show ?thesis
    using safe' capinv' budinv' Pcoeffs inv mud by simp
qed


section \<open>The pop \<open>safe'\<close> lemma, weakened like the two push lemmas\<close>

lemma defl_loop_safe_invar_pop_all:
  assumes stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    \<comment> \<open>\<^bold>\<open>The deflating coupling.\<close> The non-deflating version takes @{const hybrid_trunc_coupling}, which fixes every
       node to its init and so gives \<open>length (qtodo ! i) = length rp\<close>, false once a child has been deflated. The proof uses only
       the pair @{const defl_node_ok} carries.\<close>
    and cpl: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and dpos: "0 < \<delta>"
    and rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_loop_safe_invar
           (((butlast lns, butlast rns, butlast ks), butlast qtodo,
             butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
proof -
  have L: "length lns = length qtodo" "length rns = length qtodo"
     and K: "length ks = length qtodo" "length gs = length qtodo"
    using cpl unfolding defl_trunc_coupling_def by simp_all
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have body: "\<And>i. i < length qtodo \<Longrightarrow>
      defl_node_ok rp (lns ! i) (rns ! i) (ks ! i) (qtodo ! i) (gs ! i) (cs ! i)"
    using cpl unfolding defl_trunc_coupling_def by simp
  have qlen: "\<And>i. i < length qtodo \<Longrightarrow>
      0 < length (qtodo ! i) \<and> length (qtodo ! i) \<le> length rp"
  proof -
    fix i :: nat assume ilt: "i < length qtodo"
    obtain XI where fr: "node_frame XI (qtodo ! i) (gs ! i)"
      and wr: "defl_node_wrel
                 (carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp) XI"
      and b3: "hybrid_cs_ok (gs ! i) (cs ! i) (carried_descartes_count XI)"
      and ble: "length XI \<le> length rp"
      and b5: "gs ! i \<le> (ks ! i + 1) * length rp \<or> 4398046511104 \<le> gs ! i"
      and b6: "4398046511106 \<le> gs ! i
                 \<longrightarrow> carried_descartes_count XI \<le> gs ! i - 4398046511104"
      and b7: "4398046511104 \<le> gs ! i \<longrightarrow> qtodo ! i = XI"
      and b8: "4 < cs ! i \<longrightarrow> 4398046511104 \<le> gs ! i"
      and b9: "gs ! i \<le> 4398046511104 + length rp"
      by (rule defl_node_okE[OF body[OF ilt]])
    have leq: "length XI = length (qtodo ! i)" by (rule cdlr_node_frame_len[OF fr])
    have nz: "(of_int_poly (Poly XI) :: real poly) \<noteq> 0" by (rule defl_node_wrelD_nz[OF wr])
    have pos: "0 < length (qtodo ! i)" using nz leq by (cases XI) auto
    show "0 < length (qtodo ! i) \<and> length (qtodo ! i) \<le> length rp"
      using pos leq ble by simp
  qed
  have stinv': "hybrid_loop_state_invar
                  (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                    butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
    by (rule hybrid_loop_state_invar_pop[OF stinv])
  show ?thesis
  proof (cases "butlast lns = []")
    case True
    \<comment> \<open>the popped worklist is empty, so the loop condition is false and \<open>step_pre\<close> is not
       required at all -- \<open>safe_invar\<close> is then just the state invariant.\<close>
    thus ?thesis
      using stinv' by (simp add: hybrid_loop_safe_invar_def hybrid_loop_cond_def)
  next
    case False
    hence lne': "butlast lns \<noteq> []" .
    have lgt: "1 < length lns" using lne' by (simp add: butlast_ne_iff)
    have ilt: "length ks - 2 < length ks" using lgt K SL by simp
    have iltq: "length qtodo - 2 < length qtodo" using lgt SL by simp
    have ne': "butlast qtodo \<noteq> []" "butlast es \<noteq> []" "butlast ss \<noteq> []"
       "butlast cs \<noteq> []" "butlast gs \<noteq> []" "butlast ks \<noteq> []" "butlast rns \<noteq> []"
      using lgt SL K L(2) by (simp_all add: butlast_ne_iff)
    \<comment> \<open>the three column-VALUE facts, at the index that is about to become last.\<close>
    have kb1: "int (ks ! (length ks - 2)) + 1 \<le> hybrid_root_potential \<delta> k0"
      by (rule hybrid_cap_invar_depth_succ_le[OF capinv ilt dpos])
    have kb2: "int (ks ! (length ks - 2)) \<le> hybrid_root_potential \<delta> k0"
      by (rule hybrid_cap_invar_depth_le[OF capinv ilt])
    have sb: "ss ! (length ks - 2) \<le> ks ! (length ks - 2)"
      by (rule hybrid_cap_invar_sigma_nth[OF capinv]) (use ilt SL K in simp)
    \<comment> \<open>as NAT facts at the index first; the \<open>last\<close>-form rewrite is then pure bookkeeping with no
       coercion in it.\<close>
    have kbn: "ks ! (length ks - 2) + 1 < max_snat LENGTH(gmp_poly_len)"
      using kb1 kcap by linarith
    have kbp: "ks ! (length ks - 2) * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
      by (rule kdepth[OF kb2])
    have sbn: "ss ! (length ks - 2) + 1 < max_snat LENGTH(gmp_poly_len)"
      using sb kbn by simp
    have kb1': "last (butlast ks) + 1 < max_snat LENGTH(gmp_poly_len)"
      using kbn by (simp add: last_butlast_conv_nth[OF ne'(6)])
    have kb2': "last (butlast ks) * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
      using kbp by (simp add: last_butlast_conv_nth[OF ne'(6)])
    have sb': "last (butlast ss) + 1 < max_snat LENGTH(gmp_poly_len)"
      using sbn by (simp add: last_butlast_conv_nth[OF ne'(3)] SL K)
    have Qle: "length (last (butlast qtodo)) \<le> length rp"
      and Qne2: "0 < length (last (butlast qtodo))"
      using qlen[OF iltq] by (simp_all add: last_butlast_conv_nth[OF ne'(1)])
    \<comment> \<open>and non-emptiness, which \<open>step_pre\<close> states as \<open>0 < length \<dots>\<close> but \<open>simp\<close> normalises to
       \<open>\<noteq> []\<close> -- it does not cross that on its own from the length equation.\<close>
    have Qne': "last (butlast qtodo) \<noteq> []"
      using Qne2 length_greater_0_conv[of "last (butlast qtodo)"] by blast
    have Qcap: "length (last (butlast qtodo)) + 1 < max_snat LENGTH(gmp_poly_len)"
      using Qle rp_bound by simp
    note Pu = pre[unfolded hybrid_loop_step_pre_def]
    show ?thesis
      unfolding hybrid_loop_safe_invar_def hybrid_loop_step_pre_def
    proof (intro conjI impI)
      show "hybrid_loop_state_invar
              (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
        by (rule stinv')
    \<comment> \<open>\<open>Qne'\<close> goes in the \<open>add:\<close> list, not the \<open>use\<close> list: as a chained fact \<open>simp\<close> discards it
       (derivable from \<open>Qlen\<close> and \<open>rp_len\<close> in context, so it counts as trivial) and the goal it
       would have closed survives; as a simp RULE a non-equational fact becomes \<open>A \<equiv> True\<close> and
       rewrites that goal away.\<close>
    qed (use lne' ne' Pu kb1' kb2' sb' Qcap rp_len rp_bound SL K in
           \<open>simp_all add: dyadic_interval_vec_pushable2_def dyadic_interval_vec_pushable_def
                          butlast_ne_iff butlast_cap_mono Qne' Qne2\<close>)
  qed
qed

text \<open>\<^bold>\<open>The POP join, with the accumulator DECOUPLED from the budget's.\<close>
  @{thm [source] defl_body_join_pop} ties \<open>safe\<close>\<open>'\<close> and @{const hybrid_budget_invar} to the
  same \<open>acc\<close>, which is right for the reject arm and wrong for the accept arm: that one pops the
  worklist AND grows the accumulator, so the budget it starts from is at the OLD accumulator and
  the one it owes is at the new. @{thm [source] hybrid_budget_invar_accept} is the classic's
  bridge and it takes the growth as a LENGTH bound, which covers the unchanged branch too --- so
  one lemma serves both POP shapes.\<close>

lemma defl_body_join_pop_acc:
  fixes rp :: gmp_poly
  assumes safe': "hybrid_loop_safe_invar
                    (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                      butlast es, butlast ss, butlast cs, butlast gs, rp), (al', ar', ak'))"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and accg: "length al' \<le> length al + 1"
    and clr: "length lns = length ks" and crr: "length rns = length ks"
    and csk: "length ss = length ks"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [nd]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [I]"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and inv: "defl_loop_invar P0 lo
                (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                  butlast es, butlast ss, butlast cs, butlast gs, rp), (al', ar', ak'))"
  \<comment> \<open>\<^bold>\<open>RIGHT-associated\<close>, which is the form \<open>clarsimp\<close> leaves the body step's goal in:
     \<open>conj_assoc\<close> is a simp rule, so the \<open>(A \<and> B) \<and> C\<close> of
     @{thm [source] defl_loop_correct}'s step obligation arrives here as \<open>A \<and> B \<and> C\<close>,
     a different TERM.\<close>
  shows "hybrid_loop_safe_invar
            (((butlast lns, butlast rns, butlast ks), butlast qtodo,
              butlast es, butlast ss, butlast cs, butlast gs, rp), (al', ar', ak'))
       \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo
              (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                butlast es, butlast ss, butlast cs, butlast gs, rp), (al', ar', ak'))
       \<and> hybrid_state_mu \<delta> l0 r0 k0
            (((butlast lns, butlast rns, butlast ks), butlast qtodo,
              butlast es, butlast ss, butlast cs, butlast gs, rp), (al', ar', ak'))
         < hybrid_state_mu \<delta> l0 r0 k0
            (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
  using safe' inv
        hybrid_state_mu_pop_less[OF nsplit]
        hybrid_cap_invar_pop[OF capinv clr crr csk]
        defl_budget_invar_accept[OF budinv vsplit accg]
        Pcoeffs
  by simp



section \<open>The body step: the three cases of the arm shape, joined\<close>

text \<open>\<^bold>\<open>The last lemma of step 3.\<close> @{thm [source] defl_loop_step_args_step} delivers
  @{const defl_loop_invar} and @{const defl_arm_shape} at the result state; this unfolds the
  shape, eliminates the disjunction and applies the three joins. Five branches: two POP (the
  reject arm, and the count-one arm which also EMITS), two PUSH2 (both split arms and the
  gate-open arms' reject half, with and without the midpoint root) and one PUSH1 (the
  gate-open arms' accept half).

  \<^bold>\<open>Three traps, all paid for here, none of them mathematical.\<close>

  \<^item> \<open>clarsimp\<close> runs while the shape is still a DISJUNCTION, so it destructures the state
    tuple but the per-branch equations are sealed inside the disjuncts. \<^bold>\<open>A second
    \<open>clarsimp\<close> after the \<open>elim disjE\<close>\<close> is what substitutes them; without it every goal stays
    at opaque parameters \<open>a aa b ab \<dots>\<close> while the joins conclude at the concrete columns, and
    the mismatch reads exactly like a wrong fact.
  \<^item> \<^bold>\<open>\<open>OF\<close> on a \<open>\<And>\<close>-quantified CONDITIONAL fact re-adds that fact's own hypothesis as a
    fresh premise AHEAD of the remaining ones\<close>, so every later \<open>OF\<close> position shifts by one and
    the whole \<open>[OF \<dots>]\<close> term fails to elaborate --- \<open>exception THM 0 \<dots> OF: no unifiers\<close>, which
    names the rule but not the slot. \<open>kdepth\<close> is the fact; either follow it with an explicit
    \<open>apply assumption\<close> (the PUSH2 branches) or supply it LAST (the PUSH1 branch).
  \<^item> The bail file states the window's grid bound in \<open>N_of\<close> form
    (@{thm [source] newton_window_pick_bail_m_bound}: \<open>m + 4 \<le> int (4 * N_of e)\<close>) while
    @{thm [source] defl_body_join_push1} takes the power form. \<open>Nnat\<close> below is that lemma's own
    internal bridge, restated.

  \<^bold>\<open>\<open>npushw\<close>/\<open>vpushw\<close> stay premises\<close>, exactly as the classic
  @{thm [source] hybrid_body_step_window_assembled} keeps its own \<open>npush_w\<close>/\<open>vpush_w\<close>: the
  split push's twins are derived below from @{thm [source] hybrid_npush_split_satisfiable} and
  @{thm [source] hybrid_alpha_views_append2}, but the window's have no such supplier yet.\<close>

text \<open>\<^bold>\<open>The accept-POP shape's \<open>safe\<close>': the accumulator GREW.\<close>
  @{thm [source] defl_loop_safe_invar_pop_all} ties its conclusion to the same \<open>acc\<close> its
  \<open>stinv\<close>/\<open>pre\<close> premises are stated at, which is right for the reject arm and wrong for the
  count-one arm --- that one pops the worklist AND emits, so the state it must satisfy
  \<open>hybrid_loop_safe_invar\<close> at carries a LONGER accumulator. Only two conjuncts see \<open>acc\<close> at
  all (@{const dyadic_interval_vec_invar} inside the state invariant, and
  @{const dyadic_interval_vec_pushable} inside \<open>step_pre\<close>), so this is a post-hoc swap rather
  than a fourth clone of the 130-line proof: \<open>accinv\<close> is three length equations and
  @{thm [source] hybrid_budget_invar_acc_grown} pays the extra slot, exactly as the two-child
  twin already does.\<close>

lemma defl_loop_safe_invar_acc_swap:
  assumes safe0: "hybrid_loop_safe_invar
                    (((lns', rns', ks'), qtodo', es', ss', cs', gs', rp), (al, ar, ak))"
    and budinv: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and lne: "lns \<noteq> []"
    and l1: "length rns = length lns" and l2: "length ks = length lns"
    and accg: "length al' \<le> length al + 1"
    and accinv: "dyadic_interval_vec_invar (al', ar', ak')"
  shows "hybrid_loop_safe_invar
           (((lns', rns', ks'), qtodo', es', ss', cs', gs', rp), (al', ar', ak'))"
proof -
  have acap: "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
    by (rule defl_budget_invar_acc_grown[OF budinv lne l1 l2])
  have apush: "dyadic_interval_vec_pushable (al', ar', ak')"
    using acap accg accinv
    unfolding dyadic_interval_vec_pushable_def dyadic_interval_vec_invar_def by simp
  show ?thesis
    unfolding hybrid_loop_safe_invar_def
  proof (intro conjI impI)
    show "hybrid_loop_state_invar
            (((lns', rns', ks'), qtodo', es', ss', cs', gs', rp), (al', ar', ak'))"
      using safe0 accinv
      unfolding hybrid_loop_safe_invar_def
      by (simp add: hybrid_loop_state_invar_def dyadic_interval_vec_invar_def Let_def)
  next
    \<comment> \<open>the loop condition reads \<open>lns\<close>\<open>'\<close> only, so it transfers to the old accumulator
       verbatim and \<open>safe0\<close>'s implication fires.\<close>
    assume cnd: "hybrid_loop_cond
                   (((lns', rns', ks'), qtodo', es', ss', cs', gs', rp), (al', ar', ak'))"
    hence cnd0: "hybrid_loop_cond
                   (((lns', rns', ks'), qtodo', es', ss', cs', gs', rp), (al, ar, ak))"
      by (simp add: hybrid_loop_cond_def)
    have pre0: "hybrid_loop_step_pre
                  (((lns', rns', ks'), qtodo', es', ss', cs', gs', rp), (al, ar, ak))"
      using safe0 cnd0 unfolding hybrid_loop_safe_invar_def by simp
    \<comment> \<open>project \<open>step_pre\<close> FIRST, then swap: chaining \<open>safe0\<close> itself leaves \<open>simp\<close> with the
       implication still wrapped, and it then normalises \<open>length (butlast qtodo\<open>'\<close>) + 2\<close> in the
       GOAL (using \<open>qtodo\<open>'\<close> \<noteq> []\<close>) but not inside the premise's conjunction, so the two
       stop matching.\<close>
    show "hybrid_loop_step_pre
            (((lns', rns', ks'), qtodo', es', ss', cs', gs', rp), (al', ar', ak'))"
      using pre0 apush unfolding hybrid_loop_step_pre_def by auto
  qed
qed


lemma defl_body_step:
  fixes rp :: gmp_poly
  assumes cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and safe: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and stinvar: "defl_state_invar \<delta> P l0 r0 k0 P0 lo
                    (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    \<comment> \<open>\<^bold>\<open>The accumulator capacity, supplied by the caller\<close> (see
       @{const defl_budget_invar}); the geometry-carrying loop derives it from the emitted
       windows' disjointness.\<close>
    and accroom: "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
    and lr0: "l0 < r0" and dpos: "0 < \<delta>"
    \<comment> \<open>\<^bold>\<open>This replaces an unconditional \<open>wide\<close> premise\<close>, which would be false for a narrow popped node. \<open>wide\<close> is used
       at exactly three places below, all inside the push joins, and on those branches the arm shape supplies a witness, so
       the caller owes the conditional form, which \<open>defl_node_wide_of_count2\<close> provides.\<close>
    and smalld: "\<And>Y. (of_int_poly (Poly Y) :: real poly)
                        dvd (of_int_poly (Poly (carried_init_same_den (last lns)
                               (2 ^ last ks) (last rns) rp)) :: real poly)
                      \<Longrightarrow> 2 \<le> carried_descartes_count Y
                      \<Longrightarrow> \<delta> < real_of_rat (snd (dyadic_iv_node_iv_of l0 r0 k0
                                   ((last lns, last rns), last ks)))
                            - real_of_rat (fst (dyadic_iv_node_iv_of l0 r0 k0
                                   ((last lns, last rns), last ks)))"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the WINDOW push's two alpha facts. The split push's twins are DERIVED below from
       @{thm [source] hybrid_npush_split_satisfiable} / @{thm [source] hybrid_alpha_views_append2};
       the window's have no such supplier yet, so they stay premises exactly as the classic
       @{thm [source] hybrid_body_step_window_assembled} keeps its own \<open>npush_w\<close>/\<open>vpush_w\<close>.\<close>
    and npushw: "\<And>m. hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [last lns * 2 ^ (2 ^ last es + 2) + m * (last rns - last lns)],
                    butlast rns @ [last lns * 2 ^ (2 ^ last es + 2)
                                     + (m + 4) * (last rns - last lns)],
                    butlast ks @ [last ks + (2 ^ last es + 2)])
                   (butlast es @ [last es + 1]) (butlast ss @ [last ss])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(fst (dyadic_iv_node_iv_of l0 r0 k0
                             ((last lns * 2 ^ (2 ^ last es + 2) + m * (last rns - last lns),
                               last lns * 2 ^ (2 ^ last es + 2)
                                 + (m + 4) * (last rns - last lns)),
                              last ks + (2 ^ last es + 2))),
                       snd (dyadic_iv_node_iv_of l0 r0 k0
                             ((last lns * 2 ^ (2 ^ last es + 2) + m * (last rns - last lns),
                               last lns * 2 ^ (2 ^ last es + 2)
                                 + (m + 4) * (last rns - last lns)),
                              last ks + (2 ^ last es + 2))),
                       ecw m, dkw m, last ss)]"
    and vpushw: "\<And>m. hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [last lns * 2 ^ (2 ^ last es + 2) + m * (last rns - last lns)],
                    butlast rns @ [last lns * 2 ^ (2 ^ last es + 2)
                                     + (m + 4) * (last rns - last lns)],
                    butlast ks @ [last ks + (2 ^ last es + 2)])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [dyadic_iv_node_iv_of l0 r0 k0
                        ((last lns * 2 ^ (2 ^ last es + 2) + m * (last rns - last lns),
                          last lns * 2 ^ (2 ^ last es + 2) + (m + 4) * (last rns - last lns)),
                         last ks + (2 ^ last es + 2))]"
    and arm: "defl_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
              \<le> SPEC (\<lambda>x.
                    defl_loop_invar P0 lo x
                  \<and> defl_arm_shape (butlast lns) (butlast rns) (butlast ks) (butlast qtodo)
                      (butlast es) (butlast ss) (butlast cs) (butlast gs) (al, ar, ak) rp
                      (last lns) (last rns) (last ks) (last es) (last ss) x)"
  shows "defl_loop_body_checked_monadic (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
proof -
  have capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and stkinv: "defl_stack_invar \<delta> l0 r0 k0 (lns, rns, ks)"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and inv0: "defl_loop_invar P0 lo (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using stinvar by simp_all
  have budinv: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    by (rule defl_budget_invarI[OF stkinv accroom])
  have cpl: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    using inv0 unfolding defl_loop_invar_def by simp
  have stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe unfolding hybrid_loop_safe_invar_def by simp
  have pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have lne: "lns \<noteq> []" using cond by (simp add: hybrid_loop_cond_def)
  have ne: "qtodo \<noteq> []" "es \<noteq> []" "ss \<noteq> []" "cs \<noteq> []" "gs \<noteq> []" "ks \<noteq> []" "rns \<noteq> []"
    using lne SL VL by auto
  have CL: "length lns = length ks" "length rns = length ks" "length ss = length ks"
    using VL SL by simp_all
  have BL: "length (butlast lns) = length (butlast rns)"
     "length (butlast rns) = length (butlast ks)"
     "length (butlast es) = length (butlast ks)"
     "length (butlast ss) = length (butlast ks)"
    using VL SL by simp_all
  define a where "a = fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
  define b where "b = snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
  have abnode: "dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks) = (a, b)"
    unfolding a_def b_def by simp
  have ilast: "length ks - 1 < length ks" using ne(6) by simp
  have ab: "a < b"
    using hybrid_cap_invar_nondeg[OF capinv ilast] lne ne VL
    unfolding a_def b_def by (simp add: last_conv_nth)
  have smalld': "\<And>Y. (of_int_poly (Poly Y) :: real poly)
                          dvd (of_int_poly (Poly (carried_init_same_den (last lns)
                                 (2 ^ last ks) (last rns) rp)) :: real poly)
                        \<Longrightarrow> 2 \<le> carried_descartes_count Y
                        \<Longrightarrow> \<delta> < real_of_rat b - real_of_rat a"
    using smalld unfolding a_def b_def by simp
  have nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
       = hybrid_alpha_nodes l0 r0 k0
           (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
         @ [(a, b, last es, last ks, last ss)]"
    using hybrid_alpha_nodes_pop_decomp[OF lne VL(1) VL(2) SL(2) SL(3)]
    unfolding a_def b_def by simp
  have vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
       = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks) @ [(a, b)]"
    using hybrid_alpha_views_pop_decomp[OF lne VL(1) VL(2)] unfolding a_def b_def by simp
  have npush2: "\<And>sv. hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [Suc (last ks), Suc (last ks)])
                   (butlast es @ [newton_child_exp (last es), newton_child_exp (last es)])
                   (butlast ss @ [sv, sv])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, (a + b) / 2, max 1 (last es - 1), last ks + 1, sv),
                      ((a + b) / 2, b, max 1 (last es - 1), last ks + 1, sv)]"
    using hybrid_npush_split_satisfiable[OF BL(1) BL(2) BL(3) BL(4)
              hybrid_node_iv_split_children(1)[OF lr0]
              hybrid_node_iv_split_children(2)[OF lr0] newton_child_exp_eq refl]
    unfolding a_def b_def by simp
  have vpush2: "hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [Suc (last ks), Suc (last ks)])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, (a + b) / 2), ((a + b) / 2, b)]"
    using hybrid_alpha_views_append2[OF BL(1) BL(2),
            of l0 r0 k0 "2 * last lns" "last lns + last rns" "last lns + last rns"
               "2 * last rns" "Suc (last ks)" "Suc (last ks)"]
          hybrid_node_iv_split_children(1)[OF lr0] hybrid_node_iv_split_children(2)[OF lr0]
    unfolding a_def b_def by simp
  have rp_len: "0 < length rp" and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    using pre unfolding hybrid_loop_step_pre_def by simp_all
  have safepop: "hybrid_loop_safe_invar
                   (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                     butlast es, butlast ss, butlast cs, butlast gs, rp), (al, ar, ak))"
    by (rule defl_loop_safe_invar_pop_all[OF stinv pre cpl capinv dpos rp_len rp_bound
              kcap kdepth])
  have ACL: "length al = length ar" "length ar = length ak"
    using stinv unfolding hybrid_loop_state_invar_def dyadic_interval_vec_invar_def
    by (simp_all add: Let_def)
  have accg0: "length al \<le> length al + 1" by simp
  have accg1: "length (al @ [last lns]) \<le> length al + 1" by simp
  have accinv1: "dyadic_interval_vec_invar (al @ [last lns], ar @ [last rns], ak @ [last ks])"
    using ACL unfolding dyadic_interval_vec_invar_def by simp
  have safeacc: "hybrid_loop_safe_invar
                   (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                     butlast es, butlast ss, butlast cs, butlast gs, rp),
                    (al @ [last lns], ar @ [last rns], ak @ [last ks]))"
    by (rule defl_loop_safe_invar_acc_swap[OF safepop budinv lne VL(1) VL(2) accg1 accinv1])

  have B1: "defl_loop_invar P0 lo
(((butlast lns, butlast rns, butlast ks), butlast qtodo, butlast es,
butlast ss, butlast cs, butlast gs, rp),
al, ar, ak) \<Longrightarrow>
hybrid_loop_safe_invar
(((butlast lns, butlast rns, butlast ks), butlast qtodo, butlast es,
butlast ss, butlast cs, butlast gs, rp),
al, ar, ak) \<and>
defl_state_invar \<delta> P l0 r0 k0 P0 lo
(((butlast lns, butlast rns, butlast ks), butlast qtodo, butlast es,
butlast ss, butlast cs, butlast gs, rp),
al, ar, ak) \<and>
hybrid_state_mu \<delta> l0 r0 k0
(((butlast lns, butlast rns, butlast ks), butlast qtodo, butlast es,
butlast ss, butlast cs, butlast gs, rp),
al, ar, ak)
< hybrid_state_mu \<delta> l0 r0 k0
(((lns, rns, ks), qtodo, es, ss, cs, gs, rp), al, ar, ak)"
    by (rule defl_body_join_pop_acc[OF safepop capinv budinv accg0 CL(1) CL(2) CL(3)
              nsplit vsplit Pcoeffs], assumption)

  have B2: "defl_loop_invar P0 lo
(((butlast lns, butlast rns, butlast ks), butlast qtodo, butlast es,
butlast ss, butlast cs, butlast gs, rp),
al @ [last lns], ar @ [last rns], ak @ [last ks]) \<Longrightarrow>
hybrid_loop_safe_invar
(((butlast lns, butlast rns, butlast ks), butlast qtodo, butlast es,
butlast ss, butlast cs, butlast gs, rp),
al @ [last lns], ar @ [last rns], ak @ [last ks]) \<and>
defl_state_invar \<delta> P l0 r0 k0 P0 lo
(((butlast lns, butlast rns, butlast ks), butlast qtodo, butlast es,
butlast ss, butlast cs, butlast gs, rp),
al @ [last lns], ar @ [last rns], ak @ [last ks]) \<and>
hybrid_state_mu \<delta> l0 r0 k0
(((butlast lns, butlast rns, butlast ks), butlast qtodo, butlast es,
butlast ss, butlast cs, butlast gs, rp),
al @ [last lns], ar @ [last rns], ak @ [last ks])
< hybrid_state_mu \<delta> l0 r0 k0
(((lns, rns, ks), qtodo, es, ss, cs, gs, rp), al, ar, ak)"
    by (rule defl_body_join_pop_acc[OF safeacc capinv budinv accg1 CL(1) CL(2) CL(3)
              nsplit vsplit Pcoeffs], assumption)

  \<comment> \<open>\<^bold>\<open>The case split is placed here\<close> because \<open>B1\<close>/\<open>B2\<close>, the two pop branches, do not mention \<open>wide\<close> and serve both
     cases, while \<open>B3\<close>/\<open>B4\<close>/\<open>B5\<close> are the three push branches; naming the \<open>True\<close> case \<open>wide'\<close> lets their apply scripts use it
     as a premise.\<close>
  show ?thesis
  proof (cases "\<delta> < real_of_rat b - real_of_rat a")
    case wide': True
    have B3: "\<And>ql cl qr cr gl gr sv.
  \<lbrakk>defl_loop_invar P0 lo
  (((butlast lns @ [2 * last lns, last lns + last rns],
  butlast rns @ [last lns + last rns, 2 * last rns],
  butlast ks @ [Suc (last ks), Suc (last ks)]),
  butlast qtodo @ [ql, qr],
  butlast es @
  [newton_child_exp (last es), newton_child_exp (last es)],
  butlast ss @ [sv, sv], butlast cs @ [cl, cr],
  butlast gs @ [gl, gr], rp),
  al, ar, ak);
  sv \<le> Suc (last ss)\<rbrakk>
  \<Longrightarrow> hybrid_loop_safe_invar
  (((butlast lns @ [2 * last lns, last lns + last rns],
  butlast rns @ [last lns + last rns, 2 * last rns],
  butlast ks @ [Suc (last ks), Suc (last ks)]),
  butlast qtodo @ [ql, qr],
  butlast es @
  [newton_child_exp (last es), newton_child_exp (last es)],
  butlast ss @ [sv, sv], butlast cs @ [cl, cr],
  butlast gs @ [gl, gr], rp),
  al, ar, ak) \<and>
  defl_state_invar \<delta> P l0 r0 k0 P0 lo
  (((butlast lns @ [2 * last lns, last lns + last rns],
  butlast rns @ [last lns + last rns, 2 * last rns],
  butlast ks @ [Suc (last ks), Suc (last ks)]),
  butlast qtodo @ [ql, qr],
  butlast es @
  [newton_child_exp (last es), newton_child_exp (last es)],
  butlast ss @ [sv, sv], butlast cs @ [cl, cr],
  butlast gs @ [gl, gr], rp),
  al, ar, ak) \<and>
  hybrid_state_mu \<delta> l0 r0 k0
  (((butlast lns @ [2 * last lns, last lns + last rns],
  butlast rns @ [last lns + last rns, 2 * last rns],
  butlast ks @ [Suc (last ks), Suc (last ks)]),
  butlast qtodo @ [ql, qr],
  butlast es @
  [newton_child_exp (last es), newton_child_exp (last es)],
  butlast ss @ [sv, sv], butlast cs @ [cl, cr],
  butlast gs @ [gl, gr], rp),
  al, ar, ak)
  < hybrid_state_mu \<delta> l0 r0 k0
  (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), al, ar, ak)"
      apply (rule defl_body_join_push2[OF stinv pre capinv budinv CL(1) CL(2) CL(3) ne(6) lr0 dpos
                ab wide' abnode kcap kdepth])
      \<comment> \<open>\<^bold>\<open>\<open>OF kdepth\<close> leaves its OWN hypothesis behind as a fresh first subgoal.\<close> A
         \<open>\<And>\<close>-quantified CONDITIONAL fact composes by its CONCLUSION, so \<open>OF\<close> discharges the
         premise and re-adds \<open>int kD \<le> hybrid_root_potential \<delta> k0\<close> --- which shifts every
         later \<open>OF\<close> position by one and makes the whole \<open>[OF \<dots>]\<close> term fail to elaborate. That
         is why both PUSH branches read as a conclusion mismatch when they were a premise one:
         bare \<open>rule\<close> leaves 23 subgoals, so the conclusion was never the problem.\<close>
             apply assumption
            apply (rule nsplit)
           apply (rule vsplit)
          apply (rule npush2)
         apply (rule refl)
        apply (rule vpush2)
       apply (rule Pcoeffs)
      apply simp
     apply simp
    apply assumption
    done

    have B4: "\<And>ql cl qr cr gl gr sv.
  \<lbrakk>defl_loop_invar P0 lo
  (((butlast lns @ [2 * last lns, last lns + last rns],
  butlast rns @ [last lns + last rns, 2 * last rns],
  butlast ks @ [Suc (last ks), Suc (last ks)]),
  butlast qtodo @ [ql, qr],
  butlast es @
  [newton_child_exp (last es), newton_child_exp (last es)],
  butlast ss @ [sv, sv], butlast cs @ [cl, cr],
  butlast gs @ [gl, gr], rp),
  al @ [last lns + last rns], ar @ [last lns + last rns],
  ak @ [Suc (last ks)]);
  sv \<le> Suc (last ss)\<rbrakk>
  \<Longrightarrow> hybrid_loop_safe_invar
  (((butlast lns @ [2 * last lns, last lns + last rns],
  butlast rns @ [last lns + last rns, 2 * last rns],
  butlast ks @ [Suc (last ks), Suc (last ks)]),
  butlast qtodo @ [ql, qr],
  butlast es @
  [newton_child_exp (last es), newton_child_exp (last es)],
  butlast ss @ [sv, sv], butlast cs @ [cl, cr],
  butlast gs @ [gl, gr], rp),
  al @ [last lns + last rns], ar @ [last lns + last rns],
  ak @ [Suc (last ks)]) \<and>
  defl_state_invar \<delta> P l0 r0 k0 P0 lo
  (((butlast lns @ [2 * last lns, last lns + last rns],
  butlast rns @ [last lns + last rns, 2 * last rns],
  butlast ks @ [Suc (last ks), Suc (last ks)]),
  butlast qtodo @ [ql, qr],
  butlast es @
  [newton_child_exp (last es), newton_child_exp (last es)],
  butlast ss @ [sv, sv], butlast cs @ [cl, cr],
  butlast gs @ [gl, gr], rp),
  al @ [last lns + last rns], ar @ [last lns + last rns],
  ak @ [Suc (last ks)]) \<and>
  hybrid_state_mu \<delta> l0 r0 k0
  (((butlast lns @ [2 * last lns, last lns + last rns],
  butlast rns @ [last lns + last rns, 2 * last rns],
  butlast ks @ [Suc (last ks), Suc (last ks)]),
  butlast qtodo @ [ql, qr],
  butlast es @
  [newton_child_exp (last es), newton_child_exp (last es)],
  butlast ss @ [sv, sv], butlast cs @ [cl, cr],
  butlast gs @ [gl, gr], rp),
  al @ [last lns + last rns], ar @ [last lns + last rns],
  ak @ [Suc (last ks)])
  < hybrid_state_mu \<delta> l0 r0 k0
  (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), al, ar, ak)"
      apply (rule defl_body_join_push2[OF stinv pre capinv budinv CL(1) CL(2) CL(3) ne(6) lr0 dpos
                ab wide' abnode kcap kdepth])
      \<comment> \<open>\<^bold>\<open>\<open>OF kdepth\<close> leaves its OWN hypothesis behind as a fresh first subgoal.\<close> A
         \<open>\<And>\<close>-quantified CONDITIONAL fact composes by its CONCLUSION, so \<open>OF\<close> discharges the
         premise and re-adds \<open>int kD \<le> hybrid_root_potential \<delta> k0\<close> --- which shifts every
         later \<open>OF\<close> position by one and makes the whole \<open>[OF \<dots>]\<close> term fail to elaborate. That
         is why both PUSH branches read as a conclusion mismatch when they were a premise one:
         bare \<open>rule\<close> leaves 23 subgoals, so the conclusion was never the problem.\<close>
             apply assumption
            apply (rule nsplit)
           apply (rule vsplit)
          apply (rule npush2)
         apply (rule refl)
        apply (rule vpush2)
       apply (rule Pcoeffs)
      apply simp
     apply simp
    apply assumption
    done

    \<comment> \<open>\<^bold>\<open>The left-only split push\<close>: @{thm [source] defl_body_join_push1l}, supplied as \<open>B3\<close> supplies the two-push join,
       with one \<open>simp\<close> fewer (no accumulator dichotomy).\<close>
    have B6: "\<And>ql cl gl sv.
  \<lbrakk>defl_loop_invar P0 lo
  (((butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
  butlast ks @ [Suc (last ks)]),
  butlast qtodo @ [ql], butlast es @ [newton_child_exp (last es)],
  butlast ss @ [sv], butlast cs @ [cl], butlast gs @ [gl], rp),
  al, ar, ak);
  sv \<le> Suc (last ss)\<rbrakk>
  \<Longrightarrow> hybrid_loop_safe_invar
  (((butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
  butlast ks @ [Suc (last ks)]),
  butlast qtodo @ [ql], butlast es @ [newton_child_exp (last es)],
  butlast ss @ [sv], butlast cs @ [cl], butlast gs @ [gl], rp),
  al, ar, ak) \<and>
  defl_state_invar \<delta> P l0 r0 k0 P0 lo
  (((butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
  butlast ks @ [Suc (last ks)]),
  butlast qtodo @ [ql], butlast es @ [newton_child_exp (last es)],
  butlast ss @ [sv], butlast cs @ [cl], butlast gs @ [gl], rp),
  al, ar, ak) \<and>
  hybrid_state_mu \<delta> l0 r0 k0
  (((butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
  butlast ks @ [Suc (last ks)]),
  butlast qtodo @ [ql], butlast es @ [newton_child_exp (last es)],
  butlast ss @ [sv], butlast cs @ [cl], butlast gs @ [gl], rp),
  al, ar, ak)
  < hybrid_state_mu \<delta> l0 r0 k0
  (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), al, ar, ak)"
      apply (rule defl_body_join_push1l[OF stinv pre capinv budinv CL(1) CL(2) CL(3) ne(6) lr0 dpos
                ab wide' abnode kcap kdepth])
            apply assumption
           apply (rule nsplit)
          apply (rule vsplit)
         apply (rule npush2)
        apply (rule refl)
       apply (rule vpush2)
      apply (rule Pcoeffs)
     apply simp
    apply assumption
    done

    have B5: "\<And>m cand v QQ.
  \<lbrakk>defl_loop_invar P0 lo
  (((butlast lns @
  [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)],
  butlast rns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  (m + 4) * (last rns - last lns)],
  butlast ks @ [Suc (Suc (last ks + 2 ^ last es))]),
  butlast qtodo @ [cand], butlast es @ [Suc (last es)],
  butlast ss @ [last ss], butlast cs @ [Suc (Suc v)],
  butlast gs @ [4398046511104 + v], rp),
  al, ar, ak);
  newton_window_pick_bail v (last es) QQ = Some (m, cand);
  last es \<le> newton_pol_ecap\<rbrakk>
  \<Longrightarrow> hybrid_loop_safe_invar
  (((butlast lns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  m * (last rns - last lns)],
  butlast rns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  (m + 4) * (last rns - last lns)],
  butlast ks @ [Suc (Suc (last ks + 2 ^ last es))]),
  butlast qtodo @ [cand], butlast es @ [Suc (last es)],
  butlast ss @ [last ss], butlast cs @ [Suc (Suc v)],
  butlast gs @ [4398046511104 + v], rp),
  al, ar, ak) \<and>
  defl_state_invar \<delta> P l0 r0 k0 P0 lo
  (((butlast lns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  m * (last rns - last lns)],
  butlast rns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  (m + 4) * (last rns - last lns)],
  butlast ks @ [Suc (Suc (last ks + 2 ^ last es))]),
  butlast qtodo @ [cand], butlast es @ [Suc (last es)],
  butlast ss @ [last ss], butlast cs @ [Suc (Suc v)],
  butlast gs @ [4398046511104 + v], rp),
  al, ar, ak) \<and>
  hybrid_state_mu \<delta> l0 r0 k0
  (((butlast lns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  m * (last rns - last lns)],
  butlast rns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  (m + 4) * (last rns - last lns)],
  butlast ks @ [Suc (Suc (last ks + 2 ^ last es))]),
  butlast qtodo @ [cand], butlast es @ [Suc (last es)],
  butlast ss @ [last ss], butlast cs @ [Suc (Suc v)],
  butlast gs @ [4398046511104 + v], rp),
  al, ar, ak)
  < hybrid_state_mu \<delta> l0 r0 k0
  (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), al, ar,
  ak)"
    proof -
      fix m :: int and cand :: "int list" and v :: nat and QQ :: "int list"
      assume pick: "newton_window_pick_bail v (last es) QQ = Some (m, cand)"
      \<comment> \<open>the gate's cap, from the arm shape's window disjunct. It cannot be a lemma premise: \<open>last es \<le> newton_pol_ecap\<close>
         holds on the branch that pushes a window, not at an arbitrary popped node.\<close>
      assume esc': "last es \<le> newton_pol_ecap"
      have jle: "int (2 ^ last es + 2) \<le> int (2 ^ newton_pol_ecap + 2)" using esc' by simp
      assume iv: "defl_loop_invar P0 lo
                    (((butlast lns @
                       [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)],
                       butlast rns @
                       [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)],
                       butlast ks @ [Suc (Suc (last ks + 2 ^ last es))]),
                      butlast qtodo @ [cand], butlast es @ [Suc (last es)],
                      butlast ss @ [last ss], butlast cs @ [Suc (Suc v)],
                      butlast gs @ [4398046511104 + v], rp),
                     al, ar, ak)"
      have t1: "0 \<le> m" by (rule newton_window_pick_bail_m_nonneg[OF pick])
      \<comment> \<open>\<^bold>\<open>The bail file states the grid bound in \<open>N_of\<close> form\<close>, not as a power ---
         @{thm [source] newton_window_pick_bail_m_bound} concludes \<open>m + 4 \<le> int (4 * N_of e)\<close>,
         while @{thm [source] defl_body_join_push1}'s \<open>m4\<close> takes the power. The bridge is that
         lemma's OWN internal step \<open>s4Ni\<close>, restated here.\<close>
      have Nnat: "N_of (last es) = 2 ^ 2 ^ last es"
        using four_N_of_pow2[of "last es"] by simp
      have t2: "m + 4 \<le> 2 ^ (2 ^ last es + 2)"
        using newton_window_pick_bail_m_bound[OF pick] by (simp add: Nnat power_add)
      \<comment> \<open>\<^bold>\<open>\<open>kdepth\<close> goes LAST, not in position.\<close> Supplying it mid-list makes \<open>OF\<close> re-add its
         own hypothesis as a fresh premise AHEAD of the remaining ones, so every later position
         shifts by one; applied last, that residue lands where position no longer matters and
         \<open>simp\<close> discharges it as the tautology it is.\<close>
      note w0 = defl_body_join_push1[OF stinv pre capinv budinv CL(1) CL(2) CL(3) ne(6) lr0 dpos
                  ab wide' abnode t1 t2 jle kcap]
      note w1 = w0[OF _ nsplit]
      note w2 = w1[OF _ vsplit]
      note w3 = w2[OF _ npushw]
      note w4 = w3[OF _ refl]
      note w5 = w4[OF _ vpushw]
      note w6 = w5[OF _ Pcoeffs]
      show "hybrid_loop_safe_invar
  (((butlast lns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  m * (last rns - last lns)],
  butlast rns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  (m + 4) * (last rns - last lns)],
  butlast ks @ [Suc (Suc (last ks + 2 ^ last es))]),
  butlast qtodo @ [cand], butlast es @ [Suc (last es)],
  butlast ss @ [last ss], butlast cs @ [Suc (Suc v)],
  butlast gs @ [4398046511104 + v], rp),
  al, ar, ak) \<and>
  defl_state_invar \<delta> P l0 r0 k0 P0 lo
  (((butlast lns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  m * (last rns - last lns)],
  butlast rns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  (m + 4) * (last rns - last lns)],
  butlast ks @ [Suc (Suc (last ks + 2 ^ last es))]),
  butlast qtodo @ [cand], butlast es @ [Suc (last es)],
  butlast ss @ [last ss], butlast cs @ [Suc (Suc v)],
  butlast gs @ [4398046511104 + v], rp),
  al, ar, ak) \<and>
  hybrid_state_mu \<delta> l0 r0 k0
  (((butlast lns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  m * (last rns - last lns)],
  butlast rns @
  [last lns * (4 * 2 ^ 2 ^ last es) +
  (m + 4) * (last rns - last lns)],
  butlast ks @ [Suc (Suc (last ks + 2 ^ last es))]),
  butlast qtodo @ [cand], butlast es @ [Suc (last es)],
  butlast ss @ [last ss], butlast cs @ [Suc (Suc v)],
  butlast gs @ [4398046511104 + v], rp),
  al, ar, ak)
  < hybrid_state_mu \<delta> l0 r0 k0
  (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), al, ar,
  ak)"
        using w6[OF kdepth] iv
        by (simp del: defl_state_invar_simp hybrid_state_mu_simp)
    qed

    show ?thesis
      apply (subst defl_loop_body_under_cond[OF cond])
      apply (subst defl_loop_step_unfold)
      apply (rule order_trans[OF arm])
      apply (rule SPEC_rule)
      apply (clarsimp simp add: defl_arm_shape_def
               simp del: defl_state_invar_simp hybrid_state_mu_simp)
      apply (elim disjE conjE exE)
      apply (all \<open>(clarsimp simp del: defl_state_invar_simp hybrid_state_mu_simp)\<close>)
      subgoal by (rule B1, assumption)
      subgoal by (rule B2, assumption)
      subgoal by (rule B3, assumption, assumption)
      subgoal by (rule B4, assumption, assumption)
      subgoal by (rule B5, assumption, assumption, assumption)
      subgoal by (rule B6, assumption, assumption)
      done
  next
    \<comment> \<open>\<^bold>\<open>The narrow case: the three PUSH branches are UNREACHABLE, not unproven.\<close> Each PUSH
       disjunct of the arm shape carries a witness \<open>X\<close> that divides the node's init and has
       \<open>2 \<le> count\<close>; \<open>smalld'\<close> turns that into \<open>\<delta> < b - a\<close>, contradicting this case. That is
       exactly the fact a narrow node cannot split --- and \<^bold>\<open>it has to be an argument, not an
       assumption\<close>: two narrow children replace one narrow parent as \<open>{0,0}\<close> for \<open>{0}\<close>, so a
       narrow PUSH would genuinely break the \<open>\<mu>\<close> measure rather than merely be unproven.\<close>
    case narrow: False
    show ?thesis
      apply (subst defl_loop_body_under_cond[OF cond])
      apply (subst defl_loop_step_unfold)
      apply (rule order_trans[OF arm])
      apply (rule SPEC_rule)
      apply (clarsimp simp add: defl_arm_shape_def defl_push_wit_def
               simp del: defl_state_invar_simp hybrid_state_mu_simp)
      apply (elim disjE conjE exE)
      apply (all \<open>(clarsimp simp del: defl_state_invar_simp hybrid_state_mu_simp)\<close>)
      subgoal by (rule B1, assumption)
      subgoal by (rule B2, assumption)
      subgoal using narrow smalld' by blast
      subgoal using narrow smalld' by blast
      subgoal using narrow smalld' by blast
      subgoal using narrow smalld' by blast
      done
  qed
qed


section \<open>The local-to-global smallness bridge\<close>

text \<open>\<^bold>\<open>What this is for.\<close> \<open>defl_body_step\<close> takes the conditional \<open>smalld\<close> rather than an unconditional \<open>wide\<close> (\<open>\<delta> < b - a\<close>
  at the popped node), and this discharges it. The shape is the non-deflating one (derive \<open>wide\<close> from \<open>2 \<le> count\<close> on the
  branches that push), but the deflating count is taken on the node's possibly deflated exact object \<open>X\<close>, in the node's local
  \<open>(0,1)\<close> frame, while \<open>\<delta>\<close> and the smallness lemma speak about the node's box in the seed frame.

  \<^bold>\<open>The route\<close>, from existing facts:
    \<^item> \<open>Bernstein_changes_eq_rescale\<close> (AFP \<open>Three_Circles\<close>) is the affine invariance
      \<open>Bernstein_changes p c d P = Bernstein_changes_01 p (P \<circ>\<^sub>p [:c,1:] \<circ>\<^sub>p [:0,d-c:])\<close>;
    \<^item> \<open>Bernstein_changes_small_interval_le_1\<close> is indexed by any \<open>p \<ge> degree D\<close> (the \<open>degree P \<le> p\<close> of
      \<open>Bernstein_changes_small_interval_le_1_of_dvd\<close> is used only to derive \<open>degree D \<le> p\<close>, so a variant taking the latter is
      immediate);
    \<^item> \<open>carried_repr_init\<close> with \<open>descartes_list_int_eq_Bernstein_changes\<close> is the count bridge used earlier in this theory.\<close>

subsection \<open>The transport, indexed by the divisor's degree\<close>

lemma defl_small_of_dvd_degD:
  fixes P D :: "real poly"
  assumes P0: "P \<noteq> 0"
      and sf: "square_free P"
      and dvd: "D dvd P"
      and degD: "degree D \<le> p"
      and p0: "p \<noteq> 0"
      and ab: "a < b"
      and small: "b - a \<le> delta_defl P"
  shows "Bernstein_changes p a b D \<le> 1"
proof -
  have D0: "D \<noteq> 0" using dvd P0 by auto
  have sfD: "square_free D" using square_free_factor[OF dvd sf] .
  have rsfD: "rsquarefree (map_poly (of_real :: real \<Rightarrow> complex) D)"
    using rsquarefree_lift[OF sfD] .
  have smallD: "b - a \<le> delta_P D"
    using small delta_defl_le_delta_P_of_dvd[OF P0 dvd] by linarith
  show ?thesis
    using Bernstein_changes_small_interval_le_1[OF D0 degD p0 rsfD ab smallD] .
qed

subsection \<open>The affine pullback of divisibility\<close>

lemma defl_affine_compose:
  fixes c d e f :: real
  shows "([:d, c:] :: real poly) \<circ>\<^sub>p [:e, f:] = [:d + e * c, f * c:]"
  by (simp add: pcompose_pCons)

lemma defl_affine_inv_right:
  fixes c d :: real
  assumes c0: "c \<noteq> 0"
  shows "([:d, c:] :: real poly) \<circ>\<^sub>p [:- d / c, 1 / c:] = [:0, 1:]"
  using c0 by (simp add: defl_affine_compose)

lemma defl_affine_inv_left:
  fixes c d :: real
  assumes c0: "c \<noteq> 0"
  shows "([:- d / c, 1 / c:] :: real poly) \<circ>\<^sub>p [:d, c:] = [:0, 1:]"
  using c0 by (simp add: defl_affine_compose)

lemma defl_dvd_affine_pullback:
  fixes P Y :: "real poly"
  assumes c0: "c \<noteq> 0"
      and dvd: "Y dvd (P \<circ>\<^sub>p [:d, c:])"
  shows "(Y \<circ>\<^sub>p [:- d / c, 1 / c:]) dvd P"
    and "(Y \<circ>\<^sub>p [:- d / c, 1 / c:]) \<circ>\<^sub>p [:d, c:] = Y"
proof -
  obtain C where C: "P \<circ>\<^sub>p [:d, c:] = Y * C" using dvd ..
  have "P = (P \<circ>\<^sub>p [:d, c:]) \<circ>\<^sub>p [:- d / c, 1 / c:]"
    by (simp flip: pcompose_assoc add: c0 defl_affine_inv_right[OF c0])
  also have "\<dots> = (Y \<circ>\<^sub>p [:- d / c, 1 / c:]) * (C \<circ>\<^sub>p [:- d / c, 1 / c:])"
    by (simp add: C pcompose_mult)
  finally show "(Y \<circ>\<^sub>p [:- d / c, 1 / c:]) dvd P" ..
  show "(Y \<circ>\<^sub>p [:- d / c, 1 / c:]) \<circ>\<^sub>p [:d, c:] = Y"
    by (simp flip: pcompose_assoc add: c0 defl_affine_inv_left[OF c0])
qed

subsection \<open>Bernstein counts between the two frames\<close>

lemma defl_Bernstein_frame:
  fixes D :: "real poly"
  assumes ab: "a \<noteq> b" and degD: "degree D \<le> p"
  shows "Bernstein_changes p a b D = Bernstein_changes p 0 1 (D \<circ>\<^sub>p [:a, b - a:])"
proof -
  have zo: "(0::real) \<noteq> 1" by simp
  have comp: "D \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:] = D \<circ>\<^sub>p [:a, b - a:]"
    by (simp flip: pcompose_assoc add: defl_affine_compose)
  have degY: "degree (D \<circ>\<^sub>p [:a, b - a:]) \<le> p"
    using degD ab by (simp add: degree_pcompose)
  have L: "Bernstein_changes p a b D = Bernstein_changes_01 p (D \<circ>\<^sub>p [:a, b - a:])"
    using Bernstein_changes_eq_rescale[OF ab degD] comp by simp
  have R: "Bernstein_changes p 0 1 (D \<circ>\<^sub>p [:a, b - a:])
             = Bernstein_changes_01 p (D \<circ>\<^sub>p [:a, b - a:])"
    using Bernstein_changes_eq_rescale[where c = 0 and d = 1, OF zo degY] by simp
  show ?thesis using L R by simp
qed

subsection \<open>The bridge\<close>

text \<open>\<open>Y\<close> is the node's exact object, read as a real polynomial in the node's LOCAL frame;
  \<open>P\<close> is the polynomial the run's \<open>\<delta>\<close> is a smallness witness for; \<open>(a, b)\<close> is the node's box
  in \<open>P\<close>'s frame. The conclusion is stated at \<open>Bernstein_changes\<close> of the LOCAL object on
  \<open>(0,1)\<close> --- which is what the count bridge already delivers.\<close>

lemma defl_local_Bernstein_le1_of_dvd:
  fixes P Y :: "real poly"
  assumes P0: "P \<noteq> 0"
      and sf: "square_free P"
      and ab: "a < b"
      and small: "b - a \<le> delta_defl P"
      and dvd: "Y dvd (P \<circ>\<^sub>p [:a, b - a:])"
      and degY: "degree Y \<le> p"
      and p0: "p \<noteq> 0"
  shows "Bernstein_changes p 0 1 Y \<le> 1"
proof -
  have c0: "b - a \<noteq> 0" using ab by simp
  have abne: "a \<noteq> b" using ab by simp
  define D where "D = Y \<circ>\<^sub>p [:- a / (b - a), 1 / (b - a):]"
  have Ddvd: "D dvd P"
    unfolding D_def using defl_dvd_affine_pullback(1)[OF c0 dvd] .
  have DY: "D \<circ>\<^sub>p [:a, b - a:] = Y"
    unfolding D_def using defl_dvd_affine_pullback(2)[OF c0 dvd] .
  have degD: "degree D \<le> p"
    using degY c0 by (simp add: DY[symmetric] degree_pcompose)
  have le1: "Bernstein_changes p a b D \<le> 1"
    by (rule defl_small_of_dvd_degD[OF P0 sf Ddvd degD p0 ab small])
  have "Bernstein_changes p a b D = Bernstein_changes p 0 1 Y"
    using defl_Bernstein_frame[OF abne degD] DY by simp
  thus ?thesis using le1 by simp
qed

subsection \<open>The count bridge, and the node init in the seed's frame\<close>

text \<open>The count bridge used earlier in this theory, in one line: \<open>defl_count_unit_box\<close> reads the count as
  \<open>descartes_list_int 0 1\<close>, and @{thm [source] descartes_list_int_eq_Bernstein_changes} turns that into a
  @{const Bernstein_changes} on the local box.\<close>

lemma defl_count_as_Bernstein:
  assumes len: "0 < length X"
  shows "int (carried_descartes_count X)
       = Bernstein_changes (length X - 1) 0 1 (of_int_poly (Poly X) :: real poly)"
proof -
  have ab: "(0::rat) < 1" by simp
  show ?thesis
    using descartes_list_int_eq_Bernstein_changes[OF len ab] defl_count_unit_box[of X]
    by simp
qed

text \<open>\<^bold>\<open>And the frame identity.\<close> The node's init is built from \<open>rp\<close> at the node's own
  numerators; \<open>\<delta>\<close> and @{const hybrid_state_mu} speak about the box
  @{const dyadic_iv_node_iv} returns, which is the node box normalised into the SEED's frame,
  and the polynomial they speak about is the SEED's init. This says the two agree up to a
  nonzero scalar --- which is all divisibility needs.\<close>

lemma defl_node_init_pcompose_seed:
  fixes rp :: "int list" and l0 r0 l r :: int and k0 k :: nat
  assumes lr0: "l0 < r0"
  shows "\<exists>c::real. c \<noteq> 0 \<and>
      (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)
        = smult c
            ((of_int_poly (Poly (carried_init_same_den l0 (2 ^ k0) r0 rp)) :: real poly)
               \<circ>\<^sub>p [: real_of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l r k)),
                      real_of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l r k))
                        - real_of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l r k)) :])"
proof -
  define N where "N = length rp - 1"
  define P0 where "P0 = (of_int_poly (Poly rp) :: real poly)"
  define lo where "lo = real_of_int l0 / 2 ^ k0"
  define hi where "hi = real_of_int r0 / 2 ^ k0"
  define a where "a = real_of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l r k))"
  define b where "b = real_of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l r k))"
  have d0: "(2::int) ^ k0 \<noteq> 0" by simp
  have d1: "(2::int) ^ k \<noteq> 0" by simp
  have lohi: "lo < hi"
    unfolding lo_def hi_def using lr0 by (simp add: divide_strict_right_mono)
  have hl: "hi - lo \<noteq> 0" using lohi by simp
  have a_eq: "a = (real_of_int l / 2 ^ k - lo) / (hi - lo)"
    unfolding a_def lo_def hi_def dyadic_iv_node_iv_def dyadic_rat_def Let_def
    by (simp add: of_rat_divide of_rat_diff of_rat_power of_rat_of_int_eq)
  have b_eq: "b = (real_of_int r / 2 ^ k - lo) / (hi - lo)"
    unfolding b_def lo_def hi_def dyadic_iv_node_iv_def dyadic_rat_def Let_def
    by (simp add: of_rat_divide of_rat_diff of_rat_power of_rat_of_int_eq)
  have A: "lo + a * (hi - lo) = real_of_int l / 2 ^ k"
    using hl by (simp add: a_eq)
  have B: "(b - a) * (hi - lo) = (real_of_int r - real_of_int l) / 2 ^ k"
  proof -
    have "b - a = (real_of_int r / 2 ^ k - real_of_int l / 2 ^ k) / (hi - lo)"
      unfolding a_eq b_eq by (simp add: diff_divide_distrib)
    hence "(b - a) * (hi - lo) = real_of_int r / 2 ^ k - real_of_int l / 2 ^ k"
      using hl by (simp add: field_simps)
    thus ?thesis by (simp add: diff_divide_distrib)
  qed
  have seed: "(of_int_poly (Poly (carried_init_same_den l0 (2 ^ k0) r0 rp)) :: real poly)
                = smult (((2::real) ^ k0) ^ N) (P0 \<circ>\<^sub>p [: lo, hi - lo :])"
    unfolding P0_def lo_def hi_def N_def
    using defl_cisd_real_pcompose[OF d0, of l0 r0 rp] by (simp add: field_simps)
  have node: "(of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)
                = smult (((2::real) ^ k) ^ N)
                    (P0 \<circ>\<^sub>p [: real_of_int l / 2 ^ k,
                              (real_of_int r - real_of_int l) / 2 ^ k :])"
    unfolding P0_def N_def
    using defl_cisd_real_pcompose[OF d1, of l r rp] by simp
  have comp: "(of_int_poly (Poly (carried_init_same_den l0 (2 ^ k0) r0 rp)) :: real poly)
                 \<circ>\<^sub>p [: a, b - a :]
              = smult (((2::real) ^ k0) ^ N)
                  (P0 \<circ>\<^sub>p [: real_of_int l / 2 ^ k,
                            (real_of_int r - real_of_int l) / 2 ^ k :])"
    by (simp add: seed pcompose_smult defl_affine_compose A B mult.commute
             flip: pcompose_assoc)
  have s0: "(((2::real) ^ k0) ^ N) \<noteq> 0" by simp
  have "(of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)
          = smult ((((2::real) ^ k) ^ N) / (((2::real) ^ k0) ^ N))
              ((of_int_poly (Poly (carried_init_same_den l0 (2 ^ k0) r0 rp)) :: real poly)
                 \<circ>\<^sub>p [: a, b - a :])"
    by (simp add: node comp s0)
  thus ?thesis
    unfolding a_def b_def by (intro exI[of _ "(((2::real) ^ k) ^ N) / (((2::real) ^ k0) ^ N)"]) simp
qed

subsection \<open>A node that splits has a box wider than \<open>\<delta>\<close>\<close>

text \<open>\<^bold>\<open>This is the fact \<open>defl_body_step\<close> is missing.\<close> It takes \<open>wide\<close> unconditionally today,
  which a narrow popped node makes unusable; the classic derives the same thing from
  \<open>small_fast\<close> together with \<open>2 \<le> count\<close>, but only on the branches that PUSH. Here the count is
  taken on the possibly-DEFLATED exact object, and a Descartes count does not transport across
  @{const defl_node_wrel} --- so the hypothesis that replaces \<open>carried_repr\<close> is DIVISIBILITY,
  which is exactly the clause step 4 adds to @{const defl_node_ok}.\<close>

lemma defl_node_wide_of_count2:
  fixes rp X :: "int list" and \<delta> :: real
    and l0 r0 l r :: int and k0 k :: nat
  defines "P \<equiv> (of_int_poly (Poly (carried_init_same_den l0 (2 ^ k0) r0 rp)) :: real poly)"
  assumes lr0: "l0 < r0"
      and Pnz: "P \<noteq> 0"
      and sf: "square_free P"
      and dlt: "\<delta> \<le> delta_defl P"
      and ab: "real_of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l r k))
                 < real_of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l r k))"
      and dvd: "(of_int_poly (Poly X) :: real poly)
                  dvd (of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)"
      and cnt2: "2 \<le> carried_descartes_count X"
      and Xlen: "1 < length X"
  shows "\<delta> < real_of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l r k))
             - real_of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l r k))"
proof (rule ccontr)
  assume ng: "\<not> \<delta> < real_of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l r k))
                    - real_of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l r k))"
  define a where "a = real_of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l r k))"
  define b where "b = real_of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l r k))"
  define Y where "Y = (of_int_poly (Poly X) :: real poly)"
  have small: "b - a \<le> delta_defl P" using ng dlt unfolding a_def b_def by simp
  have ab': "a < b" using ab unfolding a_def b_def by simp
  obtain c :: real where c0: "c \<noteq> 0"
    and ceq: "(of_int_poly (Poly (carried_init_same_den l (2 ^ k) r rp)) :: real poly)
                = smult c (P \<circ>\<^sub>p [: a, b - a :])"
    using defl_node_init_pcompose_seed[OF lr0, of l k r rp k0] unfolding P_def a_def b_def by blast
  have dvd': "Y dvd (P \<circ>\<^sub>p [: a, b - a :])"
  proof -
    have "Y dvd smult (1 / c) (smult c (P \<circ>\<^sub>p [: a, b - a :]))"
      using dvd unfolding Y_def ceq by (rule dvd_smult)
    thus ?thesis using c0 by simp
  qed
  \<comment> \<open>the same two steps @{thm [source] descartes_list_int_eq_Bernstein_changes} uses for its
     own \<open>degP\<close>; a \<open>metis\<close> over these three facts does not finish.\<close>
  have degY: "degree Y \<le> length X - 1"
  proof -
    have "degree Y \<le> degree (Poly X)" unfolding Y_def by (rule degree_map_poly_le)
    also have "\<dots> \<le> length X - 1"
      using Xlen by (simp add: degree_le coeff_Poly nth_default_beyond)
    finally show ?thesis .
  qed
  have p0: "length X - 1 \<noteq> 0" using Xlen by simp
  have le1: "Bernstein_changes (length X - 1) 0 1 Y \<le> 1"
    by (rule defl_local_Bernstein_le1_of_dvd[OF Pnz sf ab' small dvd' degY p0])
  have "2 \<le> Bernstein_changes (length X - 1) 0 1 Y"
    using cnt2 defl_count_as_Bernstein[of X] Xlen unfolding Y_def by simp
  thus False using le1 by simp
qed


section \<open>\<open>defl_step_all_cols\<close>: the loop-level assembly\<close>

text \<open>The deflating twin of @{thm [source] hybrid_step_all_cols}
  (\<open>Hybrid_Keystone.thy\<close>), and it is far smaller for a structural reason: the classic
  case-splits on the count at the TOP and dispatches to four \<open>hybrid_step_discharge_*\<close>
  lemmas, because @{thm [source] hybrid_resolve_bind} pins its exact object to a FORMULA.
  Here the resolve may REPLACE the object, so the arm split lives BELOW it and there is exactly
  ONE body step to feed.\<close>

lemma defl_step_all_cols:
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
    and accroom: "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
    and cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    \<comment> \<open>the ROOT list's own two facts. \<open>Pr\<close> above is the SEED's local poly --- a different
       object, and \<open>\<delta>\<close> is a smallness witness for that one.\<close>
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and sfrp: "square_free (of_int_poly (Poly rp) :: real poly)"
  shows "defl_loop_body_checked_monadic (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> defl_state_invar \<delta> P l0 r0 k0 (of_int_poly (Poly rp) :: real poly) lo s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
proof -
  have capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and stkinv: "defl_stack_invar \<delta> l0 r0 k0 (lns, rns, ks)"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and inv0: "defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using stinvar by simp_all
  have budinv: "defl_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    by (rule defl_budget_invarI[OF stkinv accroom])
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
  show ?thesis
    apply (rule defl_body_step[OF cond safe stinvar accroom lr0 dpos smalld kcap kdepth])
    \<comment> \<open>\<^bold>\<open>\<open>OF smalld\<close> re-adds \<open>smalld\<close>'s OWN two hypotheses as fresh goals\<close> --- a
       \<open>\<And>\<close>-quantified CONDITIONAL fact composes by its conclusion, which is the trap this
       file records at \<open>defl_body_step\<close>'s \<open>kdepth\<close>. They close by \<open>assumption\<close>.\<close>
        apply assumption
       apply assumption
    \<comment> \<open>and \<open>kdepth\<close>'s own residue, which is the tautology it always is\<close>
      apply assumption
     apply (rule hybrid_alpha_nodes_append1[OF BL(1) BL(2) BL(3) BL(4)])
    apply (rule hybrid_alpha_views_append1[OF BL(1) BL(2)])
    apply (rule defl_loop_step_args_step[OF tinv lne VL(1) VL(2) ne(1) ne(2) ne(3) ne(4) ne(5)
             node g_roomk rpnz sfrp lrne rp_len rp_gb rp_sint rp_small rp_pb krp kcapl
             kroom258 accpush qcap gcap ecapl sscap ccap
             push2 push1 kslen scap1 coupb isob covb BL(1) BL(2)[symmetric] lal lak])
    done
qed


section \<open>The seed, and \<open>defl_main_list_correct\<close>\<close>

text \<open>\<^bold>\<open>Step 4's exit criterion.\<close> \<open>defl_loop_correct\<close> has taken
  \<open>defl_step_all_cols\<close>'s exact shape since step 1, so what is left of step 4 is the seed
  assembly --- the monadic prefix of @{const defl_main_list_monadic} and the three invariant
  clauses at the initial state.

  \<^bold>\<open>And the deflating exit is far cheaper than the classic's\<close>: it is
  @{thm [source] defl_loop_invar_exit}'s two clauses, not an \<open>\<exists>pol\<close> multiset equality.\<close>

subsection \<open>The two seed clauses\<close>

lemma defl_acc_isolates_seed: "defl_acc_isolates P0 ([], [], [])"
  unfolding defl_acc_isolates_def dyadic_interval_vec_triples_def by simp

text \<open>\<^bold>\<open>The seed's coverage is a CALLER obligation\<close>: every root
  of \<open>P\<^sub>0\<close> above \<open>lo\<close> lies strictly inside the seed box. At the reflect level that is
  \<open>kpos_sound\<close> --- \<open>\<forall>x > 0. ripoly (Poly xs) x = 0 \<longrightarrow> x < 2\<^sup>k\<^sup>p\<^sup>o\<^sup>s\<close>.\<close>

lemma defl_pending_covers_seed:
  assumes cover: "\<And>y::real. lo < y \<Longrightarrow> poly P0 y = 0 \<Longrightarrow>
                    real_of_int l / 2 ^ k < y \<and> y < real_of_int r / 2 ^ k"
  shows "defl_pending_covers P0 lo ([l], [r], [k]) ([], [], [])"
  unfolding defl_pending_covers_def defl_todo_box_def using cover by auto

lemma defl_loop_invar_seed:
  assumes cover: "\<And>y::real. lo < y \<Longrightarrow> poly (of_int_poly (Poly rp) :: real poly) y = 0 \<Longrightarrow>
                    real_of_int l_num / 2 ^ k < y \<and> y < real_of_int r_num / 2 ^ k"
    and P_eq: "Pl = carried_init_same_den l_num (2 ^ k) r_num rp"
    and canon: "coeffs (Poly Pl) = Pl"
    and c_ok: "hybrid_cs_ok 0 c (carried_descartes_count Pl)"
    and c_le: "c \<le> 4"
    and Pnz: "(of_int_poly (Poly Pl) :: real poly) \<noteq> 0"
  shows "defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo
           ((([l_num], [r_num], [k]), [Pl], [e0], [0], [c], [0], rp), ([], [], []))"
  unfolding defl_loop_invar_def
  by (simp add: defl_acc_isolates_seed defl_pending_covers_seed[OF cover]
                defl_trunc_coupling_init[OF P_eq c_ok c_le Pnz])

subsection \<open>The seed's polynomial is the run's, and that has to be DERIVED\<close>

text \<open>\<^bold>\<open>The step obligation quantifies over every state the invariant admits\<close>, and such a state
  carries its OWN \<open>rp\<close> --- while \<open>defl_step_all_cols\<close> ties \<open>P\<^sub>0\<close> to it. The invariant does not
  pin \<open>rp\<close> to a constant, so the tie is not free. \<^bold>\<open>It is derivable, though\<close>, and without
  touching @{const defl_state_invar}: the invariant's own \<open>coeffs P = carried_init_same_den \<dots> rp\<close>
  clause makes the two root lists agree AFTER the map, and that map is injective on the real
  image --- it is an affine reparametrisation, and \<open>defl_dvd_affine_pullback\<close>'s inverse is
  already in the file.\<close>

lemma defl_cisd_inj_real:
  fixes l r :: int and k :: nat
  assumes lr: "l < r"
    and eq: "carried_init_same_den l (2 ^ k) r xs = carried_init_same_den l (2 ^ k) r ys"
  shows "(of_int_poly (Poly xs) :: real poly) = of_int_poly (Poly ys)"
proof -
  define A where "A = real_of_int l / 2 ^ k"
  define B where "B = (real_of_int r - real_of_int l) / 2 ^ k"
  define I where "I = [: - A / B, 1 / B :]"
  have len: "length xs = length ys"
    using eq by (metis truncate_length_carried_init_same_den)
  have d0: "(2::int) ^ k \<noteq> 0" by simp
  have c0: "B \<noteq> 0" using lr unfolding B_def by simp
  have px: "(of_int_poly (Poly (carried_init_same_den l (2 ^ k) r xs)) :: real poly)
              = smult (((2::real) ^ k) ^ (length xs - 1))
                  ((of_int_poly (Poly xs) :: real poly) \<circ>\<^sub>p [: A, B :])"
    unfolding A_def B_def using defl_cisd_real_pcompose[OF d0, of l r xs] by simp
  have py: "(of_int_poly (Poly (carried_init_same_den l (2 ^ k) r ys)) :: real poly)
              = smult (((2::real) ^ k) ^ (length ys - 1))
                  ((of_int_poly (Poly ys) :: real poly) \<circ>\<^sub>p [: A, B :])"
    unfolding A_def B_def using defl_cisd_real_pcompose[OF d0, of l r ys] by simp
  have C: "(of_int_poly (Poly xs) :: real poly) \<circ>\<^sub>p [: A, B :]
         = (of_int_poly (Poly ys) :: real poly) \<circ>\<^sub>p [: A, B :]"
    using px py eq len by simp
  \<comment> \<open>compose both sides with the INVERSE affine; \<open>pcompose_idR\<close> is \<open>[simp]\<close>\<close>
  have inv: "\<And>Z :: real poly. (Z \<circ>\<^sub>p [: A, B :]) \<circ>\<^sub>p I = Z"
    unfolding I_def by (simp flip: pcompose_assoc add: defl_affine_inv_right[OF c0] c0)
  have "(of_int_poly (Poly xs) :: real poly)
      = ((of_int_poly (Poly xs) :: real poly) \<circ>\<^sub>p [: A, B :]) \<circ>\<^sub>p I" by (simp add: inv)
  also have "\<dots> = ((of_int_poly (Poly ys) :: real poly) \<circ>\<^sub>p [: A, B :]) \<circ>\<^sub>p I" using C by simp
  also have "\<dots> = (of_int_poly (Poly ys) :: real poly)" by (simp add: inv)
  finally show ?thesis .
qed

subsection \<open>The exit, including the tail's own ASSERT\<close>

text \<open>The wrapper's tail is \<open>ASSERT (qtodo = [])\<close> then the frees, so the loop's
  postcondition owes that column fact as well as the two accumulator ones.\<close>

subsection \<open>The seed's cache value, WITH its class bound\<close>

text \<open>@{thm [source] hybrid_count_trunc_cs_ok} exports only \<open>hybrid_cs_ok 0 c\<^sub>0 \<dots>\<close>, and
  that predicate does not bound \<open>c\<^sub>0\<close> above --- its second disjunct is the classify
  TRICHOTOMY, which is satisfied by any \<open>c\<^sub>0\<close> agreeing on \<open>0\<close>/\<open>1\<close>/\<open>\<ge> 2\<close>.
  @{thm [source] defl_trunc_coupling_init} needs \<open>c \<le> 4\<close> (the seed class is
  @{const hybrid_class_of}'s), so the same one-line proof exports it too.\<close>

lemma defl_count_trunc_cs_ok_le4:
  assumes len_bound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_descartes_count_trunc_monadic xs
       \<le> SPEC (\<lambda>c0. hybrid_cs_ok 0 c0 (carried_descartes_count xs) \<and> c0 \<le> 4)"
  using carried_descartes_count_trunc_monadic_classify_le3[OF len_bound]
  by (auto simp: hybrid_cs_ok_def dyadic_iv_cs_invar_def pw_le_iff refine_pw_simps)

lemma defl_exit_acc:
  assumes inv: "defl_loop_invar P0 lo
                  (((lns, rns, ks), qtodo, es, ss, cs, gs, rpx), (al, ar, ak))"
    and safe: "hybrid_loop_safe_invar
                 (((lns, rns, ks), qtodo, es, ss, cs, gs, rpx), (al, ar, ak))"
    and ncond: "\<not> hybrid_loop_cond
                    (((lns, rns, ks), qtodo, es, ss, cs, gs, rpx), (al, ar, ak))"
    \<comment> \<open>\<^bold>\<open>Last\<close>: the budget invariant, for the accumulator cap. It is an unguarded conjunct of @{const defl_state_invar} and
       so still holds at the exit.\<close>
    and accroom: "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
  shows "qtodo = []
       \<and> dyadic_interval_vec_invar (al, ar, ak)
       \<and> length (dyadic_interval_vec_triples (al, ar, ak)) + 1
           < max_snat LENGTH(gmp_poly_len)
       \<and> defl_acc_isolates P0 (al, ar, ak) \<and> defl_acc_covers P0 lo (al, ar, ak)"
proof -
  have stinv: "hybrid_loop_state_invar
                 (((lns, rns, ks), qtodo, es, ss, cs, gs, rpx), (al, ar, ak))"
    using safe unfolding hybrid_loop_safe_invar_def by simp
  have lnil: "lns = []" using ncond by (simp add: hybrid_loop_cond_def)
  \<comment> \<open>\<^bold>\<open>The two predicates read DIFFERENT columns\<close> --- @{const hybrid_loop_cond} tests
     \<open>lns\<close>, the tail's \<open>ASSERT\<close> tests \<open>qtodo\<close> and
     @{thm [source] defl_loop_invar_exit} counts \<open>rns\<close>. The state invariant's column-length
     conjunct is the bridge, which is why \<open>safe\<close> is a premise here.\<close>
  have lq: "length qtodo = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have lr: "length rns = length lns"
    using stinv unfolding hybrid_loop_state_invar_def dyadic_interval_vec_invar_def
    by (simp add: Let_def)
  have empty: "fst (snd (lns, rns, ks)) = []" using lnil lr by simp
  \<comment> \<open>\<^bold>\<open>The accumulator's two facts\<close>, the first and fourth conjuncts of \<open>qsolve\<close>. The vector invariant is a conjunct of
     @{const hybrid_loop_state_invar}; the cap is @{thm [source] hybrid_budget_invar_acc_cap}, whose \<open>_acc_cap\<close> form (not
     \<open>_acc_grown\<close>) needs no live node, and at the exit there is none.\<close>
  have accinv: "dyadic_interval_vec_invar (al, ar, ak)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have alcap: "length al + 1 < max_snat LENGTH(gmp_poly_len)"
    using accroom by linarith
  have acclen: "length (dyadic_interval_vec_triples (al, ar, ak)) + 1
                  < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<open>triples\<close> is a \<open>zip\<close>, so its length is the SHORTER column's; the vec invariant's
       equal-length conjunct makes that \<open>al\<close>'s.\<close>
    using alcap accinv
    by (simp add: dyadic_interval_vec_triples_def dyadic_interval_vec_invar_def)
  show ?thesis
    using lnil lq accinv acclen
          defl_loop_invar_exit(1)[OF inv empty] defl_loop_invar_exit(2)[OF inv empty]
    by simp
qed

text \<open>The capstone \<open>defl_main_list_correct\<close> is in \<open>Deflation_Loop_Geom\<close>: its accumulator
  capacity comes from the emitted windows' disjointness, which that theory carries.\<close>

end
