theory Power_Sub_Sound
  imports "IsaRRI_LLVM.Power_Sub_Emit_All_Impl"
begin

text \<open>\<^bold>\<open>The soundness chain of the power-substitution back-map.\<close> Nothing here is synthesised.

  \<^bold>\<open>Why this theory is not beside the ops.\<close> The implementation session is compiled by every export, so a slow
  proof there would be paid by every artifact build. Nothing downstream of the \<open>.ll\<close> needs these facts, so they
  are proved here, in the session that can see the capstone, the entry op and these facts at once.

  \<^bold>\<open>What is proved.\<close> The claim is isolation, @{const dsc_pair_ok} per emitted window. The chain is

    \<open>pow_sub_emit_ok\<close>  (what the per-interval ops decide)
      \<longrightarrow>  \<open>dsc_pair_ok Q\<close> on the reduced window  (certify / sign test)
      \<longrightarrow>  \<open>dsc_pair_ok P\<close> on the emitted window   (the back-map bridges of the specification layer),

  where the last step is @{thm [source] pow_sub_pair_ok_interval} and @{thm [source] pow_sub_pair_ok_degenerate}.
  \<open>Power_Sub_Emit_All_Impl\<close> carries only HNR lemmas, and its loop invariant \<open>\<lambda>(i, ok, out). i \<le> n\<close> has no
  isolation content, so the first step is proved here, up to \<open>pow_sub_backmap_all_monadic_correct\<close>, the back-map
  loop's abstract postcondition.

  The loop's postcondition is conditional on \<open>pow_sub_iv_pre\<close> at every index of the reduced solve's positive vector.
  \<open>0 \<le> A\<close>, \<open>0 \<le> B\<close> and the word bounds are not supplied by the reduced solve's capstone (it states
  @{const dsc_pair_ok} and root coverage per interval, nothing about an endpoint's sign or the precision column);
  they are decided by the room guard (below).\<close>

section \<open>The abstraction: a \<open>gmp_poly\<close> as a real polynomial\<close>

text \<open>The ops speak of an \<open>int list\<close>; the isolation predicates speak of a \<open>real poly\<close>. Everything
  below is stated against this one abbreviation so the two never drift.\<close>

abbreviation poly_of_gmp :: "int list \<Rightarrow> real poly" where
  "poly_of_gmp xs \<equiv> map_poly real_of_int (Poly xs)"

section \<open>Endpoint arithmetic: the emitted numerators ARE the spec's endpoints\<close>

text \<open>@{const pow_sub_num_lo} and @{const pow_sub_num_hi} are the numerators of @{const pow_sub_lo}
  and @{const pow_sub_hi} at the same \<open>m\<close> — immediate from the definitions, but stated once here
  because every branch below needs to move between the integer and the real form.\<close>

lemma pow_sub_lo_num: "pow_sub_lo h m a = real_of_int (pow_sub_num_lo h m a) / 2 ^ m"
  by (simp add: pow_sub_lo_def pow_sub_num_lo_def)

lemma pow_sub_hi_num: "pow_sub_hi h m a = real_of_int (pow_sub_num_hi h m a) / 2 ^ m"
  by (simp add: pow_sub_hi_def pow_sub_num_hi_def)

text \<open>The window in \<open>Q\<close>-space is the emitted window raised to the \<open>h\<close>-th power, and the certify op
  states it as an exact integer ratio over a shared \<open>2\<^sup>h\<^sup>\<cdot>\<^sup>m\<close>. This is the reconciliation.\<close>

lemma real_div_pow_pow:
  fixes L :: int
  shows "(real_of_int L / 2 ^ m) ^ h = real_of_int (L ^ h) / 2 ^ (h * m)"
  \<comment> \<open>\<open>power_mult\<close> must be FLIPPED: left to right it drives \<open>2\<^sup>h\<^sup>\<cdot>\<^sup>m\<close> to \<open>(2\<^sup>h)\<^sup>m\<close> while the goal's
     other side is \<open>(2\<^sup>m)\<^sup>h\<close>, leaving the un-closable \<open>(2\<^sup>m)\<^sup>h = (2\<^sup>h)\<^sup>m\<close>. Flipped, both collapse to a
     single power and \<open>mult.commute\<close> (permutative, so ordered rewriting keeps it safe) finishes.\<close>
  by (simp add: power_divide mult.commute flip: of_int_power power_mult)

lemma pow_sub_num_lo_nonneg:
  fixes A :: int
  assumes A0: "0 \<le> A"
  shows "0 \<le> pow_sub_num_lo h m (real_of_int A / 2 ^ k)"
proof -
  have "0 \<le> (real_of_int A / 2 ^ k) powr (1 / real h) * 2 ^ m" by simp
  then show ?thesis unfolding pow_sub_num_lo_def by simp
qed

(*FASTLOOP_FREEZE_ABOVE*)
section \<open>The DEGENERATE branch: the reduced window is a single \<open>Q\<close>-root\<close>

text \<open>The reduced solve may emit a degenerate pair \<open>(a, a)\<close>, an exactly representable root of \<open>Q\<close>. Two sub-cases,
  decided by the exact integer identity the search already evaluates:

  \<^item> the \<open>h\<close>-th root is representable at this \<open>m\<close> (\<open>L\<^sup>h \<cdot> 2\<^sup>k = A \<cdot> 2\<^sup>h\<^sup>\<cdot>\<^sup>m\<close>): then \<open>R = L\<close> and the emitted pair is degenerate
    too, carrying \<open>poly P (L / 2\<^sup>m) = 0\<close>;
  \<^item> otherwise \<open>R = 1 + L\<close>, and the window \<open>(L, 1+L) / 2\<^sup>m\<close> is certified by a Descartes count.\<close>

lemma pow_sub_deg_tst_pair_ok:
  fixes Q0 :: "int poly" and A :: int
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len: "0 < length q"
    and A0: "0 \<le> A"
    and iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int A / 2 ^ k)"
    and tst: "pow_sub_deg_tst h A k q m"
    and Ldef: "L = pow_sub_num_lo h m (real_of_int A / 2 ^ k)"
    and Rdef: "R = (if L ^ h * 2 ^ k = A * 2 ^ (h * m) then L else 1 + L)"
  shows "dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)"
proof (cases "L ^ h * 2 ^ k = A * 2 ^ (h * m)")
  case True
  \<comment> \<open>exact: the emitted point IS the \<open>h\<close>-th root of the \<open>Q\<close>-root, so \<open>P\<close> vanishes there\<close>
  have R: "R = L" using Rdef True by simp
  have rootQ: "poly Q (real_of_int A / 2 ^ k) = 0"
    using iv unfolding dsc_pair_ok_def by simp
  have pw: "(real_of_int L / 2 ^ m) ^ h = real_of_int A / 2 ^ k"
  proof -
    \<comment> \<open>the exactness identity is an INTEGER equation; move it to \<open>real\<close> in its own step rather
       than asking \<open>field_simps\<close> to cross the embedding and rearrange at once\<close>
    have eq: "real_of_int (L ^ h) * 2 ^ k = real_of_int A * 2 ^ (h * m)"
    proof -
      have "real_of_int (L ^ h * 2 ^ k) = real_of_int (A * 2 ^ (h * m))"
        using True by simp
      then show ?thesis by simp
    qed
    have "(real_of_int L / 2 ^ m) ^ h = real_of_int (L ^ h) / 2 ^ (h * m)"
      by (rule real_div_pow_pow)
    also have "\<dots> = real_of_int A / 2 ^ k"
      using eq by (simp add: field_simps)
    finally show ?thesis .
  qed
  have "poly Q ((real_of_int L / 2 ^ m) ^ h) = 0" using pw rootQ by simp
  from pow_sub_pair_ok_degenerate[OF h Pdef this]
  show ?thesis using R by simp
next
  case False
  \<comment> \<open>not exact: \<open>R = 1 + L\<close> and the Descartes count certifies the open window\<close>
  have R: "R = 1 + L" using Rdef False by simp
  have cnt: "descartes_preprocess (L ^ h) (2 ^ (h * m)) ((1 + L) ^ h) (2 ^ (h * m)) q = 1"
    using tst False unfolding pow_sub_deg_tst_def Ldef[symmetric] by (simp add: Let_def)
  have L0: "0 \<le> L" unfolding Ldef by (rule pow_sub_num_lo_nonneg[OF A0])
  have lt: "L ^ h * 2 ^ (h * m) < (1 + L) ^ h * 2 ^ (h * m)"
  proof -
    have "L ^ h < (1 + L) ^ h" using L0 h by (simp add: power_strict_mono)
    then show ?thesis by simp
  qed
  have lenc: "0 < length (coeffs Q0)" using len qdef by simp
  have one: "roots_in Q (real_of_int (L ^ h) / 2 ^ (h * m))
                        (real_of_int ((1 + L) ^ h) / 2 ^ (h * m)) = 1"
    using pow_sub_certify_isolates[OF lenc _ lt cnt[unfolded qdef]] Qdef by simp
  have u0: "0 \<le> real_of_int L / 2 ^ m" using L0 by simp
  have uv: "real_of_int L / 2 ^ m < real_of_int (1 + L) / 2 ^ m" by (simp add: divide_strict_right_mono)
  \<comment> \<open>\<open>simp only\<close>, not \<open>simp\<close>: full \<open>simp\<close> pushes \<open>real_of_int (1 + L)\<close> to \<open>1 + real_of_int L\<close>
     FIRST, after which @{thm real_div_pow_pow}'s \<open>real_of_int ?L\<close> pattern no longer matches the
     high endpoint — it rewrote the low one and stalled on the high one\<close>
  have "roots_in Q ((real_of_int L / 2 ^ m) ^ h) ((real_of_int (1 + L) / 2 ^ m) ^ h) = 1"
    using one by (simp only: real_div_pow_pow)
  from pow_sub_pair_ok_interval[OF h Pdef sf u0 uv this]
  show ?thesis using R by simp
qed

text \<open>The exactness identity, taken out of \<open>pow_sub_deg_tst_pair_ok\<close>'s \<open>True\<close> branch so that the covering lemma
  below can use it.\<close>

lemma pow_sub_deg_exact_pow:
  fixes A L :: int
  assumes exact: "L ^ h * 2 ^ k = A * 2 ^ (h * m)"
  shows "(real_of_int L / 2 ^ m) ^ h = real_of_int A / 2 ^ k"
proof -
  have eq: "real_of_int (L ^ h) * 2 ^ k = real_of_int A * 2 ^ (h * m)"
  proof -
    have "real_of_int (L ^ h * 2 ^ k) = real_of_int (A * 2 ^ (h * m))" using exact by simp
    then show ?thesis by simp
  qed
  have "(real_of_int L / 2 ^ m) ^ h = real_of_int (L ^ h) / 2 ^ (h * m)"
    by (rule real_div_pow_pow)
  also have "\<dots> = real_of_int A / 2 ^ k" using eq by (simp add: field_simps)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>The degenerate branch covers its own \<open>Q\<close>-root\<close>, in the closed sense, which is the best available: on an
  exactly representable root the emitted window is the point, so both bounds are equalities. No count reasoning is
  needed; it is floor/ceiling arithmetic on @{const pow_sub_lo}. It is stated over \<open>A\<close> because the degenerate input
  pins the \<open>Q\<close>-root: @{const dsc_pair_ok} at \<open>(a, a)\<close> says \<open>poly Q a = 0\<close>.\<close>

lemma pow_sub_deg_tst_cover:
  fixes A L R :: int
  assumes h: "0 < h" and A0: "0 \<le> A"
    and Ldef: "L = pow_sub_num_lo h m (real_of_int A / 2 ^ k)"
    and Rdef: "R = (if L ^ h * 2 ^ k = A * 2 ^ (h * m) then L else 1 + L)"
  shows "(real_of_int L / 2 ^ m) ^ h \<le> real_of_int A / 2 ^ k
       \<and> real_of_int A / 2 ^ k \<le> (real_of_int R / 2 ^ m) ^ h"
proof -
  define a where "a = real_of_int A / 2 ^ k"
  have a0: "0 \<le> a" unfolding a_def using A0 by simp
  have uLo: "real_of_int L / 2 ^ m = pow_sub_lo h m a"
    unfolding Ldef a_def[symmetric] by (simp add: pow_sub_lo_num)
  have lo: "(real_of_int L / 2 ^ m) ^ h \<le> a"
    unfolding uLo by (rule pow_sub_lo_pow_le[OF a0 h])
  have hi: "a \<le> (real_of_int R / 2 ^ m) ^ h"
  proof (cases "L ^ h * 2 ^ k = A * 2 ^ (h * m)")
    case True
    \<comment> \<open>exact: the emitted point's \<open>h\<close>-th power IS the root, so the bound is an equality\<close>
    have "R = L" using Rdef True by simp
    then show ?thesis using pow_sub_deg_exact_pow[OF True] unfolding a_def by simp
  next
    case False
    \<comment> \<open>not exact: \<open>R = 1 + L\<close>, and \<open>\<lfloor>\<rfloor>\<close>'s own lower bound puts \<open>a\<^sup>1\<^sup>/\<^sup>h\<close> strictly under
       \<open>(L+1)/2\<^sup>m\<close> — no count reasoning, just @{thm [source] pow_sub_lo_bounds}\<close>
    have R: "R = 1 + L" using Rdef False by simp
    \<comment> \<open>state the bound at the FIXED \<open>h\<close>/\<open>m\<close> first: \<open>pow_sub_lo_bounds\<close> leaves them schematic, and
       the rearrangement \<open>x - c < y \<Longrightarrow> x < y + c\<close> is \<open>linarith\<close>'s job, not \<open>simp\<close>'s\<close>
    have bnd: "a powr (1 / real h) - 1 / 2 ^ m < pow_sub_lo h m a"
      using pow_sub_lo_bounds[OF a0] by blast
    have "a powr (1 / real h) < pow_sub_lo h m a + 1 / 2 ^ m" using bnd by linarith
    also have "\<dots> = real_of_int (1 + L) / 2 ^ m" unfolding uLo[symmetric] by (simp add: field_simps)
    finally have lt: "a powr (1 / real h) < real_of_int (1 + L) / 2 ^ m" .
    have "a = (a powr (1 / real h)) ^ h" using a0 h by (rule powr_root_pow[symmetric])
    also have "\<dots> \<le> (real_of_int (1 + L) / 2 ^ m) ^ h" using lt by (simp add: power_mono)
    finally show ?thesis unfolding R a_def by simp
  qed
  from lo hi show ?thesis unfolding a_def by simp
qed

section \<open>Why the certify op has to test the window's ORIENTATION\<close>

text \<open>\<^bold>\<open>Why the certify op tests the sign of the width.\<close> @{const descartes_preprocess} reduces to
  \<open>descartes_transform na da (nb\<cdot>da - na\<cdot>db) db\<close>, whose width argument is signed. On an inverted window the width is
  negative, the Moebius image is the same open interval traversed backwards, and the count is still 1: a root count
  does not depend on the direction of the interval. Both evaluations below are \<open>by code_simp\<close> (kernel-checked, no evaluation
  oracle), on \<open>Q(y) = 2y - 3\<close>, whose
  only root is \<open>3/2\<close>:\<close>

lemma descartes_count_ordered:  "descartes_preprocess 1 1 2 1 [-3,2::int] = 1" by code_simp
lemma descartes_count_inverted: "descartes_preprocess 2 1 1 1 [-3,2::int] = 1" by code_simp

text \<open>\<^bold>\<open>Why an inverted window can reach the count.\<close> The proper branch emits \<open>L = \<lceil>a\<^sup>1\<^sup>/\<^sup>h \<cdot> 2\<^sup>m\<rceil>\<close> and
  \<open>R = \<lfloor>b\<^sup>1\<^sup>/\<^sup>h \<cdot> 2\<^sup>m\<rfloor>\<close>, and the search's first probe is \<open>m = k\<close>. Taking \<open>h\<close>-th roots compresses the gap (for \<open>h = 2\<close> near \<open>1\<close>,
  \<open>b\<^sup>1\<^sup>/\<^sup>2 - a\<^sup>1\<^sup>/\<^sup>2 \<approx> (b-a)/2\<close>), so at \<open>m = k\<close> the ceiling can exceed the floor and the window is inverted.
  @{const pow_sub_sign_tst} rejects that case (its first conjunct is \<open>L\<^sup>h < R\<^sup>h\<close>), so without the width test an
  inverted window would fall through to the count, which would accept it; the emitted pair would have \<open>fst > snd\<close>,
  for which @{const dsc_pair_ok} is false on both disjuncts, and the root would be lost. The certify op therefore
  includes one \<open>mpz_sgn\<close> on a value it already computes, and both pure tests (@{const pow_sub_deg_tst},
  @{const pow_sub_loop_tst}) carry the ordering conjunct, which the two bridges below need.\<close>

section \<open>The rational sign test, transported to the reals\<close>

text \<open>@{const pow_sub_sign_tst} is stated over \<open>rat\<close> (that is what the evaluation op computes);
  @{const dsc_pair_ok} and @{const roots_in} live over \<open>real\<close>. \<open>of_rat\<close> is a strict ring
  embedding, so the sign of a product survives.\<close>

lemma map_poly_rat_real:
  fixes Q0 :: "int poly"
  shows "map_poly (real_of_rat) (map_poly rat_of_int Q0) = map_poly real_of_int Q0"
proof -
  have "(real_of_rat \<circ> rat_of_int) = real_of_int" by (rule ext) simp
  then show ?thesis by (simp add: map_poly_map_poly)
qed

lemma poly_rat_to_real:
  fixes Q0 :: "int poly" and x :: rat
  shows "real_of_rat (poly (map_poly rat_of_int Q0) x)
           = poly (map_poly real_of_int Q0) (real_of_rat x)"
proof -
  have "poly (map_poly real_of_rat (map_poly rat_of_int Q0)) (real_of_rat x)
          = real_of_rat (poly (map_poly rat_of_int Q0) x)"
    by (rule of_rat_hom.poly_map_poly)
  \<comment> \<open>\<open>simp only\<close>: a full \<open>simp\<close> folds both sides into the \<open>of_int_poly\<close> / \<open>real_of_int_poly\<close>
     abbreviations before @{thm map_poly_rat_real} can fire on the composed \<open>map_poly\<close>\<close>
  then show ?thesis by (simp only: map_poly_rat_real)
qed

lemma pow_sub_sign_tst_real:
  fixes Q0 :: "int poly" and L R :: int
  assumes Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and tst: "pow_sub_sign_tst h m L R q"
  shows "L ^ h < R ^ h"
    and "poly Q (real_of_int (L ^ h) / 2 ^ (h * m))
         * poly Q (real_of_int (R ^ h) / 2 ^ (h * m)) < 0"
proof -
  have pq: "Poly q = Q0" using qdef by simp
  show lt: "L ^ h < R ^ h" using tst unfolding pow_sub_sign_tst_def by simp
  \<comment> \<open>the evaluation points: \<open>of_rat\<close> commutes with the division and with \<open>rat_of_int\<close>\<close>
  \<comment> \<open>stated in the form simp NORMALISES the op's term to: it pushes \<open>rat_of_int (L\<^sup>h)\<close> inwards to
     \<open>(rat_of_int L)\<^sup>h\<close> and \<open>rat_of_int (2\<^sup>h\<^sup>\<cdot>\<^sup>m)\<close> to the \<open>rat\<close> numeral, so a lemma phrased on
     \<open>rat_of_int n\<close> alone never matches\<close>
  have pt: "\<And>n::int. real_of_rat ((rat_of_int n) ^ h / 2 ^ (h * m))
                      = (real_of_int n) ^ h / 2 ^ (h * m)"
    by (simp add: of_rat_divide of_rat_power)
  have prod: "poly (map_poly rat_of_int Q0) (rat_of_int (L ^ h) / rat_of_int (2 ^ (h * m)))
              * poly (map_poly rat_of_int Q0) (rat_of_int (R ^ h) / rat_of_int (2 ^ (h * m)))
              < 0"
    using tst unfolding pow_sub_sign_tst_def pq by simp
  have "real_of_rat (poly (map_poly rat_of_int Q0)
                       (rat_of_int (L ^ h) / rat_of_int (2 ^ (h * m)))
                     * poly (map_poly rat_of_int Q0)
                       (rat_of_int (R ^ h) / rat_of_int (2 ^ (h * m)))) < 0"
    using prod by (metis of_rat_less_0_iff)
  then show "poly Q (real_of_int (L ^ h) / 2 ^ (h * m))
             * poly Q (real_of_int (R ^ h) / 2 ^ (h * m)) < 0"
    unfolding Qdef by (simp add: of_rat_mult poly_rat_to_real pt)
qed

section \<open>The PROPER branch: a shrunk window inside an isolating \<open>Q\<close>-interval\<close>

text \<open>Both disjuncts of @{const pow_sub_loop_tst} now deliver the orientation \<open>L\<^sup>h < R\<^sup>h\<close>, which is
  what lets the two of them share an endpoint argument. They differ only in how they establish
  \<open>roots_in Q = 1\<close> on the shrunk window:

  \<^item> the COUNT decides it outright (@{thm [source] pow_sub_certify_isolates});
  \<^item> the SIGN test decides it only \<^emph>\<open>relative to the enclosing \<open>Q\<close>-interval\<close> — a sign change gives
    at least one root by IVT, and the enclosing interval's own count of 1 caps it at one
    (@{thm [source] roots_in_one_of_sign_change}). This is why the reduced arm's
    @{const dsc_pair_ok} is a hypothesis here and not an afterthought.\<close>

text \<open>\<^bold>\<open>The completeness kernel.\<close> A shrunk window that isolates a root of its own, inside an enclosing interval
  that isolates exactly one root, isolates that same root, so every root of the enclosing interval survives into the
  shrunk one. The witness \<open>r\<close> is available in @{thm [source] pow_sub_shrink_exists}'s proof, and
  \<open>pow_sub_loop_tst_pair_ok\<close> below derives \<open>one\<close> and the containments \<open>lo\<close>/\<open>hi\<close>. Both counts are over open intervals,
  so this says nothing about a root exactly on an endpoint of \<open>(a, b)\<close>; that case is the degenerate branch.\<close>

lemma pow_sub_roots_in_sub_unique:
  fixes p :: "real poly" and y :: real
  assumes sf: "squarefree p"
    and core: "roots_in p a b = 1" and one: "roots_in p a' b' = 1"
    and le1: "a \<le> a'" and le2: "b' \<le> b"
    and y1: "a < y" and y2: "y < b" and ry: "poly p y = 0"
  shows "a' < y \<and> y < b'"
proof -
  from roots_in_one_witness[OF sf one] obtain r
    where r1: "a' < r" and r2: "r < b'" and rr: "poly p r = 0" by blast
  have card1: "card {x. a < x \<and> x < b \<and> poly p x = 0} = 1"
    using core roots_in_squarefree_card[OF sf] by simp
  \<comment> \<open>\<open>r\<close> lands in the ENCLOSING interval through the two containments\<close>
  have rin: "r \<in> {x. a < x \<and> x < b \<and> poly p x = 0}" using r1 r2 rr le1 le2 by simp
  have yin: "y \<in> {x. a < x \<and> x < b \<and> poly p x = 0}" using y1 y2 ry by simp
  from card1 obtain w where "{x. a < x \<and> x < b \<and> poly p x = 0} = {w}"
    by (rule card_1_singletonE)
  then have "r = y" using rin yin by auto
  with r1 r2 show ?thesis by simp
qed

lemma pow_sub_loop_tst_pair_ok_strong:
  fixes Q0 :: "int poly" and A B :: int
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len: "0 < length q"
    and A0: "0 \<le> A" and B0: "0 \<le> B"
    and ab: "real_of_int A / 2 ^ k < real_of_int B / 2 ^ k"
    and iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    and tst: "pow_sub_loop_tst h A B k q m"
    and Ldef: "L = pow_sub_num_hi h m (real_of_int A / 2 ^ k)"
    and Rdef: "R = pow_sub_num_lo h m (real_of_int B / 2 ^ k)"
  shows "dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
    \<and> (\<forall>y. real_of_int A / 2 ^ k < y \<longrightarrow> y < real_of_int B / 2 ^ k \<longrightarrow> poly Q y = 0
          \<longrightarrow> (real_of_int L / 2 ^ m) ^ h < y \<and> y < (real_of_int R / 2 ^ m) ^ h)"
proof -
  define a where "a = real_of_int A / 2 ^ k"
  define b where "b = real_of_int B / 2 ^ k"
  have a0: "0 \<le> a" unfolding a_def using A0 by simp
  have b0: "0 \<le> b" unfolding b_def using B0 by simp
  have sfQ: "squarefree Q" using h sf Pdef by (simp add: pcompose_monom_squarefreeD)
  have Qnz: "Q \<noteq> 0" using sfQ by auto
  have lenc: "0 < length (coeffs Q0)" using len qdef by simp

  \<comment> \<open>orientation, from either disjunct\<close>
  have lt: "L ^ h < R ^ h"
    using tst unfolding pow_sub_loop_tst_def pow_sub_sign_tst_def
      Ldef[symmetric, unfolded a_def[symmetric]] Rdef[symmetric, unfolded b_def[symmetric]]
      a_def[symmetric] b_def[symmetric]
    by auto
  have R0: "0 \<le> R" unfolding Rdef b_def[symmetric] unfolding b_def
    by (rule pow_sub_num_lo_nonneg[OF B0])
  have LR: "L < R" using lt R0 by (metis power_less_imp_less_base)

  define u where "u = real_of_int L / 2 ^ m"
  define v where "v = real_of_int R / 2 ^ m"
  have uhi: "u = pow_sub_hi h m a"
    unfolding u_def Ldef a_def[symmetric] by (simp add: pow_sub_hi_num)
  have vlo: "v = pow_sub_lo h m b"
    unfolding v_def Rdef b_def[symmetric] by (simp add: pow_sub_lo_num)
  have u0: "0 \<le> u" unfolding uhi by (rule pow_sub_hi_nonneg)
  have uv: "u < v" unfolding u_def v_def using LR by (simp add: divide_strict_right_mono)

  have uh: "u ^ h = real_of_int (L ^ h) / 2 ^ (h * m)"
    unfolding u_def by (rule real_div_pow_pow)
  have vh: "v ^ h = real_of_int (R ^ h) / 2 ^ (h * m)"
    unfolding v_def by (rule real_div_pow_pow)
  \<comment> \<open>cross the \<open>int \<rightarrow> real\<close> embedding in its OWN step: \<open>simp\<close> normalises \<open>real_of_int (L\<^sup>h)\<close> to
     \<open>(real_of_int L)\<^sup>h\<close> on sight, after which the \<open>int\<close> hypothesis no longer matches anything\<close>
  have ltr: "(real_of_int L) ^ h < (real_of_int R) ^ h"
  proof -
    \<comment> \<open>\<open>simp\<close> normalises the GOAL before it can use the \<open>int\<close> fact; \<open>of_int_less_iff\<close> is the
       bridge (sledgehammer-verified)\<close>
    have "real_of_int (L ^ h) < real_of_int (R ^ h)" using lt by (metis of_int_less_iff)
    then show ?thesis by simp
  qed
  have uvh: "u ^ h < v ^ h"
    unfolding uh vh using ltr by (simp add: divide_strict_right_mono)

  \<comment> \<open>the shrink: the emitted window's \<open>Q\<close>-image sits INSIDE the reduced interval\<close>
  have lo: "a \<le> u ^ h" unfolding uhi by (rule pow_sub_hi_pow_ge[OF a0 h])
  have hi: "v ^ h \<le> b" unfolding vlo by (rule pow_sub_lo_pow_le[OF b0 h])

  have one: "roots_in Q (u ^ h) (v ^ h) = 1"
  proof (cases "pow_sub_sign_tst h m L R q")
    case True
    \<comment> \<open>IVT gives \<open>\<ge> 1\<close>; the enclosing interval's count of 1 gives \<open>\<le> 1\<close>\<close>
    have core: "roots_in Q a b = 1"
      using iv ab unfolding dsc_pair_ok_def a_def[symmetric] b_def[symmetric] by simp
    have chg: "poly Q (u ^ h) * poly Q (v ^ h) < 0"
      using pow_sub_sign_tst_real(2)[OF Qdef qdef True] unfolding uh vh .
    show ?thesis by (rule roots_in_one_of_sign_change[OF Qnz uvh lo hi core chg])
  next
    case False
    have cnt: "descartes_preprocess (L ^ h) (2 ^ (h * m)) (R ^ h) (2 ^ (h * m)) q = 1"
      using tst False unfolding pow_sub_loop_tst_def
        Ldef[symmetric, unfolded a_def[symmetric]] Rdef[symmetric, unfolded b_def[symmetric]]
        a_def[symmetric] b_def[symmetric]
      by auto
    have lt': "L ^ h * 2 ^ (h * m) < R ^ h * 2 ^ (h * m)" using lt by simp
    show ?thesis
      using pow_sub_certify_isolates[OF lenc _ lt' cnt[unfolded qdef]] Qdef
      unfolding uh vh by simp
  qed
  have pk: "dsc_pair_ok P (u, v)"
    by (rule pow_sub_pair_ok_interval[OF h Pdef sf u0 uv one])
  \<comment> \<open>The enclosing count, outside the sign branch (it needs only \<open>iv\<close> and \<open>ab\<close>; \<open>ab\<close> rules out
     @{const dsc_pair_ok}'s degenerate disjunct), so the covering clause is available on both branches.\<close>
  have coreAB: "roots_in Q a b = 1"
    using iv ab unfolding dsc_pair_ok_def a_def[symmetric] b_def[symmetric] by simp
  have cover: "\<forall>y. a < y \<longrightarrow> y < b \<longrightarrow> poly Q y = 0 \<longrightarrow> u ^ h < y \<and> y < v ^ h"
    using pow_sub_roots_in_sub_unique[OF sfQ coreAB one lo hi] by blast
  from pk cover
  show ?thesis unfolding u_def[symmetric] v_def[symmetric] a_def[symmetric] b_def[symmetric]
    by blast
qed

text \<open>The ORIGINAL statement, kept verbatim so \<open>pow_sub_emit_ok_pair_ok\<close>'s call site
  is untouched. A strict weakening — the first conjunct.\<close>
lemma pow_sub_loop_tst_pair_ok:
  fixes Q0 :: "int poly" and A B :: int
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len: "0 < length q"
    and A0: "0 \<le> A" and B0: "0 \<le> B"
    and ab: "real_of_int A / 2 ^ k < real_of_int B / 2 ^ k"
    and iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    and tst: "pow_sub_loop_tst h A B k q m"
    and Ldef: "L = pow_sub_num_hi h m (real_of_int A / 2 ^ k)"
    and Rdef: "R = pow_sub_num_lo h m (real_of_int B / 2 ^ k)"
  shows "dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)"
  using pow_sub_loop_tst_pair_ok_strong[OF h Pdef sf Qdef qdef len A0 B0 ab iv tst Ldef Rdef]
  by blast

section \<open>What one emitted interval establishes\<close>

text \<open>The bundle @{const pow_sub_emit_ok} is the per-interval postcondition the loop carries; this lemma takes it
  to @{const dsc_pair_ok}, which needs \<open>P = Q \<circ>\<^sub>p monom 1 h\<close> in scope. The reduced solve's own isolation,
  \<open>dsc_pair_ok Q\<close> on the input interval, is a hypothesis: the degenerate branch needs it to know that \<open>Q\<close> vanishes at
  the point, and the sign branch needs its count of 1 as the upper bound the intermediate value theorem does not
  give.\<close>

theorem pow_sub_emit_ok_pair_ok:
  fixes Q0 :: "int poly" and A B :: int
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len: "0 < length q"
    and A0: "0 \<le> A" and B0: "0 \<le> B" and AB: "A \<le> B"
    and iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    and ok: "pow_sub_emit_ok h q ((A, B), k) ((L, R), m)"
  shows "dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)"
proof (cases "A = B")
  case True
  have tst: "pow_sub_deg_tst h A k q m"
    and Ld: "L = pow_sub_num_lo h m (real_of_int A / 2 ^ k)"
    and Rd: "R = (if L ^ h * 2 ^ k = A * 2 ^ (h * m) then L else 1 + L)"
    using ok True unfolding pow_sub_emit_ok_def by (simp_all add: Let_def)
  have iv': "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int A / 2 ^ k)"
    using iv True by simp
  show ?thesis
    by (rule pow_sub_deg_tst_pair_ok[OF h Pdef sf Qdef qdef len A0 iv' tst Ld Rd])
next
  case False
  have ab: "real_of_int A / 2 ^ k < real_of_int B / 2 ^ k"
    using AB False by (simp add: divide_strict_right_mono)
  have tst: "pow_sub_loop_tst h A B k q m"
    and Ld: "L = pow_sub_num_hi h m (real_of_int A / 2 ^ k)"
    and Rd: "R = pow_sub_num_lo h m (real_of_int B / 2 ^ k)"
    using ok False unfolding pow_sub_emit_ok_def by (simp_all add: Let_def)
  show ?thesis
    by (rule pow_sub_loop_tst_pair_ok[OF h Pdef sf Qdef qdef len A0 B0 ab iv tst Ld Rd])
qed

text \<open>\<^bold>\<open>The covering counterpart of the bundle\<close>: every \<open>Q\<close>-root the reduced interval isolates survives into the
  emitted window's \<open>Q\<close>-image, so no root is lost per interval.

  The second hypothesis makes the endpoint case explicit: on a degenerate input the root is pinned (\<open>y = a\<close>); on a
  proper one it lies strictly inside \<open>(a, b)\<close>, which is all @{const dsc_pair_ok} constrains (its count is over the
  open interval). That a \<open>Q\<close>-root never lies on an endpoint of a proper emitted interval is a fact about the reduced
  solve's output, supplied separately.

  The conclusion is closed (\<open>\<le>\<close>) although the proper branch proves strict: the degenerate branch cannot do better (on
  an exactly representable root the emitted window is the point), and closed is what the lift needs.\<close>

theorem pow_sub_emit_ok_pair_ok_strong:
  fixes Q0 :: "int poly" and A B :: int
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len: "0 < length q"
    and A0: "0 \<le> A" and B0: "0 \<le> B" and AB: "A \<le> B"
    and iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    and ok: "pow_sub_emit_ok h q ((A, B), k) ((L, R), m)"
  shows "dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
    \<and> (\<forall>y. poly Q y = 0
        \<longrightarrow> (if A = B then y = real_of_int A / 2 ^ k
             else real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
        \<longrightarrow> (real_of_int L / 2 ^ m) ^ h \<le> y \<and> y \<le> (real_of_int R / 2 ^ m) ^ h)"
proof (cases "A = B")
  case True
  have tst: "pow_sub_deg_tst h A k q m"
    and Ld: "L = pow_sub_num_lo h m (real_of_int A / 2 ^ k)"
    and Rd: "R = (if L ^ h * 2 ^ k = A * 2 ^ (h * m) then L else 1 + L)"
    using ok True unfolding pow_sub_emit_ok_def by (simp_all add: Let_def)
  have iv': "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int A / 2 ^ k)"
    using iv True by simp
  have pk: "dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)"
    by (rule pow_sub_deg_tst_pair_ok[OF h Pdef sf Qdef qdef len A0 iv' tst Ld Rd])
  have cov: "(real_of_int L / 2 ^ m) ^ h \<le> real_of_int A / 2 ^ k
           \<and> real_of_int A / 2 ^ k \<le> (real_of_int R / 2 ^ m) ^ h"
    by (rule pow_sub_deg_tst_cover[OF h A0 Ld Rd])
  show ?thesis using pk cov True by simp
next
  case False
  have ab: "real_of_int A / 2 ^ k < real_of_int B / 2 ^ k"
    using AB False by (simp add: divide_strict_right_mono)
  have tst: "pow_sub_loop_tst h A B k q m"
    and Ld: "L = pow_sub_num_hi h m (real_of_int A / 2 ^ k)"
    and Rd: "R = pow_sub_num_lo h m (real_of_int B / 2 ^ k)"
    using ok False unfolding pow_sub_emit_ok_def by (simp_all add: Let_def)
  show ?thesis
    using pow_sub_loop_tst_pair_ok_strong[OF h Pdef sf Qdef qdef len A0 B0 ab iv tst Ld Rd]
          False by auto
qed

text \<open>\<^bold>\<open>The lift step\<close>, the formal content of the wrapper storing one vector into both output slots. If the emitted
  window's \<open>Q\<close>-image brackets \<open>x\<^sup>d\<close>, then \<open>x\<close> lies in the window or in its reflection, because for even \<open>d\<close> the map
  \<open>t \<mapsto> t\<^sup>d\<close> is 2-to-1 through the origin and order-reflecting on the nonnegatives. For odd \<open>d\<close> the conclusion is false:
  the map is a bijection, \<open>x\<close> has the sign of \<open>x\<^sup>d\<close>, and the reflected window brackets nothing.\<close>

lemma pow_sub_window_covers_lift:
  fixes x u v :: real
  assumes d: "0 < d" and ev: "even d"
    and u0: "0 \<le> u" and v0: "0 \<le> v"
    and lo: "u ^ d \<le> x ^ d" and hi: "x ^ d \<le> v ^ d"
  shows "(u \<le> x \<and> x \<le> v) \<or> (- v \<le> x \<and> x \<le> - u)"
proof -
  have abs_pow: "\<bar>x\<bar> ^ d = x ^ d" using ev by (simp add: power_even_abs)
  have a0: "0 \<le> \<bar>x\<bar>" by simp
  \<comment> \<open>both directions through @{thm [source] power_le_imp_le_base}, which needs a nonnegative base; that is why the
     window's \<open>0 \<le> L\<close> is carried with the isolation. It is stated over \<open>Suc n\<close>, so the exponent is destructured
     first.\<close>
  obtain n where dn: "d = Suc n" using d by (cases d) auto
  have ul: "u \<le> \<bar>x\<bar>"
  proof -
    have "u ^ Suc n \<le> \<bar>x\<bar> ^ Suc n" using lo abs_pow dn by simp
    then show ?thesis by (rule power_le_imp_le_base[OF _ a0])
  qed
  have uv: "\<bar>x\<bar> \<le> v"
  proof -
    have "\<bar>x\<bar> ^ Suc n \<le> v ^ Suc n" using hi abs_pow dn by simp
    then show ?thesis by (rule power_le_imp_le_base[OF _ v0])
  qed
  show ?thesis
  proof (cases "0 \<le> x")
    case True
    then show ?thesis using ul uv by simp
  next
    case False
    then have "\<bar>x\<bar> = - x" by simp
    then show ?thesis using ul uv by simp
  qed
qed

section \<open>The per-interval ops, with abstract specifications\<close>

text \<open>\<open>Power_Sub_Emit_All_Impl\<close> gives these ops HNR rules only, so the loop below has nothing to
  reason with. Each spec here is the shape of the one proven analog in the tree,
  @{thm [source] pow_sub_backmap_iv_monadic_correct}.\<close>

lemma pow_sub_backmap_deg_iv_correct:
  fixes A :: int
  assumes h: "0 < h" and A0: "0 \<le> A"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
    and hm: "h * m < max_snat LENGTH(gmp_poly_len)"
    and adef: "a = real_of_int A / 2 ^ k"
  shows "pow_sub_backmap_deg_iv_monadic h m A k
           \<le> SPEC (\<lambda>(l, r). pow_sub_lo h m a = real_of_int l / 2 ^ m
                             \<and> pow_sub_hi h m a = real_of_int r / 2 ^ m)"
  unfolding pow_sub_backmap_deg_iv_monadic_def PR_CONST_def
  using h A0 hb k hm
  apply (refine_vcg
         root_floor_gmp2_is_pow_sub_lo[OF h A0 hb k hm adef, THEN order_trans]
         pow_sub_ceil_monadic_is_pow_sub_hi[OF h A0 hb k hm adef, THEN order_trans])
  apply (all \<open>(simp; fail) | blast\<close>)
  done

text \<open>The emit op, in the NUMERATOR form @{const pow_sub_emit_ok} speaks. Dividing by \<open>2\<^sup>m\<close> is
  injective, which is what @{thm [source] pow_sub_num_lo_unique} and
  @{thm [source] pow_sub_num_hi_unique} turn into an equation on the integer the op returns.\<close>

lemma pow_sub_iv_emit_mop_correct:
  fixes A B :: int
  assumes h: "0 < h" and A0: "0 \<le> A" and B0: "0 \<le> B"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
    and hm: "h * m < max_snat LENGTH(gmp_poly_len)"
    and adef: "a = real_of_int A / 2 ^ k" and bdef: "b = real_of_int B / 2 ^ k"
  shows "pow_sub_iv_emit_mop h m A B k dg
           \<le> SPEC (\<lambda>(l, r).
                 if dg then l = pow_sub_num_lo h m a \<and> r = pow_sub_num_hi h m a
                 else l = pow_sub_num_hi h m a \<and> r = pow_sub_num_lo h m b)"
  unfolding pow_sub_iv_emit_mop_def PR_CONST_def
  using h A0 B0 hb k hm
  apply (refine_vcg
         pow_sub_backmap_deg_iv_correct[OF h A0 hb k hm adef, THEN order_trans]
         pow_sub_backmap_iv_monadic_correct[OF h A0 B0 hb k hm adef bdef, THEN order_trans])
  apply (all \<open>(auto simp: pow_sub_num_lo_unique pow_sub_num_hi_unique; fail)
              | (simp; fail) | blast\<close>)
  done

text \<open>The search op. \<open>mcap = k + dlt\<close> is relative to the caller's exponent: the reduced interval is already known to
  precision \<open>2\<^sup>-\<^sup>k\<close>, so the search starts at \<open>k\<close>.\<close>

lemma pow_sub_iv_search_mop_correct:
  fixes A B :: int
  assumes h: "0 < h" and A0: "0 \<le> A" and B0: "0 \<le> B"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
    and kd: "k + dlt < max_snat LENGTH(gmp_poly_len)"
    and hkd: "h * (k + dlt) < max_snat LENGTH(gmp_poly_len)"
    and ekd: "h * (k + dlt) * length q < max_snat LENGTH(gmp_poly_len)"
    and len0: "0 < length q"
    and len: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_iv_search_mop h q dlt A B k dg
           \<le> SPEC (\<lambda>(m, ok). k \<le> m \<and> m \<le> k + dlt
                              \<and> (ok \<longrightarrow> (if dg then pow_sub_deg_tst h A k q m
                                          else pow_sub_loop_tst h A B k q m)))"
  unfolding pow_sub_iv_search_mop_def PR_CONST_def
  using h A0 B0 hb k kd hkd ekd len0 len
  apply (refine_vcg
         pow_sub_deg_search_monadic_correct[OF h A0 hb le_add1 k hkd kd len,
                                            THEN order_trans]
         pow_sub_search_monadic_correct[OF h A0 B0 hb le_add1 k hkd ekd kd len0 len,
                                        THEN order_trans])
  apply (all \<open>(auto; fail) | (simp; fail) | blast\<close>)
  done

text \<open>The degenerate branch's high endpoint, as @{const pow_sub_emit_ok} states it. The emit op
  returns \<open>\<lceil>\<cdot>\<rceil>\<close>; the bundle states \<open>L\<close> or \<open>1 + L\<close> according to the SAME exact integer identity the
  search evaluates. @{thm [source] pow_sub_hi_num_exact} / @{thm [source] pow_sub_hi_num_strict}
  are the two halves.\<close>

lemma pow_sub_num_hi_of_lo:
  fixes A :: int
  assumes h: "0 < h" and A0: "0 \<le> A" and adef: "a = real_of_int A / 2 ^ k"
  shows "pow_sub_num_hi h m a
           = (if (pow_sub_num_lo h m a) ^ h * 2 ^ k = A * 2 ^ (h * m)
              then pow_sub_num_lo h m a else 1 + pow_sub_num_lo h m a)"
proof (cases "(pow_sub_num_lo h m a) ^ h * 2 ^ k = A * 2 ^ (h * m)")
  case True
  have "pow_sub_hi h m a = real_of_int (pow_sub_num_lo h m a) / 2 ^ m"
    by (rule pow_sub_hi_num_exact[OF h A0 adef pow_sub_lo_num True])
  from pow_sub_num_hi_unique[OF this] show ?thesis using True by simp
next
  case False
  have "pow_sub_hi h m a = real_of_int (1 + pow_sub_num_lo h m a) / 2 ^ m"
    by (rule pow_sub_hi_num_strict[OF h A0 adef pow_sub_lo_num False])
  from pow_sub_num_hi_unique[OF this] show ?thesis using False by simp
qed

section \<open>One interval's work establishes \<open>pow_sub_emit_ok\<close>\<close>

text \<open>The body's per-interval core, in the order the op runs it: decide degeneracy, search for a
  precision, emit at the accepted precision. The \<open>m\<close> the emit uses is the one the search
  accepted — that is what ties the two halves of @{const pow_sub_emit_ok} together.\<close>

lemma pow_sub_iv_emit_ok:
  fixes A B :: int
  assumes h: "0 < h" and A0: "0 \<le> A" and B0: "0 \<le> B"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
    and kd: "k + dlt < max_snat LENGTH(gmp_poly_len)"
    and hkd: "h * (k + dlt) < max_snat LENGTH(gmp_poly_len)"
    and ekd: "h * (k + dlt) * length q < max_snat LENGTH(gmp_poly_len)"
    and len0: "0 < length q"
    and len: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "doN {
           dg \<leftarrow> pow_sub_iv_degen_mop A B;
           sr \<leftarrow> pow_sub_iv_search_mop h q dlt A B k dg;
           case sr of (m, ok') \<Rightarrow> doN {
             lr \<leftarrow> pow_sub_iv_emit_mop h m A B k dg;
             RETURN (lr, m, ok')
           }
         } \<le> SPEC (\<lambda>(lr, m, ok'). ok' \<longrightarrow> pow_sub_emit_ok h q ((A, B), k) (lr, m))"
proof -
  have hm: "\<And>m. m \<le> k + dlt \<Longrightarrow> h * m < max_snat LENGTH(gmp_poly_len)"
    using hkd by (meson mult_le_mono2 order_le_less_trans)
  show ?thesis
    apply (refine_vcg
           pow_sub_iv_degen_mop_correct[THEN order_trans]
           pow_sub_iv_search_mop_correct[OF h A0 B0 hb k kd hkd ekd len0 len,
                                         THEN order_trans]
           pow_sub_iv_emit_mop_correct[OF h A0 B0 hb k _ refl refl, THEN order_trans])
    \<comment> \<open>one \<open>subgoal\<close> per obligation rather than a blanket \<open>all\<close>: the two are unrelated (a word
       bound, then the bundle) and a blanket closer reports both as failing when either does\<close>
    \<comment> \<open>\<^bold>\<open>\<open>use hm in\<close>, not \<open>intro!: hm\<close>.\<close> \<open>LENGTH(gmp_poly_len)\<close> is \<open>len_of TYPE(64)\<close>, a term rather than the numeral;
       \<open>auto\<close> normalises it to \<open>64\<close> in the goal via the Word library's \<open>len_num1\<close>/\<open>len_bit0\<close>, while an \<open>intro!\<close> rule is
       matched unnormalised, so \<open>hm\<close> would not unify. Inserting \<open>hm\<close> into the goal lets simp normalise fact and goal
       together. \<open>auto\<close> splits this into two bounds (the \<open>ok' = False\<close> exit and the certified exit), and the closer
       discharges both.\<close>
    subgoal by (use hm in \<open>auto split: prod.splits\<close>)
    \<comment> \<open>\<^bold>\<open>BOTH instances of @{thm [source] pow_sub_num_hi_of_lo}, at \<open>A\<close> and at \<open>B\<close>.\<close> The degenerate
       branch carries \<open>A = B\<close> as a premise, and \<open>auto\<close> orients it left-to-right, so the goal it
       actually leaves speaks of \<open>real_of_int B / 2\<^sup>k\<close> while the \<open>A\<close>-instance supplied as a simp
       rule is pinned at \<open>A\<close> and never fires — a supplied rule is NOT re-oriented by the goal's own
       premises. \<open>B0\<close> is what makes the \<open>B\<close>-instance available; it is otherwise unused here.\<close>
    subgoal by (auto simp: pow_sub_emit_ok_def Let_def
                           pow_sub_num_hi_of_lo[OF h A0 refl]
                           pow_sub_num_hi_of_lo[OF h B0 refl]
                    split: prod.splits if_splits)
    done
qed

section \<open>The loop's per-entry precondition\<close>

text \<open>The body ASSERTs six facts about the interval it just read out of the reduced arm's vector.
  They are not derivable from anything the loop knows, so they are a PRECONDITION on \<open>accQ\<close> —
  and naming them once, per entry, is what keeps the loop statement readable. The entry
  (\<open>Power_Sub_Entry_Impl\<close>, which only \<open>export.sh full\<close> compiles) is what must establish them.

  \<open>0 \<le> A\<close> and \<open>0 \<le> B\<close> are the substantive ones: the back-map is defined on the POSITIVE half
  only, and the reduced solve's positive vector is what the entry passes here. The other four are
  word headroom.\<close>

definition pow_sub_iv_pre :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> (int \<times> int) \<times> nat \<Rightarrow> bool" where
  "pow_sub_iv_pre h q dlt iv \<equiv>
     (let ((A, B), k) = iv in
        0 \<le> A \<and> 0 \<le> B
        \<and> k < max_snat LENGTH(gmp_poly_len)
        \<and> k + dlt < max_snat LENGTH(gmp_poly_len)
        \<and> h * (k + dlt) < max_snat LENGTH(gmp_poly_len)
        \<and> h * (k + dlt) * length q < max_snat LENGTH(gmp_poly_len))"

section \<open>The tail op appends exactly one triple\<close>

text \<open>@{const pow_sub_emit_push_mop} inlines the three column appends rather than calling
  @{const dyadic_interval_vec_push_monadic} (the wrapper does not synthesise from a nested loop state), so it needs its
  own specification. Its body is the wrapper's body under the same two ASSERTs, plus the index increment and the flag
  conjunction.\<close>

lemma pow_sub_emit_push_mop_correct:
  assumes ivo: "dyadic_interval_vec_invar out"
    and capo: "dyadic_interval_vec_pushable out"
    and i1: "i + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_emit_push_mop (i, ok, out) L R m ok'
           \<le> SPEC (\<lambda>(i', ok'', out').
                 i' = i + 1 \<and> ok'' = (ok \<and> ok')
                 \<and> dyadic_interval_vec_invar out'
                 \<and> dyadic_interval_vec_triples out'
                     = dyadic_interval_vec_triples out @ [((L, R), m)])"
proof -
  \<comment> \<open>\<^bold>\<open>not \<open>o\<close>\<close> for the destructuring equation — that name parses as function composition\<close>
  obtain lns rns ks where outeq: "out = (lns, rns, ks)" by (cases out)
  show ?thesis
    unfolding pow_sub_emit_push_mop_def PR_CONST_def outeq
      poly_push_coeff_monadic_def mop_list_append_alt
      pow_sub_succ_mop_def pow_sub_and_mop_def
    using ivo capo i1
    apply (refine_vcg)
    apply (all \<open>auto simp: outeq Let_def dyadic_interval_vec_invar_def
                           dyadic_interval_vec_pushable_def
                           dyadic_interval_vec_triples_def\<close>)
    done
qed

section \<open>Assembling the bundle from what the ops return\<close>

text \<open>The per-interval ops return the degeneracy flag, the accepted precision and the two
  endpoints separately; @{const pow_sub_emit_ok} is the conjunction of exactly those, with the
  degenerate branch's high endpoint written as \<open>L\<close>-or-\<open>1 + L\<close> rather than as a ceiling. Stating
  the assembly ONCE, as an intro rule, keeps @{thm [source] pow_sub_emit_ok_def} out of the body's
  closing simp set, where \<open>auto\<close> would unfold the bundle and then have to guess the
  appended triple's witness from the exploded form.\<close>

lemma pow_sub_emit_ok_intro:
  fixes A B :: int
  \<comment> \<open>\<open>B0\<close> is needed ONLY for the \<open>A = B\<close> branch, where \<open>auto\<close> orients the premise left-to-right
     and leaves the goal on \<open>B\<close> — the same trap as in @{thm [source] pow_sub_iv_emit_ok}. Both
     instances of @{thm [source] pow_sub_num_hi_of_lo} are supplied for that reason.\<close>
  assumes h: "0 < h" and A0: "0 \<le> A" and B0: "0 \<le> B"
    and tst: "if A = B then pow_sub_deg_tst h A k q m
              else pow_sub_loop_tst h A B k q m"
    and L: "L = (if A = B then pow_sub_num_lo h m (real_of_int A / 2 ^ k)
                 else pow_sub_num_hi h m (real_of_int A / 2 ^ k))"
    and R: "R = (if A = B then pow_sub_num_hi h m (real_of_int A / 2 ^ k)
                 else pow_sub_num_lo h m (real_of_int B / 2 ^ k))"
  shows "pow_sub_emit_ok h q ((A, B), k) ((L, R), m)"
  unfolding pow_sub_emit_ok_def
  using tst L R
  by (auto simp: Let_def pow_sub_num_hi_of_lo[OF h A0 refl]
                 pow_sub_num_hi_of_lo[OF h B0 refl]
           split: if_splits)

section \<open>One body step: read, decide, emit, append\<close>

text \<open>The body reads interval \<open>i\<close> out of \<open>accQ\<close>, runs the per-interval core proved above, and
  appends the result. Everything the step establishes about the OUTPUT vector is relative: it
  grows by exactly one triple, and when the flag survives, that triple carries the bundle for
  input \<open>i\<close>. The loop below turns "relative" into "for every index".\<close>

text \<open>\<^bold>\<open>The core is its own lemma because \<open>copy_get\<close> introduces fresh variables.\<close>
  @{const dyadic_interval_vec_copy_get_monadic} binds its result to fresh variables, and their connection to \<open>A\<close>, \<open>B\<close>,
  \<open>k\<close> is an equation in the premises, not a syntactic identity, so a hint instantiated at \<open>A\<close>, \<open>B\<close>, \<open>k\<close> would not unify
  and \<open>refine_vcg\<close> would stall with the remaining chain inside a \<open>SPEC\<close>. Stated generally, the hint unifies with
  whatever \<open>copy_get\<close> produced, and its hypotheses return as subgoals that the equation discharges.\<close>

lemma pow_sub_emit_body_core:
  fixes A B :: int
  assumes h: "0 < h" and A0: "0 \<le> A" and B0: "0 \<le> B"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and kb: "k < max_snat LENGTH(gmp_poly_len)"
    and kd: "k + dlt < max_snat LENGTH(gmp_poly_len)"
    and hkd: "h * (k + dlt) < max_snat LENGTH(gmp_poly_len)"
    and ekd: "h * (k + dlt) * length q < max_snat LENGTH(gmp_poly_len)"
    and len0: "0 < length q"
    and len: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
    and i1: "i + 1 < max_snat LENGTH(gmp_poly_len)"
    and ivo: "dyadic_interval_vec_invar out"
    and capo: "dyadic_interval_vec_pushable out"
  shows "doN {
           dg \<leftarrow> pow_sub_iv_degen_mop A B;
           sr \<leftarrow> pow_sub_iv_search_mop h q dlt A B k dg;
           case sr of (m, ok') \<Rightarrow> doN {
             ASSERT (h * m < max_snat LENGTH(gmp_poly_len));
             lr \<leftarrow> pow_sub_iv_emit_mop h m A B k dg;
             case lr of (L, R) \<Rightarrow> doN {
               \<comment> \<open>\<^bold>\<open>Bare, not \<open>PR_CONST mpzb_discard_monadic\<close>.\<close> The body proof unfolds \<open>PR_CONST_def\<close>, so its goal carries
                  the bare constant, and a statement keeping the \<open>PR_CONST\<close> marker would not unify with it.\<close>
               mpzb_discard_monadic A;
               mpzb_discard_monadic B;
               pow_sub_emit_push_mop (i, ok, out) L R m ok'
             }
           }
         } \<le> SPEC (\<lambda>(i', ok'', out').
                 i' = i + 1
                 \<and> dyadic_interval_vec_invar out'
                 \<and> length (dyadic_interval_vec_triples out')
                     = length (dyadic_interval_vec_triples out) + 1
                 \<and> (\<forall>j < length (dyadic_interval_vec_triples out).
                        dyadic_interval_vec_triples out' ! j
                          = dyadic_interval_vec_triples out ! j)
                 \<and> (ok'' \<longrightarrow> ok \<and> pow_sub_emit_ok h q ((A, B), k)
                                     (dyadic_interval_vec_triples out'
                                        ! length (dyadic_interval_vec_triples out))))"
proof -
  have hm: "\<And>m. m \<le> k + dlt \<Longrightarrow> h * m < max_snat LENGTH(gmp_poly_len)"
    using hkd by (meson mult_le_mono2 order_le_less_trans)
  show ?thesis
    unfolding PR_CONST_def mpzb_discard_monadic_def
    apply (refine_vcg
           pow_sub_iv_degen_mop_correct[THEN order_trans]
           pow_sub_iv_search_mop_correct[OF h A0 B0 hb kb kd hkd ekd len0 len,
                                         THEN order_trans]
           pow_sub_iv_emit_mop_correct[OF h A0 B0 hb kb _ refl refl, THEN order_trans]
           pow_sub_emit_push_mop_correct[OF ivo capo i1, THEN order_trans])
    apply (all \<open>(use hm in \<open>auto simp: nth_append
                                intro!: pow_sub_emit_ok_intro[OF h A0 B0]
                                 split: prod.splits\<close>)\<close>)
    done
qed

lemma pow_sub_emit_body_mop_correct:
  assumes h: "0 < h" and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and len0: "0 < length q" and len: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
    and ivQ: "dyadic_interval_vec_invar accQ"
    and nlen: "n = length (fst accQ)"
    and ilt: "i < n"
    and i1: "i + 1 < max_snat LENGTH(gmp_poly_len)"
    and pre: "pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! i)"
    and ivo: "dyadic_interval_vec_invar out"
    and capo: "dyadic_interval_vec_pushable out"
  \<comment> \<open>\<^bold>\<open>No existential.\<close> The appended triple is named by its POSITION — \<open>triples out' !
     length (triples out)\<close> — so nothing has to guess a witness, and the three conjuncts are
     exactly what the loop invariant consumes: the prefix is untouched, the length grows by one,
     and the new entry carries the bundle whenever the flag survives.\<close>
  shows "pow_sub_emit_body_mop h q dlt accQ n (i, ok, out)
           \<le> SPEC (\<lambda>(i', ok'', out').
                 i' = i + 1
                 \<and> dyadic_interval_vec_invar out'
                 \<and> length (dyadic_interval_vec_triples out')
                     = length (dyadic_interval_vec_triples out) + 1
                 \<and> (\<forall>j < length (dyadic_interval_vec_triples out).
                        dyadic_interval_vec_triples out' ! j
                          = dyadic_interval_vec_triples out ! j)
                 \<and> (ok'' \<longrightarrow> ok \<and> pow_sub_emit_ok h q
                                     (dyadic_interval_vec_triples accQ ! i)
                                     (dyadic_interval_vec_triples out'
                                        ! length (dyadic_interval_vec_triples out))))"
proof -
  obtain lns rns ks where Qeq: "accQ = (lns, rns, ks)" by (cases accQ)
  obtain A B k where trip: "dyadic_interval_vec_triples accQ ! i = ((A, B), k)"
    by (metis surj_pair)
  have A0: "0 \<le> A" and B0: "0 \<le> B"
    and kb: "k < max_snat LENGTH(gmp_poly_len)"
    and kd: "k + dlt < max_snat LENGTH(gmp_poly_len)"
    and hkd: "h * (k + dlt) < max_snat LENGTH(gmp_poly_len)"
    and ekd: "h * (k + dlt) * length q < max_snat LENGTH(gmp_poly_len)"
    using pre unfolding pow_sub_iv_pre_def trip by (simp_all add: Let_def)
  have ilns: "i < length lns" using ilt nlen Qeq by simp
  show ?thesis
    unfolding pow_sub_emit_body_mop_def PR_CONST_def Qeq
    using h hb len0 len ivQ ilt i1 ivo capo ilns
    \<comment> \<open>\<^bold>\<open>the core hint is left UNINSTANTIATED\<close> so it unifies with whatever \<open>copy_get\<close> bound; its
       twelve hypotheses come back as subgoals and \<open>trip\<close> — rewriting the spec's equation
       \<open>((A', B'), k') = triples accQ ! i\<close> down to \<open>((A, B), k)\<close> — is what discharges them\<close>
    apply (refine_vcg
           dyadic_interval_vec_copy_get_monadic_spec[THEN order_trans]
           pow_sub_emit_body_core[THEN order_trans])
    \<comment> \<open>\<^bold>\<open>the entry facts are INSERTED, not supplied as simp rules\<close> — the third instance of the
       same trap in this file. \<open>trip\<close> speaks of \<open>accQ\<close>; the goal, after \<open>copy_get\<close> re-generalised
       the columns, speaks of a fresh triple with \<open>accQ = (x1, x1a, x2a)\<close> only as a PREMISE. A
       supplied rule is matched as written, so \<open>trip\<close> never fires; inserted, it is normalised by
       that premise along with the goal and the chain
       \<open>((aba, aca), bc) = triples accQ ! i = ((A, B), k)\<close> closes each bound.\<close>
    \<comment> \<open>\<open>invar_def\<close> is what turns the ASSERTed \<open>i < length rns\<close> / \<open>i < length ks\<close> into
       \<open>i < length lns\<close> — the three columns are equal-length by the vector invariant\<close>
    apply (all \<open>use trip A0 B0 kb kd hkd ekd in
                \<open>auto simp: Qeq dyadic_interval_vec_invar_def split: prod.splits\<close>\<close>)
    done
qed


section \<open>The loop: every emitted window carries the bundle\<close>

text \<open>\<^bold>\<open>The op's loop invariant is \<open>\<lambda>(i, ok, out). i \<le> n\<close> and carries no isolation content\<close>, so
  @{thm [source] WHILEIT_rule} applied to it concludes nothing. @{thm [source] WHILEIT_weaken} has direction
  \<open>(\<And>x. I x \<Longrightarrow> I' x) \<Longrightarrow> WHILEIT I' b f x \<le> WHILEIT I b f x\<close>: instantiated with the stronger invariant as \<open>I\<close>, it gives
  \<open>WHILEIT weak \<le> WHILEIT strong\<close>, and the strong loop is handled by @{thm [source] WHILEIT_rule}. The op itself is
  unchanged: a \<open>WHILEIT\<close> invariant is a proof annotation that does not reach the generated code.

  \<^bold>\<open>The stronger invariant\<close> accumulates the body step: the output holds exactly \<open>i\<close> triples, and while the flag
  holds, each carries the bundle for the input at the same index. At exit \<open>i = n\<close>, which is the theorem.

  \<open>ok\<close> is the running conjunction of the per-interval flags, so once an interval fails to certify it stays false.
  Hence the invariant may state the bundle under \<open>ok\<close> alone: a flag that is still true at exit means every index
  certified, which is what lets the entry fall back for the whole vector rather than per interval.\<close>

lemma pow_sub_backmap_run_monadic_correct:
  assumes h: "0 < h" and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and len0: "0 < length q" and len: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
    and ivQ: "dyadic_interval_vec_invar accQ"
    and nn: "n = length (dyadic_interval_vec_triples accQ)"
    and n1: "n + 1 < max_snat LENGTH(gmp_poly_len)"
    and pre: "\<And>j. j < n \<Longrightarrow>
                 pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)"
  shows "pow_sub_backmap_run_monadic h q dlt accQ n
           \<le> SPEC (\<lambda>(out, ok).
                 dyadic_interval_vec_invar out
                 \<and> length (dyadic_interval_vec_triples out) = n
                 \<and> (ok \<longrightarrow> (\<forall>j < n.
                        pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                                            (dyadic_interval_vec_triples out ! j))))"
proof -
  obtain lns rns ks where Qeq: "accQ = (lns, rns, ks)" by (cases accQ)
  define I where
    "I \<equiv> \<lambda>(i, ok, out).
        i \<le> n \<and> dyadic_interval_vec_invar out
        \<and> length (dyadic_interval_vec_triples out) = i
        \<and> (ok \<longrightarrow> (\<forall>j < i. pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                                               (dyadic_interval_vec_triples out ! j)))"
  \<comment> \<open>the op's own \<open>ASSERT\<close> is phrased on the FIRST COLUMN, the invariant's reading on the
     triples; @{thm [source] dyadic_interval_vec_triples_length} bridges them but needs the
     destructured form, so it is discharged here rather than in the closing simp set\<close>
  have nfst: "length (dyadic_interval_vec_triples accQ) = length (fst accQ)"
    using ivQ Qeq by (simp add: dyadic_interval_vec_triples_length)
  \<comment> \<open>the body step, restated against the invariant rather than against raw bounds\<close>
  have body: "\<And>i ok out. I (i, ok, out) \<Longrightarrow> i < n \<Longrightarrow>
      pow_sub_emit_body_mop h q dlt accQ n (i, ok, out)
        \<le> SPEC (\<lambda>s'. I s' \<and> (s', (i, ok, out)) \<in> measure (\<lambda>(i, _, _). n - i))"
  proof -
    fix i :: nat and ok :: bool and out
    assume inv: "I (i, ok, out)" and iln: "i < n"
    have ivo: "dyadic_interval_vec_invar out"
      and leno: "length (dyadic_interval_vec_triples out) = i"
      and okj: "ok \<Longrightarrow> \<forall>j < i. pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                                                   (dyadic_interval_vec_triples out ! j)"
      using inv by (auto simp: I_def)
    have capo: "dyadic_interval_vec_pushable out"
      using ivo leno iln n1
      by (cases out) (auto simp: dyadic_interval_vec_pushable_def
                                 dyadic_interval_vec_invar_def
                                 dyadic_interval_vec_triples_def)
    have i1: "i + 1 < max_snat LENGTH(gmp_poly_len)" using iln n1 by simp
    have nlen: "n = length (fst accQ)" using nn nfst by simp
    show "pow_sub_emit_body_mop h q dlt accQ n (i, ok, out)
            \<le> SPEC (\<lambda>s'. I s' \<and> (s', (i, ok, out)) \<in> measure (\<lambda>(i, _, _). n - i))"
      apply (rule order_trans[OF pow_sub_emit_body_mop_correct
                                  [OF h hb len0 len ivQ nlen iln i1
                                      pre[OF iln] ivo capo]])
      using okj leno iln
      by (auto simp: I_def nth_append less_Suc_eq)
  qed
  \<comment> \<open>the inductive step with the state kept as ONE variable, which is the shape
     @{thm [source] WHILEIT_rule}'s third premise has\<close>
  have body': "\<And>s. I s \<Longrightarrow> pow_sub_emit_cond n s \<Longrightarrow>
      pow_sub_emit_body_mop h q dlt accQ n s
        \<le> SPEC (\<lambda>s'. I s' \<and> (s', s) \<in> measure (\<lambda>(i, _, _). n - i))"
  proof -
    fix s assume Is: "I s" and cnd: "pow_sub_emit_cond n s"
    obtain i ok out where seq: "s = (i, ok, out)" by (cases s)
    have iln: "i < n" using cnd unfolding seq pow_sub_emit_cond_def by simp
    show "pow_sub_emit_body_mop h q dlt accQ n s
            \<le> SPEC (\<lambda>s'. I s' \<and> (s', s) \<in> measure (\<lambda>(i, _, _). n - i))"
      using body[OF Is[unfolded seq] iln] unfolding seq by simp
  qed
  \<comment> \<open>\<^bold>\<open>The loop.\<close> @{thm [source] WHILEIT_weaken} is applied once, with an explicit \<open>rule\<close>: its conclusion
     \<open>WHILEIT ?I' b f x \<le> WHILEIT I b f x\<close> has \<open>?I'\<close> schematic and is itself a \<open>WHILEIT\<close>, so as a \<open>refine_vcg\<close> hint composed
     with \<open>order_trans\<close> it would apply to its own output indefinitely.\<close>
  have loop: "\<And>out'. dyadic_interval_vec_invar out' \<Longrightarrow>
      dyadic_interval_vec_triples out' = [] \<Longrightarrow>
      WHILEIT (\<lambda>(i, ok, out). i \<le> n)
              (\<lambda>st. pow_sub_emit_cond n st)
              (\<lambda>st. pow_sub_emit_body_mop h q dlt accQ n st)
              (0, True, out')
        \<le> SPEC (\<lambda>(i, ok, out).
              dyadic_interval_vec_invar out
              \<and> length (dyadic_interval_vec_triples out) = n
              \<and> (ok \<longrightarrow> (\<forall>j < n. pow_sub_emit_ok h q
                     (dyadic_interval_vec_triples accQ ! j)
                     (dyadic_interval_vec_triples out ! j))))"
  proof -
    fix out'
    assume ivo0: "dyadic_interval_vec_invar out'"
      and tr0: "dyadic_interval_vec_triples out' = []"
    show "WHILEIT (\<lambda>(i, ok, out). i \<le> n)
              (\<lambda>st. pow_sub_emit_cond n st)
              (\<lambda>st. pow_sub_emit_body_mop h q dlt accQ n st)
              (0, True, out')
        \<le> SPEC (\<lambda>(i, ok, out).
              dyadic_interval_vec_invar out
              \<and> length (dyadic_interval_vec_triples out) = n
              \<and> (ok \<longrightarrow> (\<forall>j < n. pow_sub_emit_ok h q
                     (dyadic_interval_vec_triples accQ ! j)
                     (dyadic_interval_vec_triples out ! j))))"
      apply (rule order_trans[OF WHILEIT_weaken[where I = I]])
       apply (auto simp: I_def)[1]
      apply (rule WHILEIT_rule[where R = "measure (\<lambda>(i, _, _). n - i)"])
         apply (rule wf_measure)
        apply (use ivo0 tr0 in \<open>auto simp: I_def\<close>)[1]
       apply (rule body'; assumption)
      apply (auto simp: I_def pow_sub_emit_cond_def split: prod.splits)[1]
      done
  qed
  show ?thesis
    unfolding pow_sub_backmap_run_monadic_def PR_CONST_def pow_sub_emit_result_mop_def
    apply (refine_vcg
           dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans]
           loop[THEN order_trans])
    apply (all \<open>use h hb len0 len ivQ n1 nn nfst in \<open>auto simp: Let_def\<close>\<close>)
    done
qed

section \<open>What the room guard decides, per interval\<close>

text \<open>\<^bold>\<open>Why there is a runtime guard, and why no proof can replace it.\<close> @{const pow_sub_iv_pre} is a hypothesis of the
  lemma above, and the entry has to discharge it against what the reduced solve returns. The reduced solve's
  specification supplies @{const dsc_pair_ok} per emitted interval and root coverage, and nothing about the sign of an
  endpoint or the size of the precision column \<open>k\<close>.

  The two sign facts are true but not exported. The four word bounds are not true in general: the pipeline's
  invariant (\<open>hybrid_loop_step_pre\<close>) guarantees \<open>k * (length rp - 1) < max_snat\<close>, while certification needs
  \<open>h * (k + dlt) * length q < max_snat\<close>, larger by a factor of \<open>h\<close>. So this is a capacity obligation, and the choices are
  an uncheckable caller obligation or a runtime test. The entry tests, for the whole vector, and refuses the
  substitution as a whole.\<close>

definition pow_sub_room_iv :: "(int \<times> int) \<times> nat \<Rightarrow> bool" where
  "pow_sub_room_iv iv \<equiv>
     (let ((A, B), k) = iv in 0 \<le> A \<and> 0 \<le> B \<and> k < 1048576)"

text \<open>\<open>max_snat 64 = 2\<^sup>6\<^sup>3\<close>, stated once so that the four bounds below are numeral arithmetic rather than an unfolding of
  @{thm [source] max_snat_def} inside each closer.\<close>

lemma pow_sub_room_max_snat:
  "max_snat LENGTH(gmp_poly_len) = 9223372036854775808"
  by (simp add: max_snat_def)

text \<open>\<^bold>\<open>The bridge the whole guard exists for\<close>: the three per-call limits plus the per-interval
  one give all six conjuncts of @{const pow_sub_iv_pre}. The limits are chosen so that even the
  widest product, \<open>h \<cdot> (k + dlt) \<cdot> length q\<close>, stays under \<open>2\<^sup>5\<^sup>1\<close> — twelve binary orders of
  magnitude of slack, so no runtime product can overflow either.\<close>

lemma pow_sub_room_iv_pre:
  assumes hb: "h < 1024" and db: "dlt < 1024" and lb: "length q < 1048576"
    and iv: "pow_sub_room_iv iv"
  shows "pow_sub_iv_pre h q dlt iv"
proof -
  \<comment> \<open>general in the triple, not stated at \<open>((A, B), k)\<close>: at the use site the interval is
     \<open>dyadic_interval_vec_triples accQ ! j\<close>, which no \<open>rule\<close> can destructure for itself\<close>
  obtain A B k where ivq: "iv = ((A, B), k)" by (metis surj_pair)
  have A0: "0 \<le> A" and B0: "0 \<le> B" and kb: "k < 1048576"
    using iv unfolding ivq pow_sub_room_iv_def by (simp_all add: Let_def)
  \<comment> \<open>\<open>rule\<close>, never \<open>intro\<close>: @{thm [source] mult_le_mono} applies to its own first subgoal,
     so \<open>intro\<close> recurses into \<open>h \<le> 1023\<close> and leaves goals nothing can close\<close>
  have p1: "h * (k + dlt) \<le> 1023 * (1048575 + 1023)"
    using hb db kb by (rule_tac mult_le_mono) auto
  have p2: "h * (k + dlt) * length q \<le> 1023 * (1048575 + 1023) * 1048575"
    using lb by (rule_tac mult_le_mono[OF p1]) auto
  show ?thesis
    unfolding ivq pow_sub_iv_pre_def pow_sub_room_max_snat
    using A0 B0 kb db p1 p2 by (simp add: Let_def)
qed

section \<open>The guard's body and its loop\<close>

text \<open>The body reads interval \<open>i\<close> out of the reduced arm, takes two \<open>mpz\<close> signs, discards the
  columns, and ANDs the verdict into the running flag.

  \<^bold>\<open>Simpler than @{thm [source] pow_sub_emit_body_mop_correct} because there is no copy-get.\<close>
  The body now reads the two columns with @{const poly_coeff_sgn_monadic} — the borrowed
  \<open>O(1)\<close> sign read, for the allocation reason recorded at the op — so nothing re-generalises the
  columns and the whole proof is one \<open>refine_vcg\<close> over unfolded definitions. That removes the
  \<open>trip\<close>-must-be-INSERTED dance the copy-get version needed: \<open>trip\<close> can now be an ordinary simp
  rule, stated on the destructured vector because the goal is unfolded at \<open>Qeq\<close>.
  \<open>0 \<le> sgn x \<longleftrightarrow> 0 \<le> x\<close> is what \<open>sgn_if\<close> supplies.\<close>

lemma pow_sub_room_body_mop_correct:
  assumes ivQ: "dyadic_interval_vec_invar accQ"
    and nlen: "n = length (fst accQ)"
    and iln: "i < n"
    and i1: "i + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_room_body_mop n accQ (i, ok)
           \<le> SPEC (\<lambda>(i', ok').
                 i' = i + 1
                 \<and> ok' = (ok \<and> pow_sub_room_iv (dyadic_interval_vec_triples accQ ! i)))"
proof -
  obtain lns rns ks where Qeq: "accQ = (lns, rns, ks)" by (cases accQ)
  have ivQ': "dyadic_interval_vec_invar (lns, rns, ks)" using ivQ Qeq by simp
  have ilns: "i < length lns" using iln nlen Qeq by simp
  have irns: "i < length rns" and iks: "i < length ks"
    using ivQ' ilns unfolding dyadic_interval_vec_invar_def by simp_all
  have trip: "dyadic_interval_vec_triples (lns, rns, ks) ! i
                = ((lns ! i, rns ! i), ks ! i)"
    using dyadic_interval_vec_triples_nth[OF ivQ' ilns] by simp
  show ?thesis
    unfolding pow_sub_room_body_mop_def PR_CONST_def Qeq
      pow_sub_room_step_mop_def pow_sub_succ_mop_def pow_sub_and_mop_def
      pow_sub_room_sgn_mop_def pow_sub_room_k_mop_def
      poly_coeff_sgn_monadic_def mop_list_get_alt
    using iln ilns irns iks i1
    apply refine_vcg
    apply (all \<open>auto simp: trip pow_sub_room_iv_def Let_def sgn_if\<close>)
    done
qed

text \<open>The guard loop, by the same two-step assembly as the back-map loop: the definition's invariant
  \<open>\<lambda>(i, ok). i \<le> n\<close> is weakened out of the way ONCE, and the strengthened one carries the
  accumulated verdict. \<open>ok\<close> starts at the three per-call limits and only ever falls.\<close>

lemma pow_sub_room_all_monadic_correct:
  assumes ivQ: "dyadic_interval_vec_invar accQ"
    and nn: "n = length (dyadic_interval_vec_triples accQ)"
    and n1: "n + 1 < max_snat LENGTH(gmp_poly_len)"
    and lq: "lenq = length q"
  shows "pow_sub_room_all_monadic h dlt lenq accQ n
           \<le> SPEC (\<lambda>g. g \<longrightarrow> (\<forall>j < n.
                 pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)))"
proof -
  obtain lns rns ks where Qeq: "accQ = (lns, rns, ks)" by (cases accQ)
  have nfst: "n = length (fst accQ)"
    using ivQ Qeq nn by (simp add: dyadic_interval_vec_triples_length)
  define J where
    "J \<equiv> \<lambda>(i, ok).
        i \<le> n
        \<and> (ok \<longrightarrow> h < 1024 \<and> dlt < 1024 \<and> lenq < 1048576
                  \<and> (\<forall>j < i. pow_sub_room_iv (dyadic_interval_vec_triples accQ ! j)))"
  have body': "\<And>s. J s \<Longrightarrow> pow_sub_room_cond n s \<Longrightarrow>
      pow_sub_room_body_mop n accQ s
        \<le> SPEC (\<lambda>s'. J s' \<and> (s', s) \<in> measure (\<lambda>(i, _). n - i))"
  proof -
    fix s assume Js: "J s" and cnd: "pow_sub_room_cond n s"
    obtain i ok where seq: "s = (i, ok)" by (cases s)
    have iln: "i < n" using cnd unfolding seq pow_sub_room_cond_def by simp
    have i1: "i + 1 < max_snat LENGTH(gmp_poly_len)" using iln n1 by simp
    show "pow_sub_room_body_mop n accQ s
            \<le> SPEC (\<lambda>s'. J s' \<and> (s', s) \<in> measure (\<lambda>(i, _). n - i))"
      unfolding seq
      apply (rule order_trans[OF pow_sub_room_body_mop_correct[OF ivQ nfst iln i1]])
      using Js iln unfolding seq
      by (auto simp: J_def less_Suc_eq)
  qed
  have loop: "WHILEIT (\<lambda>(i, ok). i \<le> n)
                (\<lambda>st. pow_sub_room_cond n st)
                (\<lambda>st. pow_sub_room_body_mop n accQ st)
                (0, h < 1024 \<and> dlt < 1024 \<and> lenq < 1048576)
        \<le> SPEC (\<lambda>(i, ok). ok \<longrightarrow> (\<forall>j < n.
              pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)))"
    apply (rule order_trans[OF WHILEIT_weaken[where I = J]])
     apply (auto simp: J_def)[1]
    apply (rule WHILEIT_rule[where R = "measure (\<lambda>(i, _). n - i)"])
       apply (rule wf_measure)
      apply (auto simp: J_def)[1]
     apply (rule body'; assumption)
    \<comment> \<open>exit: \<open>i = n\<close>, and every index's verdict becomes its \<open>pow_sub_iv_pre\<close> instance\<close>
    apply (clarsimp simp: J_def pow_sub_room_cond_def)
    apply (rule pow_sub_room_iv_pre[where q = q])
       apply (simp_all add: lq)
    done
  show ?thesis
    unfolding pow_sub_room_all_monadic_def PR_CONST_def
      pow_sub_room_hd_mop_def pow_sub_room_result_mop_def
    apply (refine_vcg loop[THEN order_trans])
    apply (all \<open>use nfst n1 in \<open>auto simp: Let_def\<close>\<close>)
    done
qed

section \<open>The guarded entry point, unconditionally\<close>

text \<open>\<^bold>\<open>The per-interval precondition is gone from the statement.\<close> Everything
  @{const pow_sub_backmap_all_monadic} needs about the reduced arm's intervals it now decides
  for itself; what is left are the caller's own bounds on \<open>h\<close> and \<open>q\<close>, plus the vector's
  structural invariant and one capacity bound on the number of intervals — all three of which
  the entry has in hand.

  The refused arm returns an EMPTY vector with \<open>ok = False\<close>, which is why the length conjunct is
  stated under \<open>ok\<close> as well: a caller that does not read the flag learns nothing about the
  output, and the fused entry reads it.\<close>

theorem pow_sub_backmap_all_monadic_correct:
  assumes h: "0 < h" and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and len0: "0 < length q" and len: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
    and ivQ: "dyadic_interval_vec_invar accQ"
    and n1: "length (dyadic_interval_vec_triples accQ) + 1
               < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_backmap_all_monadic h q dlt accQ
           \<le> SPEC (\<lambda>(out, ok).
                 dyadic_interval_vec_invar out
                 \<and> (ok \<longrightarrow> length (dyadic_interval_vec_triples out)
                             = length (dyadic_interval_vec_triples accQ)
                       \<and> (\<forall>j < length (dyadic_interval_vec_triples accQ).
                            pow_sub_iv_pre h q dlt
                              (dyadic_interval_vec_triples accQ ! j))
                       \<and> (\<forall>j < length (dyadic_interval_vec_triples accQ).
                            pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                                                (dyadic_interval_vec_triples out ! j))))"
proof -
  obtain lns rns ks where Qeq: "accQ = (lns, rns, ks)" by (cases accQ)
  \<comment> \<open>\<^bold>\<open>An abbreviation, not a \<open>define\<close>.\<close> A \<open>define\<close> introduces a fixed variable, and the two hints below would then carry
     \<open>n\<close> where the goal carries \<open>length (dyadic_interval_vec_triples accQ)\<close>, which no \<open>rule\<close> can bridge.\<close>
  let ?n = "length (dyadic_interval_vec_triples accQ)"
  have nfst: "?n = length (fst accQ)"
    using ivQ Qeq by (simp add: dyadic_interval_vec_triples_length)
  \<comment> \<open>\<^bold>\<open>Both hints are stated over a parameter \<open>n'\<close> with \<open>n' = ?n\<close> as a premise.\<close> The length op's specification has
     two conjuncts, \<open>n = length (triples accQ)\<close> and \<open>n = length (to_list accQ)\<close>; \<open>auto\<close> orients the resulting equation
     \<open>triples \<rightarrow> to_list\<close>, and the goal then speaks of \<open>length (to_list accQ)\<close>, which a hint fixed at
     \<open>length (triples accQ)\<close> would not match. With \<open>n'\<close> free, unification takes whatever the goal carries and the
     equation returns as a subgoal.\<close>
  have guard: "pow_sub_room_all_monadic h dlt (length q) accQ n'
        \<le> SPEC (\<lambda>g. g \<longrightarrow> (\<forall>j < n'.
              pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)))"
    if nn': "n' = ?n" for n'
  proof -
    have n1': "n' + 1 < max_snat LENGTH(gmp_poly_len)" using n1 nn' by simp
    show ?thesis by (rule pow_sub_room_all_monadic_correct[OF ivQ nn' n1' refl])
  qed
  \<comment> \<open>\<^bold>\<open>\<open>pow_sub_iv_pre\<close> is carried out as well as in.\<close> The guard decides it and the run arm consumes it, but the
     entry theorem needs two of its conjuncts, \<open>0 \<le> A\<close> and \<open>0 \<le> B\<close>, and nothing else establishes them there
     (\<open>dsc_pair_ok\<close> constrains no endpoint's sign). Since \<open>pre'\<close> is a hypothesis here, restating it in the postcondition
     is free.\<close>
  have run: "pow_sub_backmap_run_monadic h q dlt accQ n'
        \<le> SPEC (\<lambda>(out, ok).
              dyadic_interval_vec_invar out
              \<and> length (dyadic_interval_vec_triples out) = n'
              \<and> (\<forall>j < n'. pow_sub_iv_pre h q dlt
                     (dyadic_interval_vec_triples accQ ! j))
              \<and> (ok \<longrightarrow> (\<forall>j < n'. pow_sub_emit_ok h q
                     (dyadic_interval_vec_triples accQ ! j)
                     (dyadic_interval_vec_triples out ! j))))"
    if nn': "n' = ?n"
      and pre': "\<And>j. j < n' \<Longrightarrow>
            pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)"
    for n'
  proof -
    have n1': "n' + 1 < max_snat LENGTH(gmp_poly_len)" using n1 nn' by simp
    show ?thesis
      using pre'
      by (rule_tac order_trans[OF pow_sub_backmap_run_monadic_correct[
             OF h hb len0 len ivQ nn' n1' pre']]) auto
  qed
  show ?thesis
    unfolding pow_sub_backmap_all_monadic_def PR_CONST_def
      pow_sub_backmap_skip_mop_def poly_length_monadic_def
    apply (refine_vcg
           dyadic_interval_vec_length_monadic_spec[of lns rns ks, folded Qeq,
                                                   THEN order_trans]
           guard[THEN order_trans]
           run[THEN order_trans]
           dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans])
    apply (all \<open>use h hb len0 len ivQ n1 nfst in \<open>auto simp: Let_def\<close>\<close>)
    done
qed

section \<open>The back-map's isolation postcondition\<close>

text \<open>The ceiling counterpart of @{thm [source] pow_sub_num_lo_nonneg}, needed by the mirror below: the emitted left
  numerator is @{const pow_sub_num_hi} of \<open>A\<close> in the proper branch and @{const pow_sub_num_lo} of \<open>A\<close> in the degenerate
  one, and @{thm [source] pow_sub_pair_ok_mirror} needs \<open>0 \<le> u\<close> for either.\<close>

lemma pow_sub_num_hi_nonneg:
  fixes A :: int
  assumes A0: "0 \<le> A"
  shows "0 \<le> pow_sub_num_hi h m (real_of_int A / 2 ^ k)"
proof -
  have nn: "0 \<le> (real_of_int A / 2 ^ k) powr (1 / real h) * 2 ^ m" by simp
  \<comment> \<open>through \<open>ceiling_mono\<close> against \<open>\<lceil>0\<rceil>\<close>, not a bare \<open>simp\<close>: \<open>simp\<close> rewrites \<open>0 \<le> \<lceil>x\<rceil>\<close> to the strict \<open>- 1 < x\<close>
     (@{thm [source] zero_le_ceiling}) and cannot reach it from \<open>0 \<le> x\<close>, and \<open>linarith\<close> treats \<open>\<lceil>x\<rceil>\<close> as an opaque atom.
     The floor counterpart does not have this problem, because \<open>0 \<le> \<lfloor>x\<rfloor>\<close> rewrites to the non-strict \<open>0 \<le> x\<close>.\<close>
  have "\<lceil>(0::real)\<rceil> \<le> \<lceil>(real_of_int A / 2 ^ k) powr (1 / real h) * 2 ^ m\<rceil>"
    using nn by (rule ceiling_mono)
  thus ?thesis unfolding pow_sub_num_hi_def by simp
qed

text \<open>\<^bold>\<open>What the entry needs from the back-map, with the reduced solve's isolation as the only hypothesis about the
  input vector.\<close> This joins the loop theorem (which yields @{const pow_sub_emit_ok} and @{const pow_sub_iv_pre} per
  index) with @{thm [source] pow_sub_emit_ok_pair_ok} (which turns one bundle into @{const dsc_pair_ok} on \<open>P\<close>). It
  mentions neither the reduced solve's capstone nor \<open>pow_sub_entry_monadic\<close>.

  \<open>A \<le> B\<close> is not a hypothesis: @{thm [source] dsc_pair_ok_def} is a disjunction with branches \<open>fst = snd\<close> and
  \<open>fst < snd\<close>, so the reduced solve's isolation implies it.\<close>

theorem pow_sub_backmap_all_pair_ok:
  fixes Q0 :: "int poly" and accQ :: gmp_dyadic_interval_vec
  assumes h: "0 < h" and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len0: "0 < length q" and len: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
    and ivQ: "dyadic_interval_vec_invar accQ"
    and n1: "length (dyadic_interval_vec_triples accQ) + 1
               < max_snat LENGTH(gmp_poly_len)"
    and isoQ: "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
          (case dyadic_interval_vec_triples accQ ! j of ((A, B), k) \<Rightarrow>
             dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k))"
  shows "pow_sub_backmap_all_monadic h q dlt accQ
           \<le> SPEC (\<lambda>(out, ok).
                 dyadic_interval_vec_invar out
                 \<and> (ok \<longrightarrow> length (dyadic_interval_vec_triples out)
                             = length (dyadic_interval_vec_triples accQ)
                       \<and> (\<forall>j < length (dyadic_interval_vec_triples accQ).
                            case dyadic_interval_vec_triples out ! j of ((L, R), m) \<Rightarrow>
                              0 \<le> L
                              \<and> dsc_pair_ok P (real_of_int L / 2 ^ m,
                                               real_of_int R / 2 ^ m))))"
proof -
  let ?n = "length (dyadic_interval_vec_triples accQ)"
  \<comment> \<open>\<^bold>\<open>The per-index step, stated over explicit \<open>L R m\<close> with the read-out equation as a premise\<close>, not as a
     \<open>case \<dots> of\<close> over \<open>triples out ! j\<close>: by the time of the final \<open>auto\<close> the \<open>SPEC\<close>'s own \<open>case\<close> has been split and the
     goal carries \<open>triples out ! j = ((ab, bb), m)\<close> as a premise with the conclusion in terms of \<open>ab\<close>/\<open>bb\<close>, which a
     \<open>case\<close>-shaped fact does not match. \<open>0 \<le> L\<close> is carried with the isolation because the mirror needs \<open>0 \<le> u\<close> and only
     this layer sees whether \<open>pow_sub_num_hi\<close> or \<open>pow_sub_num_lo\<close> produced it.\<close>
  have step: "0 \<le> L \<and> dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)"
    if jn: "j < ?n"
      and pre: "pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)"
      and emit: "pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                                     (dyadic_interval_vec_triples out ! j)"
      and outj: "dyadic_interval_vec_triples out ! j = ((L, R), m)"
    for j L R m and out :: gmp_dyadic_interval_vec
  proof -
    obtain A B k where inj: "dyadic_interval_vec_triples accQ ! j = ((A, B), k)"
      by (metis surj_pair)
    have A0: "0 \<le> A" and B0: "0 \<le> B"
      using pre unfolding inj pow_sub_iv_pre_def by (simp_all add: Let_def)
    have iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
      using isoQ[OF jn] unfolding inj by simp
    \<comment> \<open>\<open>A \<le> B\<close> out of the isolation itself — both \<open>dsc_pair_ok\<close> branches give it\<close>
    have AB: "A \<le> B"
    proof -
      have "real_of_int A / 2 ^ k \<le> real_of_int B / 2 ^ k"
        using iv unfolding dsc_pair_ok_def by auto
      thus ?thesis by (simp add: divide_right_mono_neg field_simps)
    qed
    have pk: "dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)"
      by (rule pow_sub_emit_ok_pair_ok[OF h Pdef sf Qdef qdef len0 A0 B0 AB iv
                 emit[unfolded inj outj]])
    \<comment> \<open>\<open>L\<close> is a \<open>pow_sub_num_hi\<close> off \<open>A\<close> in the non-degenerate branch and a \<open>pow_sub_num_lo\<close>
       off \<open>A\<close> in the degenerate one; both are nonneg for \<open>0 \<le> A\<close>\<close>
    have L0: "0 \<le> L"
    proof (cases "A = B")
      case True
      have "L = pow_sub_num_lo h m (real_of_int A / 2 ^ k)"
        using emit[unfolded inj outj] True
        unfolding pow_sub_emit_ok_def by (simp add: Let_def)
      thus ?thesis using pow_sub_num_lo_nonneg[OF A0] by simp
    next
      case False
      have "L = pow_sub_num_hi h m (real_of_int A / 2 ^ k)"
        using emit[unfolded inj outj] False
        unfolding pow_sub_emit_ok_def by (simp add: Let_def)
      thus ?thesis using pow_sub_num_hi_nonneg[OF A0] by simp
    qed
    show ?thesis using L0 pk by simp
  qed
  show ?thesis
    by (rule order_trans[OF pow_sub_backmap_all_monadic_correct[
             OF h hb len0 len ivQ n1]])
       (use step in auto)
qed

section \<open>The negative half, a completeness obligation\<close>

text \<open>\<^bold>\<open>Why this is needed.\<close> \<open>isarri_wrapper\<close> (\<open>Public_Export\<close>) stores the same \<open>out\<close> vector into both the positive
  and the negative output slots, so the negative half is the positive windows read under the interface's
  negate-and-swap convention. For even \<open>h\<close> each positive \<open>Q\<close>-root lifts to two \<open>P\<close>-roots \<open>\<plusminus>y\<close>, so a positive-only claim
  would leave half the real roots unaccounted for and the mirrored store unjustified. The entry's parity test
  (\<open>2 \<le> gcd d 2\<close>, i.e. \<open>even d\<close>) is what makes the reflection valid.

  \<^bold>\<open>The two \<open>dsc_pair_ok\<close> branches are treated separately\<close>, and only one needs the substitution algebra: the
  degenerate window reflects by @{thm [source] pow_sub_poly_even_sym} alone, while the proper window goes through
  @{const roots_in} and @{thm [source] pow_sub_pair_ok_mirror}.\<close>

text \<open>\<^bold>\<open>The loop's covering, as a pure consequence of @{thm [source] pow_sub_backmap_all_monadic_correct}\<close>, which
  gives \<open>length out = length accQ\<close>, @{const pow_sub_iv_pre} per index and @{const pow_sub_emit_ok} per index, what the
  per-interval covering consumes.

  \<^bold>\<open>A root on an endpoint needs no hypothesis.\<close> \<open>covQ\<close> below is strict-or-degenerate: the reduced recursion emits a
  degenerate pair at every exactly representable root, so \<open>newdsc_pol_bail_complete_strong\<close> can say so, and both branch
  conditions follow: at \<open>A = B\<close> the strict disjunct is vacuous and the degenerate one pins \<open>y\<close>; at \<open>A \<noteq> B\<close> the degenerate
  disjunct would force \<open>A = B\<close>.\<close>

lemma pow_sub_backmap_cover_of_post:
  fixes Q0 :: "int poly" and y :: real
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len0: "0 < length q"
    and isoQ: "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
          (case dyadic_interval_vec_triples accQ ! j of ((A, B), k) \<Rightarrow>
             dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k))"
    and covQ: "\<exists>j A B k. j < length (dyadic_interval_vec_triples accQ)
          \<and> dyadic_interval_vec_triples accQ ! j = ((A, B), k)
          \<and> ((real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
             \<or> (real_of_int A / 2 ^ k = y \<and> real_of_int B / 2 ^ k = y))"
    and pre: "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
          pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)"
    and lenEq: "length (dyadic_interval_vec_triples out)
                  = length (dyadic_interval_vec_triples accQ)"
    and emit: "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
          pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                              (dyadic_interval_vec_triples out ! j)"
    and ry: "poly Q y = 0"
  shows "\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
      \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
      \<and> 0 \<le> L \<and> L \<le> R
      \<and> (real_of_int L / 2 ^ m) ^ h \<le> y \<and> y \<le> (real_of_int R / 2 ^ m) ^ h"
proof -
  from covQ obtain j A B k where jn: "j < length (dyadic_interval_vec_triples accQ)"
    and inj: "dyadic_interval_vec_triples accQ ! j = ((A, B), k)"
    and bnds: "(real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
                \<or> (real_of_int A / 2 ^ k = y \<and> real_of_int B / 2 ^ k = y)" by blast
  obtain L R m where outj: "dyadic_interval_vec_triples out ! j = ((L, R), m)"
    by (metis surj_pair)
  have A0: "0 \<le> A" and B0: "0 \<le> B"
    using pre[OF jn] unfolding inj pow_sub_iv_pre_def by (simp_all add: Let_def)
  have iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    using isoQ[OF jn] unfolding inj by simp
  have AB: "A \<le> B"
  proof -
    have "real_of_int A / 2 ^ k \<le> real_of_int B / 2 ^ k"
      using iv unfolding dsc_pair_ok_def by auto
    thus ?thesis by (simp add: divide_right_mono_neg field_simps)
  qed
  \<comment> \<open>the branch condition of @{thm [source] pow_sub_emit_ok_pair_ok_strong}, DERIVED from the
     strict-or-degenerate covering alone\<close>
  have branch: "if A = B then y = real_of_int A / 2 ^ k
                else real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k"
  proof (cases "A = B")
    case True
    \<comment> \<open>the strict disjunct is vacuous at \<open>A = B\<close> (it reads \<open>c < y \<and> y < c\<close>), so the degenerate
       one fires and pins \<open>y\<close>. \<open>auto\<close>, not \<open>simp\<close>: killing that disjunct is a linear-arithmetic
       step, and \<open>simp\<close> leaves it standing beside the goal\<close>
    then show ?thesis using bnds by auto
  next
    case False
    \<comment> \<open>\<^bold>\<open>Here the degenerate disjunct is impossible\<close>: it forces \<open>A / 2\<^sup>k = B / 2\<^sup>k\<close>, hence \<open>A = B\<close>. So the strict
       disjunct holds.\<close>
    have "real_of_int A / 2 ^ k \<noteq> real_of_int B / 2 ^ k"
      using False by simp
    then show ?thesis using bnds False by auto
  qed
  have emitb: "dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
      \<and> (\<forall>y. poly Q y = 0
          \<longrightarrow> (if A = B then y = real_of_int A / 2 ^ k
               else real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
          \<longrightarrow> (real_of_int L / 2 ^ m) ^ h \<le> y \<and> y \<le> (real_of_int R / 2 ^ m) ^ h)"
    by (rule pow_sub_emit_ok_pair_ok_strong[OF h Pdef sf Qdef qdef len0 A0 B0 AB iv
              emit[OF jn, unfolded inj outj]])
  have cov: "(real_of_int L / 2 ^ m) ^ h \<le> y \<and> y \<le> (real_of_int R / 2 ^ m) ^ h"
    using emitb branch ry by blast
  \<comment> \<open>\<open>0 \<le> L\<close> is read off the emitted numerator's form (a floor of \<open>A\<close> in the degenerate branch, a ceiling of \<open>A\<close> in
     the proper one), and \<open>L \<le> R\<close> from the isolation the bundle carries. Both are carried with the covering because the
     lift step needs a nonnegative base.\<close>
  have L0: "0 \<le> L"
  proof (cases "A = B")
    case True
    have "L = pow_sub_num_lo h m (real_of_int A / 2 ^ k)"
      using emit[OF jn, unfolded inj outj] True
      unfolding pow_sub_emit_ok_def by (simp add: Let_def)
    then show ?thesis using pow_sub_num_lo_nonneg[OF A0] by simp
  next
    case False
    have "L = pow_sub_num_hi h m (real_of_int A / 2 ^ k)"
      using emit[OF jn, unfolded inj outj] False
      unfolding pow_sub_emit_ok_def by (simp add: Let_def)
    then show ?thesis using pow_sub_num_hi_nonneg[OF A0] by simp
  qed
  have LR: "L \<le> R"
  proof -
    have "real_of_int L / 2 ^ m \<le> real_of_int R / 2 ^ m"
      using emitb unfolding dsc_pair_ok_def by auto
    thus ?thesis by (simp add: divide_right_mono_neg field_simps)
  qed
  show ?thesis
  proof (intro exI conjI)
    show "j < length (dyadic_interval_vec_triples out)" using jn lenEq by simp
    show "dyadic_interval_vec_triples out ! j = ((L, R), m)" by (rule outj)
    show "0 \<le> L" by (rule L0)
    show "L \<le> R" by (rule LR)
    show "(real_of_int L / 2 ^ m) ^ h \<le> y" using cov by simp
    show "y \<le> (real_of_int R / 2 ^ m) ^ h" using cov by simp
  qed
qed

text \<open>\<^bold>\<open>The monadic wrapper\<close> of the covering.\<close>

theorem pow_sub_backmap_all_cover:
  fixes Q0 :: "int poly" and accQ :: gmp_dyadic_interval_vec
  assumes h: "0 < h" and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len0: "0 < length q" and len: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
    and ivQ: "dyadic_interval_vec_invar accQ"
    and n1: "length (dyadic_interval_vec_triples accQ) + 1
               < max_snat LENGTH(gmp_poly_len)"
    and isoQ: "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
          (case dyadic_interval_vec_triples accQ ! j of ((A, B), k) \<Rightarrow>
             dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k))"
    and covQ: "\<And>y::real. 0 < y \<Longrightarrow> poly Q y = 0 \<Longrightarrow>
          (\<exists>j A B k. j < length (dyadic_interval_vec_triples accQ)
             \<and> dyadic_interval_vec_triples accQ ! j = ((A, B), k)
             \<and> ((real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
                \<or> (real_of_int A / 2 ^ k = y \<and> real_of_int B / 2 ^ k = y)))"
  shows "pow_sub_backmap_all_monadic h q dlt accQ
           \<le> SPEC (\<lambda>(out, ok). ok \<longrightarrow>
                 (\<forall>y::real. 0 < y \<longrightarrow> poly Q y = 0 \<longrightarrow>
                   (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
                      \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
                      \<and> 0 \<le> L \<and> L \<le> R
                      \<and> (real_of_int L / 2 ^ m) ^ h \<le> y
                      \<and> y \<le> (real_of_int R / 2 ^ m) ^ h)))"
proof -
  have main: "pow_sub_backmap_all_monadic h q dlt accQ
           \<le> SPEC (\<lambda>(out, ok).
                 dyadic_interval_vec_invar out
                 \<and> (ok \<longrightarrow> length (dyadic_interval_vec_triples out)
                             = length (dyadic_interval_vec_triples accQ)
                       \<and> (\<forall>j < length (dyadic_interval_vec_triples accQ).
                            pow_sub_iv_pre h q dlt
                              (dyadic_interval_vec_triples accQ ! j))
                       \<and> (\<forall>j < length (dyadic_interval_vec_triples accQ).
                            pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                                                (dyadic_interval_vec_triples out ! j))))"
    by (rule pow_sub_backmap_all_monadic_correct[OF h hb len0 len ivQ n1])
  show ?thesis
    \<comment> \<open>\<open>clarsimp\<close> destructures the output vector into its three columns \<open>(a, aa, b)\<close> and rewrites
       the bound \<open>j < length (triples out)\<close> to \<open>\<dots> accQ\<close> along \<open>lenEq\<close>; both are why the pure
       helper's conclusion is re-quantified rather than applied by \<open>rule\<close>\<close>
    apply (rule weaken_SPEC[OF main])
    apply clarsimp
    subgoal premises p for a aa b ba y
    proof -
      have pre': "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
            pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)"
        using p(6) by blast
      have emit': "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
            pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                                (dyadic_interval_vec_triples (a, aa, b) ! j)"
        using p(7) by blast
      have "\<exists>j L R m. j < length (dyadic_interval_vec_triples (a, aa, b))
          \<and> dyadic_interval_vec_triples (a, aa, b) ! j = ((L, R), m)
          \<and> 0 \<le> L \<and> L \<le> R
          \<and> (real_of_int L / 2 ^ m) ^ h \<le> y \<and> y \<le> (real_of_int R / 2 ^ m) ^ h"
        by (rule pow_sub_backmap_cover_of_post[OF h Pdef sf Qdef qdef len0 isoQ
                   covQ[OF p(3) p(4)] pre' p(5) emit' p(4)])
      thus ?thesis using p(5) by auto
    qed
    done
qed

lemma pow_sub_pair_ok_mirror_window:
  fixes u v :: real
  assumes h: "0 < h" and ev: "even h"
    and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and u0: "0 \<le> u" and pk: "dsc_pair_ok P (u, v)"
  shows "dsc_pair_ok P (- v, - u)"
proof (cases "u = v")
  case True
  \<comment> \<open>degenerate: the reflected point is a root because \<open>P\<close> is an even function of \<open>x\<close>\<close>
  have "poly P (- u) = poly P u" by (rule pow_sub_poly_even_sym[OF Pdef ev])
  with pk True show ?thesis unfolding dsc_pair_ok_def by simp
next
  case False
  with pk have uv: "u < v" and one: "roots_in P u v = 1"
    unfolding dsc_pair_ok_def by auto
  have "roots_in Q (u ^ h) (v ^ h) = 1"
    using one pow_sub_roots_in_eq[OF h Pdef sf u0 less_imp_le[OF uv]] by simp
  thus ?thesis by (rule pow_sub_pair_ok_mirror[OF h Pdef sf ev u0 uv])
qed

text \<open>The whole-vector form: for even \<open>h\<close> every emitted window isolates on BOTH sides of the
  origin, so one vector legitimately serves both output slots.\<close>

theorem pow_sub_backmap_all_pair_ok_mirror:
  fixes Q0 :: "int poly" and accQ :: gmp_dyadic_interval_vec
  assumes h: "0 < h" and ev: "even h" and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len0: "0 < length q" and len: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
    and ivQ: "dyadic_interval_vec_invar accQ"
    and n1: "length (dyadic_interval_vec_triples accQ) + 1
               < max_snat LENGTH(gmp_poly_len)"
    and isoQ: "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
          (case dyadic_interval_vec_triples accQ ! j of ((A, B), k) \<Rightarrow>
             dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k))"
  shows "pow_sub_backmap_all_monadic h q dlt accQ
           \<le> SPEC (\<lambda>(out, ok).
                 dyadic_interval_vec_invar out
                 \<and> (ok \<longrightarrow> length (dyadic_interval_vec_triples out)
                             = length (dyadic_interval_vec_triples accQ)
                       \<and> (\<forall>j < length (dyadic_interval_vec_triples accQ).
                            case dyadic_interval_vec_triples out ! j of ((L, R), m) \<Rightarrow>
                              dsc_pair_ok P (real_of_int L / 2 ^ m,
                                             real_of_int R / 2 ^ m)
                              \<and> dsc_pair_ok P (- (real_of_int R / 2 ^ m),
                                               - (real_of_int L / 2 ^ m)))))"
  by (rule order_trans[OF pow_sub_backmap_all_pair_ok[
           OF h hb Pdef sf Qdef qdef len0 len ivQ n1 isoQ]])
     (use pow_sub_pair_ok_mirror_window[OF h ev Pdef sf] in auto)

end
