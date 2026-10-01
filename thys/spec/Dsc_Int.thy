theory Dsc_Int

imports Dsc_Taylor

begin

text \<open>The INTEGER-coefficient specification — the layer the whole GMP development refines.
  Layer: FUNCTIONAL SPEC.
  Main exports: \<open>dsc_int\<close> / \<open>newdsc_int\<close> (the multiset targets of every capstone),
  \<open>scale_for_fractional_shift\<close>, \<open>fractional_taylor_shift\<close>.\<close>

fun scale_for_fractional_shift :: "int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list" where
  "scale_for_fractional_shift den acc [] = []"
| "scale_for_fractional_shift den acc (x # xs) = (x * acc) # scale_for_fractional_shift den (acc * den) xs"

definition fractional_taylor_shift :: "rat \<Rightarrow> int list \<Rightarrow> int list" where
  "fractional_taylor_shift c xs =
    (let (n, d) = quotient_of c;
         scaled_xs = rev (scale_for_fractional_shift d 1 (rev xs))
     in taylor_shift_list n scaled_xs)"

definition descartes_list_int :: "rat \<Rightarrow> rat \<Rightarrow> int list \<Rightarrow> nat" where
  "descartes_list_int a b xs = 
    (let 
        (na, da) = quotient_of a;
        p1 = fractional_taylor_shift a xs;
        
        (nw, dw) = quotient_of ((b - a) * of_int da);

        p3 = scale_for_fractional_shift dw 1 (rev (scale_poly_list nw p1));
        
        p4 = (taylor_shift_list :: int \<Rightarrow> int list \<Rightarrow> int list) 1 p3
        
     in sign_changes_fold p4)"

lemma scale_for_fractional_shift_gen:
  "scale_for_fractional_shift d (acc * d^n) xs = 
   map (\<lambda>(i, c). c * acc * d^i) (List.enumerate n xs)"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "acc * d ^ n * d = acc * d ^ Suc n"
    by (simp add: algebra_simps)
  then show ?case
    using Cons.IH[of "Suc n"] by (simp add: algebra_simps)
qed

lemma scale_for_fractional_shift_eq_map:
  "scale_for_fractional_shift d acc xs = map (\<lambda>(i, c). c * acc * d^i) (List.enumerate 0 xs)"
proof -
  have "acc = acc * d^0" by simp
  then show ?thesis
    using scale_for_fractional_shift_gen[of d acc 0 xs] by simp
qed

lemma length_scale_for_fractional_shift [simp]:
  "length (scale_for_fractional_shift d acc xs) = length xs"
  by (induction xs arbitrary: acc) simp_all

lemma rev_scale_rev_descending:
  "rev (scale_for_fractional_shift d 1 (rev xs)) = 
   map (\<lambda>(i, c). c * d^(length xs - 1 - i)) (List.enumerate 0 xs)"
proof (rule nth_equalityI)
  show "length (rev (scale_for_fractional_shift d 1 (rev xs))) = 
        length (map (\<lambda>(i, c). c * d ^ (length xs - 1 - i)) (List.enumerate 0 xs))"
    by simp
next
  fix i
  assume "i < length (rev (scale_for_fractional_shift d 1 (rev xs)))"
  then have "i < length xs" by simp
  have "rev (scale_for_fractional_shift d 1 (rev xs)) ! i = 
        scale_for_fractional_shift d 1 (rev xs) ! (length xs - 1 - i)"
    by (simp add: rev_nth \<open>i < length xs\<close>)
  also have "... = map (\<lambda>(j, c). c * 1 * d^j) (List.enumerate 0 (rev xs)) ! (length xs - 1 - i)"
    using scale_for_fractional_shift_eq_map[of d 1 "rev xs"] by simp
  also have "... = (rev xs ! (length xs - 1 - i)) * d ^ (length xs - 1 - i)"
    by (smt (verit, ccfv_threshold) One_nat_def Suc_diff_Suc
        \<open>i < length xs\<close> arith_simps(49) bot_nat_0.not_eq_extremum
        diff_less diff_zero enumerate_eq_zip length_rev length_upt
        less_trans not_less_eq nth_map2_dsc nth_upt)
  also have "... = (xs ! i) * d ^ (length xs - 1 - i)"
    using rev_nth
    by (metis \<open>i < length xs\<close> diff_Suc_eq_diff_pred length_rev
        rev_rev_ident)
  also have "... = map (\<lambda>(j, c). c * d ^ (length xs - 1 - j)) (List.enumerate 0 xs) ! i"
    by (simp add: \<open>i < length xs\<close> enumerate_eq_zip)
  finally show "rev (scale_for_fractional_shift d 1 (rev xs)) ! i = 
                map (\<lambda>(j, c). c * d ^ (length xs - 1 - j)) (List.enumerate 0 xs) ! i" 
    by simp
qed

definition smult_list :: "'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "smult_list c xs = map ((*) c) xs"

lemma length_smult_list [simp]:
  "length (smult_list c xs) = length xs"
  by (simp add: smult_list_def)

lemma nth_smult_list [simp]:
  "i < length xs \<Longrightarrow> smult_list c xs ! i = c * (xs ! i)"
  by (simp add: smult_list_def)

lemma Poly_smult_list [simp]:
  "Poly (smult_list c xs) = Polynomial.smult c (Poly xs)"
  by (induction xs) (auto simp: smult_list_def)

lemma ruffini_step_smult:
  "ruffini_step c (k * a) (smult_list k qs) = smult_list k (ruffini_step c a qs)"
proof (induction qs arbitrary: a)
  case Nil
  then show ?case by (simp add: smult_list_def)
next
  case (Cons q qs)
  have "k * a + c * (k * q) = k * (a + c * q)"
    by (simp add: algebra_simps)
  then show ?case
    using Cons.IH[of q] by (simp add: smult_list_def)
qed

lemma taylor_shift_list_smult:
  "taylor_shift_list c (smult_list k xs) = smult_list k (taylor_shift_list c xs)"
proof (induction xs)
  case Nil
  then show ?case by (simp add: smult_list_def)
next
  case (Cons a xs)
  then show ?case 
    using smult_list_def ruffini_step_smult
    by (metis smult_list_def ruffini_step_smult Cons.IH taylor_shift_list.simps(2) list.map(2))
qed

lemma poly_eq_same_length:
  assumes "length xs = length ys" and "Poly xs = Poly ys"
  shows "xs = ys"
proof (rule nth_equalityI)
  show "length xs = length ys" by fact
  fix i assume "i < length xs"
  have "xs ! i = nth_default 0 xs i" 
    by (simp add: \<open>i < length xs\<close> nth_default_def)
  also have "... = coeff (Poly xs) i" 
    by (simp add: nth_default_coeffs_eq)
  also have "... = coeff (Poly ys) i" 
    by (simp add: assms(2))
  also have "... = nth_default 0 ys i" 
    by (simp add: nth_default_coeffs_eq)
  also have "... = ys ! i" 
    by (metis nth_default_def assms(1) \<open>i < length xs\<close>)
  finally show "xs ! i = ys ! i" .
qed

lemma nth_scale_poly_list [simp]:
  "i < length xs \<Longrightarrow> scale_poly_list c xs ! i = (xs ! i) * c^i"
  using scale_poly_list_eq_map
  by (metis (no_types, lifting) arith_extra_simps(5) diff_zero
      enumerate_eq_zip length_upt nth_map2_dsc nth_upt)

lemma Poly_scale_poly_list:
  "Poly (scale_poly_list d xs) = pcompose (Poly xs) [:0, d:]"
proof (rule poly_eqI)
  fix i
  have "coeff (Poly (scale_poly_list d xs)) i = nth_default 0 (scale_poly_list d xs) i"
    by (simp add: coeff_Poly)
  also have "... = nth_default 0 xs i * d^i"
    by (simp add: nth_default_def)
  also have "... = coeff (Poly xs) i * d^i"
    by (simp add: coeff_Poly)
  also have "... = coeff (pcompose (Poly xs) [:0, d:]) i"
    by (simp add: coeff_pcompose_linear)
  finally show "coeff (Poly (scale_poly_list d xs)) i = coeff (pcompose (Poly xs) [:0, d:]) i" .
qed

lemma scale_poly_list_scale_poly_list:
  "scale_poly_list c (scale_poly_list d xs) = scale_poly_list (c * d) xs"
proof (rule poly_eq_same_length)
  show "length (scale_poly_list c (scale_poly_list d xs)) = length (scale_poly_list (c * d) xs)" by simp
  have "Poly (scale_poly_list c (scale_poly_list d xs)) = pcompose (pcompose (Poly xs) [:0, d:]) [:0, c:]"
    by (simp add: Poly_scale_poly_list)
  also have "... = pcompose (Poly xs) [:0, c * d:]"
    by (metis (no_types, lifting) mult_pCons_0 mult_pCons_left
        mult_zero_left one_pCons pCons_as_add pcompose_assoc
        pcompose_const pcompose_pCons smult_0_right smult_pCons
        x_as_monom)
  also have "... = Poly (scale_poly_list (c * d) xs)"
    by (simp add: Poly_scale_poly_list)
  finally show "Poly (scale_poly_list c (scale_poly_list d xs)) = Poly (scale_poly_list (c * d) xs)" .
qed

lemma Poly_map_rat_of_int:
  "Poly (map rat_of_int xs) = map_poly rat_of_int (Poly xs)"
proof (induction xs)
  case Nil
  then show ?case by fastforce
next
  case (Cons a xs)
  then show ?case
    by (simp add: comm_semiring_hom.map_poly_pCons_hom
        of_int_poly_hom.base.comm_semiring_hom_axioms)
qed

lemma map_rat_of_int_scale_poly_list:
  "map rat_of_int (scale_poly_list c xs) = scale_poly_list (rat_of_int c) (map rat_of_int xs)"
proof (rule poly_eq_same_length)
  show "length (map rat_of_int (scale_poly_list c xs)) = length (scale_poly_list (rat_of_int c) (map rat_of_int xs))" by simp
  have "Poly (map rat_of_int (scale_poly_list c xs)) = map_poly rat_of_int (pcompose (Poly xs) [:0, c:])"
    by (simp add: Poly_map_rat_of_int Poly_scale_poly_list)
  also have "... = pcompose (map_poly rat_of_int (Poly xs)) [:0, rat_of_int c:]"
    by (simp add: of_int_hom.map_poly_pCons_hom
        of_int_hom.map_poly_pcompose)
  also have "... = Poly (scale_poly_list (rat_of_int c) (map rat_of_int xs))"
    by (simp add: Poly_map_rat_of_int Poly_scale_poly_list)
  finally show "Poly (map rat_of_int (scale_poly_list c xs)) = Poly (scale_poly_list (rat_of_int c) (map rat_of_int xs))" .
qed

lemma scale_poly_list_smult_list:
  "scale_poly_list c (smult_list k xs) = smult_list k (scale_poly_list c xs)"
  by (rule poly_eq_same_length) (simp_all add: Poly_scale_poly_list pcompose_smult)

lemma taylor_scale_commute_rat:
  fixes c d :: rat
  shows "taylor_shift_list c (scale_poly_list d xs) = scale_poly_list d (taylor_shift_list (c * d) xs)"
proof (rule poly_eq_same_length)
  show "length (taylor_shift_list c (scale_poly_list d xs)) = length (scale_poly_list d (taylor_shift_list (c * d) xs))"
    by simp
  have "Poly (taylor_shift_list c (scale_poly_list d xs)) = pcompose (pcompose (Poly xs) [:0, d:]) [:c, 1:]"
    by (simp add: Poly_taylor_shift_list Poly_scale_poly_list)
  also have "... = pcompose (Poly xs) [:c * d, d:]"
    by (metis (no_types, lifting) add.right_neutral add_0
        mult_pCons_left mult_zero_left mult_zero_right pCons_0_0
        pCons_as_add pcompose_assoc pcompose_const pcompose_pCons
        smult_pCons x_as_monom)
  also have "... = pcompose (pcompose (Poly xs) [:c * d, 1:]) [:0, d:]"
    by (metis scale_poly_eq_pcompose scale_taylor_compose
        taylor_shift_def)
  also have "... = Poly (scale_poly_list d (taylor_shift_list (c * d) xs))"
    by (simp add: Poly_taylor_shift_list Poly_scale_poly_list)
  finally show "Poly (taylor_shift_list c (scale_poly_list d xs)) = Poly (scale_poly_list d (taylor_shift_list (c * d) xs))" .
qed

lemma scale_poly_list_rev:
  fixes c :: rat
  assumes "c \<noteq> 0"
  shows "scale_poly_list c (rev xs) = smult_list (c ^ (length xs - 1)) (rev (scale_poly_list (1 / c) xs))"
proof (rule nth_equalityI)
  show "length (scale_poly_list c (rev xs)) = length (smult_list (c ^ (length xs - 1)) (rev (scale_poly_list (1 / c) xs)))"
    by simp
next
  fix i assume "i < length (scale_poly_list c (rev xs))"
  then have i_len: "i < length xs" by simp
  have "scale_poly_list c (rev xs) ! i = (rev xs ! i) * c^i"
    using i_len by simp
  also have "... = (xs ! (length xs - 1 - i)) * c^i"
    using i_len by (simp add: rev_nth)
  also have "... = (xs ! (length xs - 1 - i)) * c^(length xs - 1) * (1 / c)^(length xs - 1 - i)"
    using \<open>c \<noteq> 0\<close> i_len by (simp add: power_diff field_simps)
  also have "... = c^(length xs - 1) * ((xs ! (length xs - 1 - i)) * (1 / c)^(length xs - 1 - i))"
    by (simp add: algebra_simps)
  also have "... = c^(length xs - 1) * (scale_poly_list (1 / c) xs ! (length xs - 1 - i))"
    using i_len by simp
  also have "... = c^(length xs - 1) * (rev (scale_poly_list (1 / c) xs) ! i)"
    using i_len by (simp add: rev_nth)
  also have "... = smult_list (c ^ (length xs - 1)) (rev (scale_poly_list (1 / c) xs)) ! i"
    using i_len by simp
  finally show "scale_poly_list c (rev xs) ! i = smult_list (c ^ (length xs - 1)) (rev (scale_poly_list (1 / c) xs)) ! i" .
qed

lemma map_rat_of_int_ruffini_step:
  "map rat_of_int (ruffini_step c a qs) = ruffini_step (rat_of_int c) (rat_of_int a) (map rat_of_int qs)"
  by (induction qs arbitrary: a) (simp_all add: algebra_simps)

lemma map_rat_of_int_taylor_shift_list:
  "map rat_of_int (taylor_shift_list c xs) = taylor_shift_list (rat_of_int c) (map rat_of_int xs)"
  by (induction xs) (simp_all add: map_rat_of_int_ruffini_step)

lemma scale_for_fractional_shift_eq_scale_poly_list:
  "scale_for_fractional_shift c 1 xs = scale_poly_list c xs"
  using scale_for_fractional_shift_eq_map
  by (metis (mono_tags, lifting) mult_cancel_right1 power.simps(1)
      scale_poly_list_aux_enumerate scale_poly_list_def)

lemma map_rat_of_int_fractional_taylor_shift:
  fixes a :: rat and xs :: "int list"
  defines "n \<equiv> fst (quotient_of a)"
  defines "d \<equiv> snd (quotient_of a)"
  shows "map rat_of_int (fractional_taylor_shift a xs) =
         smult_list (rat_of_int d ^ (length xs - 1)) (scale_poly_list (1 / rat_of_int d) (taylor_shift_list a (map rat_of_int xs)))"
proof (cases "xs = []")
  case True
  then show ?thesis
    by (simp add: fractional_taylor_shift_def Let_def n_def d_def split_def smult_list_def scale_poly_list_def scale_for_fractional_shift_eq_scale_poly_list)
next
  case False
  have d_pos: "d > 0"
    using d_def quotient_of_denom_pos[of a]
    using quotient_of_denom_pos' by blast
  have d_neq_0: "rat_of_int d \<noteq> 0"
    using d_pos by simp
  have a_eq: "a = rat_of_int n / rat_of_int d"
    using n_def d_def quotient_of_div[of a] by simp

  have "map rat_of_int (fractional_taylor_shift a xs) =
        map rat_of_int (taylor_shift_list n (rev (scale_for_fractional_shift d 1 (rev xs))))"
    unfolding fractional_taylor_shift_def Let_def split_def n_def d_def by simp
  also have "... = taylor_shift_list (rat_of_int n) (map rat_of_int (rev (scale_poly_list d (rev xs))))"
    by (simp add: map_rat_of_int_taylor_shift_list scale_for_fractional_shift_eq_scale_poly_list)
  also have "... = taylor_shift_list (rat_of_int n) (rev (scale_poly_list (rat_of_int d) (map rat_of_int (rev xs))))"
    using map_rat_of_int_scale_poly_list rev_map by metis
  also have "... = taylor_shift_list (rat_of_int n) (rev (scale_poly_list (rat_of_int d) (rev (map rat_of_int xs))))"
    by (simp add: rev_map)
  also have "... = taylor_shift_list (rat_of_int n) (rev (smult_list (rat_of_int d ^ (length xs - 1)) (rev (scale_poly_list (1 / rat_of_int d) (map rat_of_int xs)))))"
    using scale_poly_list_rev[OF d_neq_0, of "map rat_of_int xs"] by simp
  also have "... = taylor_shift_list (rat_of_int n) (smult_list (rat_of_int d ^ (length xs - 1)) (scale_poly_list (1 / rat_of_int d) (map rat_of_int xs)))"
    using rev_rev_ident 
    by (simp add: rev_map smult_list_def)
  also have "... = smult_list (rat_of_int d ^ (length xs - 1)) (taylor_shift_list (rat_of_int n) (scale_poly_list (1 / rat_of_int d) (map rat_of_int xs)))"
    by (simp add: taylor_shift_list_smult)
  also have "... = smult_list (rat_of_int d ^ (length xs - 1)) (scale_poly_list (1 / rat_of_int d) (taylor_shift_list (rat_of_int n * (1 / rat_of_int d)) (map rat_of_int xs)))"
    by (simp add: taylor_scale_commute_rat)
  also have "... = smult_list (rat_of_int d ^ (length xs - 1)) (scale_poly_list (1 / rat_of_int d) (taylor_shift_list a (map rat_of_int xs)))"
    using a_eq by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma smult_list_smult_list:
  "smult_list a (smult_list b xs) = smult_list (a * b) xs"
  by (simp add: smult_list_def algebra_simps)

lemma rev_smult_list:
  "rev (smult_list c xs) = smult_list c (rev xs)"
  by (simp add: smult_list_def rev_map)

lemma p3_rat_equiv:
  fixes a b :: rat and xs :: "int list"
  assumes "length xs > 0" and "a \<noteq> b"
  defines "k \<equiv> length xs - 1"
  defines "da \<equiv> snd (quotient_of a)"
  defines "dw \<equiv> snd (quotient_of ((b - a) * of_int da))"
  defines "nw \<equiv> fst (quotient_of ((b - a) * of_int da))"
  defines "p1 \<equiv> fractional_taylor_shift a xs"
  defines "p3 \<equiv> scale_for_fractional_shift dw 1 (rev (scale_poly_list nw p1))"
  shows "map rat_of_int p3 = smult_list ((rat_of_int da * rat_of_int dw) ^ k) (rev (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int xs))))"
proof -
  have da_pos: "da > 0" using da_def quotient_of_denom_pos[of a] 
    using quotient_of_denom_pos' by blast
  have dw_pos: "dw > 0" using dw_def quotient_of_denom_pos[of "(b - a) * rat_of_int da"]
    using quotient_of_denom_pos' by presburger
  have da_neq_0: "rat_of_int da \<noteq> 0" using da_pos by simp
  have dw_neq_0: "rat_of_int dw \<noteq> 0" using dw_pos by simp
  have width_eq: "rat_of_int nw / (rat_of_int da * rat_of_int dw) = b - a"
    using nw_def dw_def quotient_of_div[of "(b - a) * rat_of_int da"]
    by (metis da_neq_0 divide_divide_eq_left' eq_divide_imp
        prod.exhaust_sel)

  let ?L_inner = "taylor_shift_list a (map rat_of_int xs)"
  
  have "map rat_of_int p3 = scale_poly_list (rat_of_int dw) (rev (scale_poly_list (rat_of_int nw) (map rat_of_int p1)))"
    unfolding p3_def scale_for_fractional_shift_eq_scale_poly_list 
    by (metis map_rat_of_int_scale_poly_list rev_map)
  also have "... = scale_poly_list (rat_of_int dw) (rev (scale_poly_list (rat_of_int nw) (smult_list (rat_of_int da ^ k) (scale_poly_list (1 / rat_of_int da) ?L_inner))))"
    using map_rat_of_int_fractional_taylor_shift[of a xs] k_def da_def p1_def by simp
  also have "... = scale_poly_list (rat_of_int dw) (rev (smult_list (rat_of_int da ^ k) (scale_poly_list (rat_of_int nw) (scale_poly_list (1 / rat_of_int da) ?L_inner))))"
    by (simp add: scale_poly_list_smult_list)
  also have "... = scale_poly_list (rat_of_int dw) (smult_list (rat_of_int da ^ k) (rev (scale_poly_list (rat_of_int nw * (1 / rat_of_int da)) ?L_inner)))"
    by (simp add: scale_poly_list_scale_poly_list rev_smult_list)
  also have "... = smult_list (rat_of_int da ^ k) (scale_poly_list (rat_of_int dw) (rev (scale_poly_list (rat_of_int nw / rat_of_int da) ?L_inner)))"
    by (simp add: scale_poly_list_smult_list)
  also have "... = smult_list (rat_of_int da ^ k) (smult_list (rat_of_int dw ^ k) (rev (scale_poly_list (1 / rat_of_int dw) (scale_poly_list (rat_of_int nw / rat_of_int da) ?L_inner))))"
  proof -
    have len_eq: "length (scale_poly_list (rat_of_int nw / rat_of_int da) ?L_inner) - 1 = k"
      using k_def by simp
    show ?thesis
      using scale_poly_list_rev[OF dw_neq_0, of "scale_poly_list (rat_of_int nw / rat_of_int da) ?L_inner"] len_eq by simp
  qed
  also have "... = smult_list ((rat_of_int da * rat_of_int dw) ^ k) (rev (scale_poly_list (1 / rat_of_int dw * (rat_of_int nw / rat_of_int da)) ?L_inner))"
    by (simp add: scale_poly_list_scale_poly_list smult_list_smult_list power_mult_distrib)
  also have "... = smult_list ((rat_of_int da * rat_of_int dw) ^ k) (rev (scale_poly_list (b - a) ?L_inner))"
    using width_eq
    by (metis divide_divide_eq_left more_arith_simps(5)
        times_divide_eq_left)
  finally show ?thesis .
qed

lemma p4_rat_equiv:
  fixes a b :: rat and xs :: "int list"
  assumes "length xs > 0" and "a \<noteq> b"
  defines "k \<equiv> length xs - 1"
  defines "da \<equiv> snd (quotient_of a)"
  defines "dw \<equiv> snd (quotient_of ((b - a) * of_int da))"
  defines "nw \<equiv> fst (quotient_of ((b - a) * of_int da))"
  defines "p1 \<equiv> fractional_taylor_shift a xs"
  defines "p3 \<equiv> scale_for_fractional_shift dw 1 (rev (scale_poly_list nw p1))"
  defines "p4 \<equiv> taylor_shift_list 1 p3"
  shows "map rat_of_int p4 = smult_list ((rat_of_int da * rat_of_int dw) ^ k) 
           (taylor_shift_list 1 (rev (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int xs)))))"
proof -
  have "map rat_of_int p4 = taylor_shift_list 1 (map rat_of_int p3)"
    unfolding p4_def by (simp add: map_rat_of_int_taylor_shift_list)
  also have "... = taylor_shift_list 1 (smult_list ((rat_of_int da * rat_of_int dw) ^ k) (rev (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int xs)))))"
    using p3_rat_equiv[OF assms(1) assms(2)] k_def da_def dw_def nw_def p1_def p3_def by simp
  also have "... = smult_list ((rat_of_int da * rat_of_int dw) ^ k) (taylor_shift_list 1 (rev (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int xs)))))"
    by (simp add: taylor_shift_list_smult)
  finally show ?thesis .
qed

lemma filter_sgn_smult_list_pos:
  fixes c :: "'a::linordered_idom"
  assumes "c > 0"
  shows "filter (\<lambda>x. x \<noteq> 0) (map sgn (smult_list c xs)) = filter (\<lambda>x. x \<noteq> 0) (map sgn xs)"
proof (induction xs)
  case Nil
  then show ?case by (simp add: smult_list_def)
next
  case (Cons x xs)
  have "sgn (c * x) = sgn x"
    using assms by (simp add: sgn_mult)
  then show ?case
    using Cons.IH by (simp add: smult_list_def)
qed

lemma sign_changes_fold_smult_list_pos:
  fixes c :: "'a::linordered_idom"
  assumes "c > 0"
  shows "sign_changes_fold (smult_list c xs) = sign_changes_fold xs"
proof -
  have "sign_changes_fold (smult_list c xs) = snd (fold sign_step (filter (\<lambda>x. x \<noteq> 0) (map sgn (smult_list c xs))) (0, 0))"
    using fold_sign_step_map_filter unfolding sign_changes_fold_def by metis
  also have "... = snd (fold sign_step (filter (\<lambda>x. x \<noteq> 0) (map sgn xs)) (0, 0))"
    using filter_sgn_smult_list_pos[OF assms] by simp
  also have "... = sign_changes_fold xs"
    using fold_sign_step_map_filter unfolding sign_changes_fold_def by metis
  finally show ?thesis .
qed

lemma sign_step_rat_of_int:
  "sign_step (rat_of_int x) (rat_of_int s, n) = 
   (let (s', n') = sign_step x (s, n) in (rat_of_int s', n'))"
  by (auto simp: sgn_if split: if_splits)

lemma fold_sign_step_rat_of_int:
  "fold sign_step (map rat_of_int xs) (rat_of_int s, n) = 
   (let (s', n') = fold sign_step xs (s, n) in (rat_of_int s', n'))"
proof (induction xs arbitrary: s n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "fold sign_step (map rat_of_int (x # xs)) (rat_of_int s, n) = 
        fold sign_step (map rat_of_int xs) (sign_step (rat_of_int x) (rat_of_int s, n))"
    by simp
  also have "... = fold sign_step (map rat_of_int xs) (let (s', n') = sign_step x (s, n) in (rat_of_int s', n'))"
    using sign_step_rat_of_int by presburger
  also have "... = (let (s', n') = sign_step x (s, n); (s'', n'') = fold sign_step xs (s', n') in (rat_of_int s'', n''))"
    using Cons.IH by (simp add: split_def)
  also have "... = (let (s'', n'') = fold sign_step (x # xs) (s, n) in (rat_of_int s'', n''))"
    by (simp add: split_def)
  finally show ?case .
qed

lemma sign_changes_fold_map_rat_of_int:
  "sign_changes_fold (map rat_of_int xs) = sign_changes_fold xs"
proof -
  have "fold sign_step (map rat_of_int xs) (0, 0) = fold sign_step (map rat_of_int xs) (rat_of_int 0, 0)"
    by simp
  also have "... = (let (s', n') = fold sign_step xs (0, 0) in (rat_of_int s', n'))"
    by (metis fold_sign_step_rat_of_int)
  finally show ?thesis
    unfolding sign_changes_fold_def
    by (metis (mono_tags, lifting) prod.sel(2) split_def)
qed

theorem descartes_list_int_correct:
  assumes "length xs > 0" and "a < b"
  shows "descartes_list_int a b xs = fast_descartes_list a b (map rat_of_int xs)"
proof -
  have a_neq_b: "a \<noteq> b" using assms(2) by simp
  
  let ?da = "snd (quotient_of a)"
  let ?dw = "snd (quotient_of ((b - a) * of_int ?da))"
  let ?nw = "fst (quotient_of ((b - a) * of_int ?da))"
  let ?k = "length xs - 1"
  
  have da_pos: "?da > 0" using quotient_of_denom_pos[of a] 
    using quotient_of_nonzero(1) by presburger
  have dw_pos: "?dw > 0" using quotient_of_denom_pos[of "(b - a) * of_int ?da"]
    using quotient_of_nonzero(1) by presburger
  have scalar_pos: "(rat_of_int ?da * rat_of_int ?dw) ^ ?k > 0"
    using da_pos dw_pos by simp

  let ?p1 = "fractional_taylor_shift a xs"
  let ?p3 = "scale_for_fractional_shift ?dw 1 (rev (scale_poly_list ?nw ?p1))"
  let ?p4 = "taylor_shift_list 1 ?p3"
  
  have "descartes_list_int a b xs = sign_changes_fold ?p4"
    unfolding descartes_list_int_def Let_def split_def by simp
  also have "... = sign_changes_fold (map rat_of_int ?p4)"
    by (simp add: sign_changes_fold_map_rat_of_int)
  also have "... = sign_changes_fold (smult_list ((rat_of_int ?da * rat_of_int ?dw) ^ ?k) 
           (taylor_shift_list 1 (rev (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int xs))))))"
    using p4_rat_equiv[OF assms(1) a_neq_b] by simp
  also have "... = sign_changes_fold (taylor_shift_list 1 (rev (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int xs)))))"
    using sign_changes_fold_smult_list_pos[OF scalar_pos] by simp
  also have "... = sign_changes_fold (taylor_shift_list 1 (reverse_array_fun (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int xs)))))"
    by (simp add: reverse_array_fun_eq_rev)
  also have "... = fast_descartes_list a b (map rat_of_int xs)"
    unfolding fast_descartes_list_def by simp
  finally show ?thesis .
qed

partial_function (tailrec) dsc_main_int ::
  "int poly \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list"
where
  [code]:
  "dsc_main_int P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b) # todo' \<Rightarrow>
          (let v = descartes_list_int a b (coeffs P) in
           if v = 0 then
             dsc_main_int P todo' acc
           else if v = 1 then
             dsc_main_int P todo' ((a,b) # acc)
           else
             (let m = (a + b) / 2;
                  acc' = (if poly (map_poly of_int P) m = 0 then (m,m) # acc else acc)
              in dsc_main_int P ((a,m) # (m,b) # todo') acc')))"

definition dsc_int :: "rat \<Rightarrow> rat \<Rightarrow> int poly \<Rightarrow> (rat \<times> rat) list"
where
  "dsc_int a b P = (dsc_main_int P [(a,b)] [])"

definition snap_window_rat :: "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> rat \<times> rat" where
  "snap_window_rat a b N lam =
     (let w    = b - a;
          s    = 4 * N;
          step = w / of_nat s;
          k0   = floor (of_nat s * ((lam - of_rat a) / of_rat w));
          k    = max 2 (min (int s - 2) k0);
          kn   = nat k
       in (a + of_nat (kn - 2) * step, a + of_nat (kn + 2) * step))"

definition try_blocks_int ::
  "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> nat \<Rightarrow> (rat \<times> rat) option"
where
  "try_blocks_int a b N P v =
     (let w = b - a;
          B1 = (a, a + w / of_nat N);
          B2 = (b - w / of_nat N, b);
          v1 = descartes_list_int (fst B1) (snd B1) (coeffs P);
          v2 = descartes_list_int (fst B2) (snd B2) (coeffs P)
      in if v1 = v then Some B1 else if v2 = v then Some B2 else None)"

definition try_newton_int ::
  "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> nat \<Rightarrow> (rat \<times> rat) option"
where
  "try_newton_int a b N P v =
     (let P_real = map_poly of_int P :: real poly;
          L1 = newton_at (int v) P_real (of_rat a); 
          L2 = newton_at (int v) P_real (of_rat b) 
      in case L1 of
        Some lam1 \<Rightarrow>
          (let I1 = snap_window_rat a b N lam1;
               v1 = descartes_list_int (fst I1) (snd I1) (coeffs P)
           in if v1 = v then Some I1
              else (case L2 of
                      Some lam2 \<Rightarrow>
                        (let I2 = snap_window_rat a b N lam2;
                             v2 = descartes_list_int (fst I2) (snd I2) (coeffs P)
                         in if v2 = v then Some I2 else None)
                    | None \<Rightarrow> None))
      | None \<Rightarrow>
          (case L2 of
             Some lam2 \<Rightarrow>
               (let I2 = snap_window_rat a b N lam2;
                    v2 = descartes_list_int (fst I2) (snd I2) (coeffs P)
                in if v2 = v then Some I2 else None)
           | None \<Rightarrow> None))"

partial_function (tailrec) newdsc_main_int ::
  "int poly \<Rightarrow> (rat \<times> rat \<times> nat) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list"
where
  [code]:
  "newdsc_main_int P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b,e) # todo' \<Rightarrow>
          (let v = descartes_list_int a b (coeffs P) in
           if v = 0 then
             newdsc_main_int P todo' acc
           else if v = 1 then
             newdsc_main_int P todo' ((a,b) # acc)
           else
             (case try_blocks_int a b (N_of e) P v of
                Some I \<Rightarrow>
                  newdsc_main_int P ((fst I, snd I, e + 1) # todo') acc
              | None \<Rightarrow>
                  (case try_newton_int a b (N_of e) P v of
                     Some I \<Rightarrow>
                       newdsc_main_int P ((fst I, snd I, e + 1) # todo') acc
                   | None \<Rightarrow>
                       (let m  = (a + b) / 2;
                            e' = max 1 (e - 1);
                            acc' = (if poly (map_poly of_int P :: rat poly) m = 0 then (m,m) # acc else acc)
                        in newdsc_main_int P ((a,m,e') # (m,b,e') # todo') acc')))))"

definition newdsc_int ::
  "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> (rat \<times> rat) list"
where
  "newdsc_int a b e P = newdsc_main_int P [(a,b,e)] []"


lemma snap_window_rat_eq:
  "snap_window (of_rat a) (of_rat b) N lam = 
   (of_rat (fst (snap_window_rat a b N lam)), of_rat (snd (snap_window_rat a b N lam)))"
proof -
  let ?w_rat = "b - a"
  let ?w_real = "of_rat b - of_rat a"
  have w_eq: "?w_real = of_rat ?w_rat" 
    by (simp add: of_rat_diff)
  
  let ?s = "4 * N"

  let ?step_rat = "?w_rat / of_nat ?s"
  let ?step_real = "?w_real / of_nat ?s"
  have step_eq: "?step_real = of_rat ?step_rat" 
    by (metis of_rat_diff of_rat_divide of_rat_hom.hom_of_nat)

  let ?k0_real = "floor (of_nat ?s * ((lam - of_rat a) / ?w_real))"
  let ?k0_rat  = "floor (of_nat ?s * ((lam - of_rat a) / of_rat ?w_rat))"
  have k0_eq: "?k0_real = ?k0_rat" 
    by (simp add: w_eq)

  show ?thesis
    unfolding snap_window_def snap_window_rat_def Let_def
    using w_eq step_eq k0_eq [[linarith_split_limit = 1000]]
  proof -
    have "(real_of_rat a + real_of_rat (rat_of_nat (nat (max 2 (min (int (4 * N) - 2) \<lfloor>real_of_rat (rat_of_nat (4 * N)) * ((lam - real_of_rat a) / real_of_rat (b - a))\<rfloor>)) - 2)) * real_of_rat ((b - a) / rat_of_nat (4 * N)), real_of_rat a + real_of_rat (rat_of_nat (nat (max 2 (min (int (4 * N) - 2) \<lfloor>real_of_rat (rat_of_nat (4 * N)) * ((lam - real_of_rat a) / real_of_rat (b - a))\<rfloor>)) + 2)) * real_of_rat ((b - a) / rat_of_nat (4 * N))) = (real_of_rat (a + rat_of_nat (nat (max 2 (min (int (4 * N) - 2) \<lfloor>real_of_rat (rat_of_nat (4 * N)) * ((lam - real_of_rat a) / real_of_rat (b - a))\<rfloor>)) - 2) * ((b - a) / rat_of_nat (4 * N))), real_of_rat (a + rat_of_nat (nat (max 2 (min (int (4 * N) - 2) \<lfloor>real_of_rat (rat_of_nat (4 * N)) * ((lam - real_of_rat a) / real_of_rat (b - a))\<rfloor>)) + 2) * ((b - a) / rat_of_nat (4 * N))))"
      by (metis (no_types) of_rat_hom.hom_add of_rat_mult)
    then show "(real_of_rat a + real (nat (max 2 (min (int (4 * N) - 2) \<lfloor>real (4 * N) * ((lam - real_of_rat a) / (real_of_rat b - real_of_rat a))\<rfloor>)) - 2) * ((real_of_rat b - real_of_rat a) / real (4 * N)), real_of_rat a + real (nat (max 2 (min (int (4 * N) - 2) \<lfloor>real (4 * N) * ((lam - real_of_rat a) / (real_of_rat b - real_of_rat a))\<rfloor>)) + 2) * ((real_of_rat b - real_of_rat a) / real (4 * N))) = (real_of_rat (fst (a + rat_of_nat (nat (max 2 (min (int (4 * N) - 2) \<lfloor>real (4 * N) * ((lam - real_of_rat a) / real_of_rat (b - a))\<rfloor>)) - 2) * ((b - a) / rat_of_nat (4 * N)), a + rat_of_nat (nat (max 2 (min (int (4 * N) - 2) \<lfloor>real (4 * N) * ((lam - real_of_rat a) / real_of_rat (b - a))\<rfloor>)) + 2) * ((b - a) / rat_of_nat (4 * N)))), real_of_rat (snd (a + rat_of_nat (nat (max 2 (min (int (4 * N) - 2) \<lfloor>real (4 * N) * ((lam - real_of_rat a) / real_of_rat (b - a))\<rfloor>)) - 2) * ((b - a) / rat_of_nat (4 * N)), a + rat_of_nat (nat (max 2 (min (int (4 * N) - 2) \<lfloor>real (4 * N) * ((lam - real_of_rat a) / real_of_rat (b - a))\<rfloor>)) + 2) * ((b - a) / rat_of_nat (4 * N)))))"
      by (metis (no_types) fst_conv of_rat_of_nat_eq snd_conv step_eq w_eq)
  qed
qed

lemma descartes_roots_test_sc_of_int:
  assumes "a < b" and "P \<noteq> 0"
  shows "int (descartes_list_int a b (coeffs P)) = 
         descartes_roots_test_sc (of_rat a) (of_rat b) (map_poly of_int P :: real poly)"
proof -
  have "coeffs (map_poly rat_of_int P) = map rat_of_int (coeffs P)"
    by (simp add: coeffs_map_poly)
  moreover have "descartes_list_int a b (coeffs P) = fast_descartes_list a b (map rat_of_int (coeffs P))"
    using assms descartes_list_int_correct by (metis coeffs_eq_Nil length_0_conv length_greater_0_conv)
  ultimately have "descartes_list_int a b (coeffs P) = fast_descartes_list a b (coeffs (map_poly rat_of_int P))"
    by simp
  also have "\<dots> = descartes_roots_test_sc_rat a b (map_poly rat_of_int P)"
    using assms fast_descartes_list_equiv
    by (metis assms(2) fast_descartes_list_equiv assms(1) less_irrefl)
  also have "int \<dots> = descartes_roots_test_sc (of_rat a) (of_rat b) (map_poly of_int P :: real poly)"
    by (simp add: descartes_roots_test_sc_rat_refine map_poly_map_poly o_def)
  finally show ?thesis .
qed

lemma try_blocks_int_eq_sc:
  assumes "a < b" and "P \<noteq> 0" and "N > 0"
  shows "try_blocks_int a b N P v = 
         (case try_blocks_sc (of_rat a) (of_rat b) N (map_poly of_int P :: real poly) (int v) of
            None \<Rightarrow> None
          | Some (a', b') \<Rightarrow> Some (THE a''. of_rat a'' = a', THE b''. of_rat b'' = b'))"
proof -
  let ?P_real = "map_poly of_int P :: real poly"

  let ?w = "(b - a) / of_nat N"
  let ?b1_l = "a"
  let ?b1_r = "a + ?w"
  let ?b2_l = "b - ?w"
  let ?b2_r = "b"

  have N_pos: "of_nat N > (0::rat)" using assms(3) by simp
  have w_pos: "?w > 0" using assms(1) N_pos by simp
  have b1_ord: "?b1_l < ?b1_r" using w_pos by simp
  have b2_ord: "?b2_l < ?b2_r" using w_pos by simp

  have v1_eq: "descartes_roots_test_sc (of_rat ?b1_l) (of_rat ?b1_r) ?P_real = 
               int (descartes_list_int ?b1_l ?b1_r (coeffs P))"
    using descartes_roots_test_sc_of_int[OF b1_ord assms(2)] by simp

  have v2_eq: "descartes_roots_test_sc (of_rat ?b2_l) (of_rat ?b2_r) ?P_real = 
               int (descartes_list_int ?b2_l ?b2_r (coeffs P))"
    using descartes_roots_test_sc_of_int[OF b2_ord assms(2)] by simp

  have real_b1_r: "(of_rat a :: real) + (of_rat b - of_rat a) / of_nat N = of_rat ?b1_r"
    by (simp add: of_rat_add of_rat_diff of_rat_divide)
  
  have real_b2_l: "(of_rat b :: real) - (of_rat b - of_rat a) / of_nat N = of_rat ?b2_l"
    by (simp add: of_rat_diff of_rat_divide)

  show ?thesis
    unfolding try_blocks_int_def try_blocks_sc_def Let_def
    using v1_eq v2_eq real_b1_r real_b2_l
    by simp
qed

lemma try_newton_int_eq_sc:
  assumes "a < b" and "P \<noteq> 0" and "N > 0"
  shows "try_newton_int a b N P v = 
         (case try_newton_sc (of_rat a) (of_rat b) N (map_poly of_int P :: real poly) (int v) of
            None \<Rightarrow> None
          | Some (a', b') \<Rightarrow> Some (THE a''. of_rat a'' = a', THE b''. of_rat b'' = b'))"
proof -
  let ?P_real = "map_poly of_int P :: real poly"
  
  have I_ord: "\<And>lam. fst (snap_window_rat a b N lam) < snd (snap_window_rat a b N lam)"
  proof -
    fix lam
    have ab_real: "(of_rat a :: real) < of_rat b" 
      using assms(1) by (simp add: of_rat_less)
    have "(of_rat (snd (snap_window_rat a b N lam)) :: real) - of_rat (fst (snap_window_rat a b N lam)) = 
          snd (snap_window (of_rat a) (of_rat b) N lam) - fst (snap_window (of_rat a) (of_rat b) N lam)"
      by (simp add: snap_window_rat_eq)
    also have "\<dots> = (of_rat b - of_rat a :: real) / of_nat N"
      using snap_window_width[OF ab_real assms(3)] by simp
    also have "\<dots> > 0"
      using ab_real assms(3) by simp
    finally show "fst (snap_window_rat a b N lam) < snd (snap_window_rat a b N lam)"
      by (metis diff_gt_0_iff_gt of_rat_less)
  qed

  have v_eq: "\<And>lam. descartes_roots_test_sc (of_rat (fst (snap_window_rat a b N lam))) (of_rat (snd (snap_window_rat a b N lam))) ?P_real =
                    int (descartes_list_int (fst (snap_window_rat a b N lam)) (snd (snap_window_rat a b N lam)) (coeffs P))"
    using descartes_roots_test_sc_of_int assms I_ord by simp

  have the_eq: "\<And>x. (THE a''. of_rat a'' = (of_rat x :: real)) = x"
    by simp

  show ?thesis
    unfolding try_newton_int_def try_newton_sc_def Let_def snap_window_rat_eq
    using v_eq by (auto split: option.splits simp: the_eq)
qed

lemma poly_rat_eq_poly_real:
  "poly (map_poly of_int P :: rat poly) x = 0 \<longleftrightarrow> poly (map_poly of_int P :: real poly) (of_rat x) = 0"
proof -
  have "of_rat (poly (map_poly of_int P :: rat poly) x) = poly (map_poly of_int P :: real poly) (of_rat x)"
    by (induction P) (auto simp: of_rat_add of_rat_mult)
  thus ?thesis by auto
qed

definition real_to_rat_pair :: "real \<times> real \<Rightarrow> rat \<times> rat" where
  "real_to_rat_pair = (\<lambda>(x,y). (THE r. of_rat r = x, THE r. of_rat r = y))"

lemma real_to_rat_pair_of_rat[simp]:
  "real_to_rat_pair (of_rat a, of_rat b) = (a, b)"
  by (simp add: real_to_rat_pair_def)

lemma dsc_main_int_sim_aux:
  assumes "dsc_dom (p, a', b', P')"
    and "a' = of_rat a"
    and "b' = of_rat b"
    and "P' = map_poly of_int P"
    and "p = degree P"
    and "P \<noteq> 0"
    and "a < b"
  shows
    "dsc_main_int P ((a,b) # todo) acc =
     dsc_main_int P todo (map real_to_rat_pair (rev (dsc p a' b' P')) @ acc)"
using assms
proof (induction p a' b' P' arbitrary: a b todo acc rule: dsc.pinduct)
  case (1 p a' b' P' a b todo acc)
  let ?P_real = "map_poly of_int P :: real poly"
  let ?v = "Bernstein_changes p (of_rat a) (of_rat b) ?P_real"

  have deg_p: "degree ?P_real = p"
    using "1.prems" by simp

  have v_eq: "int (descartes_list_int a b (coeffs P)) = ?v"
    using descartes_roots_test_sc_of_int[OF \<open>a < b\<close> \<open>P \<noteq> 0\<close>]
    by (simp add: descartes_roots_test_sc_eq_Bernstein_changes deg_p "1.prems")

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have dsc0: "dsc p a' b' P' = []"
      using "1.hyps" "1.prems" v0 by (subst dsc.psimps, auto)
    show ?thesis
      using dsc0 dsc_main_int.simps v0 v_eq "1.prems" by auto
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have dsc1: "dsc p a' b' P' = [(a',b')]"
        using "1.hyps" "1.prems" v1 v0 by (subst dsc.psimps, auto)
      show ?thesis
        using dsc_main_int.simps Let_def v0 v1 v_eq dsc1 "1.prems" by auto
    next
      case v1: False
      define m where "m = (a + b) / 2"
      let ?m_real = "(of_rat a + of_rat b) / 2"
      have m_real_eq: "of_rat m = ?m_real" by (simp add: m_def of_rat_add of_rat_divide)

      let ?mid_rat = "(if poly (map_poly of_int P :: rat poly) m = 0 then [(m,m)] else [])"
      let ?mid_real = "(if poly ?P_real ?m_real = 0 then [(?m_real,?m_real)] else [])"

      have mid_map: "map real_to_rat_pair ?mid_real = ?mid_rat"
        using poly_rat_eq_poly_real m_real_eq 
        by (smt (verit, ccfv_threshold) list.map(1,2)
            real_to_rat_pair_of_rat)

      have dsc_split:
        "dsc p a' b' P' = ?mid_real @ dsc p a' ?m_real P' @ dsc p ?m_real b' P'"
        using "1.hyps" "1.prems" v0 v1 by (subst dsc.psimps, auto simp add: Let_def)

      have mid_acc_eq:
        "(if poly (map_poly of_int P :: rat poly) m = 0 then (m,m) # acc else acc) = ?mid_rat @ acc"
        by auto

      have main_split:
        "dsc_main_int P ((a,b) # todo) acc =
         dsc_main_int P ((a,m) # (m,b) # todo) (?mid_rat @ acc)"
      proof -
        let ?v_int = "descartes_list_int a b (coeffs P)"
        have v_neq_0: "?v_int \<noteq> 0" using v0 v_eq by auto
        have v_neq_1: "?v_int \<noteq> 1" using v1 v_eq by auto
        have tmp:
          "dsc_main_int P ((a,b) # todo) acc =
           dsc_main_int P ((a,m) # (m,b) # todo)
             (if poly (map_poly of_int P :: rat poly) m = 0 then (m,m) # acc else acc)"
          apply (subst dsc_main_int.simps)
          using v_neq_0 v_neq_1 m_def
          by (smt (verit, ccfv_threshold) list.case(2) prod.simps(2))
        show ?thesis
          using tmp by (simp add: mid_acc_eq)
      qed

      have a_lt_m: "a < m" using \<open>a < b\<close> m_def by auto
      have m_lt_b: "m < b" using \<open>a < b\<close> m_def by auto

      have stepL:
        "dsc_main_int P ((a,m) # (m,b) # todo) (?mid_rat @ acc) =
         dsc_main_int P ((m,b) # todo) (map real_to_rat_pair (rev (dsc p a' ?m_real P')) @ (?mid_rat @ acc))"
      proof -
        have "dsc_main_int P ((a,m) # (m,b) # todo) (?mid_rat @ acc) =
              dsc_main_int P ((m,b) # todo) (map real_to_rat_pair (rev (dsc p a' (of_rat m) P')) @ (?mid_rat @ acc))"
          apply (rule "1.IH"(1))
          using v0 v1 \<open>a' = of_rat a\<close> m_real_eq \<open>P' = map_poly of_int P\<close> \<open>p = degree P\<close> \<open>P \<noteq> 0\<close> a_lt_m
          apply blast
          using "1"(4,5) "1.prems"(3) v0 apply blast
          apply (simp add: "1"(4,5) \<open>P' = real_of_int_poly P\<close> v1)
          using "1"(4,5) m_real_eq apply blast
               apply (metis "1"(4))
              apply simp
             apply (metis "1"(6))
            apply (metis "1"(7))
          apply (metis "1"(8))
          by (metis a_lt_m)
          thus ?thesis using m_real_eq
            by metis
      qed

      have stepR:
        "dsc_main_int P ((m,b) # todo) (map real_to_rat_pair (rev (dsc p a' ?m_real P')) @ (?mid_rat @ acc)) =
         dsc_main_int P todo
           (map real_to_rat_pair (rev (dsc p ?m_real b' P')) @ (map real_to_rat_pair (rev (dsc p a' ?m_real P')) @ (?mid_rat @ acc)))"
      proof -
        have "dsc_main_int P ((m,b) # todo) (map real_to_rat_pair (rev (dsc p a' ?m_real P')) @ (?mid_rat @ acc)) =
              dsc_main_int P todo (map real_to_rat_pair (rev (dsc p (of_rat m) b' P')) @ (map real_to_rat_pair (rev (dsc p a' ?m_real P')) @ (?mid_rat @ acc)))"
          apply (rule "1.IH"(2))
          using v0 v1 m_real_eq \<open>b' = of_rat b\<close> \<open>P' = map_poly of_int P\<close> \<open>p = degree P\<close> \<open>P \<noteq> 0\<close> m_lt_b
          apply blast
          using "1"(4,5) "1.prems"(3) v0 apply blast
          apply (simp add: "1"(4,5) \<open>P' = real_of_int_poly P\<close> v1)
          using "1"(4,5) m_real_eq apply blast
               apply (metis "1"(4))
              apply (metis "1"(5))
             apply (metis "1"(6))
            apply (metis "1"(7))
           apply (metis "1"(8))
          by (metis m_lt_b)
              
        thus ?thesis using m_real_eq
          by metis
      qed

      have LHS_rewrite:
        "dsc_main_int P ((a,b) # todo) acc =
         dsc_main_int P todo
           (map real_to_rat_pair (rev (dsc p ?m_real b' P') @ rev (dsc p a' ?m_real P') @ ?mid_real) @ acc)"
        using main_split stepL stepR mid_map by simp

      have RHS_rewrite:
        "dsc_main_int P todo (map real_to_rat_pair (rev (dsc p a' b' P')) @ acc) =
         dsc_main_int P todo
           (map real_to_rat_pair (rev (dsc p ?m_real b' P') @ rev (dsc p a' ?m_real P') @ ?mid_real) @ acc)"
        using dsc_split by simp

      show ?thesis
        using LHS_rewrite RHS_rewrite by simp
    qed
  qed
qed

lemma dsc_int_eq_dsc:
  assumes dom: "dsc_dom (p, of_rat a, of_rat b, map_poly of_int P :: real poly)"
    and pdeg: "p = degree P"
    and P0: "P \<noteq> 0"
    and ab: "a < b"
  shows "rev (dsc_int a b P) = map real_to_rat_pair (dsc p (of_rat a) (of_rat b) (map_poly of_int P))"
proof -
  have tr: "dsc_int a b P = map real_to_rat_pair (rev (dsc p (of_rat a) (of_rat b) (map_poly of_int P)))"
    unfolding dsc_int_def
    using dsc_main_int_sim_aux[OF dom refl refl refl pdeg P0 ab, of "[]" "[]"]
    by (simp add: dsc_main_int.simps)
  thus ?thesis by (simp add: rev_map)
qed

lemma try_blocks_int_Some_iff:
  assumes "a < b" and "P \<noteq> 0" and "N > 0" and "p = degree (map_poly of_int P :: real poly)"
  shows "(try_blocks_int a b N P v = Some I_rat) \<longleftrightarrow>
         (try_blocks p (of_rat a) (of_rat b) N (map_poly of_int P :: real poly) (int v) = Some (of_rat (fst I_rat), of_rat (snd I_rat)))"
proof -
  have "(try_blocks_int a b N P v = Some I_rat) \<longleftrightarrow> (try_blocks_sc (of_rat a) (of_rat b) N (map_poly of_int P :: real poly) (int v) = Some (of_rat (fst I_rat), of_rat (snd I_rat)))"
    using try_blocks_int_eq_sc[OF assms(1-3)]
    by (smt (verit) Ratreal_def assms(1,2,3)
        descartes_roots_test_sc_of_int divide_pos_pos of_nat_0_less_iff
        of_nat_eq_iff of_rat_diff of_rat_divide of_rat_hom.hom_of_nat
        of_rat_less option.distinct(2) option.inject real_plus_code
        real_to_rat_pair_of_rat split_pairs try_blocks_int_def
        try_blocks_sc_def)
  thus ?thesis using try_block_sc_eq[OF assms(4)] by simp
qed

lemma try_newton_int_Some_iff:
  assumes "a < b" and "P \<noteq> 0" and "N > 0" and "p = degree (map_poly of_int P :: real poly)"
  shows "(try_newton_int a b N P v = Some I_rat) \<longleftrightarrow>
         (try_newton p (of_rat a) (of_rat b) N (map_poly of_int P :: real poly) (int v) = Some (of_rat (fst I_rat), of_rat (snd I_rat)))"
proof -
  let ?P_real = "map_poly of_int P :: real poly"
  
  have I_ord: "\<And>lam. fst (snap_window_rat a b N lam) < snd (snap_window_rat a b N lam)"
  proof -
    fix lam
    have ab_real: "(of_rat a :: real) < of_rat b" 
      using assms(1) by (simp add: of_rat_less)
    have "(of_rat (snd (snap_window_rat a b N lam)) :: real) - of_rat (fst (snap_window_rat a b N lam)) = 
          snd (snap_window (of_rat a) (of_rat b) N lam) - fst (snap_window (of_rat a) (of_rat b) N lam)"
      by (simp add: snap_window_rat_eq)
    also have "\<dots> = (of_rat b - of_rat a :: real) / of_nat N"
      using snap_window_width[OF ab_real assms(3)] by simp
    also have "\<dots> > 0"
      using ab_real assms(3) by simp
    finally show "fst (snap_window_rat a b N lam) < snd (snap_window_rat a b N lam)"
      by (metis diff_gt_0_iff_gt of_rat_less)
  qed

  have v_eq: "\<And>lam. (descartes_list_int (fst (snap_window_rat a b N lam)) (snd (snap_window_rat a b N lam)) (coeffs P) = v) \<longleftrightarrow>
                    (Bernstein_changes p (of_rat (fst (snap_window_rat a b N lam))) (of_rat (snd (snap_window_rat a b N lam))) ?P_real = int v)"
  proof -
    fix lam
    let ?l_rat = "fst (snap_window_rat a b N lam)"
    let ?r_rat = "snd (snap_window_rat a b N lam)"
    have real_lt: "of_rat ?l_rat < (of_rat ?r_rat :: real)" 
      using I_ord by (simp add: of_rat_less)
    have P_real_neq: "?P_real \<noteq> 0" using assms(2) by simp
    
    have "int (descartes_list_int ?l_rat ?r_rat (coeffs P)) = descartes_roots_test_sc (of_rat ?l_rat) (of_rat ?r_rat) ?P_real"
      using descartes_roots_test_sc_of_int[OF I_ord assms(2)] by simp
    also have "\<dots> = Bernstein_changes p (of_rat ?l_rat) (of_rat ?r_rat) ?P_real"
      using descartes_roots_test_sc_eq_Bernstein_changes assms(4) by blast
    finally show "(descartes_list_int ?l_rat ?r_rat (coeffs P) = v) \<longleftrightarrow> 
                  (Bernstein_changes p (of_rat ?l_rat) (of_rat ?r_rat) ?P_real = int v)"
      by linarith
  qed

  show ?thesis
    unfolding try_newton_int_def try_newton_def Let_def
    using v_eq snap_window_rat_eq[symmetric]
    by (smt (verit) fst_conv newton_at_def option.simps(1,3,4,5)
        real_to_rat_pair_of_rat snd_conv
        surjective_pairing)
qed

lemma N_of_ge_2: "N_of e \<ge> 2"
  unfolding N_of_def
  by (simp add: self_le_power)

lemma newdsc_main_int_sim_aux:
  assumes "newdsc_dom (p, a', b', N_of e, P')"
    and "a' = of_rat a"
    and "b' = of_rat b"
    and "P' = map_poly of_int P"
    and "p = degree P"
    and "P \<noteq> 0"
    and "a < b"
  shows
    "newdsc_main_int P ((a,b,e) # todo) acc =
     newdsc_main_int P todo (map real_to_rat_pair (rev (newdsc p a' b' (N_of e) P')) @ acc)"
using assms
proof (induction p a' b' "N_of e" P' arbitrary: a b e todo acc rule: newdsc.pinduct)
  case (1 p a' b' P' e a b todo acc)
  let ?P_real = "map_poly of_int P :: real poly"
  let ?v = "Bernstein_changes p (of_rat a) (of_rat b) ?P_real"

  have deg_p: "degree ?P_real = p"
    using "1.prems" by simp

  have v_eq: "int (descartes_list_int a b (coeffs P)) = ?v"
    using descartes_roots_test_sc_of_int[OF \<open>a < b\<close> \<open>P \<noteq> 0\<close>]
    by (simp add: descartes_roots_test_sc_eq_Bernstein_changes deg_p "1.prems")

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have nd0: "newdsc p a' b' (N_of e) P' = []"
      using "1.hyps" "1.prems" v0 newdsc.psimps by fastforce
    show ?thesis
      using nd0 newdsc_main_int.simps Let_def v0 v_eq "1.prems" by auto
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have nd1: "newdsc p a' b' (N_of e) P' = [(a',b')]"
        using "1.hyps" "1.prems" v1 v0 newdsc.psimps by fastforce
      show ?thesis
        using nd1 newdsc_main_int.simps Let_def v0 v1 v_eq "1.prems" by auto
    next
      case v1: False
      show ?thesis
      proof (cases "try_blocks_int a b (N_of e) P (nat ?v)")
        case (Some I_rat)
        let ?I_real = "(real_of_rat (fst I_rat), of_rat (snd I_rat))"
        have Npos: "N_of e > 0" using N_of_ge_2
          by (metis N_of_ge_2 bot_nat_0.not_eq_extremum not_le pos2)
        have TB_real: "try_blocks p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = Some ?I_real"
          using try_blocks_int_Some_iff Some "1.prems" Npos v0 v_eq by auto

        have nd_block:
          "newdsc p a' b' (N_of e) P' = newdsc p (fst ?I_real) (snd ?I_real) (Nq (N_of e)) P'"
          using "1.hyps" "1.prems" v0 v1 TB_real newdsc.psimps
          by fastforce

        have main_block:
          "newdsc_main_int P ((a,b,e) # todo) acc =
           newdsc_main_int P ((fst I_rat, snd I_rat, e + 1) # todo) acc"
        proof -
          let ?v_nat = "descartes_list_int a b (coeffs P)"
          have v_nat_eq: "?v_nat = nat ?v" using v_eq by linarith
          have v_neq_0: "?v_nat \<noteq> 0" using v0 v_eq by auto
          have v_neq_1: "?v_nat \<noteq> 1" using v1 v_eq by auto
          show ?thesis
            apply (subst newdsc_main_int.simps)
            using v_neq_0 v_neq_1 Some v_nat_eq
            by (auto simp add: Let_def)
        qed

        have ab_real: "((of_rat a)::real) < of_rat b" using \<open>a < b\<close>
          by (metis "1"(11) of_rat_less)
        have "fst ?I_real < snd ?I_real"
        proof -
          have N2: "N_of e \<ge> 2" using N_of_ge_2 by simp
          from try_blocks_Some_fst_lt_snd[OF TB_real ab_real N2]
          show ?thesis by simp
        qed
        hence rat_lt: "fst I_rat < snd I_rat" 
          using of_rat_less by auto

        have stepI:
          "newdsc_main_int P ((fst I_rat, snd I_rat, e + 1) # todo) acc =
           newdsc_main_int P todo (map real_to_rat_pair (rev (newdsc p (fst ?I_real) (snd ?I_real) (N_of (e + 1)) P')) @ acc)"
        proof -
          have "newdsc_main_int P ((fst I_rat, snd I_rat, e + 1) # todo) acc =
                newdsc_main_int P todo (map real_to_rat_pair (rev (newdsc p (real_of_rat (fst I_rat)) (real_of_rat (snd I_rat)) (N_of (e + 1)) P')) @ acc)"
            using "1"(10,5,9) "1.prems"(1,2,3) N_of_Nq TB_real rat_lt v0 v1
            by force
          thus ?thesis by simp
        qed

        show ?thesis
          using main_block stepI nd_block N_of_Nq "1.prems" by simp
      next
        case TB0_rat: None
        have Npos: "N_of e > 0"
          by (metis N_of_ge_2 bot_nat_0.not_eq_extremum not_le pos2)
        have TB0: "try_blocks p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = None"
        proof -
          have "int (nat ?v) = ?v" using v_eq by linarith
          moreover have "try_blocks_sc (of_rat a) (of_rat b) (N_of e) ?P_real (int (nat ?v)) = 
                         try_blocks p (of_rat a) (of_rat b) (N_of e) ?P_real (int (nat ?v))"
            using try_block_sc_eq[OF deg_p[symmetric]] by simp
          moreover have "(try_blocks_int a b (N_of e) P (nat ?v) = None) = 
                         (try_blocks_sc (of_rat a) (of_rat b) (N_of e) ?P_real (int (nat ?v)) = None)"
            using try_blocks_int_eq_sc[OF \<open>a < b\<close> \<open>P \<noteq> 0\<close> Npos, of "nat ?v"] 
            by (auto split: option.splits)
          ultimately show ?thesis
            using TB0_rat by simp
        qed

        show ?thesis
        proof (cases "try_newton_int a b (N_of e) P (nat ?v)")
          case (Some I_rat)
          let ?I_real = "(real_of_rat (fst I_rat), real_of_rat (snd I_rat))"
          have TN_real: "try_newton p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = Some ?I_real"
            using try_newton_int_Some_iff Some "1.prems" Npos v0 v_eq by auto

          have nd_newton:
            "newdsc p a' b' (N_of e) P' = newdsc p (fst ?I_real) (snd ?I_real) (Nq (N_of e)) P'"
            using "1.hyps" "1.prems" v0 v1 TB0 TN_real newdsc.psimps
            by (smt (verit, best) fst_conv option.case(1,2) snd_conv)

          have main_newton:
            "newdsc_main_int P ((a,b,e) # todo) acc =
             newdsc_main_int P ((fst I_rat, snd I_rat, e + 1) # todo) acc"
          proof -
            let ?v_nat = "descartes_list_int a b (coeffs P)"
            have v_nat_eq: "?v_nat = nat ?v" using v_eq by linarith
            have v_neq_0: "?v_nat \<noteq> 0" using v0 v_eq by auto
            have v_neq_1: "?v_nat \<noteq> 1" using v1 v_eq by auto
            show ?thesis
              apply (subst newdsc_main_int.simps)
              using v_neq_0 v_neq_1 TB0_rat Some v_nat_eq
              by (auto simp add: Let_def)
          qed

          have ab_real: "((of_rat a)::real) < of_rat b" using \<open>a < b\<close>
            by (metis "1"(11) of_rat_less)
          
          have "fst ?I_real < snd ?I_real"
          proof -
            have N2: "N_of e \<ge> 2" using N_of_ge_2 by simp
            from try_newton_Some_fst_lt_snd[OF TN_real ab_real N2]
            show ?thesis by simp
          qed
          hence rat_lt: "fst I_rat < snd I_rat" 
            using of_rat_less by auto

          have stepI:
            "newdsc_main_int P ((fst I_rat, snd I_rat, e + 1) # todo) acc =
             newdsc_main_int P todo (map real_to_rat_pair (rev (newdsc p (fst ?I_real) (snd ?I_real) (N_of (e + 1)) P')) @ acc)"
          proof -
            have "newdsc_main_int P ((fst I_rat, snd I_rat, e + 1) # todo) acc =
                  newdsc_main_int P todo (map real_to_rat_pair (rev (newdsc p (real_of_rat (fst I_rat)) (real_of_rat (snd I_rat)) (N_of (e + 1)) P')) @ acc)"
              using  "1.prems"(1,2,3) N_of_Nq TB0 TN_real rat_lt v0 v1
              by (simp add: "1"(10,9) "1.hyps"(4) split_pairs2)
            thus ?thesis by simp
          qed

          show ?thesis
            using main_newton stepI nd_newton N_of_Nq "1.prems" by simp
        next
          case TN0_rat: None
          have Npos: "N_of e > 0"
            by (metis N_of_ge_2 bot_nat_0.not_eq_extremum not_le pos2)
            
          have TN0: "try_newton p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = None"
          proof -
            have "int (nat ?v) = ?v" using v_eq by linarith
            moreover have "try_newton_sc (of_rat a) (of_rat b) (N_of e) ?P_real (int (nat ?v)) = 
                           try_newton p (of_rat a) (of_rat b) (N_of e) ?P_real (int (nat ?v))"
              using try_newton_sc_eq[OF deg_p[symmetric]] by simp
            moreover have "(try_newton_int a b (N_of e) P (nat ?v) = None) = 
                           (try_newton_sc (of_rat a) (of_rat b) (N_of e) ?P_real (int (nat ?v)) = None)"
              using try_newton_int_eq_sc[OF \<open>a < b\<close> \<open>P \<noteq> 0\<close> Npos, of "nat ?v"] 
              by (auto split: option.splits)
            ultimately show ?thesis
              using TN0_rat by simp
          qed

          define m where "m = (a + b) / 2"
          define e' where "e' = max 1 (e - 1)"
          let ?m_real = "(of_rat a + of_rat b) / 2"
          have m_real_eq: "of_rat m = ?m_real" by (simp add: m_def of_rat_add of_rat_divide)

          let ?mid_rat = "(if poly (map_poly of_int P :: rat poly) m = 0 then [(m,m)] else [])"
          let ?mid_real = "(if poly ?P_real ?m_real = 0 then [(?m_real,?m_real)] else [])"

          have mid_map: "map real_to_rat_pair ?mid_real = ?mid_rat"
            using poly_rat_eq_poly_real m_real_eq 
            by (smt (verit, ccfv_threshold) list.map(1,2) real_to_rat_pair_of_rat)

          have nd_split:
            "newdsc p a' b' (N_of e) P' = ?mid_real @ newdsc p a' ?m_real (Nlin (N_of e)) P' @ newdsc p ?m_real b' (Nlin (N_of e)) P'"
            using "1.hyps" "1.prems" newdsc.psimps Let_def v0 v1 TB0 TN0 m_real_eq[symmetric]
            by (smt (verit, ccfv_SIG) option.case(1))

          have mid_acc_eq:
            "(if poly (map_poly of_int P :: rat poly) m = 0 then (m,m) # acc else acc) = ?mid_rat @ acc"
            by auto

          have main_split:
            "newdsc_main_int P ((a,b,e) # todo) acc =
             newdsc_main_int P ((a,m,e') # (m,b,e') # todo) (?mid_rat @ acc)"
          proof -
            let ?v_nat = "descartes_list_int a b (coeffs P)"
            have v_nat_eq: "?v_nat = nat ?v" using v_eq by linarith
            have v_neq_0: "?v_nat \<noteq> 0" using v0 v_eq by auto
            have v_neq_1: "?v_nat \<noteq> 1" using v1 v_eq by auto
            have tmp:
              "newdsc_main_int P ((a,b,e) # todo) acc =
               newdsc_main_int P ((a,m,e') # (m,b,e') # todo)
                 (if poly (map_poly of_int P :: rat poly) m = 0 then (m,m) # acc else acc)"
              apply (subst newdsc_main_int.simps)
              using v_neq_0 v_neq_1 TB0_rat TN0_rat m_def e'_def v_nat_eq
              by (smt (verit, ccfv_threshold) list.case(2) option.simps(4) prod.simps(2))
            show ?thesis
              using tmp by (simp add: mid_acc_eq)
          qed

          have a_lt_m: "a < m" using \<open>a < b\<close> m_def by auto
          have m_lt_b: "m < b" using \<open>a < b\<close> m_def by auto

          have stepL:
            "newdsc_main_int P ((a,m,e') # (m,b,e') # todo) (?mid_rat @ acc) =
             newdsc_main_int P ((m,b,e') # todo)
               (map real_to_rat_pair (rev (newdsc p a' ?m_real (N_of e') P')) @ (?mid_rat @ acc))"
          proof -
            have "newdsc_main_int P ((a,m,e') # (m,b,e') # todo) (?mid_rat @ acc) =
                  newdsc_main_int P ((m,b,e') # todo)
                    (map real_to_rat_pair (rev (newdsc p a' (of_rat m) (N_of e') P')) @ (?mid_rat @ acc))"
              using  "1" v0 v1 TB0 TN0 \<open>a' = of_rat a\<close> m_real_eq \<open>P' = map_poly of_int P\<close> \<open>p = degree P\<close> \<open>P \<noteq> 0\<close> a_lt_m N_of_Nlin e'_def "1.prems"(1,2,3)
              by metis
            thus ?thesis using m_real_eq by metis
          qed

          have stepR:
            "newdsc_main_int P ((m,b,e') # todo) (map real_to_rat_pair (rev (newdsc p a' ?m_real (N_of e') P')) @ (?mid_rat @ acc)) =
             newdsc_main_int P todo
               (map real_to_rat_pair (rev (newdsc p ?m_real b' (N_of e') P')) @ (map real_to_rat_pair (rev (newdsc p a' ?m_real (N_of e') P')) @ (?mid_rat @ acc)))"
          proof -
            have "newdsc_main_int P ((m,b,e') # todo) (map real_to_rat_pair (rev (newdsc p a' ?m_real (N_of e') P')) @ (?mid_rat @ acc)) =
                  newdsc_main_int P todo
                    (map real_to_rat_pair (rev (newdsc p (of_rat m) b' (N_of e') P')) @ (map real_to_rat_pair (rev (newdsc p a' ?m_real (N_of e') P')) @ (?mid_rat @ acc)))"
              using "1" v0 v1 TB0 TN0 m_real_eq \<open>b' = of_rat b\<close> \<open>P' = map_poly of_int P\<close> \<open>p = degree P\<close> \<open>P \<noteq> 0\<close> m_lt_b N_of_Nlin e'_def "1.prems"(1,2,3)
              by metis
            thus ?thesis using m_real_eq by metis
          qed

          have LHS_rewrite:
            "newdsc_main_int P ((a,b,e) # todo) acc =
             newdsc_main_int P todo
               (map real_to_rat_pair (rev (newdsc p ?m_real b' (N_of e') P') @ rev (newdsc p a' ?m_real (N_of e') P') @ ?mid_real) @ acc)"
            using main_split stepL stepR mid_map by simp

          have RHS_rewrite:
            "newdsc_main_int P todo (map real_to_rat_pair (rev (newdsc p a' b' (N_of e) P')) @ acc) =
             newdsc_main_int P todo
               (map real_to_rat_pair (rev (newdsc p ?m_real b' (N_of e') P') @ rev (newdsc p a' ?m_real (N_of e') P') @ ?mid_real) @ acc)"
            using nd_split N_of_Nlin e'_def by simp

          show ?thesis
            using LHS_rewrite RHS_rewrite by simp
        qed
      qed
    qed
  qed
qed

lemma newdsc_int_eq_newdsc:
  assumes dom: "newdsc_dom (p, of_rat a, of_rat b, N_of e, map_poly of_int P :: real poly)"
    and pdeg: "p = degree P"
    and P0: "P \<noteq> 0"
    and ab: "a < b"
  shows "rev (newdsc_int a b e P) = map real_to_rat_pair (newdsc p (of_rat a) (of_rat b) (N_of e) (map_poly of_int P))"
proof -
  have tr: "newdsc_int a b e P = map real_to_rat_pair (rev (newdsc p (of_rat a) (of_rat b) (N_of e) (map_poly of_int P)))"
    unfolding newdsc_int_def
    using newdsc_main_int_sim_aux[OF dom refl refl refl pdeg P0 ab, of "[]" "[]"]
    by (simp add: newdsc_main_int.simps)
  thus ?thesis by (simp add: rev_map)
qed

end