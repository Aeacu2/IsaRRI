theory Dsc_Rat

  imports Dsc_Exec

begin

text \<open>The rational-coefficient layer: \<open>of_rat\<close> transport of the real-poly specs.
  Layer: FUNCTIONAL SPEC.
  Main exports: the \<open>fcompose\<close>/\<open>of_rat\<close> commutation lemmas the integer layer is built on.\<close>

lemma fcompose_fold_helper:
  "foldr (\<lambda>a (c, d). (d * [:of_rat a:] + map_poly of_rat q * c, map_poly of_rat r * d)) 
         (map of_rat xs) (map_poly of_rat c0, map_poly of_rat d0) =
   (map_poly of_rat (fst (foldr (\<lambda>a (c, d). (d * [:a:] + q * c, r * d)) xs (c0, d0))),
    map_poly of_rat (snd (foldr (\<lambda>a (c, d). (d * [:a:] + q * c, r * d)) xs (c0, d0))))"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  obtain C D where REC: "foldr (\<lambda>a (c, d). (d * [:a:] + q * c, r * d)) xs (c0, d0) = (C, D)"
    by fastforce

  thm Cons.IH

  have add_hom: "\<And>A B. map_poly of_rat (A + B) = map_poly of_rat A + map_poly of_rat B"
    by (intro map_poly_add) (auto simp: of_rat_add)

  have mult_hom: "\<And>A B. map_poly of_rat (A * B) = map_poly of_rat A * map_poly of_rat B"
    by (rule poly_eqI) (simp add: coeff_map_poly coeff_mult of_rat_sum of_rat_mult)

  have smult_hom: "\<And>x P. Polynomial.smult (of_rat x) (map_poly of_rat P) = map_poly of_rat (Polynomial.smult x P)"
    by (rule poly_eqI) (simp add: coeff_map_poly of_rat_mult)

  have step_hom: "\<And>C D. (Polynomial.smult (of_rat a) (map_poly of_rat D) + map_poly of_rat q * map_poly of_rat C, map_poly of_rat r * map_poly of_rat D) =
                         (map_poly of_rat (Polynomial.smult a D + q * C), map_poly of_rat (r * D))"
    unfolding smult_hom mult_hom add_hom by simp

  show ?case
    using Cons.IH REC
    by (simp add: split_def step_hom)
qed

lemma fcompose_of_rat:
  "map_poly of_rat (fcompose p q r) = 
   fcompose (map_poly of_rat p) (map_poly of_rat q) (map_poly of_rat r)"
proof -
  have "fcompose (map_poly of_rat p) (map_poly of_rat q) (map_poly of_rat r) =
        fst (foldr (\<lambda>a (c, d). (Polynomial.smult a d + map_poly of_rat q * c, map_poly of_rat r * d))
             (coeffs (map_poly of_rat p)) (0, 1))"
    unfolding fcompose_def fold_coeffs_def by simp
  also have "... = fst (foldr (\<lambda>a (c, d). (Polynomial.smult a d + map_poly of_rat q * c, map_poly of_rat r * d))
                        (map of_rat (coeffs p)) (map_poly of_rat 0, map_poly of_rat 1))"
    by (simp add: coeffs_map_poly)
  also have "... = fst (foldr (\<lambda>a (c, d). (Polynomial.smult (of_rat a) d + map_poly of_rat q * c, map_poly of_rat r * d))
                        (coeffs p) (map_poly of_rat 0, map_poly of_rat 1))"
    using split_def comp_def
    by (metis (no_types, lifting) ext foldr_map)
  also have "... = fst (map_poly of_rat (fst (foldr (\<lambda>a (c, d). (Polynomial.smult a d + q * c, r * d)) (coeffs p) (0, 1))),
                        map_poly of_rat (snd (foldr (\<lambda>a (c, d). (Polynomial.smult a d + q * c, r * d)) (coeffs p) (0, 1))))"
  proof -
    have "foldr (\<lambda>a (c, d). (Polynomial.smult (of_rat a) d + map_poly of_rat q * c, map_poly of_rat r * d)) (coeffs p) (0, 1) =
          (map_poly of_rat (fst (foldr (\<lambda>a (c, d). (Polynomial.smult a d + q * c, r * d)) (coeffs p) (0, 1))),
           map_poly of_rat (snd (foldr (\<lambda>a (c, d). (Polynomial.smult a d + q * c, r * d)) (coeffs p) (0, 1))))"
      using fcompose_fold_helper[of q r "coeffs p" 0 1] by simp
    then have "fst (foldr (\<lambda>a (c, d). (Polynomial.smult (of_rat a) d + map_poly of_rat q * c, map_poly of_rat r * d)) (coeffs p) (0, 1)) =
               fst (map_poly of_rat (fst (foldr (\<lambda>a (c, d). (Polynomial.smult a d + q * c, r * d)) (coeffs p) (0, 1))),
                    map_poly of_rat (snd (foldr (\<lambda>a (c, d). (Polynomial.smult a d + q * c, r * d)) (coeffs p) (0, 1))))"
      by (metis (lifting) ext fst_conv)
    then show ?thesis
      by simp
  qed
  finally show ?thesis
    by (metis (lifting) fst_conv id_apply of_rat_eq_id
        of_rat_hom.coeff_map_poly_hom poly_eqI)
qed

lemma sign_changes_map_of_rat:
  "Descartes_Sign_Rule.sign_changes (map (of_rat:: rat \<Rightarrow> real) xs) = Descartes_Sign_Rule.sign_changes xs"
proof -
  have filt_hom: "filter (\<lambda>x. x \<noteq> 0) (map (sgn \<circ> (of_rat:: rat \<Rightarrow> real)) xs) = map of_rat (filter (\<lambda>x. x \<noteq> 0) (map sgn xs))"
  proof (induction xs)
    case Nil
    show ?case by simp
  next
    case (Cons x xs)
    then show ?case
      using real_of_rat_sgn by force
  qed

  have rem_hom: "\<And>ys. remdups_adj (map (of_rat:: rat \<Rightarrow> real) ys) = map of_rat (remdups_adj ys)"
  proof -
    fix ys show "remdups_adj (map of_rat ys) = map of_rat (remdups_adj ys)"
      by (induction ys rule: remdups_adj.induct) auto
  qed

  have "length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map sgn (map (of_rat:: rat \<Rightarrow> real) xs)))) = 
        length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map (sgn \<circ> (of_rat:: rat \<Rightarrow> real)) xs)))"
    by force
  also have "... = length (remdups_adj (map (of_rat:: rat \<Rightarrow> real) (filter (\<lambda>x. x \<noteq> 0) (map sgn xs))))"
    by (simp only: filt_hom)
  also have "... = length (map (of_rat:: rat \<Rightarrow> real) (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map sgn xs))))"
    by (simp only: rem_hom)
  also have "... = length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map sgn xs)))"
    by simp
  finally show ?thesis
    unfolding Descartes_Sign_Rule.sign_changes_def by simp
qed

definition descartes_roots_test_sc_rat :: "rat \<Rightarrow> rat \<Rightarrow> rat poly \<Rightarrow> nat" where
  "descartes_roots_test_sc_rat a b P = Descartes_Sign_Rule.sign_changes (coeffs (fcompose P [:a, b:] [:1, 1:]))"

lemma descartes_roots_test_sc_rat_refine:
  "descartes_roots_test_sc_rat a b P = descartes_roots_test_sc (of_rat a) (of_rat b) (map_poly of_rat P)"
proof -
  have hom: "map_poly of_rat (fcompose P [:a, b:] [:1, 1:]) = 
             fcompose (map_poly of_rat P) [:of_rat a, of_rat b:] [:1, 1:]"
    using fcompose_of_rat[of P "[:a, b:]" "[:1, 1:]"] 
    by (simp add: of_rat_hom.map_poly_pCons_hom)
  
  have "coeffs (map_poly of_rat (fcompose P [:a, b:] [:1, 1:])) = 
        map of_rat (coeffs (fcompose P [:a, b:] [:1, 1:]))"
    by (simp add: coeffs_map_poly)
  then have "Descartes_Sign_Rule.sign_changes (map (of_rat:: rat \<Rightarrow> real) (coeffs (fcompose P [:a, b:] [:1, 1:]))) =
             Descartes_Sign_Rule.sign_changes (coeffs (map_poly (of_rat:: rat \<Rightarrow> real)  (fcompose P [:a, b:] [:1, 1:])))"
    by simp
  also have "... = Descartes_Sign_Rule.sign_changes (coeffs (fcompose (map_poly (of_rat:: rat \<Rightarrow> real)  P) [:of_rat a, of_rat b:] [:1, 1:]))"
    by (metis hom)
  also have "Descartes_Sign_Rule.sign_changes (map (of_rat:: rat \<Rightarrow> real)  (coeffs (fcompose P [:a, b:] [:1, 1:]))) =
             Descartes_Sign_Rule.sign_changes (coeffs (fcompose P [:a, b:] [:1, 1:]))"
    using sign_changes_map_of_rat by simp
  finally show ?thesis
    unfolding descartes_roots_test_sc_rat_def descartes_roots_test_sc_def
    by simp
qed

end