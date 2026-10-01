theory IICF_Shared_Lists2
imports Isabelle_LLVM.IICF IICF_More_Array
begin


  lemma int_snat_eq_sint: "snat_invar i \<Longrightarrow> int (snat i) = sint i"  
    by (simp add: cnv_snat_to_uint(2) snat_eq_unat_aux2)
      
    
  lemma RETURN_le_ASSUME_iff: "RETURN x \<le> ASSUME P \<longleftrightarrow> P"
    by (simp add: refine_pw_simps pw_le_iff)

  lemma RETURN_le_ASSERT_iff: "RETURN x \<le> ASSERT P"
    by (simp add: refine_pw_simps pw_le_iff)
    
        
  (* Transfer between concrete euqalities (cp) and abstract level.
    While normal ASSERT/ASSUME is also visible during sepref, these variants use the 
    concrete equality mechanism of sepref
  *)
  definition "ASSERT_conc P x \<equiv> doN {ASSERT (P x); RETURN x}" \<comment> \<open>The parameter is passed through to be constrained\<close>
  definition "ASSUME_conc P x \<equiv> ASSUME (P x)"  
    
  context fixes P :: "'a \<Rightarrow> bool"
  begin
    sepref_register "ASSERT_conc P" "ASSUME_conc P"
  end

  (* Template rules to instantiate P *)
  (* ASSERT_conc: show that concrete precondition, assertion for parameters, and abstract condition imply concrete postcondition *)
  lemma ASSERT_conc_hn_tmpl:
    assumes [simp]: "\<And>x xi. \<lbrakk> CPre xi; pure_part (A x xi); P x \<rbrakk> \<Longrightarrow> CPost xi xi"
    shows "(Mreturn, PR_CONST (ASSERT_conc P)) \<in> [CPre]\<^sub>c A\<^sup>d \<rightarrow> A [CPost]\<^sub>c"
    apply sepref_to_hoare
    unfolding ASSERT_conc_def
    apply (simp add: RETURN_le_ASSERT_iff refine_pw_simps)
    apply (rule htriple_pure_preI)
    by vcg

    
  (* ASSUME_conc: show that concrete precondition and assertion for parameters imply abstract condition *)
  lemma ASSUME_conc_hn_tmpl:
    assumes [simp]: "\<And>x xi. CP xi \<Longrightarrow> pure_part (A x xi) \<Longrightarrow> P x"
    shows "(\<lambda>_. Mreturn (), PR_CONST (ASSUME_conc P)) \<in> [CP]\<^sub>c A\<^sup>k \<rightarrow> unit_assn [\<lambda>_ _. True]\<^sub>c"
    apply sepref_to_hoare
    unfolding ASSUME_conc_def
    apply (simp add: RETURN_le_ASSUME_iff)
    apply (rule htriple_pure_preI)
    by vcg

  (* Instantiation for snat-equality *)      
  lemma snat_inj_iff: "snat_invar a \<Longrightarrow> snat_invar b \<Longrightarrow> snat a = snat b \<longleftrightarrow> a=b"
    by (metis int_snat_eq_sint word_eq_iff_signed)

  lemma ASSUME_conc_snat_eq[sepref_fr_rules]: 
    shows "(\<lambda>_. Mreturn (), PR_CONST (ASSUME_conc (\<lambda>(i,j). i=j))) \<in> [\<lambda>iji. CP_cond (fst iji = snd iji)]\<^sub>c (snat_assn \<times>\<^sub>a snat_assn)\<^sup>k \<rightarrow> unit_assn [\<lambda>_ _. True]\<^sub>c"
    apply (rule ASSUME_conc_hn_tmpl)
    by (auto simp: snat_rel_def snat.rel_def in_br_conv CP_cond_def)

  lemma fold_ASSUME_conc_eq: "ASSUME (a=b) = ASSUME_conc (\<lambda>(i,j). i=j) (a,b)"
    unfolding ASSUME_conc_def by simp

  lemma ASSUME_conc_snat_eq0[sepref_fr_rules]: 
    shows "(\<lambda>_. Mreturn (), PR_CONST (ASSUME_conc (\<lambda>i. i=0))) \<in> [\<lambda>i. CP_cond (i=0)]\<^sub>c (snat_assn)\<^sup>k \<rightarrow> unit_assn [\<lambda>_ _. True]\<^sub>c"
    apply (rule ASSUME_conc_hn_tmpl)
    by (auto simp: snat_rel_def snat.rel_def in_br_conv CP_cond_def)

  lemma fold_ASSUME_conc_eq0: "ASSUME (a=0) = ASSUME_conc (\<lambda>i. i=0) a"
    unfolding ASSUME_conc_def by simp
    

  lemma ASSERT_conc_snat_eq[sepref_fr_rules]: 
    shows "(Mreturn, PR_CONST (ASSERT_conc (\<lambda>(i,j). i=j))) 
      \<in> [\<lambda>_. True]\<^sub>c (snat_assn \<times>\<^sub>a snat_assn)\<^sup>d \<rightarrow> snat_assn \<times>\<^sub>a snat_assn [\<lambda>(ai,aj) (i,j). i=j \<and> j=aj]\<^sub>c"
    apply (rule ASSERT_conc_hn_tmpl)
    by (auto simp: snat_rel_def snat.rel_def in_br_conv CP_cond_def snat_inj_iff)

  (*lemma fold_ASSERT_conc_eq: "ASSERT (a=b) = ASSERT_conc (\<lambda>(i,j). i=j) (a,b)"
    unfolding ASSERT_conc_def by simp
  *)  

  
  lemma ASSERT_conc_snat_eq0[sepref_fr_rules]: 
    shows "(Mreturn, PR_CONST (ASSERT_conc (\<lambda>i. i=0))) \<in> [\<lambda>_. True]\<^sub>c snat_assn\<^sup>d \<rightarrow> snat_assn [\<lambda>_ i. i=0]\<^sub>c"
    apply (rule ASSERT_conc_hn_tmpl)
    apply (auto simp: snat_rel_def snat.rel_def in_br_conv CP_cond_def snat_inj_iff[OF _ snat_invar_0, simplified]) 
    done
    
  definition [simp]: "cp_snat0 TYPE('l::len2) \<equiv> 0"
  sepref_register "cp_snat0 TYPE(_)"
  
  lemmas fold_cp_snat0 = cp_snat0_def[symmetric]
  
  
  lemma cp_snat0_aux: "RETURN (cp_snat0 TYPE('l::len2)) = ASSERT_conc (\<lambda>i. i=0) (snat_const TYPE('l) 0)"
    unfolding ASSERT_conc_def
    by (simp)
  
  sepref_def cp_snat0_impl [llvm_inline,sepref_opt_simps] 
    is "uncurry0 (RETURN (PR_CONST (cp_snat0 TYPE('l::len2))))" :: "[\<lambda>_. True]\<^sub>c unit_assn\<^sup>k \<rightarrow> snat_assn' TYPE('l) [\<lambda>_ i. i=0]\<^sub>c" 
    unfolding cp_snat0_aux PR_CONST_def
    by sepref
    
    
    
    
    

  (*  
  lemma fold_ASSERT_conc_eq0: "ASSERT (a=0) = ASSERT_conc (\<lambda>i. i=0) a"
    unfolding ASSERT_conc_def by simp
  *)  
    
            

  lemma take_slice: "take i (Misc.slice l h xs) = Misc.slice l (min (l+i) h) xs"  
    unfolding Misc.slice_def min_def by simp

  lemma drop_slice: "drop i (Misc.slice l h xs) = Misc.slice (l+i) h xs"
    unfolding Misc.slice_def by (simp add: drop_take algebra_simps)
    
  lemma slice_len': "length (Misc.slice l h xs) = min (length xs) h - l"  
    by (simp add: Misc.slice_def)
    
    



  definition "sl2_indexes xs \<equiv> {i. i<length xs \<and> xs!i \<noteq> None }"

  definition "sl2_of_list = map Some"
  definition "list_of_sl2 = map the"
  
  definition "sl2_get xs i = (if i<length xs then the (xs!i) else undefined (i-length xs))"
  definition "sl2_put xs i x = xs[i:=Some x]"
  
  
  definition "sl2_restr s xs = map (\<lambda>i. if i\<in>s \<and> i<length xs then xs!i else None) [0..<length xs]"

  
  definition "mop_list_of_sl2 xs \<equiv> doN { ASSERT (sl2_indexes xs = {0..<length xs}); RETURN (list_of_sl2 xs) }"  
  
  (* Allows to drop None-suffix. *)
  definition "mop_list_of_sl2N n xs \<equiv> doN { 
    ASSERT(sl2_indexes xs = {0..<n} \<and> n\<noteq>0); 
    RETURN (list_of_sl2 (take n xs))
  }"
  
  
  (* Join *)
  fun sl2_join where
    "sl2_join [] ys = ys"
  | "sl2_join xs [] = xs"  
  | "sl2_join (Some x # xs) (None # ys) = Some x # sl2_join xs ys"
  | "sl2_join (None # xs) (Some y # ys) = Some y # sl2_join xs ys"
  | "sl2_join (_ # xs) (_ # ys) = None # sl2_join xs ys"
    
  lemma sl2_join_add_simps[simp]: "sl2_join xs [] = xs" by (cases xs) auto
    

  lemma sl2_indexes_of_list[simp]: "sl2_indexes (sl2_of_list xs) = {0..<length xs}"
    unfolding sl2_indexes_def sl2_of_list_def by auto
  
  lemma sl2_of_list_length[simp]: "length (sl2_of_list xs) = length xs"  
    unfolding sl2_of_list_def by auto
  
  lemma list_of_sl2_length[simp]: "length (list_of_sl2 xs) = length xs"  
    unfolding list_of_sl2_def by auto

    
  lemma mop_list_of_sl2_correct[refine_vcg]: "sl2_indexes xs = {0..<length xs} \<Longrightarrow> mop_list_of_sl2 xs \<le> SPEC (\<lambda>r. r = list_of_sl2 xs)"
    unfolding mop_list_of_sl2_def by auto

  lemma mop_list_of_sl2N_correct[refine_vcg]: "\<lbrakk>sl2_indexes xs = {0..<n}; n\<noteq>0\<rbrakk> \<Longrightarrow> mop_list_of_sl2N n xs \<le> SPEC (\<lambda>r. r = take n (list_of_sl2 xs))"
    unfolding list_of_sl2_def mop_list_of_sl2N_def
    apply refine_vcg
    by (auto simp: take_map)
          
  lemma sl2_get_of_list[simp]: "i<length xs \<Longrightarrow> sl2_get (sl2_of_list xs) i = xs!i"
    unfolding sl2_get_def sl2_of_list_def by simp

  lemma sl2_get_put[simp]: "i\<in>sl2_indexes xs \<Longrightarrow> sl2_get (sl2_put xs j v) i = (if i=j then v else sl2_get xs i)"  
    unfolding sl2_get_def sl2_indexes_def sl2_put_def
    by (auto)

  lemma sl2_put_put[simp]: "i\<in>sl2_indexes xs \<Longrightarrow> sl2_put (sl2_put xs i vv) i v = (sl2_put xs i v)"  
    unfolding sl2_get_def sl2_indexes_def sl2_put_def
    by (auto)
    
  lemma sl2_put_swap: "\<lbrakk>i\<in>sl2_indexes xs; j\<in>sl2_indexes xs; i\<noteq>j\<rbrakk> \<Longrightarrow> sl2_put (sl2_put xs i v\<^sub>1) j v\<^sub>2 = sl2_put (sl2_put xs j v\<^sub>2) i v\<^sub>1"  
    unfolding sl2_get_def sl2_indexes_def sl2_put_def
    by (auto simp: list_update_swap)
            
  lemma sl2_put_indexes[simp]: "i\<in>sl2_indexes xs \<Longrightarrow> sl2_indexes (sl2_put xs i v) = sl2_indexes xs"
    unfolding sl2_indexes_def sl2_put_def
    by (auto simp: nth_list_update)

  lemma sl2_put_length[simp]: "length (sl2_put xs i v) = length xs"
    unfolding sl2_put_def by auto
    
  lemma sl2_restr_indexes[simp]: "sl2_indexes (sl2_restr s xs) = s \<inter> sl2_indexes xs"  
    unfolding sl2_indexes_def sl2_restr_def
    by (auto split: if_splits)
    
  lemma sl2_restr_get[simp]: "i\<in>s \<inter> sl2_indexes xs \<Longrightarrow> sl2_get (sl2_restr s xs) i = sl2_get xs i"
    unfolding sl2_indexes_def sl2_restr_def sl2_get_def
    by (auto split: if_splits)

    
  lemma sl2_indexes_internal_simps1: 
    "sl2_indexes [] = {}" 
    by (auto simp: sl2_indexes_def) 
    
  lemma sl2_indexes_internal_simps2: "sl2_indexes (None#xs) = Suc`(sl2_indexes xs)"  
    unfolding sl2_indexes_def 
    apply (clarsimp simp: nth_Cons split: nat.splits; safe) 
    subgoal for i by (cases i) auto
    by auto
    
  lemma sl2_indexes_internal_simps3: "sl2_indexes (Some x#xs) = insert 0 (Suc`(sl2_indexes xs))"  
    unfolding sl2_indexes_def 
    apply (clarsimp simp: nth_Cons split: nat.splits; safe) 
    subgoal for i by (cases i) auto
    done
    
  lemmas sl2_indexes_internal_simps = sl2_indexes_internal_simps1 sl2_indexes_internal_simps2 sl2_indexes_internal_simps3  
    
  lemma sl2_get_internal_simps:
    "sl2_get (Some x#xs) 0 = x"
    "sl2_get (xx#xs) (Suc n) = sl2_get xs n"
    unfolding sl2_get_def by auto
  
    
  lemma sl2_join_indexes[simp]: "sl2_indexes xs\<^sub>1 \<inter> sl2_indexes xs\<^sub>2 = {} \<Longrightarrow> sl2_indexes (sl2_join xs\<^sub>1 xs\<^sub>2) = sl2_indexes xs\<^sub>1 \<union> sl2_indexes xs\<^sub>2"
    apply (induction xs\<^sub>1 xs\<^sub>2 rule: sl2_join.induct)
    apply (simp_all add: sl2_indexes_internal_simps) 
    apply blast+
    done

  lemma sl2_join_get1[simp]: "\<lbrakk>sl2_indexes xs\<^sub>1 \<inter> sl2_indexes xs\<^sub>2 = {}; i\<in>sl2_indexes xs\<^sub>1\<rbrakk> \<Longrightarrow> sl2_get (sl2_join xs\<^sub>1 xs\<^sub>2) i = sl2_get xs\<^sub>1 i"
    supply [simp] = sl2_indexes_internal_simps sl2_get_internal_simps
  proof (induction xs\<^sub>1 xs\<^sub>2 arbitrary: i rule: sl2_join.induct)
    case (1 ys)
    then show ?case by simp
  next
    case (2 v va)
    then show ?case by simp
  next
    case (3 x xs ys)
    then show ?case by (cases i) auto 
  next
    case (4 xs y ys)
    then show ?case by (cases i) auto
  next
    case ("5_1" xs ys)
    then show ?case by (cases i) auto
  next
    case ("5_2" va xs v ys)
    then show ?case by simp
  qed

  lemma sl2_join_get2[simp]: "\<lbrakk>sl2_indexes xs\<^sub>1 \<inter> sl2_indexes xs\<^sub>2 = {}; i\<in>sl2_indexes xs\<^sub>2\<rbrakk> \<Longrightarrow> sl2_get (sl2_join xs\<^sub>1 xs\<^sub>2) i = sl2_get xs\<^sub>2 i"
    supply [simp] = sl2_indexes_internal_simps sl2_get_internal_simps
  proof (induction xs\<^sub>1 xs\<^sub>2 arbitrary: i rule: sl2_join.induct)
    case (1 ys)
    then show ?case by simp
  next
    case (2 v va)
    then show ?case by simp
  next
    case (3 x xs ys)
    then show ?case by (cases i) auto 
  next
    case (4 xs y ys)
    then show ?case by (cases i) auto
  next
    case ("5_1" xs ys)
    then show ?case by (cases i) auto
  next
    case ("5_2" va xs v ys)
    then show ?case by simp
  qed

  definition "sl2_get_join_undef xs\<^sub>1 xs\<^sub>2 i \<equiv> sl2_get (sl2_join xs\<^sub>1 xs\<^sub>2) i"
  
  lemma sl2_get_join_iff: "sl2_indexes xs\<^sub>1 \<inter> sl2_indexes xs\<^sub>2 = {} \<Longrightarrow> sl2_get (sl2_join xs\<^sub>1 xs\<^sub>2) i = 
    (if i\<in>sl2_indexes xs\<^sub>1 then sl2_get xs\<^sub>1 i
    else if i\<in>sl2_indexes xs\<^sub>2 then sl2_get xs\<^sub>2 i
    else sl2_get_join_undef xs\<^sub>1 xs\<^sub>2 i)"
    unfolding sl2_get_join_undef_def by auto
  
  
  
  lemma sl2_eq_iff: "xs\<^sub>1=xs\<^sub>2 \<longleftrightarrow> (sl2_indexes xs\<^sub>1 = sl2_indexes xs\<^sub>2 \<and> length xs\<^sub>1 = length xs\<^sub>2 \<and> (\<forall>i\<in>sl2_indexes xs\<^sub>2. sl2_get xs\<^sub>1 i = sl2_get xs\<^sub>2 i))"
    apply (auto simp: list_eq_iff_nth_eq sl2_indexes_def)
    unfolding sl2_get_def
    apply (auto)
    by (smt (verit) mem_Collect_eq option.exhaust_sel option.simps(3))
  
  lemma sl2_join_length[simp]: "length (sl2_join xs\<^sub>1 xs\<^sub>2) = max (length xs\<^sub>1) (length xs\<^sub>2)"  
    apply (induction xs\<^sub>1 xs\<^sub>2 rule: sl2_join.induct)
    apply auto
    done
    
  lemma sl2_restr_length[simp]: "length (sl2_restr s xs) = length xs"  
    unfolding sl2_restr_def by auto
    
  lemma sl2_join_split[simp]: "sl2_join (sl2_restr s xs) (sl2_restr (- s) xs) = xs"
    apply (subst sl2_eq_iff; intro conjI ballI)
    subgoal by auto
    subgoal by (simp)
    subgoal for i by (cases "i\<in>s") auto
    done

  lemma nat_less_set_eq_all_conv: "{i::nat. i < n \<and> P i} = {0..<n} \<longleftrightarrow> (\<forall>i<n. P i)" by fastforce
  lemma nat_less_set_eq_all_conv': "l\<le>h \<Longrightarrow> h\<le>n \<Longrightarrow> {i::nat. i < n \<and> P i} = {l..<h} \<longleftrightarrow> (\<forall>i<l. \<not>P i) \<and> (\<forall>i\<in>{l..<h}. P i) \<and> (\<forall>i\<in>{h..<n}. \<not>P i)" 
    apply (safe)
    subgoal by (metis atLeastLessThan_iff dual_order.trans le_def mem_Collect_eq)
    apply blast
    subgoal apply clarsimp by (metis atLeastLessThan_iff le_def mem_Collect_eq)
    subgoal apply clarsimp  by (meson atLeastLessThan_iff leI)
    apply (simp; fail)
    apply blast
    done
    
    
    
  definition "sl2_split s xs \<equiv> (sl2_restr s xs, sl2_restr (-s) xs)"
  lemma sl2_split_eq_prod_conv[simp]: "sl2_split s xs = (xs\<^sub>1,xs\<^sub>2) \<longleftrightarrow> xs\<^sub>1 = sl2_restr s xs \<and> xs\<^sub>2 = sl2_restr (-s) xs"
    unfolding sl2_split_def by auto
  
   
    
  lemma list_of_sl2_inv[simp]: "sl2_indexes xs = {0..<length xs} \<Longrightarrow> sl2_of_list (list_of_sl2 xs) = xs"  
    unfolding sl2_indexes_def sl2_of_list_def list_of_sl2_def
    apply (clarsimp simp: nat_less_set_eq_all_conv)
    by (simp add: list_eq_iff_nth_eq)
    
  lemma sl2_of_list_inv[simp]: "list_of_sl2 (sl2_of_list xs) = xs"  
    unfolding sl2_indexes_def sl2_of_list_def list_of_sl2_def by simp
    

    
  (* More on sl2 *)

  (* list_of_sl2 *)  
  lemma take_list_of_sl2: "take i (list_of_sl2 xs) = list_of_sl2 (take i xs)"  
    unfolding list_of_sl2_def
    by (simp_all add: take_map)
    
  lemma drop_list_of_sl2: "drop i (list_of_sl2 xs) = list_of_sl2 (drop i xs)"  
    unfolding list_of_sl2_def
    by (simp_all add: drop_map)
    
  lemma slice_list_of_sl2: "Misc.slice l h (list_of_sl2 xs) = list_of_sl2 (Misc.slice l h xs)"
    unfolding Misc.slice_def
    by (auto simp: take_list_of_sl2 drop_list_of_sl2)
    
  lemma list_of_sl2_append: "list_of_sl2 (xs@ys) = list_of_sl2 xs @ list_of_sl2 ys"  
    unfolding list_of_sl2_def by auto
  

  (* sl2_indexes *)  
  lemma sl2_indexes_subset: "sl2_indexes xs \<subseteq> {0..<length xs}"      
    unfolding sl2_indexes_def
    by auto

  lemma sl2_indexes_append: "sl2_indexes (xs\<^sub>1@xs\<^sub>2) = sl2_indexes xs\<^sub>1 \<union> ((+)(length xs\<^sub>1))`sl2_indexes xs\<^sub>2"  
    unfolding sl2_indexes_def 
    apply (safe;clarsimp simp: nth_append) 
    subgoal by (smt (verit) add_diff_inverse_nat image_iff mem_Collect_eq nat_add_left_cancel_less)
    subgoal by (smt (verit) add_diff_inverse_nat image_iff mem_Collect_eq nat_add_left_cancel_less)
    done
    
  lemma sl2_indexes_take: "sl2_indexes (take n xs) = sl2_indexes xs \<inter> {0..<n}"  
    unfolding sl2_indexes_def 
    by auto

  lemma sl2_indexes_drop: "sl2_indexes (drop n xs) = {i-n | i. i\<in>sl2_indexes xs \<and> n\<le>i}"  
    unfolding sl2_indexes_def 
    by (auto intro: exI[where x="n+_"])
    
  lemma sl2_indexes_slice: "sl2_indexes (Misc.slice l h xs) = {i-l | i. i\<in>sl2_indexes xs \<and> l\<le>i \<and> i<h}"  
    unfolding Misc.slice_def
    by (auto simp: sl2_indexes_take sl2_indexes_drop) 
      
  lemma sl2_len_slice_aux: "\<lbrakk>l \<le> h; sl2_indexes xs = {l..<h}\<rbrakk> \<Longrightarrow> length (Misc.slice l h xs) = h-l"
    using sl2_indexes_subset[of xs]
    by (auto simp add: slice_len') 

  (* sl2_restr *)  
                                  
  lemma slice_restr_swap: "Misc.slice l h (sl2_restr {l..<h} xs) = sl2_restr {0..<h-l} (Misc.slice l h xs)"  
    unfolding Misc.slice_def sl2_restr_def
    apply (clarsimp simp: take_map drop_map)
    apply (subst list_eq_iff_nth_eq)
    apply auto
    done
    
        
  lemma sl2_restr_supset: "length xs \<le> h \<Longrightarrow> sl2_restr {0..<h} xs = xs"  
    apply (rule list_eq_iff_nth_eq[THEN iffD2])
    unfolding sl2_restr_def by auto
    
  lemma sl2_restr_inv_conv: "sl2_restr (-s) xs = sl2_restr (sl2_indexes xs - s) xs"  
    unfolding sl2_restr_def sl2_indexes_def
    by auto
  

  (* sl2_get *)    

  lemma sl2_get_take: "i<n \<Longrightarrow> sl2_get (take n xs) i = sl2_get xs i"
    unfolding sl2_get_def
    by (auto simp: algebra_simps)

  lemma sl2_get_drop: "n\<le>i \<Longrightarrow> i\<le>length xs \<Longrightarrow> sl2_get (drop n xs) i = sl2_get xs (i+n)"
    unfolding sl2_get_def
    by (auto simp: algebra_simps)
    
      
  lemma sl2_get_slice: "i<h-l \<Longrightarrow> h\<le>length xs \<Longrightarrow> sl2_get (Misc.slice l h xs) i = sl2_get xs (i+l)"
    unfolding sl2_get_def Misc.slice_def
    by (auto simp: algebra_simps)
    
  lemma sl2_get_append: "sl2_get (xs\<^sub>1@xs\<^sub>2) i = (if i<length xs\<^sub>1 then sl2_get xs\<^sub>1 i else sl2_get xs\<^sub>2 (i-length xs\<^sub>1))"
    unfolding sl2_get_def by (auto simp: nth_append)
    

  lemma sl2_get_as_list_of_nth: "i<length xs \<Longrightarrow> sl2_get xs i = list_of_sl2 xs ! i"  
    unfolding sl2_get_def list_of_sl2_def by auto
    
    
    
    
        
      
  definition "sl2_array_assn xs p \<equiv>  
    if xs=[] then \<box>
    else \<upharpoonleft>(ll_range (int ` sl2_indexes xs)) (sl2_get xs o nat) p
  "
  
  lemma sl2_of_list_Nil_iff: "sl2_of_list xs = [] \<longleftrightarrow> xs=[]"
    unfolding sl2_of_list_def by auto
  
  lemma raw_array_slice_to_sl2_assn: "raw_array_slice_assn xs p = sl2_array_assn (sl2_of_list xs) p"
    unfolding LLVM_DS_NArray.array_slice_assn_def sl2_array_assn_def 
    apply (clarsimp simp: sl2_of_list_Nil_iff)
    apply (rule ll_range_cong)
    apply (simp_all add: image_int_atLeastLessThan)
    by force

  lemma array_slice_to_sl2_assn: "array_slice_assn id_assn xs p = sl2_array_assn (sl2_of_list xs) p"
    unfolding array_slice_assn_def
    by (simp add: raw_array_slice_to_sl2_assn)

  lemma sl2_to_raw_array_slice_assn: "sl2_indexes xs = {0..<length xs} \<Longrightarrow> sl2_array_assn xs p = raw_array_slice_assn (list_of_sl2 xs) p"
    apply (subst raw_array_slice_to_sl2_assn)
    by (simp)
          
  lemma sl2_to_array_slice_assn: "sl2_indexes xs = {0..<length xs} \<Longrightarrow> sl2_array_assn xs p = array_slice_assn id_assn (list_of_sl2 xs) p"
    apply (subst array_slice_to_sl2_assn)
    by (simp)
    
  lemma sl2_array_assn_join: "sl2_indexes xs\<^sub>1 \<inter> sl2_indexes xs\<^sub>2 = {} \<Longrightarrow> sl2_array_assn (sl2_join xs\<^sub>1 xs\<^sub>2) p = (sl2_array_assn xs\<^sub>1 p \<and>* sl2_array_assn xs\<^sub>2 p)"
    unfolding sl2_array_assn_def
    apply (clarsimp simp: image_Un sl2_indexes_internal_simps split!: if_split)
    subgoal using sl2_join.elims by blast
    
    subgoal
      apply (subst ll_range_merge[symmetric])
      subgoal by auto
      apply (fo_rule cong)
      apply (fo_rule arg_cong)
      apply (rule ll_range_cong; fastforce)
      apply (rule ll_range_cong; fastforce)
      done
    done  
      
  lemma sl2_array_assn_split: 
    "(sl2_array_assn (sl2_restr s xs) p \<and>* sl2_array_assn (sl2_restr (-s) xs) p) = sl2_array_assn xs p"  
    apply (subst sl2_array_assn_join[symmetric])
    apply simp 
    apply simp 
    done


  definition "mop_sl2_get xs i \<equiv> doN {
    ASSERT (i\<in>sl2_indexes xs);
    RETURN (sl2_get xs i)
  }"  
    
  definition "mop_sl2_put xs i v \<equiv> doN {
    ASSERT (i\<in>sl2_indexes xs);
    RETURN (sl2_put xs i v)
  }"  
  
  lemma mop_sl2_get_correct[refine_vcg]: "i\<in>sl2_indexes xs \<Longrightarrow> mop_sl2_get xs i \<le> SPEC (\<lambda>r. r = sl2_get xs i)"
    unfolding mop_sl2_get_def by auto
  
  lemma mop_sl2_put_correct[refine_vcg]: "i\<in>sl2_indexes xs \<Longrightarrow> mop_sl2_put xs i v \<le> SPEC (\<lambda>r. r = sl2_put xs i v)"
    unfolding mop_sl2_put_def by auto

  sepref_register mop_sl2_get mop_sl2_put
        
  
  lemma sl2_array_assn_cnv_range_upd:  
    "i\<in>sl2_indexes xs \<Longrightarrow> sl2_array_assn (sl2_put xs i x) p = (\<upharpoonleft>(ll_range (int ` sl2_indexes xs)) ((sl2_get xs o nat)(int i := x)) p)"
    unfolding sl2_array_assn_def
    apply (clarsimp simp: sep_algebra_simps; intro impI conjI)
    subgoal by (metis emptyE2 sl2_indexes_internal_simps1 sl2_put_indexes)
    apply (rule ll_range_cong)
    by auto
  
    
  context
  begin
  
    interpretation llvm_prim_mem_setup .
  
    lemma mop_sl2_get_hnr[sepref_fr_rules]: "(uncurry array_nth, uncurry mop_sl2_get) \<in> sl2_array_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
      apply sepref_to_hoare
      unfolding mop_sl2_get_def sl2_array_assn_def array_nth_def snat_rel_def snat.rel_def
      apply (auto simp: refine_pw_simps sl2_indexes_internal_simps)
      apply vcg'
      apply (auto simp: in_br_conv snat_def SOLVE_AUTO_def)
      apply (metis Word.of_nat_unat cnv_snat_to_uint(2) image_iff nat_uint_eq)
      apply (metis Word.of_nat_unat cnv_snat_to_uint(2) image_iff nat_uint_eq)
      done

    thm array_assn_cnv_range_upd
  
    lemma sl2_put_hnr_aux1: "(\<lambda>s. \<exists>x. P1 x \<and> (P2 x \<and>* \<up>(x=c)) s) = (\<up>P1 c \<and>* P2 c)"
      by (auto simp: sep_algebra_simps)
      
    lemma sl2_put_hnr_aux2: "i \<in> sl2_indexes xs \<Longrightarrow> 
        \<upharpoonleft>(ll_range (int ` sl2_indexes xs)) (sl2_get (sl2_put xs i v) \<circ> nat) p
      = \<upharpoonleft>(ll_range (int ` sl2_indexes xs)) ((sl2_get xs \<circ> nat)(int i := v)) p
      "  
      apply (rule ll_range_cong)
      apply auto
      done
      
    lemma mop_sl2_put_hnr[sepref_fr_rules]: "(uncurry2 array_upd, uncurry2 mop_sl2_put) 
      \<in> [\<lambda>_. True]\<^sub>c sl2_array_assn\<^sup>d *\<^sub>a snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> sl2_array_assn [\<lambda>((p,_),_) r. r=p]\<^sub>c"
      apply sepref_to_hoare
      
      subgoal for v vi i ii xs p
        apply (rule htriple_pure_preI)
        unfolding mop_sl2_put_def sl2_array_assn_def array_upd_def snat_rel_def snat.rel_def
        apply (subgoal_tac "[]\<noteq>sl2_put xs i v \<and> abase p")
        apply (auto simp: refine_pw_simps sl2_indexes_internal_simps sl2_put_hnr_aux1 in_br_conv)
        apply (subst sl2_put_hnr_aux2, simp)
        supply [simp] = int_snat_eq_sint
        apply vcg' []
        subgoal by (simp add: rev_image_eqI SOLVE_AUTO_def)
        subgoal by (simp add: rev_image_eqI SOLVE_AUTO_def)
        subgoal by (metis empty_iff sl2_indexes_internal_simps1 sl2_put_indexes)
        subgoal by (smt (verit) empty_iff ll_range_base pure_part_split_conj sl2_indexes_internal_simps1)
        done
      done 
  
  end  

  
  context fixes s :: "nat set" begin
    sepref_register "sl2_split s" 
  end
      
  definition [llvm_inline,sepref_opt_simps]: "sl2_split_impl p \<equiv> Mreturn (p,p)"
  
  lemma sl2_split_hnr[sepref_fr_rules]: 
    "(sl2_split_impl, RETURN o PR_CONST (sl2_split s)) \<in> [\<lambda>_. True]\<^sub>c sl2_array_assn\<^sup>d \<rightarrow> sl2_array_assn \<times>\<^sub>a sl2_array_assn [\<lambda>p (r\<^sub>1,r\<^sub>2). r\<^sub>1=p \<and> r\<^sub>2=p]\<^sub>c"
    unfolding sl2_split_impl_def PR_CONST_def sl2_split_def
    apply sepref_to_hoare
    apply (subst sl2_array_assn_split[of s,symmetric])
    by vcg
  
  definition "mop_sl2_join xs\<^sub>1 xs\<^sub>2 \<equiv> doN { ASSERT (sl2_indexes xs\<^sub>1 \<inter> sl2_indexes xs\<^sub>2 = {}); RETURN (sl2_join xs\<^sub>1 xs\<^sub>2) }"
  lemma mop_sl2_join_correct[refine_vcg]: "sl2_indexes xs\<^sub>1 \<inter> sl2_indexes xs\<^sub>2 = {} \<Longrightarrow> mop_sl2_join xs\<^sub>1 xs\<^sub>2 \<le> SPEC(\<lambda>r. r = sl2_join xs\<^sub>1 xs\<^sub>2)"
    unfolding mop_sl2_join_def apply refine_vcg by simp
    
  definition [llvm_inline,sepref_opt_simps]: "sl2_join_impl p\<^sub>1 p\<^sub>2 \<equiv> Mreturn p\<^sub>1"
  
  lemma sl2_join_hnr[sepref_fr_rules]: "(uncurry sl2_join_impl, uncurry mop_sl2_join) \<in> [\<lambda>(p\<^sub>1,p\<^sub>2). CP_cond (p\<^sub>2=p\<^sub>1)]\<^sub>c sl2_array_assn\<^sup>d *\<^sub>a sl2_array_assn\<^sup>d \<rightarrow> sl2_array_assn [\<lambda>(p\<^sub>1,p\<^sub>2) r. r=p\<^sub>1]\<^sub>c"
    unfolding sl2_join_impl_def mop_sl2_join_def CP_defs
    apply sepref_to_hoare
    apply (simp add: refine_pw_simps)
    apply (subst sl2_array_assn_join[symmetric], simp)
    apply vcg
    done
  
  (* To and from array_slice *)
      
  lemma sl2_of_list_hnr[sepref_fr_rules]: "(Mreturn,RETURN o sl2_of_list) \<in> [\<lambda>_. True]\<^sub>c (array_slice_assn id_assn)\<^sup>d \<rightarrow> sl2_array_assn [\<lambda>p r. r=p]\<^sub>c"
    unfolding sl2_of_list_def array_slice_to_sl2_assn
    apply sepref_to_hoare
    apply vcg
    done
  
  sepref_register mop_list_of_sl2 
  lemma list_of_sl2_impl[sepref_fr_rules]: "(Mreturn, mop_list_of_sl2) \<in> [\<lambda>_. True]\<^sub>c sl2_array_assn\<^sup>d \<rightarrow> array_slice_assn id_assn [\<lambda>p r. r=p]\<^sub>c"
    (* Some delicate handling of invalid_assn is required here *)
    apply (rule hfrefI; simp add: array_slice_assn_def)
    apply sepref_to_hoare
    apply (rule htriple_pure_preI; simp add: invalid_assn_def mop_list_of_sl2_def refine_pw_simps)
    apply (subst sl2_to_raw_array_slice_assn)
    subgoal by (simp)
    by vcg

  context fixes n :: nat begin
    sepref_register "mop_list_of_sl2N n"
  end
    
  lemma sl2_array_assn_take:
    assumes "sl2_indexes xs \<subseteq> {0..<n}" "n\<noteq>0"
    shows "sl2_array_assn (take n xs) p = sl2_array_assn xs p"
    unfolding sl2_array_assn_def
    using assms
    by (auto simp: ll_range_empty sl2_indexes_take sl2_get_take intro!: ll_range_cong)
  
  lemma list_of_sl2N_impl[sepref_fr_rules]: "(Mreturn, PR_CONST (mop_list_of_sl2N n)) \<in> [\<lambda>_. True]\<^sub>c sl2_array_assn\<^sup>d \<rightarrow> array_slice_assn id_assn [\<lambda>p r. r=p]\<^sub>c"
    (* Some delicate handling of invalid_assn is required here *)
    apply (rule hfrefI; simp add: array_slice_assn_def)
    apply sepref_to_hoare
    apply (rule htriple_pure_preI; simp add: invalid_assn_def mop_list_of_sl2N_def refine_pw_simps)
    apply (subst sl2_array_assn_take[symmetric, where n=n])
    subgoal by simp
    subgoal by simp
    apply (subst sl2_to_raw_array_slice_assn)
    subgoal for p xs
      using sl2_indexes_subset[of xs]
      by (auto simp: sl2_indexes_take)
    by vcg
  
  
    
  experiment
  begin
    
    definition "my_test xs \<equiv> doN {
      let xs = sl2_of_list xs;
    
      let (xs\<^sub>1,xs\<^sub>2) = sl2_split {0} xs;
      
      t \<leftarrow> mop_sl2_get xs\<^sub>1 0;
      xs\<^sub>2 \<leftarrow> mop_sl2_put xs\<^sub>2 1 t;
    
      xs \<leftarrow> mop_sl2_join xs\<^sub>1 xs\<^sub>2;
    
      xs \<leftarrow> mop_list_of_sl2 xs;
      
      RETURN xs
    }"  
      
    
    lemma list_of_sl2_eq_swapI: "xs = sl2_of_list ys \<Longrightarrow> list_of_sl2 xs = ys" by simp
      
    lemma list_of_sl2_eqI:
      assumes "length xs = length ys"
      assumes "sl2_indexes xs = {0..<length ys}"
      assumes "\<And>i. i<length ys \<Longrightarrow> sl2_get xs i = ys!i"
      shows "list_of_sl2 xs = ys"
      apply (rule list_of_sl2_eq_swapI)
      apply (subst sl2_eq_iff)
      by (simp add: assms)
      
      
    lemma "2\<le>length xs \<Longrightarrow> my_test xs \<le> SPEC (\<lambda>xs'. xs' = xs[ 1 := xs!0 ])"
      unfolding my_test_def
      apply refine_vcg
      apply (auto intro!: list_of_sl2_eqI simp: sl2_get_join_iff)
      done
    
    sepref_def my_test_impl is "my_test" 
      :: "[\<lambda>_. True]\<^sub>c (array_slice_assn id_assn)\<^sup>d \<rightarrow> array_slice_assn id_assn [\<lambda>p r. r=p]\<^sub>c"
      unfolding my_test_def
      apply (annot_snat_const "TYPE(64)")
      by sepref
  
    export_llvm "my_test_impl :: 64 word ptr \<Rightarrow> _"
  
  
  end  
          

  
  
  
  (* Using shared lists for list slices *)
  
  type_synonym 'a ls2 = "'a option list \<times> nat \<times> nat"
  
  definition "ls2_invar \<equiv> \<lambda>(xs,l,h). l\<le>h \<and> sl2_indexes xs = {l..<h}"
  definition "ls2_\<alpha> \<equiv> \<lambda>(xs,l,h). list_of_sl2 (Misc.slice l h xs)"
  
  abbreviation "ls2_aux_rel \<equiv> br ls2_\<alpha> ls2_invar"
  

  definition "mop_ls2_of_list xs n \<equiv> doN { 
    ASSERT(n=length xs); 
    RETURN (sl2_of_list xs, 0, n)
  }" 
  
  definition "mop_list_of_ls2 \<equiv> \<lambda>(xs,l,h). doN {
    ASSUME (l=0); \<comment> \<open>By concrete equality\<close>
    ASSERT (0<h); \<comment> \<open>Via abstract \<open>\<noteq> []\<close>\<close>
    mop_list_of_sl2N h xs
  }"

  definition "mop_ls2_len \<equiv> \<lambda>(xs,l,h). doN { ASSERT(l\<le>h); RETURN (h-l) }"
      
  definition "mop_ls2_split \<equiv> \<lambda>i (xs,l,h). doN {  
    ASSERT (l+i\<le>h); \<comment> \<open>Inferred from i<=length(\<alpha>)\<close>
    let (xs\<^sub>1,xs\<^sub>2) = sl2_split {l..<l+i} xs;
    let m = l+i; \<comment> \<open>Important to use same variable \<open>m\<close>, rather than inlining, such that sepref can prove cp-equality\<close>
    RETURN ((xs\<^sub>1,l,m),(xs\<^sub>2,m,h))
  }"

  definition "mop_ls2_join \<equiv> \<lambda>(xs\<^sub>1,l\<^sub>1,h\<^sub>1) (xs\<^sub>2,l\<^sub>2,h\<^sub>2). doN {
    ASSUME (h\<^sub>1=l\<^sub>2); \<comment> \<open>Proved by concrete equality\<close>
    xs \<leftarrow> mop_sl2_join xs\<^sub>1 xs\<^sub>2;
    RETURN (xs,l\<^sub>1,h\<^sub>2)
  }"
    
  definition "mop_ls2_get \<equiv> \<lambda>(xs,l,h) i. doN {
    ASSERT (l+i<h);  \<comment> \<open>Inferred from i<length(\<alpha>)\<close>
    mop_sl2_get xs (l+i)
  }"  
  
  definition "mop_ls2_put \<equiv> \<lambda>(xs,l,h) i v. doN {
    ASSERT (l+i<h);  \<comment> \<open>Inferred from i<length(\<alpha>)\<close>
    xs \<leftarrow> mop_sl2_put xs (l+i) v;
    RETURN (xs,l,h)
  }"  

  
  
  lemma mop_ls2_of_list_correct[refine_vcg]: "n=length xs \<Longrightarrow> mop_ls2_of_list xs n \<le> SPEC (\<lambda>r. ls2_invar r \<and> ls2_\<alpha> r = xs)"
    unfolding ls2_invar_def ls2_\<alpha>_def mop_ls2_of_list_def
    apply refine_vcg by (auto simp: Misc.slice_def)
      
    
  sepref_decl_op mk_lslice: "\<lambda>(xs::_ list) (n::nat). xs" :: "[\<lambda>(xs,n). n=length xs]\<^sub>f \<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
    
  lemma mop_ls2_of_list_refine: "(mop_ls2_of_list, mop_mk_lslice) \<in> Id \<rightarrow> nat_rel \<rightarrow> \<langle>ls2_aux_rel\<rangle>nres_rel"   
    unfolding mop_mk_lslice_alt
    apply refine_vcg
    by (auto simp: in_br_conv)

    
  lemma list_of_ls2_correct[refine_vcg]: "\<lbrakk>ls2_invar xs; ls2_\<alpha> xs \<noteq> []\<rbrakk> \<Longrightarrow> mop_list_of_ls2 xs \<le> SPEC (\<lambda>r. r = ls2_\<alpha> xs)"
    unfolding mop_list_of_ls2_def ls2_\<alpha>_def ls2_invar_def
    apply refine_vcg
    by (auto simp add: Misc.slice_def simp flip: take_list_of_sl2)

  sepref_decl_op list_of_lslice: "\<lambda>x :: _ list. x" :: "[\<lambda>xs. xs\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" by auto
  
  lemma mop_list_of_ls2_refine: "(mop_list_of_ls2, mop_list_of_lslice) \<in> ls2_aux_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
    unfolding mop_list_of_lslice_alt
    apply refine_vcg
    by (auto simp: in_br_conv)
    
    
    
  lemma mop_ls2_len_correct[refine_vcg]: "\<lbrakk> ls2_invar xs \<rbrakk> \<Longrightarrow> mop_ls2_len xs \<le> SPEC (\<lambda>r. r = length (ls2_\<alpha> xs))"
    unfolding ls2_invar_def mop_ls2_len_def ls2_\<alpha>_def
    apply refine_vcg
    by (auto simp: sl2_len_slice_aux)
    
  lemma mop_ls2_len_refine: "(mop_ls2_len, mop_list_length) \<in> ls2_aux_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"  
    unfolding mop_list_length_alt
    apply refine_vcg
    by (auto simp: in_br_conv)
    
        
  lemma mop_ls2_split_correct[refine_vcg]: "\<lbrakk>ls2_invar xs; i\<le>length (ls2_\<alpha> xs)\<rbrakk> 
    \<Longrightarrow> mop_ls2_split i xs \<le> SPEC (\<lambda>(xs\<^sub>1,xs\<^sub>2). 
      ls2_invar xs\<^sub>1 \<and> ls2_invar xs\<^sub>2 \<and> ls2_\<alpha> xs\<^sub>1 = take i (ls2_\<alpha> xs) \<and> ls2_\<alpha> xs\<^sub>2 = drop i (ls2_\<alpha> xs) )"
    unfolding mop_ls2_split_def
    apply refine_vcg
    apply (clarsimp_all simp: ls2_invar_def ls2_\<alpha>_def sl2_len_slice_aux) 
    subgoal by simp
    subgoal by force
    subgoal by (simp add: take_list_of_sl2 slice_restr_swap take_slice sl2_restr_supset slice_len') 
    subgoal by (simp add: drop_list_of_sl2 slice_restr_swap drop_slice sl2_restr_supset slice_len' sl2_restr_inv_conv) 
    done

  lemma mop_ls2_split_refine: "(mop_ls2_split, mop_split_list) \<in> nat_rel \<rightarrow> ls2_aux_rel \<rightarrow> \<langle>ls2_aux_rel \<times>\<^sub>r ls2_aux_rel\<rangle>nres_rel"  
    unfolding mop_split_list_alt
    apply refine_vcg
    by (auto simp: in_br_conv)
    
    
  (* Main lemma to justify joining of adjacent slices *)
  lemma slice_join_adjacent:
    assumes LZH: "l\<le>z" "z\<le>h"
    assumes IDXS: "sl2_indexes xs\<^sub>1 = {l..<z}" "sl2_indexes xs\<^sub>2 = {z..<h}"
    shows "Misc.slice l h (sl2_join xs\<^sub>1 xs\<^sub>2) = Misc.slice l z xs\<^sub>1 @ Misc.slice z h xs\<^sub>2" (is "?l = ?r")
  proof -
    (* Case distinction if the intervals l..<z and z..<h are empty or not *)
    {
      assume [simp]: "l=z"
      
      {
        assume "z=h" 
        hence ?thesis by simp
      } moreover {
        assume "z<h" 
        hence "h\<le>length xs\<^sub>2"  
          using IDXS(2) sl2_indexes_subset[of xs\<^sub>2] by auto
        hence ?thesis
          apply (clarsimp simp: sl2_eq_iff slice_len' sl2_indexes_slice; intro conjI allI impI; clarsimp?)
          subgoal using IDXS by auto
          subgoal for i using IDXS by (auto simp: sl2_get_slice)
          done
      } ultimately have ?thesis using \<open>z\<le>h\<close> by linarith
    } moreover {
      assume "l<z"
      hence ZLE: "z\<le>length xs\<^sub>1"  
        using IDXS(1) sl2_indexes_subset[of xs\<^sub>1] by auto
      
      hence [simp]: "min (max (length xs\<^sub>1) (length xs\<^sub>2)) h = h"
        using IDXS(2) sl2_indexes_subset[of xs\<^sub>2] \<open>z\<le>h\<close> by auto
      
        
      {
        assume "z=h"
      
        hence ?thesis using ZLE
          apply (clarsimp simp: sl2_eq_iff slice_len' sl2_indexes_slice; intro conjI allI impI; clarsimp?)
          subgoal using IDXS by auto
          subgoal for i using IDXS by (auto simp: sl2_get_slice)
          done
      } moreover {
        assume "z<h"
        hence HLE: "h\<le>length xs\<^sub>2"  
          using IDXS(2) sl2_indexes_subset[of xs\<^sub>2] by auto
        
        hence ?thesis using ZLE \<open>l<z\<close> \<open>z<h\<close>
          apply (clarsimp simp: sl2_eq_iff slice_len' sl2_indexes_slice; intro conjI allI impI; clarsimp?)
          subgoal
            apply (clarsimp simp: sl2_indexes_append sl2_indexes_slice IDXS) 
            apply (safe; force)
            done
          subgoal  
            using IDXS
            apply (clarsimp simp: sl2_get_append sl2_indexes_slice sl2_get_slice)
            apply (subst sl2_get_slice)
            apply (all \<open>auto simp: sl2_indexes_append sl2_indexes_slice; fail\<close>)[2]
            apply (subst sl2_get_slice)
            apply (all \<open>auto simp: sl2_indexes_append sl2_indexes_slice; fail\<close>)[3]
            done
          done  
      } ultimately have ?thesis using \<open>z\<le>h\<close> by linarith
    } ultimately show ?thesis using \<open>l\<le>z\<close> \<open>z\<le>h\<close> by linarith
  qed
    
        
  lemma mop_ls2_join_correct[refine_vcg]: "\<lbrakk> ls2_invar xs\<^sub>1; ls2_invar xs\<^sub>2 \<rbrakk> \<Longrightarrow> mop_ls2_join xs\<^sub>1 xs\<^sub>2 \<le> SPEC (\<lambda>xs. ls2_invar xs \<and> ls2_\<alpha> xs = ls2_\<alpha> xs\<^sub>1 @ ls2_\<alpha> xs\<^sub>2)"
    unfolding mop_ls2_join_def
    apply refine_vcg
    unfolding ls2_invar_def ls2_\<alpha>_def
    by (auto simp: slice_join_adjacent  simp flip: list_of_sl2_append)
    
  lemma mop_ls2_join_refine: "(mop_ls2_join, mop_join_list) \<in> ls2_aux_rel \<rightarrow> ls2_aux_rel \<rightarrow> \<langle>ls2_aux_rel\<rangle>nres_rel"  
    unfolding mop_join_list_alt
    apply refine_vcg
    by (auto simp: in_br_conv)
    
    
  lemma mop_ls2_get_correct[refine_vcg]: "\<lbrakk>ls2_invar xs; i<length (ls2_\<alpha> xs)\<rbrakk> \<Longrightarrow> mop_ls2_get xs i \<le> SPEC (\<lambda>r. r = ls2_\<alpha> xs ! i)"
    unfolding mop_ls2_get_def
    apply refine_vcg
    unfolding ls2_invar_def ls2_\<alpha>_def
    apply (simp_all add: slice_len') 
    apply clarsimp
    subgoal for xs' l h
      using sl2_indexes_subset[of xs']
      by (auto simp: sl2_get_as_list_of_nth Misc.slice_nth simp flip: slice_list_of_sl2)
    done  

  lemma mop_ls2_get_refine: "(mop_ls2_get, mop_list_get) \<in> ls2_aux_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"  
    unfolding mop_list_get_alt
    apply refine_vcg
    by (auto simp: in_br_conv)
    
    
            
  lemma mop_ls2_put_correct[refine_vcg]: "\<lbrakk>ls2_invar xs; i<length (ls2_\<alpha> xs)\<rbrakk> \<Longrightarrow> mop_ls2_put xs i v \<le> SPEC (\<lambda>r. ls2_invar r \<and> ls2_\<alpha> r = (ls2_\<alpha> xs)[i:=v])"
    unfolding mop_ls2_put_def
    apply refine_vcg
    unfolding ls2_invar_def ls2_\<alpha>_def
    apply (simp_all add: slice_len') 
    apply clarsimp
    subgoal for xs' l h
      using sl2_indexes_subset[of xs']
      apply (auto simp: simp flip: slice_list_of_sl2)
      by (simp add: Misc.slice_def drop_update_swap list_of_sl2_def map_update sl2_put_def) 
    done

  lemma mop_ls2_put_refine: "(mop_ls2_put, mop_list_set) \<in> ls2_aux_rel \<rightarrow> nat_rel \<rightarrow> Id \<rightarrow> \<langle>ls2_aux_rel\<rangle>nres_rel"  
    unfolding mop_list_set_alt
    apply refine_vcg
    by (auto simp: in_br_conv)
    
    
    
  (* Implementation *)      
    
  definition ls2_assn_aux :: "'a::llvm_rep option list \<times> nat \<times> nat \<Rightarrow> 'a ptr \<times> 'l::len2 word \<times> 'l word \<Rightarrow> assn"
    where "ls2_assn_aux \<equiv> sl2_array_assn \<times>\<^sub>a snat_assn \<times>\<^sub>a snat_assn"
    
  abbreviation ls2_assn_aux' :: "'l::len2 itself \<Rightarrow> 'a::llvm_rep option list \<times> nat \<times> nat \<Rightarrow> 'a ptr \<times> 'l::len2 word \<times> 'l word \<Rightarrow> assn" 
    where "ls2_assn_aux' TYPE('l) \<equiv> ls2_assn_aux"  
    

  sepref_register  
    mop_ls2_of_list
    mop_list_of_ls2
    mop_ls2_len
    mop_ls2_split  
    mop_ls2_join (* done *)
    mop_ls2_get
    mop_ls2_put
        
  sepref_definition ls2_of_list_impl [llvm_inline] is "uncurry mop_ls2_of_list" 
    :: "[\<lambda>_. True]\<^sub>c (array_slice_assn id_assn)\<^sup>d *\<^sub>a (snat_assn' TYPE('l::len2))\<^sup>k \<rightarrow> ls2_assn_aux' TYPE('l) [\<lambda>(a,n) (p,l,_). p=a \<and> l=0]\<^sub>c"
    unfolding mop_ls2_of_list_def ls2_assn_aux_def
    apply (subst fold_cp_snat0[where 'l='l])
    by sepref
    
  sepref_definition list_of_ls2_impl [llvm_inline] is "mop_list_of_ls2"  
    :: "[\<lambda>x. CP_cond (case x of (p,l,h) \<Rightarrow> l=0)]\<^sub>c ls2_assn_aux\<^sup>d \<rightarrow> array_slice_assn id_assn [\<lambda>(p,_,_) r. r=p]\<^sub>c"
    unfolding mop_list_of_ls2_def  ls2_assn_aux_def
    apply (subst fold_ASSUME_conc_eq0)
    by sepref
    
  sepref_definition ls2_len_impl [llvm_inline] is "mop_ls2_len" :: "(ls2_assn_aux' TYPE('l::len2))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('l)"
    unfolding mop_ls2_len_def ls2_assn_aux_def
    by sepref
    
    
  type_synonym ('a,'l) ls2_impl = "'a ptr \<times> 'l word \<times> 'l word"
  abbreviation (input) ls2_split_post :: "('a,'l) ls2_impl \<Rightarrow> ('a,'l) ls2_impl \<Rightarrow> ('a,'l) ls2_impl \<Rightarrow> bool" 
    where "ls2_split_post \<equiv> \<lambda>(p,l,h) (p\<^sub>1,l\<^sub>1,h\<^sub>1) (p\<^sub>2,l\<^sub>2,h\<^sub>2). p\<^sub>1=p \<and> p\<^sub>2=p \<and> l\<^sub>1=l \<and> h\<^sub>1=l\<^sub>2 \<and> h\<^sub>2=h"  
    
  sepref_definition ls2_split_impl [llvm_inline] is "uncurry mop_ls2_split" 
    :: "[\<lambda>_. True]\<^sub>c 
      (snat_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (ls2_assn_aux' TYPE('l))\<^sup>d \<rightarrow> ls2_assn_aux' TYPE('l) \<times>\<^sub>a ls2_assn_aux' TYPE('l) 
      [\<lambda>(_,src) (left,right). ls2_split_post src left right ]\<^sub>c"
    unfolding mop_ls2_split_def ls2_assn_aux_def
    apply sepref_dbg_preproc
    apply sepref_dbg_cons_init
    apply sepref_dbg_id
    apply sepref_dbg_monadify
    apply sepref_dbg_opt_init
    apply sepref_dbg_trans
    apply sepref_dbg_opt
    apply sepref_dbg_cons_solve
    apply sepref_dbg_cons_solve
    apply (clarsimp simp: CP_defs; fail)  
    apply sepref_dbg_constraints
    done
    
  abbreviation (input) ls2_join_pre :: "('a,'l) ls2_impl \<Rightarrow> ('a,'l) ls2_impl \<Rightarrow> bool" where
    "ls2_join_pre \<equiv> \<lambda>(xs\<^sub>1,l\<^sub>1,h\<^sub>1) (xs\<^sub>2,l\<^sub>2,h\<^sub>2). xs\<^sub>2 = xs\<^sub>1 \<and> l\<^sub>2 = h\<^sub>1"

  abbreviation (input) ls2_join_post :: "('a,'l) ls2_impl \<Rightarrow> ('a,'l) ls2_impl \<Rightarrow> ('a,'l) ls2_impl \<Rightarrow> bool" where
    "ls2_join_post \<equiv> \<lambda>(xs\<^sub>1,l\<^sub>1,h\<^sub>1) (xs\<^sub>2,l\<^sub>2,h\<^sub>2) (xs,l,h). xs=xs\<^sub>1 \<and> l=l\<^sub>1 \<and> h=h\<^sub>2"
    
        
  sepref_definition ls2_join_impl [llvm_inline,sepref_opt_simps] is "uncurry mop_ls2_join" 
    :: "[\<lambda>x. CP_cond (case x of (l,r) \<Rightarrow> ls2_join_pre l r)]\<^sub>c 
          (ls2_assn_aux' TYPE('l::len2))\<^sup>d *\<^sub>a (ls2_assn_aux' TYPE('l))\<^sup>d \<rightarrow> ls2_assn_aux' TYPE('l) 
        [\<lambda>(l,r) t. ls2_join_post l r t ]\<^sub>c" 
    unfolding mop_ls2_join_def ls2_assn_aux_def
    apply (subst fold_ASSUME_conc_eq)
    (*apply (rewrite at "ASSUME \<hole>" CP_cond_def[symmetric])*)
    by sepref

  sepref_definition ls2_get_impl [llvm_inline] is "uncurry mop_ls2_get" :: "(ls2_assn_aux' TYPE('l::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('l))\<^sup>k \<rightarrow>\<^sub>a id_assn"
    unfolding mop_ls2_get_def ls2_assn_aux_def
    by sepref
    
  sepref_definition ls2_put_impl [llvm_inline] is "uncurry2 mop_ls2_put" 
    :: "[\<lambda>_. True]\<^sub>c (ls2_assn_aux' TYPE('l::len2))\<^sup>d *\<^sub>a (snat_assn' TYPE('l))\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> ls2_assn_aux' TYPE('l) [\<lambda>(((p,l,h),_),_) (p',l',h'). p'=p \<and> l'=l \<and> h'=h]\<^sub>c"
    unfolding mop_ls2_put_def ls2_assn_aux_def
    by sepref
    
  definition "ls2_assn A \<equiv> hr_comp (hr_comp ls2_assn_aux ls2_aux_rel) (\<langle>the_pure A\<rangle>list_rel)"
  abbreviation ls2_assn' 
    :: "'l::len2 itself \<Rightarrow> ('a \<Rightarrow> 'b::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'b ptr \<times> 'l word \<times> 'l word \<Rightarrow> assn"
    where "ls2_assn' TYPE('l) A \<equiv> ls2_assn A"
  
  find_theorems array_slice_assn id_assn hr_comp
  
  context
    notes [fcomp_norm_unfold] = ls2_assn_def[symmetric] array_slice_assn_comp
  begin
  
    thm ls2_of_list_impl.refine[FCOMP mop_ls2_of_list_refine]
  
    sepref_decl_impl (ismop) ls2_of_list_impl.refine[FCOMP mop_ls2_of_list_refine] .
    sepref_decl_impl (ismop) list_of_ls2_impl.refine[FCOMP mop_list_of_ls2_refine] .
    sepref_decl_impl (ismop) ls2_len_impl.refine[FCOMP mop_ls2_len_refine] .
    sepref_decl_impl (ismop) ls2_split_impl.refine[FCOMP mop_ls2_split_refine] .
    sepref_decl_impl (ismop) ls2_join_impl.refine[FCOMP mop_ls2_join_refine] .
    sepref_decl_impl (ismop) ls2_get_impl.refine[FCOMP mop_ls2_get_refine] .
    sepref_decl_impl (ismop) ls2_put_impl.refine[FCOMP mop_ls2_put_refine] .
  end
    
  
  experiment
  begin

    
  definition "test xs n \<equiv> doN {
    ASSERT (length xs = n \<and> 2<n);
    xs \<leftarrow> mop_mk_lslice xs n;
    
    (xs\<^sub>1,xs\<^sub>2) \<leftarrow> mop_split_list 2 xs;
    
    v \<leftarrow> mop_list_get xs\<^sub>2 0;
    xs\<^sub>1 \<leftarrow> mop_list_set xs\<^sub>1 0 v;
    v \<leftarrow> mop_list_get xs\<^sub>1 1;
    xs\<^sub>2 \<leftarrow> mop_list_set xs\<^sub>2 0 v;
    
    xs \<leftarrow> mop_join_list xs\<^sub>1 xs\<^sub>2;
    
    xs \<leftarrow> mop_list_of_lslice xs;
    
    RETURN xs
  }"
  
  sepref_def test_impl is "uncurry test" :: "(array_slice_assn id_assn)\<^sup>d *\<^sub>a (snat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a array_slice_assn id_assn"
    unfolding test_def
    apply (annot_snat_const "TYPE(64)")
    apply sepref_dbg_keep
    done

  end
    
  
  
  
    
    
    
        



end
