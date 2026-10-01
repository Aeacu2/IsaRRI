theory IICF_More_Array
imports IICF_For_Loop_Add "Isabelle_LLVM.Proto_IICF_EOArray"
  "Examples.IICF_DS_Array_Idxs"
begin
  lemma frame_rotate2_rl:
    assumes "FRAME_INFER P (Q\<^sub>2\<and>*Q\<^sub>1) F"
    shows "FRAME_INFER P (Q\<^sub>1\<and>*Q\<^sub>2) F"
    using assms by (simp add: sep_conj_c) 

  method frame_rotate2 = rule frame_rotate2_rl; (simp only: sep_conj_assoc)?
        
  lemma ENTAILS_drule: "A\<turnstile>A' \<Longrightarrow> ENTAILS A' B \<Longrightarrow> ENTAILS A B"
    unfolding ENTAILS_def
    by (rule entails_trans)

  lemma ENTAILS_exE:
    assumes "\<And>x. ENTAILS (P x) Q"
    shows "ENTAILS (EXS x. P x) Q"  
    using assms unfolding ENTAILS_def by (rule entails_exE)
    
  lemma ENTAILS_extract_pre_pure:
    assumes "P\<^sub>1 \<Longrightarrow> ENTAILS P\<^sub>2 Q"
    shows "ENTAILS (\<up>P\<^sub>1 \<and>* P\<^sub>2) Q"  
    using assms unfolding ENTAILS_def by (cases P\<^sub>1) (auto simp: sep_algebra_simps)



(* More complete than array.fold_replicate_init *)
thm array.fold_replicate_init
lemma array_fold_replicate_init':
  "replicate n i = array_replicate_init i n"
  "op_list_replicate n i = array_replicate_init i n"
  "mop_list_replicate n i = RETURN (array_replicate_init i n)"
  by auto



definition "woarray_slice_diff_assn n p \<equiv> if n=0 then \<up>(p=null) else \<upharpoonleft>array_base_assn n p"  
  

find_theorems abase

(* Array to array-slice material, adapted from Sorting_Ex_Array_Idxs *)

context begin
  interpretation llvm_prim_mem_setup .
  lemma ll_malloc_tag_null[sep_algebra_simps]: "ll_malloc_tag n null = sep_false"
    unfolding ll_malloc_tag_def null_def llvm_blockp_def
    by simp


  lemma array_base_assn_simps[sep_algebra_simps]:
    "\<upharpoonleft>array_base_assn 0 null = \<box>"
    "\<upharpoonleft>array_base_assn 0 p = \<up>(p=null)"
    "\<upharpoonleft>array_base_assn n null = \<up>(n=0)"
    unfolding array_base_assn_def
    by (auto simp: sep_algebra_simps) 

end  
  

lemma wo_array_assn_to_slice: "woarray_assn A xs p = 
  (woarray_slice_assn A xs p ** woarray_slice_diff_assn (length xs) p)"  
  unfolding woarray_assn_conv eoarray_assn_def Proto_EOArray.nao_assn_def
     array_assn_split hr_comp_def
  apply (clarsimp simp add: sep_algebra_simps fun_eq_iff)
  unfolding woarray_slice_assn_conv eoarray_slice_assn_def sao_assn_def woarray_slice_diff_assn_def 
  apply (cases "xs=[]"; cases "p=null"; simp)
  subgoal by (auto simp: sep_algebra_simps)
  subgoal by (clarsimp simp: sep_algebra_simps)
  subgoal by (clarsimp simp: sep_algebra_simps)
  apply (clarsimp simp: sep_algebra_simps sep_conj_c)
  apply safe
  subgoal for s xs'
    apply (cases "length xs = length xs'"; simp)
    apply auto
    done
  subgoal for s xs'
    apply (cases "length xs = length xs'"; cases "xs'\<noteq>[]"; simp)
    apply auto
    done
  done      


lemma eo_array_assn_to_slice: "eoarray_assn A xs p = 
  (eoarray_slice_assn A xs p ** woarray_slice_diff_assn (length xs) p)"  
  unfolding woarray_assn_conv eoarray_assn_def Proto_EOArray.nao_assn_def
     array_assn_split hr_comp_def
  apply (clarsimp simp add: sep_algebra_simps fun_eq_iff)
  unfolding woarray_slice_assn_conv eoarray_slice_assn_def sao_assn_def woarray_slice_diff_assn_def 
  apply (cases "xs=[]"; cases "p=null"; simp)
  subgoal by (auto simp: sep_algebra_simps)
  subgoal by (clarsimp simp: sep_algebra_simps)
  subgoal by (clarsimp simp: sep_algebra_simps)
  apply (clarsimp simp: sep_algebra_simps sep_conj_c)
  apply safe
  subgoal for s xs'
    apply (cases "length xs = length xs'"; simp)
    apply auto
    done
  subgoal for s xs'
    apply (cases "length xs = length xs'"; cases "xs'\<noteq>[]"; simp)
    apply auto
    done
  done      
  
  
  
(* Converting woarray into slice, and back *)
definition "split_woarray xs = RETURN (xs,length xs)"  
definition [llvm_inline]: "split_woarray_impl p = Mreturn (p,p)"  

definition "combine_woarray xs tag = doN {ASSERT (length xs = tag); RETURN xs}"  
definition [llvm_inline]: "combine_woarray_impl p p' = Mreturn p"


  
sepref_register split_woarray combine_woarray

lemma split_woarray_impl_hnr[sepref_fr_rules]: 
  "(split_woarray_impl, split_woarray) \<in> [\<lambda>_. True]\<^sub>c (woarray_assn A)\<^sup>d \<rightarrow> woarray_slice_assn A \<times>\<^sub>a woarray_slice_diff_assn [\<lambda>p (p1,p2). p1=p \<and> p2=p]\<^sub>c"
  apply sepref_to_hoare
  unfolding split_woarray_impl_def wo_array_assn_to_slice split_woarray_def
  by vcg'

  
lemma combine_woarray_impl_hnr[sepref_fr_rules]:
  "(uncurry combine_woarray_impl, uncurry combine_woarray) 
    \<in> [\<lambda>(p1,p2). CP_cond (p1=p2)]\<^sub>c (woarray_slice_assn A)\<^sup>d *\<^sub>a (woarray_slice_diff_assn)\<^sup>d \<rightarrow> woarray_assn A [\<lambda>(p1,p2) p. p=p1]\<^sub>c"  
  apply sepref_to_hoare
  unfolding combine_woarray_impl_def combine_woarray_def CP_cond_def
  apply (subst wo_array_assn_to_slice)
  apply (clarsimp simp: refine_pw_simps invalid_assn_def)
  by vcg'

  
(* Converting eoarray into slice, and back *)
definition "split_eoarray xs = RETURN (xs,length xs)"  
definition [llvm_inline]: "split_eoarray_impl p = Mreturn (p,p)"  

definition "combine_eoarray xs tag = doN {ASSERT (length xs = tag); RETURN xs}"  
definition [llvm_inline]: "combine_eoarray_impl p p' = Mreturn p"


lemmas split_eoarray_correct[refine_vcg] = vcg_of_RETURN_np[OF split_eoarray_def[THEN eq_reflection]]
lemmas combine_eoarray_correct[refine_vcg] = vcg_of_RETURN[OF combine_eoarray_def[THEN eq_reflection]]
   
  
sepref_register split_eoarray combine_eoarray

lemma split_eoarray_impl_hnr[sepref_fr_rules]: 
  "(split_eoarray_impl, split_eoarray) \<in> [\<lambda>_. True]\<^sub>c (eoarray_assn A)\<^sup>d \<rightarrow> eoarray_slice_assn A \<times>\<^sub>a woarray_slice_diff_assn [\<lambda>p (p1,p2). p1=p \<and> p2=p]\<^sub>c"
  apply sepref_to_hoare
  unfolding split_eoarray_impl_def eo_array_assn_to_slice split_eoarray_def
  by vcg'

  
lemma combine_eoarray_impl_hnr[sepref_fr_rules]:
  "(uncurry combine_eoarray_impl, uncurry combine_eoarray) 
    \<in> [\<lambda>(p1,p2). CP_cond (p1=p2)]\<^sub>c (eoarray_slice_assn A)\<^sup>d *\<^sub>a (woarray_slice_diff_assn)\<^sup>d \<rightarrow> eoarray_assn A [\<lambda>(p1,p2) p. p=p1]\<^sub>c"  
  apply sepref_to_hoare
  unfolding combine_eoarray_impl_def combine_eoarray_def CP_cond_def
  apply (subst eo_array_assn_to_slice)
  apply (clarsimp simp: refine_pw_simps invalid_assn_def)
  by vcg'

lemma split_woarray_rule[refine_vcg]: "split_woarray xs \<le> SPEC (\<lambda>(xs',tag). xs'=xs \<and> tag=length xs)"
  unfolding split_woarray_def by auto

lemma combine_woarray_rule[refine_vcg]: "tag=length xs \<Longrightarrow> combine_woarray xs tag \<le> SPEC (\<lambda>r. r=xs)"  
  unfolding combine_woarray_def by auto
  
  
experiment
begin

  definition "test_split_combine_woarray xs \<equiv> doN {
    (xs,tag) \<leftarrow> split_woarray xs;
    
    xs \<leftarrow> mop_list_set xs 2 True;
    
    xs \<leftarrow> combine_woarray xs tag;
  
    RETURN xs
  }"

  
  find_theorems CP_cond
  
  
  sepref_def test_split_combine_woarray_impl is test_split_combine_woarray :: "(woarray_assn bool1_assn)\<^sup>d \<rightarrow>\<^sub>a woarray_assn bool1_assn"
    unfolding test_split_combine_woarray_def
    apply (annot_snat_const "TYPE(64)")
    by sepref
  

  find_theorems eoarray_assn  snat_assn
    
  definition "test_split_combine_eoarray xs \<equiv> doN {
    (xs,tag) \<leftarrow> split_eoarray xs;
    
    xs \<leftarrow> mop_eo_set xs 2 True;
    
    xs \<leftarrow> combine_eoarray xs tag;
  
    RETURN xs
  }"

  
  find_theorems CP_cond
  
  
  sepref_def test_split_combine_eoarray_impl is test_split_combine_eoarray :: "(eoarray_assn bool1_assn)\<^sup>d \<rightarrow>\<^sub>a eoarray_assn bool1_assn"
    unfolding test_split_combine_eoarray_def
    apply (annot_snat_const "TYPE(64)")
    by sepref
    
    
    
end




lemma array_assn_to_slice: "array_assn A xs p = 
  (array_slice_assn A xs p ** woarray_slice_diff_assn (length xs) p)"  
  unfolding array_assn_def array_slice_assn_def
     array_assn_split hr_comp_def
  apply (clarsimp simp add: sep_algebra_simps fun_eq_iff)
  unfolding woarray_slice_diff_assn_def 
  apply (cases "xs=[]"; cases "p=null"; simp)
  subgoal by (auto simp: sep_algebra_simps)
  subgoal by (clarsimp simp: sep_algebra_simps)
  subgoal by (clarsimp simp: sep_algebra_simps)
  subgoal by (auto simp: list_rel_pres_length)
  done      




(* Converting narray into slice, and back *)
definition "split_array xs = RETURN (xs,length xs)"  
definition [llvm_inline]: "split_array_impl p = Mreturn (p,p)"  

definition "combine_array xs tag = doN {ASSERT (length xs = tag); RETURN xs}"  
definition [llvm_inline]: "combine_array_impl p p' = Mreturn p"

  
sepref_register split_array combine_array

term array_base_assn
find_theorems array_base_assn
  
lemma split_array_impl_hnr[sepref_fr_rules]: 
  "(split_array_impl, split_array) \<in> [\<lambda>_. True]\<^sub>c (array_assn A)\<^sup>d \<rightarrow> array_slice_assn A \<times>\<^sub>a woarray_slice_diff_assn [\<lambda>p (p1,p2). p1=p \<and> p2=p]\<^sub>c"
  apply sepref_to_hoare
  unfolding split_array_impl_def array_assn_to_slice split_array_def
  by vcg'

  
lemma combine_array_impl_hnr[sepref_fr_rules]:
  "(uncurry combine_array_impl, uncurry combine_array) 
    \<in> [\<lambda>(p1,p2). CP_cond (p1=p2)]\<^sub>c (array_slice_assn A)\<^sup>d *\<^sub>a (woarray_slice_diff_assn)\<^sup>d \<rightarrow> array_assn A [\<lambda>(p1,p2) p. p=p1]\<^sub>c"  
  apply sepref_to_hoare
  unfolding combine_array_impl_def combine_array_def CP_cond_def
  apply (subst array_assn_to_slice)
  apply (clarsimp simp: refine_pw_simps invalid_assn_def)
  by vcg'

  
experiment
begin

  definition "test_split_combine_array xs \<equiv> doN {
    (xs,tag) \<leftarrow> split_array xs;
    
    xs \<leftarrow> mop_list_set xs 2 True;
    
    xs \<leftarrow> combine_array xs tag;
  
    RETURN xs
  }"

  
  find_theorems CP_cond
  
  
  sepref_def test_split_combine_array_impl is test_split_combine_array :: "(array_assn bool1_assn)\<^sup>d \<rightarrow>\<^sub>a array_assn bool1_assn"
    unfolding test_split_combine_array_def
    apply (annot_snat_const "TYPE(64)")
    by sepref
  

end













  (* Adapted from lrat_isa/LRAT_Sepref_Base *)
  
  subsection \<open>More default initializer\<close>  
  
  lemma init_hnr[sepref_fr_rules]: "(uncurry0 (Mreturn init), uncurry0 (RETURN init)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
    apply sepref_to_hoare
    by vcg  
  
  lemma GEN_ALGO_is_init_pure: "GEN_ALGO dflt (is_init A) \<Longrightarrow> is_pure A"
    by (auto simp: is_init_def GEN_ALGO_def)  
  
  lemma drop_upd_first: "a<length xs \<Longrightarrow> (drop a xs)[0:=x] = x#drop (Suc a) xs"
    by (simp add: drop_Suc_nth) 
  
  
  (* More default initializer: The is_init is too weak, assuming pure assertions.
  
    We only need to be pure at init!
    Also, in typical cases, the assertion will only hold on the empty memory,
    allowing us to convert between assertion and empty memory.
  *)
  
  definition is_init' :: "('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> bool" 
    where "is_init' A i \<equiv> \<box> \<turnstile> A i init"
    
  lemma is_init_imp_init': "is_init A i \<Longrightarrow> is_init' A i"  
    unfolding is_init_def is_init'_def
    by (metis (full_types) entails_eq_iff pure_app_eq pure_the_pure pure_true_conv)
    
  lemma is_init'_id_assn[sepref_gen_algo_rules]: "GEN_ALGO init (is_init' id_assn)"
    by (auto simp: GEN_ALGO_def is_init'_def pure_def sep_algebra_simps)
  
  lemma is_init'_array_assn[sepref_gen_algo_rules]: "GEN_ALGO [] (is_init' (array_assn A))"
    apply (simp add: GEN_ALGO_def is_init'_def)
    unfolding array_assn_def hr_comp_def
    by fri
  
    
  definition is_init_eq :: "('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> bool" 
    where "is_init_eq A i \<equiv> \<forall>ii. A i ii = \<up>(ii=init)"
    
  lemma is_init_eq_imp_init': "is_init_eq A i \<Longrightarrow> is_init' A i"  
    unfolding is_init_eq_def is_init'_def 
    by (metis (full_types) entails_eq_iff pure_true_conv)

      
  lemma is_init_eq_imp_init'_GA: "GEN_ALGO x (is_init_eq A) \<Longrightarrow> GEN_ALGO x (is_init' A)"
    unfolding GEN_ALGO_def
    by (rule is_init_eq_imp_init')
  
    
        
  lemma is_init_eq_id_assn[sepref_gen_algo_rules]: "GEN_ALGO init (is_init_eq id_assn)"
    by (auto simp: GEN_ALGO_def is_init_eq_def pure_def sep_algebra_simps)
    
    
  lemma is_init_eq_array_assn[sepref_gen_algo_rules]: "GEN_ALGO [] (is_init_eq (array_assn A))"
    apply (simp add: GEN_ALGO_def is_init_eq_def)
    unfolding array_assn_def hr_comp_def
    unfolding LLVM_DS_NArray.narray_assn_def
    by (auto simp: entails_def sep_algebra_simps)
    
    
  definition [simp]: "mop_free_dflt iv x \<equiv> do { ASSERT (x=iv); RETURN () }"  
  
  lemma mop_free_dflt_rl[refine_vcg]: "x=iv \<Longrightarrow> mop_free_dflt iv x \<le> SPEC (\<lambda>_. True)" by simp
    
  context fixes iv begin
    sepref_register "mop_free_dflt iv"
  end
  
  lemma mop_free_dflt_hnr[sepref_fr_rules]:
    assumes "GEN_ALGO iv (is_init_eq A)"
    shows "(\<lambda>_. Mreturn (), PR_CONST (mop_free_dflt iv)) \<in> A\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  proof -
    from assms have [simp]: "A iv xs = (\<up>(xs=init))" for xs
      unfolding GEN_ALGO_def is_init_eq_def by auto
  
      
    show ?thesis
      supply [simp] = refine_pw_simps
      apply sepref_to_hoare
      by vcg
      
  qed
  
  subsection \<open>Default Option where init is default value\<close>
  
  
  locale dflt_option_init = dflt_option init A is_dflt for A is_dflt 
  begin
    
    lemma is_init_eqI[sepref_gen_algo_rules]:
      "GEN_ALGO None (is_init_eq option_assn)"
      unfolding GEN_ALGO_def is_init_eq_def option_assn_def
      by auto
      
    lemma is_init'I[sepref_gen_algo_rules]: "GEN_ALGO None (is_init' option_assn)"
      by (meson is_init_eqI is_init_eq_imp_init'_GA)  
  
  end  
  
  
  subsection \<open>More EO and WO Array\<close>


  subsubsection \<open>Helper Lemmas\<close>
  
    
  lemma sep_set_img_all_box[sep_algebra_simps]: "finite s \<Longrightarrow> (\<Union>*x\<in>s. \<box>) = \<box>"
    apply (induction s rule: finite_induct)
    by (auto)
    
  lemma list_oelem_assn_NoneI: "PRECOND (SOLVE_DEFAULT_AUTO (n=n')) \<Longrightarrow> \<box> \<turnstile> \<upharpoonleft>(list_assn (oelem_assn A)) (replicate n None) (replicate n' xs)"
    by (cases "n'=n"; simp add: sep_algebra_simps list_assn_def PRECOND_def SOLVE_DEFAULT_AUTO_def)
    
  lemma list_oelem_assn_initI:
    assumes "\<box> \<turnstile> A x init"
    shows "\<box> \<turnstile> \<upharpoonleft>(list_assn (oelem_assn (mk_assn A))) (replicate n (Some x)) (replicate n init)"  
    unfolding list_assn_def
    apply (simp add: sep_algebra_simps)
    using nao_repl_init_aux[where A="mk_assn A", simplified, OF assms]
    by blast
  
  
  lemma list_assn_None_emp_eq: "set xs \<subseteq> {None} 
    \<Longrightarrow> \<upharpoonleft>(list_assn (oelem_assn (mk_assn A))) xs xs' = \<up>(length xs = length xs')"
    unfolding PRECOND_def SOLVE_DEFAULT_AUTO_def
    apply (induction xs arbitrary: xs')
    subgoal for xs'
      by auto
    subgoal for a xs xs'
      apply (cases xs')
      apply (auto simp: sep_algebra_simps entails_def list_assn_cons1_conv)
      done
    done
  
    
    
    
  lemma nao_new_rule: "llvm_htriple 
    (\<upharpoonleft>snat.assn n ni) 
    (narray_new TYPE('a::llvm_rep) ni) 
    (\<lambda>ri. \<upharpoonleft>(Proto_EOArray.nao_assn A) (replicate n None) ri)"
    unfolding Proto_EOArray.nao_assn_def
    supply [fri_rules] = list_oelem_assn_NoneI
    by vcg
    
  

  subsubsection \<open>New\<close>
    
  text \<open>Create unowned elements\<close>
  definition op_eoarray_new :: "('a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn) \<Rightarrow> nat \<Rightarrow> 'a option list"
    where [simp]: "op_eoarray_new A n \<equiv> replicate n None"  
    
  context
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn"
  begin
    sepref_register "op_eoarray_new A"
    
    lemma op_eoarray_new_hnr[sepref_fr_rules]: "(narray_new TYPE('c), RETURN o PR_CONST (op_eoarray_new A)) \<in> snat_assn\<^sup>k \<rightarrow>\<^sub>a eoarray_assn A"
      unfolding eoarray_assn_def
      unfolding snat_rel_def snat.assn_is_rel[symmetric]
      apply sepref_to_hoare
      supply [vcg_rules] = nao_new_rule (* This rule clashes with other rules for narray_new, and is only resolved by backtracking. *)
      by (vcg)
    
    
  end  
  

  text \<open>Create default-initialized elements\<close>    
  definition [simp]: "op_woarray_replicate x n \<equiv> replicate n x"
  lemmas woarray_fold_custom_replicate = op_woarray_replicate_def[symmetric]
  
  lemma repl_in_list_rel_conv: "(replicate n a, replicate n' b) \<in> \<langle>R\<rangle>list_rel \<longleftrightarrow> n'=n \<and> (n=0 \<or> (a,b)\<in>R)"
    apply (induction n arbitrary: n')
    subgoal for n'
      apply (cases n')
      apply auto
      done
    subgoal for n n'
      apply (cases n')
      apply auto
      done
    done  
  
  
  (* Auxiliary Definition *)  
  definition [llvm_inline]: "woarray_new TYPE('a::llvm_rep) ni \<equiv> narray_new TYPE('a::llvm_rep) ni"  
    
  lemma woarray_assn_repl_init[vcg_rules]:
    assumes "PRECOND (SOLVE_DEFAULT_AUTO (\<box> \<turnstile> A x init))"
    shows "llvm_htriple 
      (\<upharpoonleft>snat.assn n ni) 
      (woarray_new TYPE('a::llvm_rep) ni) 
      (\<lambda>ri. (woarray_assn A) (replicate n x) ri)"
    unfolding woarray_new_def woarray_assn_def eoarray_assn_def Proto_EOArray.nao_assn_def hr_comp_def
    apply simp
    supply [fri_rules] = list_oelem_assn_initI[where A=A,OF assms[unfolded PRECOND_def SOLVE_DEFAULT_AUTO_def]]
    supply [simp] = repl_in_list_rel_conv
    by vcg
  
    
    
  
  context fixes x begin
  sepref_register "op_woarray_replicate x" 
  end
  
  lemma woarray_replicate_hnr[sepref_fr_rules]:
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn"
    assumes "GEN_ALGO x (is_init' A)"
    shows "(woarray_new TYPE('c), RETURN o PR_CONST (op_woarray_replicate x)) \<in> snat_assn\<^sup>k \<rightarrow>\<^sub>a woarray_assn A"
  proof -
  
    from assms have A[intro!]: "\<box> \<turnstile> A x init"
      by (simp add: GEN_ALGO_def is_init'_def)
    
    show ?thesis  
      unfolding snat_rel_def snat.assn_is_rel[symmetric]
      apply sepref_to_hoare
      apply vcg
      done
      
  qed
  
  
  
  
  
  subsubsection \<open>Free\<close>

  
  lemma eoarray_free_empty_rl[vcg_rules]: "llvm_htriple (eoarray_assn A xs xsi ** \<up>(set xs\<subseteq>{None})) (narray_free xsi) (\<lambda>_. \<box>)"
    unfolding eoarray_assn_def Proto_EOArray.nao_assn_def
    supply [simp] = list_assn_None_emp_eq
    by vcg

  (* Free if no elements owned *)    
  definition "mop_eoarray_free_empty xs \<equiv> doN {
    ASSERT (set xs \<subseteq> {None});
    RETURN ()
  }"
      
  sepref_register "mop_eoarray_free_empty"
  
  lemma mop_eoarray_free_empty_hnr[sepref_fr_rules]: 
    "(narray_free,mop_eoarray_free_empty) \<in> (eoarray_assn A)\<^sup>d \<rightarrow>\<^sub>a unit_assn"
    unfolding mop_eoarray_free_empty_def
    apply sepref_to_hoare
    apply (simp add: refine_pw_simps)
    by vcg
  
  lemma mop_eoarray_free_empty_rule[refine_vcg]: 
    "set xs \<subseteq> {None} \<Longrightarrow> mop_eoarray_free_empty xs \<le> SPEC (\<lambda>_. True)"  
    unfolding mop_eoarray_free_empty_def
    apply refine_vcg
    by auto
    
  (* Deep-Free wo-array *)    
  definition "mop_woarray_free l xs \<equiv> doN {
    ASSERT (l=length xs);
    xs \<leftarrow> mop_to_eo_conv xs;
  
    (_,xs) \<leftarrow> WHILEIT (\<lambda>(i,xs'). i\<le>l \<and> xs' = replicate i None @ drop i xs) 
      (\<lambda>(i,xs). i<l) (\<lambda>(i,xs). doN {
      (vi,xs) \<leftarrow> mop_eo_extract xs i;
      mop_free vi;
      ASSERT (i+1\<le>l);
      RETURN (i+1,xs)
    }) (0,xs);
    
    mop_eoarray_free_empty xs
  }"
    
  
  lemma mop_woarray_free_rl[refine_vcg]: "l=length xs \<Longrightarrow> mop_woarray_free l xs \<le> SPEC (\<lambda>_. True)"
    unfolding mop_woarray_free_def mop_free_def
    apply simp
    thm WHILEIT_rule
    apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda>(i,_). length xs - i)"])
    apply (simp_all add: nth_append)
    apply (clarsimp simp: list_update_append drop_upd_first replicate_append_same)
    by fastforce
    
  
  context
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn" and freeA
    assumes [sepref_frame_free_rules]: "MK_FREE A freeA"
  begin  
    
  sepref_definition woarray_free_impl_aux is "uncurry mop_woarray_free" :: "(snat_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (woarray_assn A)\<^sup>d \<rightarrow>\<^sub>a unit_assn"
    unfolding mop_woarray_free_def
    apply (annot_snat_const "TYPE('l)")
    by sepref
    
  end  
  
  sepref_register mop_woarray_free
  
  concrete_definition woarray_free_impl [llvm_code] is woarray_free_impl_aux_def
  
  context
    fixes A :: "'a \<Rightarrow> 'c::llvm_rep \<Rightarrow> assn" and freeA
    assumes F: "MK_FREE A freeA"
  begin  
  
    lemmas woarray_free_impl_hnr[sepref_fr_rules] = woarray_free_impl_aux.refine[OF F, unfolded woarray_free_impl.refine[OF F]]
  end


  subsubsection \<open>Conversion between EO and WO\<close>

  definition "oe_assn A \<equiv> \<upharpoonleft>(oelem_assn (mk_assn A))"  

  lemma eoarray_slice_assn_as_wo_oelem: "eoarray_slice_assn A = woarray_slice_assn (oe_assn A)"
    by (simp add: eoarray_slice_assn_def sao_assn_as_comp woarray_slice_assn_assn_as_comp_list oe_assn_def) 
  
  definition op_eo_slice_to_wo_oelem :: "'a list \<Rightarrow> 'a list" where [simp]: "op_eo_slice_to_wo_oelem xs \<equiv> xs"  
  definition op_wo_oelem_to_eo_slice :: "'a list \<Rightarrow> 'a list" where [simp]: "op_wo_oelem_to_eo_slice xs \<equiv> xs"  

    
  sepref_register op_eo_slice_to_wo_oelem op_wo_oelem_to_eo_slice
  lemma op_eo_slice_to_wo_oelem_hnr[sepref_fr_rules]: "(Mreturn,RETURN o op_eo_slice_to_wo_oelem) 
    \<in> [\<lambda>_. True]\<^sub>c (eoarray_slice_assn A)\<^sup>d \<rightarrow> woarray_slice_assn (oe_assn A) [\<lambda>p r. r=p]\<^sub>c"
    apply sepref_to_hoare
    unfolding eoarray_slice_assn_as_wo_oelem
    by vcg
    
  lemma op_wo_oelem_to_eo_slice_hnr[sepref_fr_rules]: "(Mreturn,RETURN o op_wo_oelem_to_eo_slice) 
    \<in> [\<lambda>_. True]\<^sub>c (woarray_slice_assn (oe_assn A))\<^sup>d \<rightarrow> eoarray_slice_assn A [\<lambda>p r. r=p]\<^sub>c"
    apply sepref_to_hoare
    unfolding eoarray_slice_assn_as_wo_oelem
    by vcg
  

  lemmas [sepref_fr_rules del] = mop_array_to_woarray_impl mop_woarray_to_array_impl
  
  lemma mop_array_to_woarray_impl'[sepref_fr_rules]: "CONSTRAINT is_pure A 
    \<Longrightarrow> (Mreturn,mop_array_to_woarray) \<in> [\<lambda>_. True]\<^sub>c (array_assn A)\<^sup>d \<rightarrow> woarray_assn A [\<lambda>p r. r=p]\<^sub>c"
    unfolding mop_array_to_woarray_def pure_woarray_assn_conv CONSTRAINT_def
    apply sepref_to_hoare
    apply vcg
    done
    
  lemma mop_woarray_to_array_impl'[sepref_fr_rules]: "CONSTRAINT is_pure A 
    \<Longrightarrow> (Mreturn,mop_woarray_to_array) \<in> [\<lambda>_. True]\<^sub>c (woarray_assn A)\<^sup>d \<rightarrow> array_assn A [\<lambda>p r. r=p]\<^sub>c"
    unfolding mop_array_to_woarray_def pure_woarray_assn_conv CONSTRAINT_def
    apply sepref_to_hoare
    apply vcg
    done
    


  lemma mop_array_to_woarray_rule[refine_vcg]: "mop_array_to_woarray xs \<le> SPEC (\<lambda>x. x=xs)" by auto
  lemma mop_woarray_to_array_rule[refine_vcg]: "mop_woarray_to_array xs \<le> SPEC (\<lambda>x. x=xs)" by auto
























definition op_cp_into_array :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where [simp]: "op_cp_into_array ini src = src"

definition "mop_cp_into_array2 ini src \<equiv> doN {
  l \<leftarrow> mop_list_length src;
  dst \<leftarrow> mop_list_replicate l ini;

  dst \<leftarrow> for 0 l (\<lambda>i dst. doN { x\<leftarrow>mop_list_get src i; mop_list_set dst i x }) dst;
  RETURN dst
}"

lemma mop_cp_into_array2_correct[refine_vcg]: "mop_cp_into_array2 i src \<le> SPEC (\<lambda>dst. dst=src)"
  unfolding mop_cp_into_array2_def
  apply (refine_vcg for_rule[where I="\<lambda>c dst. c\<le>length src \<and> length dst = length src \<and> (\<forall>i<c. dst!i=src!i)"])
  by (auto simp: nth_list_update list_eq_iff_nth_eq)

lemma mop_cp_into_array2_refine: "(mop_cp_into_array2,RETURN oo op_cp_into_array) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel" 
  apply (simp add: comp_def)
  apply (refine_vcg refine_IdI) 
  by (simp)
  
sepref_register mop_cp_into_array2 op_cp_into_array 

sepref_def al_cp_into_array is "uncurry mop_cp_into_array2" :: "[\<lambda>_. is_pure A]\<^sub>a A\<^sup>k *\<^sub>a (al_assn' TYPE('l::len2) A)\<^sup>k \<rightarrow> array_assn A" 
  unfolding mop_cp_into_array2_def 
  
  apply (subst for_by_while)
  apply (subst array_fold_custom_replicate)
  
  apply (annot_snat_const "TYPE('l)")
  
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref
  
lemmas [sepref_fr_rules] = al_cp_into_array.refine[FCOMP mop_cp_into_array2_refine]
  

find_theorems al_assn name: empty  
  
definition "mop_cp_into_al src len \<equiv> doN {
  ASSERT(len \<le> length src);
  
  dst \<leftarrow> mop_al_empty_sz len;

  dst \<leftarrow> for 0 len (\<lambda>i dst. doN { x\<leftarrow>mop_list_get src i; ASSERT(length dst+1 \<le> len); mop_list_append dst x }) dst;
  RETURN dst
}"

lemma mop_cp_into_al_correct[refine_vcg]: "\<lbrakk> len \<le> length src \<rbrakk> \<Longrightarrow> mop_cp_into_al src len \<le> SPEC (\<lambda>dst. dst=take len src)"
  unfolding mop_cp_into_al_def
  apply (refine_vcg for_rule[where I="\<lambda>c dst. dst = take c src"])
  apply (auto simp: nth_list_update nth_append take_Suc_conv_app_nth)  
  done

  
sepref_register mop_cp_into_al

sepref_def al_cp_into_al is "uncurry mop_cp_into_al" :: "[\<lambda>_. is_pure A \<and> 4 < LENGTH('l)]\<^sub>a (array_assn A)\<^sup>k *\<^sub>a (snat_assn' TYPE('l::len2))\<^sup>k \<rightarrow> al_assn' TYPE('l::len2) A" 
  unfolding mop_cp_into_al_def 
  
  apply (subst for_by_while)
  
  apply (annot_snat_const "TYPE('l)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref
    
  
  
  
  








end
