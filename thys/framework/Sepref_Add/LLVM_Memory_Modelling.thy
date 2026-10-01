section \<open>Memory Management for Modelling external Function Bindings\<close>
theory LLVM_Memory_Modelling
imports Isabelle_LLVM.IICF
begin
  
  subsection \<open>Internals\<close>  
  context begin  
    interpretation llvm_prim_mem_setup .

    lemma split_0_interval: "i<h \<Longrightarrow> [0..<h] = [0..<i]@i#[Suc i..<h]"
      by (metis upt_append upt_conv_Cons)
    lemma sepsum_list_distinct_elemwiseI: "\<lbrakk> sep_distinct as; sep_distinct bs; \<forall>a\<in>set as. \<forall>b\<in>set bs. a##b \<rbrakk> \<Longrightarrow> sepsum_list as ## sepsum_list bs"  
      apply (induction as)
      by (auto simp: disj_sepsum_list1)
    lemma llvm_blockvp_NULL[simp]: "llvm_blockvp xs PTR_NULL = sep_false"  
      unfolding llvm_blockvp_def by simp
    

    subsubsection \<open>Alloc\<close>          
    
    qualified definition llvmt_alloc_list :: "llvm_val list \<Rightarrow> nat llM" where "llvmt_alloc_list xs \<equiv> doM {
      Mmalloc xs
    }"
    
    qualified lemma llvmt_alloc_list_rule: "htriple \<box> (llvmt_alloc_list xs) (\<lambda>b. 
      EXACT (llvm_block b (length xs)) \<and>* EXACT (llvm_blockv xs b)
    )"
      unfolding llvmt_alloc_list_def
      (*apply rule*)
      supply [split] = prod.splits
      
      apply vcg_all
      apply vcg_normalize
      apply (simp add: sep_algebra_simps STATE_def POSTCOND_def flip: EXACT_split)
      apply (intro conjI)
      subgoal
        apply (clarsimp simp add: sep_algebra_simps disj_block_init)
        apply transfer
        apply (auto simp add: sep_algebra_simps llvm_\<alpha>m_def)
        done
      subgoal
        apply transfer'
        apply (auto simp: sep_algebra_simps llvm_\<alpha>b_def)
        done
      subgoal
        unfolding llvm_block_init_alt
        apply transfer
        apply (auto simp add: sep_algebra_simps llvm_\<alpha>m_def llvm_block_init_raw_def)
        subgoal
          apply (clarsimp 
            simp: fun_eq_iff llvm_\<alpha>m_def sep_algebra_simps
            split: addr.splits)
          done  
        subgoal for s r xs 
          by (auto 
            simp: fun_eq_iff llvm_\<alpha>b_def 
            dest:   )
        done
        
      done

    qualified definition llvmt_allocp_list :: "llvm_val list \<Rightarrow> _ llM"
      where "llvmt_allocp_list xs \<equiv> doM {
      b \<leftarrow> llvmt_alloc_list xs;
      Mreturn (PTR_ADDR (ADDR b 0))
    }"
  
    qualified lemma llvmt_allocp_list_rule: "htriple \<box> (llvmt_allocp_list xs) (\<lambda>p. 
      llvm_blockp p (length xs) \<and>* llvm_blockvp xs p
    )"
      unfolding llvm_blockp_def llvm_blockvp_def llvm_ptr_is_block_base_def llvm_ptr_the_block_def 
        llvmt_allocp_list_def
      supply [vcg_rules] = llvmt_alloc_list_rule
      apply vcg
      done

    subsubsection \<open>Load\<close>
        
    qualified definition "llvmt_load_from_block b i \<equiv> llvmt_load (ADDR b (int i))"
      
    qualified definition "llvm_blockv_gen xs b l h \<equiv> sepsum_list (map (\<lambda>i. llvm_ato (xs!i) (ADDR b (int i))) [l..<h])"
      
    qualified lemma llvm_blockv_eq_gen: "llvm_blockv xs b = llvm_blockv_gen xs b 0 (length xs)"
      unfolding llvm_blockv_def llvm_blockv_gen_def by simp
    

    qualified lemma block_distinct_aux1: "distinct is \<Longrightarrow> sep_distinct (map (\<lambda>i. llvm_ato (zi i) (ADDR b (int i))) is)"  
      apply (induction "is")
      apply auto
      using block_init_aux by blast
      
      
    qualified lemma block_distinct_aux2: "llvm_ato (xs ! i) (ADDR b (int i)) ## sepsum_list (map (\<lambda>i. llvm_ato (xs ! i) (ADDR b (int i))) [Suc i..<length xs])"  
      by (metis (full_types) Suc_n_not_le_n atLeastLessThan_iff atLeastLessThan_upt block_init_aux distinct_upt)
      
    qualified lemma block_distinct_aux3: "sepsum_list (map (\<lambda>i. llvm_ato (xs ! i) (ADDR b (int i))) [0..<i]) ## llvm_ato (xs ! i) (ADDR b (int i))"
      by (simp add: block_init_aux sep_disj_commute)
      
    qualified lemma block_distinct_aux4: "sepsum_list (map (\<lambda>i. llvm_ato (xs ! i) (ADDR b (int i))) [0..<i]) ## sepsum_list (map (\<lambda>i. llvm_ato (xs ! i) (ADDR b (int i))) [Suc i..<length xs])"  
      apply (rule sepsum_list_distinct_elemwiseI)  
      apply (auto simp: sep_algebra_simps block_distinct_aux1)
      done
    
    qualified lemmas block_distinct_aux = block_distinct_aux1 block_distinct_aux2 block_distinct_aux3 block_distinct_aux4  
      
    
    qualified lemma llvm_blockv_split_gen: "i<length xs 
      \<Longrightarrow> EXACT (llvm_blockv xs b) = ( EXACT (llvm_blockv_gen xs b 0 i) \<and>* EXACT (llvm_ato (xs!i) (ADDR b (int i))) \<and>* EXACT (llvm_blockv_gen xs b (Suc i) (length xs)) )"
      unfolding llvm_blockv_def llvm_blockv_gen_def
      by (simp add: split_0_interval block_distinct_aux EXACT_split )
      
      
    qualified lemma llvmt_load_from_block_rule: 
      "htriple 
        (EXACT (llvm_blockv xs b) \<and>* \<up>(i<length xs)) 
        (llvmt_load_from_block b i) 
        (\<lambda>r. \<up>(r=xs!i) \<and>* EXACT (llvm_blockv xs b))"
      unfolding llvmt_load_from_block_def
      supply [simp] = llvm_blockv_split_gen
      by vcg
      
      
    subsection \<open>Interface\<close>  
      
    text \<open>Pointer to memory block with specified content\<close>
    definition extmem_assn :: "'a::llvm_rep list \<Rightarrow> 'a ptr \<Rightarrow> assn" where
      "extmem_assn xs p \<equiv> llvm_blockp (the_raw_ptr p) (length xs) \<and>* llvm_blockvp (map to_val xs) (the_raw_ptr p)"
      
    definition extmem_alloc :: "'a::llvm_rep list \<Rightarrow> 'a ptr llM"
      where "extmem_alloc xs \<equiv> doM {
      p \<leftarrow> llvmt_allocp_list (map to_val xs);
      let p = LL_PTR p;
      Mreturn (from_val p)
    }"
    
    lemma extmem_alloc_rule[vcg_rules]: 
      "llvm_htriple 
        (\<box>) 
        (extmem_alloc xs) 
        (\<lambda>r. extmem_assn xs r)"
      unfolding extmem_alloc_def extmem_assn_def
      supply [vcg_rules] = llvmt_allocp_list_rule
      apply vcg
      done

    definition extmem_free :: "'a::llvm_rep ptr \<Rightarrow> unit llM" where
      "extmem_free p \<equiv> doM {
        p \<leftarrow> llvm_extract_ptr (to_val p);
        llvmt_freep p
      }"

    lemma extmem_free_rule[vcg_rules]:  
      "llvm_htriple (extmem_assn xs p) (extmem_free p) (\<lambda>_. \<box>)"
    proof -
    
      have [fri_rules]: "llvm_blockp pp (length xs) \<turnstile> llvm_blockp pp (length (map to_val xs))" for pp
        by simp
    
      show ?thesis
        unfolding extmem_free_def extmem_assn_def 
          llvm_extract_ptr_def to_val_ptr_def
        apply (cases p; simp)  
        subgoal for pp
          apply (cases "llvm_ptr_is_block_base pp")
          subgoal by vcg
        subgoal by (simp add: llvm_blockp_def)
        done  
      done
    qed  

    
        
    definition extmem_load :: "'a::llvm_rep ptr \<Rightarrow> nat \<Rightarrow> 'a llM" where "extmem_load p i \<equiv> doM {
      a \<leftarrow> llvm_extract_addr (to_val p);
      r \<leftarrow> llvmt_load_from_block (addr.block a) i;
      checked_from_val r
    }"
    
    lemma extmem_load_rule[vcg_rules]: 
      "llvm_htriple 
        (extmem_assn xs p \<and>* \<up>(i<length xs)) 
        (extmem_load p i) 
        (\<lambda>r. \<up>(r=xs!i) \<and>* extmem_assn xs p)"
      unfolding extmem_load_def extmem_assn_def llvm_extract_addr_def to_val_ptr_def llvm_blockvp_def
      apply (simp add: llvm_pto_def split!: llvm_ptr.splits)
      supply [simp] = llvm_ptr_the_block_def
      supply [vcg_rules] = llvmt_load_from_block_rule
      apply vcg
      done
    
  end



  subsection \<open>Encoding nat in block of words (needs not to be efficient, as only used for ex-proofs)\<close>

  context begin
    definition extmem_nat_assn :: "nat \<Rightarrow> 'l::len word ptr \<Rightarrow> llvm_amemory \<Rightarrow> bool"
      where "extmem_nat_assn n p \<equiv> EXS xs. extmem_assn xs p \<and>* \<up>(xs = replicate n 0 @ [1])"

    qualified definition extmem_obtain_nat_gen :: "'l::len word ptr \<Rightarrow> nat \<Rightarrow> nat llM"
       where "extmem_obtain_nat_gen p i \<equiv> Mwhile (\<lambda>i. doM { r\<leftarrow>extmem_load p i; Mreturn (r=0) }) (\<lambda>i. Mreturn (Suc i)) i"
    
    qualified lemma extmem_obtain_nat_gen_unfold: "extmem_obtain_nat_gen p i = doM {
      r\<leftarrow>extmem_load p i;
      if r=0 then extmem_obtain_nat_gen p (Suc i)
      else Mreturn i
    }"
      unfolding extmem_obtain_nat_gen_def
      apply (subst Mwhile_unfold)
      apply (simp cong: if_cong)
      done
    
    
    qualified lemma extmem_load_nat_rule: "llvm_htriple (extmem_nat_assn n p \<and>* \<up>(i\<le>n)) (extmem_load p i) (\<lambda>r. \<up>(r=0 \<and>i<n \<or> r=1\<and>i=n) \<and>* extmem_nat_assn n p)"  
      unfolding extmem_nat_assn_def
      supply [simp] = nth_append
      by vcg
      
      
    qualified lemma extmem_obtain_nat_gen_rule: "llvm_htriple (extmem_nat_assn n p \<and>* \<up>(i\<le>n)) (extmem_obtain_nat_gen p i) (\<lambda>n'. \<up>(n' = n) \<and>* extmem_nat_assn n p)"
      apply (cases "i\<le>n"; simp add: sep_algebra_simps)
    proof (induction rule: inc_induct)
      case base
      then show ?case
        apply (subst extmem_obtain_nat_gen_unfold)
        supply [vcg_rules] = extmem_load_nat_rule
        by vcg
    next
      case (step n)
      
      note [vcg_rules] = step.IH extmem_load_nat_rule

      
      from step.hyps show ?case 
        apply (subst extmem_obtain_nat_gen_unfold)
        by vcg
    qed      

    
    definition extmem_obtain_nat :: "'l::len word ptr \<Rightarrow> nat llM"
      where "extmem_obtain_nat p \<equiv> extmem_obtain_nat_gen p 0"
    definition extmem_alloc_nat :: "nat \<Rightarrow> 'l::len word ptr llM" 
      where "extmem_alloc_nat n \<equiv> extmem_alloc (replicate n 0 @ [1::_ word])"
  
    lemma extmem_alloc_nat_rule[vcg_rules]: "llvm_htriple \<box> (extmem_alloc_nat n) (extmem_nat_assn n)"
      unfolding extmem_alloc_nat_def extmem_nat_assn_def
      by vcg
    
    lemma extmem_free_nat_rule[vcg_rules]: "llvm_htriple (extmem_nat_assn n p) (extmem_free p) (\<lambda>_. \<box>)"
      unfolding extmem_nat_assn_def
      by vcg
            
    lemma extmem_obtain_nat_rule[vcg_rules]: 
      "llvm_htriple (extmem_nat_assn n p) (extmem_obtain_nat p) (\<lambda>n'. \<up>(n'=n) \<and>* extmem_nat_assn n p)"
      unfolding extmem_obtain_nat_def
      supply [vcg_rules] = extmem_obtain_nat_gen_rule
      by vcg
  
  end

end
