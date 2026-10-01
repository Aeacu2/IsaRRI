theory GMP_Bindings
imports Isabelle_LLVM.LLVM_DS_Block_Alloc 
  IICF_Uint_Ops LLVM_Memory_Modelling
  IICF_Flexible_Cast
  IICF_For_Loop_Add
  IICF_More_Array
begin







  attribute_setup vcg_rules_conj_elims = \<open>
    let
      fun norm_thm ctxt = HOLogic.conj_elims #>  map (Object_Logic.rulify ctxt)
    
    
      fun with_elim_conjs f thm context = let 
        val ctxt = Context.proof_of context 
        val thms = norm_thm ctxt thm
      in 
        fold f thms context 
      end
      
      val add_vcg_rules_conj = Thm.declaration_attribute (with_elim_conjs (Named_Theorems.add_thm @{named_theorems vcg_rules}))
      val del_vcg_rules_conj = Thm.declaration_attribute (with_elim_conjs (Named_Theorems.del_thm @{named_theorems vcg_rules}))
    in
      Attrib.add_del add_vcg_rules_conj del_vcg_rules_conj
    end
  \<close>



  (* Need injective function from int to 64 word list. 
     Exact encoding does not matter.   
     
     replicate n 0!
     
  *)

  definition "nat_to_list n \<equiv> replicate n 0"
  
  lemma inj_nat_to_list: "inj_on nat_to_list A"
    unfolding nat_to_list_def inj_on_def by auto
  
  definition "int_to_list \<equiv> nat_to_list o int_encode"
        
  lemma int_to_list_inj: "inj_on int_to_list A"
    unfolding int_to_list_def
    by (simp add: comp_inj_on inj_int_encode inj_nat_to_list)
    

  subsection \<open>Target Configuration\<close>
  text \<open>The following settings must match the GMP library you are linking to!\<close>
  
  type_synonym gmp_int_len = 32
  type_synonym gmp_long_len = 64
  type_synonym gmp_limb_len = 64
  type_synonym gmp_bitcnt_len = "64"
  type_synonym gmp_size_len = 64  \<comment> \<open>Length of \<open>size_t\<close> type\<close>
  
  abbreviation (input) "gmp_int_t \<equiv> TYPE(gmp_int_len)"
  abbreviation (input) "gmp_int_len \<equiv> LENGTH(gmp_int_len)"
  
  abbreviation (input) "gmp_long_t \<equiv> TYPE(gmp_long_len)"
  abbreviation (input) "gmp_long_len \<equiv> LENGTH(gmp_long_len)"

  abbreviation (input) "gmp_size_t \<equiv> TYPE(gmp_size_len)"
  abbreviation (input) "gmp_size_len \<equiv> LENGTH(gmp_size_len)"
  
    
  subsection \<open>MPZ-Structure\<close>
  type_synonym gmp_int_t = "gmp_int_len word"
  type_synonym gmp_long_t = "gmp_long_len word"
  type_synonym gmp_limb_t = "gmp_limb_len word"
  type_synonym gmp_bitcnt_t = "gmp_bitcnt_len word"
  type_synonym gmp_size_t = "gmp_size_len word"
  
  
  abbreviation (input) "gmp_uint_assn \<equiv> uint_assn' TYPE(gmp_int_len)"
  abbreviation (input) "gmp_sint_assn \<equiv> sint_assn' TYPE(gmp_int_len)"
  
  abbreviation (input) "gmp_ulong_assn \<equiv> uint_assn' TYPE(gmp_long_len)"
  abbreviation (input) "gmp_slong_assn \<equiv> sint_assn' TYPE(gmp_long_len)"
  
  abbreviation (input) "gmp_size_assn \<equiv> unat_assn' TYPE(gmp_size_len)"
  (*abbreviation (input) "gmp_ssize_assn \<equiv> snat_assn' TYPE(gmp_size_len)"*)

  abbreviation (input) "gmp_uint_rel \<equiv> uint_rel' TYPE(gmp_int_len)"
  abbreviation (input) "gmp_sint_rel \<equiv> sint_rel' TYPE(gmp_int_len)"
  
  abbreviation (input) "gmp_ulong_rel \<equiv> uint_rel' TYPE(gmp_long_len)"
  abbreviation (input) "gmp_slong_rel \<equiv> sint_rel' TYPE(gmp_long_len)"
  
  abbreviation (input) "gmp_usize_rel \<equiv> uint_rel' TYPE(gmp_size_len)"
  abbreviation (input) "gmp_ssize_rel \<equiv> sint_rel' TYPE(gmp_size_len)"
    
  datatype gmp_mpz_struct =
    GMP_MPZ_STRUCT 
      (gmp_mpz_alloc: gmp_int_t)
      (gmp_mpz_size: gmp_int_t)
      (gmp_mpz_d: "gmp_limb_t ptr")
      
  term struct_of
         
  
  instantiation gmp_mpz_struct :: llvm_rep
  begin
    definition "from_val \<equiv> (\<lambda>LL_STRUCT [a,b,c] \<Rightarrow> GMP_MPZ_STRUCT (from_val a) (from_val b) (from_val c))"
    definition "to_val \<equiv> (\<lambda>s. LL_STRUCT [
      to_val (gmp_mpz_alloc s), to_val (gmp_mpz_size s), to_val (gmp_mpz_d s)])"
      
    definition [simp]: "struct_of (_:: gmp_mpz_struct itself) 
      \<equiv> VS_STRUCT [struct_of TYPE(gmp_int_t), struct_of TYPE(gmp_int_t), struct_of TYPE(gmp_limb_t ptr)]"
    definition "init_gmp_mpz_struct \<equiv> GMP_MPZ_STRUCT init init init"
  
    instance
      apply standard
      unfolding from_val_gmp_mpz_struct_def to_val_gmp_mpz_struct_def struct_of_gmp_mpz_struct_def init_gmp_mpz_struct_def
      apply (simp_all add: fun_eq_iff split: prod.splits)
      subgoal for v by (cases v; auto)
      subgoal by (auto simp: to_val_word_def to_val_ptr_def null_def)
      done
  
  end

  lemma gmp_mpz_id_struct[ll_identified_structures]: "ll_is_identified_structure ''gmp_mpz_struct'' TYPE(gmp_mpz_struct)"
    unfolding ll_is_identified_structure_def
    apply (simp add: )
    done
    
  lemma [ll_struct_of]: "struct_of TYPE(gmp_mpz_struct) 
      = VS_STRUCT [struct_of TYPE(gmp_int_t), struct_of TYPE(gmp_int_t), struct_of TYPE(gmp_limb_t ptr)]"
    by simp    
    
  thm ll_identified_structures  
    
  thm ll_struct_of
  
  

  subsection \<open>Specifying basic witness-creation Operations\<close>  
  type_synonym mpz_t = "gmp_mpz_struct ptr"
  
  definition "ex_gmpz_assn i x \<equiv> extmem_nat_assn (int_encode i) (gmp_mpz_d x)"
  
  definition "ex_gmpz_make i \<equiv> doM {
    p \<leftarrow> extmem_alloc_nat (int_encode i);
    Mreturn (GMP_MPZ_STRUCT 0 0 p)
  }"
  
  definition "ex_gmpz_get s \<equiv> doM {
    n \<leftarrow> extmem_obtain_nat (gmp_mpz_d s);
    Mreturn (int_decode n)
  }"
  
  definition "ex_gmpz_set i s \<equiv> doM {
    extmem_free (gmp_mpz_d s);
    p \<leftarrow> extmem_alloc_nat (int_encode i);
    Mreturn (GMP_MPZ_STRUCT (gmp_mpz_alloc s) (gmp_mpz_size s) p)
  }"
      
  definition "ex_gmpz_free s \<equiv> doM {
    extmem_free (gmp_mpz_d s)
  }"
  
  consts 
    mpzs_assn ::  "int \<Rightarrow> gmp_mpz_struct \<Rightarrow> assn"
    internal_mpz_make :: "int \<Rightarrow> gmp_mpz_struct llM"
    internal_mpz_get :: "gmp_mpz_struct \<Rightarrow> int llM"
    internal_mpz_set :: "int \<Rightarrow> gmp_mpz_struct \<Rightarrow> gmp_mpz_struct llM"
    internal_mpz_free :: "gmp_mpz_struct \<Rightarrow> unit llM"
   
  specification (mpzs_assn internal_mpz_make internal_mpz_get internal_mpz_set internal_mpz_free) 
    internal_mpz_make_rule: "llvm_htriple \<box> (internal_mpz_make i) (\<lambda>r. mpzs_assn i r)"
    internal_mpz_free_rule: "llvm_htriple (mpzs_assn i s) (internal_mpz_free s) (\<lambda>r. \<box>)"
    internal_mpz_get_rule: "llvm_htriple (mpzs_assn i s) (internal_mpz_get s) (\<lambda>r. \<up>(r=i) \<and>* mpzs_assn i s)"
    internal_mpz_set_rule: "llvm_htriple (mpzs_assn i s) (internal_mpz_set i' s) (\<lambda>s'. mpzs_assn i' s')"
    apply (rule exI[where x=ex_gmpz_assn])
    apply (rule exI[where x=ex_gmpz_make])
    apply (rule exI[where x=ex_gmpz_get])
    apply (rule exI[where x=ex_gmpz_set])
    apply (rule exI[where x=ex_gmpz_free])
    unfolding ex_gmpz_assn_def ex_gmpz_make_def ex_gmpz_get_def ex_gmpz_set_def ex_gmpz_free_def 
    by vcg

  subsection \<open>Mpz-Assertions\<close>  
    
  text \<open>Pointer to mpz-structure\<close>
  definition "mpz_assn i p \<equiv> EXS s. \<upharpoonleft>ll_pto s p \<and>* mpzs_assn i s"  
        
  text \<open>Pointer to mpz-structure allocated as own block\<close>
  definition "mpzb_assn i p \<equiv> EXS s. \<upharpoonleft>ll_bpto s p \<and>* mpzs_assn i s"
  
  text \<open>mpzb_assn - mpz_assn\<close>
  definition "mpzbr_assn p \<equiv> \<up>(abase p) \<and>* llvm_prim_mem_setup.ll_malloc_tag 1 p"
  
  lemma mpzb_assn_open: "mpzb_assn i p = (mpz_assn i p \<and>* mpzbr_assn p)"
    unfolding mpzb_assn_def mpz_assn_def mpzbr_assn_def ll_bpto_def
    apply (simp add: sep_algebra_simps fun_eq_iff)
    apply (simp add: sep_conj_c) 
    done

  definition [llvm_inline]: "mpzb_open x \<equiv> Mreturn ()"  
  definition [llvm_inline]: "mpzb_close x \<equiv> Mreturn ()"  
    
  lemma mpzb_open_rule[vcg_rules]: 
    "llvm_htriple (mpzb_assn i p) (mpzb_open p) (\<lambda>_. mpz_assn i p \<and>* mpzbr_assn p)"
  and mpzb_close_rule[vcg_rules]: 
    "llvm_htriple (mpz_assn i p \<and>* mpzbr_assn p) (mpzb_close p) (\<lambda>_. mpzb_assn i p)"
    unfolding mpzb_assn_open mpzb_open_def mpzb_close_def
    by vcg
    

  subsection \<open>Specfying basic create/free Operations\<close>  
  (*
    Function: void mpz_init (mpz_t x)
    Initialize x, and set its value to 0.
  *)
  consts raw_mpz_init :: "mpz_t \<Rightarrow> unit llM"
  specification (raw_mpz_init)
    mpz_init_rl[vcg_rules]: "llvm_htriple (\<upharpoonleft>ll_pto s p) (raw_mpz_init p) (\<lambda>_. mpz_assn 0 p)"
  proof -
    interpret llvm_prim_mem_setup .
    show ?thesis  
      unfolding mpz_assn_def
      apply (rule exI[where x="\<lambda>p. doM { s\<leftarrow>internal_mpz_make 0; ll_store s p }"])
      supply [vcg_rules] = internal_mpz_make_rule
      by vcg
  qed  
  lemmas [llvm_code_raw] = LLVM_EXTERNALI[of raw_mpz_init "''__gmpz_init''"]
      
  (*
    Function: void mpz_clear (mpz_t x)
    Free the space occupied by x. Call this function for all mpz_t variables when you are done with them.
  *)
  consts raw_mpz_clear :: "mpz_t \<Rightarrow> unit llM"
  specification (raw_mpz_clear)
    mpz_clear_rl[vcg_rules]: "llvm_htriple (mpz_assn i p) (raw_mpz_clear p) (\<lambda>_. EXS s. \<upharpoonleft>ll_pto s p)"
  proof -
    interpret llvm_prim_mem_setup .
    show ?thesis  
      unfolding mpz_assn_def
      apply (rule exI[where x="\<lambda>p. doM { s\<leftarrow>ll_load p; internal_mpz_free s }"])
      supply [vcg_rules] = internal_mpz_free_rule
      by vcg
      
  qed  
  lemmas [llvm_code_raw] = LLVM_EXTERNALI[of raw_mpz_clear "''__gmpz_clear''"]
  
  subsubsection \<open>Constructor/Destructor for mpzb-assn\<close>  
  context
  begin
    interpretation llvm_prim_mem_setup .
  
    definition [llvm_inline]: "mpzb_new \<equiv> doM {
      p\<leftarrow>ll_balloc' TYPE(gmp_mpz_struct);
      raw_mpz_init p;
      Mreturn p
    }"
    
    lemma mpzb_new_rule[vcg_rules]: "llvm_htriple \<box> mpzb_new (mpzb_assn 0)"
      unfolding mpzb_new_def
      apply vcg 
      unfolding ll_bpto_def
      apply vcg 
      unfolding mpzb_assn_open mpzbr_assn_def
      by fri

    definition [simp]: "op_mpz_new \<equiv> (0::int)"  
    sepref_register op_mpz_new
    lemma mpzb_new_hnr[sepref_fr_rules]: "(uncurry0 mpzb_new, uncurry0 (RETURN op_mpz_new)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
      apply sepref_to_hoare
      by vcg
      
      
    definition [llvm_code,llvm_inline]: "mpzb_free p \<equiv> doM {
      raw_mpz_clear p;
      ll_free p
    }"
    
    lemma ll_free_base_pto_tag_rule: "llvm_htriple (\<up>(abase p) \<and>* \<upharpoonleft>ll_pto x p \<and>* ll_malloc_tag 1 p) (ll_free p) (\<lambda>_. \<box>)"
      apply (rule cons_rule[where P="\<upharpoonleft>ll_bpto x p" and Q="\<lambda>_. \<box>"])
      apply vcg
      unfolding ll_bpto_def 
      by simp_all
      
    
    lemma mpzb_free_rule[vcg_rules]: "llvm_htriple (mpzb_assn i p) (mpzb_free p) (\<lambda>_. \<box>)"
      unfolding mpzb_free_def mpzb_assn_open
      unfolding mpzbr_assn_def
      supply [vcg_rules] = ll_free_base_pto_tag_rule
      by vcg

    lemma mpzb_assn_free[sepref_frame_free_rules]: "MK_FREE mpzb_assn mpzb_free"
      apply rule by vcg
    
  end    
  
  
  subsection \<open>Setup for Specifying Operations\<close>  
    
  locale gmp_internals_loc begin
    definition "is_loader B ldb \<equiv> \<forall>b bi. llvm_htriple (B b bi) (ldb bi) (\<lambda>r. \<up>(r=b) \<and>* B b bi)"

    lemma is_loaderD: "is_loader B ldb \<Longrightarrow> llvm_htriple (B b bi) (ldb bi) (\<lambda>r. \<up>(r=b) \<and>* B b bi)"
      unfolding is_loader_def by blast
      
    
    definition "mpz_ld_mpz p \<equiv> doM { s\<leftarrow>ll_load p; internal_mpz_get s }"   
    lemma mpz_ld_mpz: "is_loader mpz_assn mpz_ld_mpz"
    proof -
      interpret llvm_prim_mem_setup .
      note [vcg_rules] = internal_mpz_get_rule
        show ?thesis
          unfolding mpz_ld_mpz_def mpz_assn_def is_loader_def
          by vcg
    qed
        
    definition mpz_ld_ui :: "gmp_long_t \<Rightarrow> int llM" where "mpz_ld_ui bi \<equiv> Mreturn (uint bi)"   
    lemma mpz_ld_ui: "is_loader uint_assn mpz_ld_ui"
      unfolding mpz_ld_ui_def is_loader_def uint_rel_def uint.rel_def br_def
      by vcg

    definition mpz_ld_si :: "gmp_long_t \<Rightarrow> int llM" where "mpz_ld_si bi \<equiv> Mreturn (sint bi)"   
    lemma mpz_ld_si: "is_loader sint_assn mpz_ld_si"
      unfolding mpz_ld_si_def is_loader_def sint_rel_def sint.rel_def br_def
      by vcg

    definition mpz_ld_bitcnt :: "gmp_bitcnt_t \<Rightarrow> nat llM" where "mpz_ld_bitcnt bi \<equiv> Mreturn (unat bi)"   
    lemma mpz_ld_bitcnt: "is_loader unat_assn mpz_ld_bitcnt"
      unfolding mpz_ld_bitcnt_def is_loader_def unat_rel_def unat.rel_def br_def
      by vcg
      
    definition "is_storer A st \<equiv> \<forall>ax a ai. llvm_htriple (A ax ai) (st a ai) (\<lambda>_::unit. A a ai)"
    lemma is_storerD: "is_storer A st \<Longrightarrow> llvm_htriple (A ax ai) (st a ai) (\<lambda>_::unit. A a ai)"
      unfolding is_storer_def by blast

    definition "mpz_st_mpz a ai \<equiv> doM {
      s\<leftarrow>ll_load ai;
      s \<leftarrow> internal_mpz_set a s;
      ll_store s ai
    }"  
    
    lemma mpz_st_mpz: "is_storer mpz_assn mpz_st_mpz"
    proof -
      interpret llvm_prim_mem_setup .
      note [vcg_rules] = internal_mpz_set_rule
        show ?thesis
          unfolding mpz_st_mpz_def mpz_assn_def is_storer_def
          by vcg
    qed
  end
  
  interpretation gmp_internals: gmp_internals_loc .

  locale llvm_external_axiom =
    fixes fi spec and name::string
    assumes satisfies_spec: "spec fi"
  begin  
    definition "op \<equiv> SOME fi. spec fi"
  
    lemmas code_printing_axiom[llvm_code_raw] = LLVM_EXTERNALI[of op name]
    
    lemma vcg_rule[vcg_rules_conj_elims]: "spec op"
      unfolding op_def apply (rule someI) by (rule satisfies_spec)
    
  end
  
  
    
  locale mpz_unary_spec =
    fixes A :: "'a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn"
    fixes ld :: "'ai \<Rightarrow> 'a llM"
    fixes P :: "'a \<Rightarrow> bool"
    fixes f :: "'a \<Rightarrow> int"
    
    assumes is_loader: "gmp_internals.is_loader A ld"
  begin  
    definition "internal_op_witness di ai \<equiv> doM {
      a\<leftarrow>ld ai;
      gmp_internals.mpz_st_mpz (f a) di
    }"
    
    abbreviation (input) "spec fi \<equiv> \<forall>xx di a ai. llvm_htriple (mpz_assn xx di \<and>* A a ai \<and>* \<up>(P a)) (fi di ai) (\<lambda>_::unit. mpz_assn (f a) di \<and>* A a ai)"

    lemmas rls = is_loader[THEN gmp_internals.is_loaderD] 
      gmp_internals.mpz_st_mpz[THEN gmp_internals.is_storerD]
    
    lemma internal_spec: "spec internal_op_witness"
      unfolding internal_op_witness_def
      supply [vcg_rules] = rls
      by vcg
        
  end

  
  locale mpz_unary_spec_axiom = mpz_unary_spec + fixes name::string begin
    sublocale llvm_external_axiom internal_op_witness spec name
      apply unfold_locales
      by (rule internal_spec)
  
    definition aop :: "int \<Rightarrow> 'a \<Rightarrow> int" where [simp]: "aop r a \<equiv> f a"  
    definition amop :: "int \<Rightarrow> 'a \<Rightarrow> int nres" where "amop r a \<equiv> doN {ASSERT (P a); RETURN (aop r a)}"
      
    lemmas [refine_vcg] = vcg_of_RETURN[OF amop_def]
    
    definition [llvm_inline]: "aop_impl r a \<equiv> doM {
      mpzb_open r;
      op r a;
      mpzb_close r;
      Mreturn r
    }"  

    sepref_register aop amop
    lemma aop_hnr[sepref_fr_rules]: 
      "(uncurry aop_impl, uncurry (RETURN oo PR_CONST aop)) 
        \<in> [\<lambda>(_,a). P a]\<^sub>a [\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a A\<^sup>k \<rightarrow> mpzb_assn [\<lambda>(r,_) r'. r'=r]\<^sub>c"
      apply sepref_to_hoare 
      unfolding aop_impl_def aop_def
      by vcg

    sepref_def amop_impl is "uncurry (PR_CONST amop)" :: "[\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a A\<^sup>k \<rightarrow> mpzb_assn [\<lambda>(r,_) r'. r'=r]\<^sub>c"
      unfolding amop_def PR_CONST_def
      by sepref

    find_theorems ASSERT SPEC  
                      
      
    lemma f_cr_refine: "f a = aop op_mpz_new a" by simp
      
    sepref_def f_cr_impl [llvm_inline] is "RETURN o f" :: "[P]\<^sub>a A\<^sup>k \<rightarrow> mpzb_assn"
      apply (subst f_cr_refine[abs_def])
      by sepref
      
  end


  locale mpz_unary_spec_m = mpz_unary_spec mpz_assn gmp_internals.mpz_ld_mpz
  begin
    abbreviation (input) "spec_m2 fi \<equiv> \<forall>a ai. llvm_htriple (mpz_assn a ai \<and>* \<up>(P a)) (fi ai ai) (\<lambda>_::unit. mpz_assn (f a) ai)"
    
    abbreviation (input) "spec_m fi \<equiv> spec_m2 fi \<and> spec fi"
    
    lemma internal_spec_m2: "spec_m2 internal_op_witness"
      unfolding internal_op_witness_def
      supply [vcg_rules] = rls
      by vcg
  
  end

  locale mpz_unary_spec_m_axiom = mpz_unary_spec_m + fixes name::string begin
    sublocale llvm_external_axiom internal_op_witness spec_m name
      apply unfold_locales
      by (intro conjI internal_spec internal_spec_m2)
  
      
    definition aop :: "int \<Rightarrow> int \<Rightarrow> int" where [simp]: "aop r a \<equiv> f a"  
    definition amop :: "int \<Rightarrow> int \<Rightarrow> int nres" where "amop r a \<equiv> doN {ASSERT (P a); RETURN (aop r a)}"
    lemmas [refine_vcg] = vcg_of_RETURN[OF amop_def]
      
    definition [llvm_inline]: "aop_impl r a \<equiv> doM {
      mpzb_open a;
      mpzb_open r;
      op r a;
      mpzb_close r;
      mpzb_close a;
      Mreturn r
    }"  

    sepref_register aop amop
    lemma aop_hnr[sepref_fr_rules]: 
      "(uncurry aop_impl, uncurry (RETURN oo PR_CONST aop)) 
        \<in> [\<lambda>(_,a). P a]\<^sub>a [\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn [\<lambda>(r,_) r'. r'=r]\<^sub>c"
      apply sepref_to_hoare 
      unfolding aop_impl_def aop_def
      by vcg
          
    sepref_def amop_impl is "uncurry (PR_CONST amop)" :: "[\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn [\<lambda>(r,_) r'. r'=r]\<^sub>c"
      unfolding amop_def PR_CONST_def
      by sepref
      
      
      
    lemma f_cr_refine: "f a = aop op_mpz_new a" by simp
      
    sepref_def f_cr_impl [llvm_inline] is "RETURN o f" :: "[P]\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn"
      apply (subst f_cr_refine[abs_def])
      by sepref
      

    definition aop_r :: "int \<Rightarrow> int" where [simp]: "aop_r a \<equiv> f a"  
    definition "amop_r a \<equiv> doN { ASSERT (P a); RETURN (aop_r a) }"
    lemmas [refine_vcg] = vcg_of_RETURN[OF amop_r_def]
      
    definition [llvm_inline]: "aop_r_impl a \<equiv> doM {
      mpzb_open a;
      op a a;
      mpzb_close a;
      Mreturn a
    }"  
      
    sepref_register aop_r amop_r
    lemma aop_r_hnr[sepref_fr_rules]: 
      "(aop_r_impl, (RETURN o PR_CONST aop_r)) 
        \<in> [P]\<^sub>a [\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d \<rightarrow> mpzb_assn [\<lambda>r r'. r'=r]\<^sub>c"
      apply sepref_to_hoare 
      unfolding aop_r_impl_def aop_r_def
      by vcg
            
    sepref_def amop_r_impl is "PR_CONST amop_r" :: "[\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d \<rightarrow> mpzb_assn [\<lambda>r r'. r'=r]\<^sub>c"
      unfolding amop_r_def PR_CONST_def
      by sepref

      
            
  end


  lemma rdomp_pure_partI: "pure_part (A x xi) \<Longrightarrow> rdomp A x"
    by (auto simp: rdomp_conv_pure_part)
  

  locale mpz_binary_spec =
    fixes A :: "'a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn" and lda
    fixes B :: "'b \<Rightarrow> 'bi::llvm_rep \<Rightarrow> assn" and ldb
    fixes P :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
    fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> int"
    
    fixes R :: "'r \<Rightarrow> 'ri::llvm_repv \<Rightarrow> assn"
    fixes fret :: "'a \<Rightarrow> 'b \<Rightarrow> 'r"
    fixes freti :: "'a \<Rightarrow> 'b \<Rightarrow> 'ri llM"
    
    assumes is_loader: "gmp_internals.is_loader A lda" "gmp_internals.is_loader B ldb"
    
    assumes fret_impl: "\<And>a b. \<lbrakk> rdomp A a; rdomp B b; P a b \<rbrakk> \<Longrightarrow> llvm_htriple \<box> (freti a b) (\<lambda>ri. R (fret a b) ri)"
    
    assumes R_pure[safe_constraint_rules]: "is_pure R"
    
  begin  
    
    definition freeR :: "'ri \<Rightarrow> unit llM" where [llvm_inline]: "freeR ri \<equiv> Mreturn ()"
    lemma freeR_rl[vcg_rules]: "llvm_htriple (R r ri) (freeR ri) (\<lambda>_. \<box>)"
      using R_pure unfolding freeR_def is_pure_def
      by vcg
      
  
    definition "internal_op_witness di ai bi \<equiv> doM {
      a \<leftarrow> lda ai;
      b \<leftarrow> ldb bi;
      gmp_internals.mpz_st_mpz (f a b) di;
      freti a b
    }"

    abbreviation (input) "spec fi \<equiv> \<forall>xx di a ai b bi. 
      llvm_htriple 
        (mpz_assn xx di \<and>* A a ai \<and>* B b bi \<and>* \<up>(P a b)) 
        (fi di ai bi) 
        (\<lambda>ri. R (fret a b) ri \<and>* mpz_assn (f a b) di \<and>* A a ai \<and>* B b bi)"

    lemmas rls = is_loader[THEN gmp_internals.is_loaderD] 
      gmp_internals.mpz_st_mpz[THEN gmp_internals.is_storerD]
      fret_impl
    
    lemma internal_spec: "spec internal_op_witness"
      unfolding internal_op_witness_def
      supply [vcg_rules] = rls
      apply (intro allI)
      apply (rule htriple_pure_preI)
      apply (elim pure_part_split_conj[elim_format] conjE)
      supply [simp] = rdomp_pure_partI
      by vcg
    
  end      

      
  locale mpz_binary_spec_mx = mpz_binary_spec where A=mpz_assn and lda=gmp_internals.mpz_ld_mpz begin
    abbreviation (input) "spec_mx2 fi \<equiv> \<forall>a ai b bi. 
      llvm_htriple (mpz_assn a ai \<and>* B b bi \<and>* \<up>(P a b)) (fi ai ai bi) (\<lambda>ri. R (fret a b) ri \<and>* mpz_assn (f a b) ai \<and>* B b bi)"
    
    abbreviation (input) "spec_mx fi \<equiv> spec fi \<and> spec_mx2 fi"
      
    lemma internal_spec_mx2: "spec_mx2 internal_op_witness"
      unfolding internal_op_witness_def
      apply (intro allI)
      apply (rule htriple_pure_preI)
      apply (elim pure_part_split_conj[elim_format] conjE)
      supply [simp] = rdomp_pure_partI
      supply [vcg_rules] = rls
      by vcg
  
  end

  locale mpz_binary_spec_xm = mpz_binary_spec where B=mpz_assn and ldb=gmp_internals.mpz_ld_mpz begin
    abbreviation (input) "spec_xm2 fi \<equiv> \<forall>a ai b bi. 
      llvm_htriple (A a ai \<and>* mpz_assn b bi \<and>* \<up>(P a b)) (fi bi ai bi) (\<lambda>ri. R (fret a b) ri \<and>* mpz_assn (f a b) bi \<and>* A a ai)"
    
    abbreviation (input) "spec_xm fi \<equiv> spec fi \<and> spec_xm2 fi"
      
    lemma internal_spec_xm2: "spec_xm2 internal_op_witness"
      unfolding internal_op_witness_def
      apply (intro allI)
      apply (rule htriple_pure_preI)
      apply (elim pure_part_split_conj[elim_format] conjE)
      supply [simp] = rdomp_pure_partI
      supply [vcg_rules] = rls
      by vcg
  
  end

  
  locale mpz_binary_spec_mm = 
     mpz_binary_spec_mx where B=mpz_assn and ldb=gmp_internals.mpz_ld_mpz
    + mpz_binary_spec_xm where A=mpz_assn and lda=gmp_internals.mpz_ld_mpz
  begin
        
    abbreviation (input) "spec_mm2 fi \<equiv> \<forall>a ai. 
      llvm_htriple (mpz_assn a ai \<and>* \<up>(P a a)) (fi ai ai ai) (\<lambda>ri. R (fret a a) ri \<and>* mpz_assn (f a a) ai)"

    abbreviation (input) "spec_xmm fi \<equiv> \<forall>xx di a ai. 
      llvm_htriple (mpz_assn xx di \<and>* mpz_assn a ai \<and>* \<up>(P a a)) (fi di ai ai) (\<lambda>ri. R (fret a a) ri \<and>* mpz_assn (f a a) di \<and>* mpz_assn a ai)"
      
          
    abbreviation (input) "spec_mm fi \<equiv> spec fi \<and> spec_xm2 fi \<and> spec_mx2 fi \<and> spec_mm2 fi \<and> spec_xmm fi"
  
    lemma internal_spec_mm2: "spec_mm2 internal_op_witness"
      unfolding internal_op_witness_def
      apply (intro allI)
      apply (rule htriple_pure_preI)
      apply (elim pure_part_split_conj[elim_format] conjE)
      supply [simp] = rdomp_pure_partI
      supply [vcg_rules] = rls
      by vcg

    lemma internal_spec_xmm: "spec_xmm internal_op_witness"
      unfolding internal_op_witness_def
      apply (intro allI)
      apply (rule htriple_pure_preI)
      apply (elim pure_part_split_conj[elim_format] conjE)
      supply [simp] = rdomp_pure_partI
      supply [vcg_rules] = rls
      by vcg
      
      
  end      

  
  locale mpz_binary_spec_nores_mx =
    fixes B :: "'b \<Rightarrow> 'bi::llvm_rep \<Rightarrow> assn" and ldb
    fixes P :: "int \<Rightarrow> 'b \<Rightarrow> bool"
    
    fixes R :: "('ri::llvm_repv \<times> 'r) set"
    fixes fret :: "int \<Rightarrow> 'b \<Rightarrow> 'r"
    fixes freti :: "int \<Rightarrow> 'b \<Rightarrow> 'ri"
    
    assumes is_loader: "gmp_internals.is_loader B ldb"
    
    assumes fret_impl: "\<lbrakk>rdomp B b; P a b\<rbrakk> \<Longrightarrow> (freti a b,fret a b) \<in> R"
    
  begin  
    
    definition "internal_op_witness ai bi \<equiv> doM {
      a \<leftarrow> gmp_internals.mpz_ld_mpz ai;
      b \<leftarrow> ldb bi;
      Mreturn (freti a b)
    }"

    abbreviation (input) "spec fi \<equiv> \<forall>a ai b bi. 
      llvm_htriple 
        (mpz_assn a ai \<and>* B b bi \<and>* \<up>(P a b)) 
        (fi ai bi) 
        (\<lambda>ri. \<up>((ri,fret a b)\<in>R) \<and>* mpz_assn a ai \<and>* B b bi)"

    lemmas rls = is_loader[THEN gmp_internals.is_loaderD] 
      gmp_internals.mpz_ld_mpz[THEN gmp_internals.is_loaderD]
    
    lemma internal_spec: "spec internal_op_witness"
      unfolding internal_op_witness_def
      supply [vcg_rules] = rls
      apply (intro allI)
      apply (rule htriple_pure_preI)
      apply (elim pure_part_split_conj[elim_format] conjE)
      supply [simp] = rdomp_pure_partI fret_impl
      apply vcg'
      done
    
  end      
  
  
  
  
  locale mpz_binary_spec_axiom = mpz_binary_spec + fixes name::string begin
    sublocale llvm_external_axiom internal_op_witness spec name
      apply unfold_locales
      by (rule internal_spec)

      
    definition aop :: "int \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> int" where [simp]: "aop r a b \<equiv> f a b"  
    definition amop :: "int \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> int nres" where "amop r a b \<equiv> doN {ASSERT (P a b); RETURN (aop r a b) }"  
    lemmas [refine_vcg] = vcg_of_RETURN[OF amop_def]
      
    definition [llvm_inline]: "aop_impl r a b \<equiv> doM {
      mpzb_open r;
      res\<leftarrow>op r a b;
      freeR res;
      mpzb_close r;
      Mreturn r
    }"  

    sepref_register aop amop
    lemma aop_hnr[sepref_fr_rules]: 
      "(uncurry2 aop_impl, uncurry2 (RETURN ooo PR_CONST aop)) 
        \<in> [\<lambda>((_,a),b). P a b]\<^sub>a [\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a A\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow> mpzb_assn [\<lambda>((r,_),_) r'. r'=r]\<^sub>c"
      apply sepref_to_hoare 
      unfolding aop_impl_def aop_def
      by vcg    

      
    sepref_def amop_impl [llvm_inline] is "uncurry2 (PR_CONST amop)" :: "[\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a A\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow> mpzb_assn [\<lambda>((r,_),_) r'. r'=r]\<^sub>c"
      unfolding amop_def PR_CONST_def
      by sepref
            
    lemma f_cr_refine: "f a b = aop op_mpz_new a b" by simp
      
    sepref_def aop_cr_impl [llvm_inline] is "uncurry (RETURN oo f)" :: "[\<lambda>(a,b). P a b]\<^sub>a A\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow> mpzb_assn"
      apply (subst f_cr_refine[abs_def])
      by sepref
      
        
  end
  
  locale mpz_binary_spec_mx_axiom = mpz_binary_spec_mx + fixes name::string begin
    sublocale llvm_external_axiom internal_op_witness spec_mx name
      apply unfold_locales
      by (rule internal_spec internal_spec_mx2 conjI)+

      
    definition aop :: "int \<Rightarrow> int \<Rightarrow> 'a \<Rightarrow> int" where [simp]: "aop r a b \<equiv> f a b"  
    definition amop :: "int \<Rightarrow> int \<Rightarrow> 'a \<Rightarrow> int nres" where "amop r a b \<equiv> doN {ASSERT (P a b); RETURN (aop r a b) }"  
    lemmas [refine_vcg] = vcg_of_RETURN[OF amop_def]
      
    definition [llvm_inline]: "aop_impl r a b \<equiv> doM {
      mpzb_open a;
      mpzb_open r;
      res\<leftarrow>op r a b;
      freeR res;
      mpzb_close r;
      mpzb_close a;
      Mreturn r
    }"  

    sepref_register aop amop
    lemma aop_hnr[sepref_fr_rules]: 
      "(uncurry2 aop_impl, uncurry2 (RETURN ooo PR_CONST aop)) 
        \<in> [\<lambda>((_,a),b). P a b]\<^sub>a [\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow> mpzb_assn [\<lambda>((r,_),_) r'. r'=r]\<^sub>c"
      apply sepref_to_hoare 
      unfolding aop_impl_def aop_def
      by vcg

    sepref_def amop_impl [llvm_inline] is "uncurry2 (PR_CONST amop)" :: "[\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow> mpzb_assn [\<lambda>((r,_),_) r'. r'=r]\<^sub>c"
      unfolding amop_def PR_CONST_def
      by sepref
                
      
    lemma f_cr_refine: "f a b = aop op_mpz_new a b" by simp
      
    sepref_def f_cr_impl [llvm_inline] is "uncurry (RETURN oo f)" :: "[\<lambda>(a,b). P a b]\<^sub>a mpzb_assn\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow> mpzb_assn"
      apply (subst f_cr_refine[abs_def])
      by sepref
      
    definition [simp]: "aop_r1 a b \<equiv> f a b"  
    definition "amop_r1 a b \<equiv> doN {ASSERT (P a b); RETURN (aop_r1 a b) }"
    lemmas [refine_vcg] = vcg_of_RETURN[OF amop_r1_def]
    
    
    definition [llvm_inline]: "aop_r1_impl a b \<equiv> doM {
      mpzb_open a;
      res\<leftarrow>op a a b;
      freeR res;
      mpzb_close a;
      Mreturn a
    }"  
      
    sepref_register aop_r1 amop_r1
    lemma aop_r1_impl_refine[sepref_fr_rules]: "(uncurry aop_r1_impl, uncurry (RETURN oo PR_CONST aop_r1)) \<in> [\<lambda>(a,b). P a b]\<^sub>a [\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a B\<^sup>k \<rightarrow> mpzb_assn [\<lambda>(a,_) r. r=a]\<^sub>c"
      apply sepref_to_hoare
      unfolding aop_r1_impl_def
      by vcg
        
    sepref_def amop_r1_impl is "uncurry (PR_CONST amop_r1)" :: "[\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a B\<^sup>k \<rightarrow> mpzb_assn [\<lambda>(a,_) r. r=a]\<^sub>c"
      unfolding amop_r1_def PR_CONST_def by sepref
      
  end
    
  locale mpz_binary_spec_xm_axiom = mpz_binary_spec_xm + fixes name::string begin
    sublocale llvm_external_axiom internal_op_witness spec_xm name
      apply unfold_locales
      by (rule internal_spec internal_spec_xm2 conjI)+

      
    definition aop :: "int \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> int" where [simp]: "aop r a b \<equiv> f a b"  
    definition amop :: "int \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> int nres" where "amop r a b \<equiv> doN {ASSERT (P a b); RETURN (aop r a b)}"  
    lemmas [refine_vcg] = vcg_of_RETURN[OF amop_def]
      
    definition [llvm_inline]: "aop_impl r a b \<equiv> doM {
      mpzb_open b;
      mpzb_open r;
      res\<leftarrow>op r a b;
      freeR res;
      mpzb_close r;
      mpzb_close b;
      Mreturn r
    }"  

    sepref_register aop amop
    lemma aop_hnr[sepref_fr_rules]: 
      "(uncurry2 aop_impl, uncurry2 (RETURN ooo PR_CONST aop)) 
        \<in> [\<lambda>((_,a),b). P a b]\<^sub>a [\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a A\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn [\<lambda>((r,_),_) r'. r'=r]\<^sub>c"
      apply sepref_to_hoare 
      unfolding aop_impl_def aop_def
      by vcg
          
    sepref_def amop_impl is "uncurry2 (PR_CONST amop)" :: "[\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a A\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn [\<lambda>((r,_),_) r'. r'=r]\<^sub>c"
      unfolding amop_def PR_CONST_def by sepref
      
      
      
    lemma f_cr_refine: "f a b = aop op_mpz_new a b" by simp
      
    sepref_def f_cr_impl [llvm_inline] is "uncurry (RETURN oo f)" :: "[\<lambda>(a,b). P a b]\<^sub>a A\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn"
      apply (subst f_cr_refine[abs_def])
      by sepref
      
    definition aop_r2 :: "'a \<Rightarrow> int \<Rightarrow> int" where [simp]: "aop_r2 a b \<equiv> f a b"  
    definition amop_r2 :: "'a \<Rightarrow> int \<Rightarrow> int nres" where  "amop_r2 a b \<equiv> doN {ASSERT (P a b); RETURN (aop_r2 a b) }"
    lemmas [refine_vcg] = vcg_of_RETURN[OF amop_r2_def]
    
    
    definition [llvm_inline]: "aop_r2_impl a b \<equiv> doM {
      mpzb_open b;
      res \<leftarrow> op b a b;
      freeR res;
      mpzb_close b;
      Mreturn b
    }"  
      
    sepref_register aop_r2 amop_r2
    lemma aop_r2_impl_refine[sepref_fr_rules]: "(uncurry aop_r2_impl, uncurry (RETURN oo PR_CONST aop_r2)) \<in> [\<lambda>(a,b). P a b]\<^sub>a [\<lambda>_. True]\<^sub>c A\<^sup>k *\<^sub>a mpzb_assn\<^sup>d \<rightarrow> mpzb_assn [\<lambda>(_,b) r. r=b]\<^sub>c"
      apply sepref_to_hoare
      unfolding aop_r2_impl_def
      by vcg
      
    sepref_def amop_r2_impl is "uncurry (PR_CONST amop_r2)" :: "[\<lambda>_. True]\<^sub>c A\<^sup>k *\<^sub>a mpzb_assn\<^sup>d \<rightarrow> mpzb_assn [\<lambda>(_,b) r. r=b]\<^sub>c"
      unfolding amop_r2_def PR_CONST_def by sepref
      
        
  end
  
  locale mpz_binary_spec_mm_axiom = mpz_binary_spec_mm + fixes name::string begin
    sublocale llvm_external_axiom internal_op_witness spec_mm name
      apply unfold_locales
      by (rule internal_spec internal_spec_mx2 internal_spec_xm2 internal_spec_mm2 internal_spec_xmm conjI)+

      
    definition aop :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where [simp]: "aop r a b \<equiv> f a b"  
    definition amop :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int nres" where "amop r a b \<equiv> doN {ASSERT (P a b); RETURN (aop r a b) }"  
    lemmas [refine_vcg] = vcg_of_RETURN[OF amop_def]
      
    definition [llvm_inline]: "aop_impl r a b \<equiv> doM {
      mpzb_open a;
      mpzb_open b;
      mpzb_open r;
      res \<leftarrow> op r a b;
      freeR res;
      mpzb_close r;
      mpzb_close b;
      mpzb_close a;
      Mreturn r
    }"  

    sepref_register aop amop
    lemma aop_hnr[sepref_fr_rules]: 
      "(uncurry2 aop_impl, uncurry2 (RETURN ooo PR_CONST aop)) 
        \<in> [\<lambda>((_,a),b). P a b]\<^sub>a [\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn [\<lambda>((r,_),_) r'. r'=r]\<^sub>c"
      apply sepref_to_hoare 
      unfolding aop_impl_def aop_def
      by vcg
          
    sepref_def amop_impl is "uncurry2 (PR_CONST amop)" :: "[\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn [\<lambda>((r,_),_) r'. r'=r]\<^sub>c"
      unfolding amop_def PR_CONST_def by sepref
      
    lemma f_cr_refine: "f a b = aop op_mpz_new a b" by simp
      
    sepref_def f_cr_impl [llvm_inline] is "uncurry (RETURN oo f)" :: "[\<lambda>(a,b). P a b]\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn"
      apply (subst f_cr_refine[abs_def])
      by sepref
      
    definition [simp]: "aop_r1 a b \<equiv> f a b"  
    definition [simp]: "aop_r2 a b \<equiv> f a b"  
    definition [simp]: "aop_r12 a \<equiv> f a a"  
    definition aop_xr12 :: "int \<Rightarrow> int \<Rightarrow> int" where [simp]: "aop_xr12 r a \<equiv> f a a"

    definition "amop_r1 a b \<equiv> doN {ASSERT (P a b); RETURN (aop_r1 a b)}"  
    definition "amop_r2 a b \<equiv> doN {ASSERT (P a b); RETURN (aop_r2 a b)}"  
    definition "amop_r12 a \<equiv> doN {ASSERT (P a a); RETURN (aop_r12 a)}"  
    definition "amop_xr12 r a \<equiv> doN {ASSERT (P a a); RETURN (aop_xr12 r a)}"  
    lemmas [refine_vcg] = vcg_of_RETURN[OF amop_r1_def] vcg_of_RETURN[OF amop_r2_def] vcg_of_RETURN[OF amop_r12_def] vcg_of_RETURN[OF amop_xr12_def]
    
        
    definition [llvm_inline]: "aop_r1_impl a b \<equiv> doM {
      mpzb_open a;
      mpzb_open b;
      res\<leftarrow>op a a b;
      freeR res;
      mpzb_close b;
      mpzb_close a;
      Mreturn a
    }"  
    definition [llvm_inline]: "aop_r2_impl a b \<equiv> doM {
      mpzb_open a;
      mpzb_open b;
      res\<leftarrow>op b a b;
      freeR res;
      mpzb_close b;
      mpzb_close a;
      Mreturn b
    }"  
    definition [llvm_inline]: "aop_r12_impl a \<equiv> doM {
      mpzb_open a;
      res\<leftarrow>op a a a;
      freeR res;
      mpzb_close a;
      Mreturn a
    }"  

    definition [llvm_inline]: "aop_xr12_impl r a \<equiv> doM {
      mpzb_open a;
      mpzb_open r;
      res\<leftarrow>op r a a;
      freeR res;
      mpzb_close r;
      mpzb_close a;
      Mreturn r
    }"  
    
          
    sepref_register aop_r1 aop_r2 aop_r12 aop_xr12 amop_r1 amop_r2 amop_r12 amop_xr12
    lemma aop_r1_impl_refine[sepref_fr_rules]: "(uncurry aop_r1_impl, uncurry (RETURN oo PR_CONST aop_r1)) \<in> [\<lambda>(a,b). P a b]\<^sub>a [\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn [\<lambda>(a,b) r. r=a]\<^sub>c"
      apply sepref_to_hoare
      unfolding aop_r1_impl_def
      by vcg
      
    lemma aop_r2_impl_refine[sepref_fr_rules]: "(uncurry aop_r2_impl, uncurry (RETURN oo PR_CONST aop_r2)) \<in> [\<lambda>(a,b). P a b]\<^sub>a [\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>d \<rightarrow> mpzb_assn [\<lambda>(a,b) r. r=b]\<^sub>c"
      apply sepref_to_hoare
      unfolding aop_r2_impl_def
      by vcg
      
    lemma aop_r12_impl_refine[sepref_fr_rules]: "(aop_r12_impl, (RETURN o PR_CONST aop_r12)) \<in> [\<lambda>a. P a a]\<^sub>a [\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d \<rightarrow> mpzb_assn [\<lambda>a r. r=a]\<^sub>c"
      apply sepref_to_hoare
      unfolding aop_r12_impl_def
      by vcg

    lemma aop_xr12_impl_refine[sepref_fr_rules]: "(uncurry aop_xr12_impl, uncurry (RETURN oo PR_CONST aop_xr12)) \<in> [\<lambda>(_,a). P a a]\<^sub>a [\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn [\<lambda>(r,a) r'. r'=r]\<^sub>c"
      apply sepref_to_hoare
      unfolding aop_xr12_impl_def
      by vcg
      
              
    sepref_def amop_r1_impl is "uncurry (PR_CONST amop_r1)" :: "[\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn [\<lambda>(a,b) r. r=a]\<^sub>c"
      unfolding amop_r1_def PR_CONST_def by sepref

    sepref_def amop_r2_impl is "uncurry (PR_CONST amop_r2)" :: "[\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>d \<rightarrow> mpzb_assn [\<lambda>(a,b) r. r=b]\<^sub>c"
      unfolding amop_r2_def PR_CONST_def by sepref
            
    sepref_def amop_r12_impl is "PR_CONST amop_r12" :: "[\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d \<rightarrow> mpzb_assn [\<lambda>a r. r=a]\<^sub>c"
      unfolding amop_r12_def PR_CONST_def by sepref

    sepref_def amop_xr12_impl is "uncurry (PR_CONST amop_xr12)" :: "[\<lambda>_. True]\<^sub>c mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn [\<lambda>(r,a) r'. r'=r]\<^sub>c"
      unfolding amop_xr12_def PR_CONST_def by sepref
      
            
  end
    
  
  locale mpz_binary_spec_nores_mx_axiom = mpz_binary_spec_nores_mx + fixes name::string begin
    sublocale llvm_external_axiom internal_op_witness spec name
      apply unfold_locales
      by (rule internal_spec internal_spec conjI)+
      
    definition "amop a b \<equiv> doN {ASSERT (P a b); RETURN (fret a b) }"  
    lemmas [refine_vcg] = vcg_of_RETURN[OF amop_def]
      
    definition [llvm_inline]: "aop_impl a b \<equiv> doM {
      mpzb_open a;
      res\<leftarrow>op a b;
      mpzb_close a;
      Mreturn res
    }"  

    lemma aop_hnr[sepref_fr_rules]: 
      "(uncurry aop_impl, uncurry (RETURN oo fret)) 
        \<in> [\<lambda>(a,b). P a b]\<^sub>a mpzb_assn\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow> pure R"
      apply sepref_to_hoare 
      unfolding aop_impl_def
      by vcg

    sepref_register amop  
      
    sepref_def amop_impl is "uncurry (PR_CONST amop)" :: "mpzb_assn\<^sup>k *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a pure R"
      supply [[sepref_register_adhoc fret]]
      unfolding amop_def PR_CONST_def by sepref
              
  end
  
  
  
  
  subsection \<open>GMP Function Bindings\<close>
  
  text \<open> 
    Interface to GMP. 
    The comments are copied from GNU MP 6.3.0 documentation \<^url>\<open>https://gmplib.org/manual/\<close>
  \<close>

  
      
  lemma ret_unit_impl: "llvm_htriple \<box> (return\<^sub>M ()) (unit_assn ())" unfolding pure_def by vcg
  
  
  
  lemmas mpz_internal_realize = 
    mpz_unary_spec_axiom.intro mpz_unary_spec.intro 
    mpz_unary_spec_m_axiom.intro mpz_unary_spec_m.intro

    mpz_binary_spec_axiom.intro mpz_binary_spec.intro 
    mpz_binary_spec_mx_axiom.intro mpz_binary_spec_mx.intro 
    mpz_binary_spec_xm_axiom.intro mpz_binary_spec_xm.intro 
    mpz_binary_spec_mm_axiom.intro mpz_binary_spec_mm.intro 
    mpz_binary_spec_nores_mx_axiom.intro mpz_binary_spec_nores_mx.intro 
      
    gmp_internals.mpz_ld_mpz gmp_internals.mpz_ld_ui gmp_internals.mpz_ld_si gmp_internals.mpz_ld_bitcnt
    
    gmp_internals.mpz_st_mpz
    
    
    ret_unit_impl pure_pure
    
  
  subsubsection \<open>More Initialization Functions\<close>
  
  (*
    Function: void mpz_init2 (mpz_t x, mp_bitcnt_t n)
    Initialize x, with space for n-bit numbers, and set its value to 0. Calling this function instead of mpz_init or mpz_inits is never necessary; reallocation is handled automatically by GMP when needed.
    
    While n defines the initial space, x will grow automatically in the normal way, if necessary, for subsequent values stored. mpz_init2 makes it possible to avoid such reallocations if a maximum size is known in advance.
    
    In preparation for an operation, GMP often allocates one limb more than ultimately needed. To make sure GMP will not perform reallocation for x, you need to add the number of bits in mp_limb_t to n.
  *)      
  consts raw_mpz_init2 :: "mpz_t \<Rightarrow> gmp_bitcnt_t \<Rightarrow> unit llM"
  specification (raw_mpz_init2)
    mpz_init2_rl[vcg_rules]: "llvm_htriple (\<upharpoonleft>ll_pto s p) (raw_mpz_init2 p n) (\<lambda>_. mpz_assn 0 p)"
  proof -
    interpret llvm_prim_mem_setup .
    show ?thesis  
      apply (rule exI[where x="\<lambda>p _. raw_mpz_init p"])
      by vcg
  qed  
  lemmas [llvm_code_raw] = LLVM_EXTERNALI[of raw_mpz_init2 "''__gmpz_init2''"]


  subsubsection \<open>Assignment Functions\<close>
  (*
    Function: void mpz_set (mpz_t rop, const mpz_t op)
    Function: void mpz_set_ui (mpz_t rop, unsigned long int op)
    Function: void mpz_set_si (mpz_t rop, signed long int op)
    
    Set the value of rop from op.
  *) find_consts name: top name: order term Orderings.top
  global_interpretation mpz_set: mpz_unary_spec_m_axiom Orderings.top id "''__gmpz_set''" defines raw_mpz_set = mpz_set.op by (rule mpz_internal_realize)+
  global_interpretation mpz_set_ui: mpz_unary_spec_axiom uint_assn gmp_internals.mpz_ld_ui Orderings.top id "''__gmpz_set_ui''" defines raw_mpz_set_ui = mpz_set_ui.op by (rule mpz_internal_realize)+
  global_interpretation mpz_set_si: mpz_unary_spec_axiom sint_assn gmp_internals.mpz_ld_si Orderings.top id "''__gmpz_set_si''" defines raw_mpz_set_si = mpz_set_si.op by (rule mpz_internal_realize)+
    
  
  subsubsection \<open>Combined Initialization and Assignment Functions\<close>
  (*
    Function: void mpz_init_set (mpz_t rop, const mpz_t op)
    Function: void mpz_init_set_ui (mpz_t rop, unsigned long int op)
    Function: void mpz_init_set_si (mpz_t rop, signed long int op)
    Initialize rop with limb space and set the initial numeric value from op.
  *)
  
  consts raw_mpz_init_set :: "mpz_t \<Rightarrow> mpz_t \<Rightarrow> unit llM"
  specification (raw_mpz_init_set)
    mpz_init_set_rl[vcg_rules]: "llvm_htriple 
      (\<upharpoonleft>ll_pto ds dp \<and>* mpz_assn i sp) 
      (raw_mpz_init_set dp sp) 
      (\<lambda>_. mpz_assn i dp \<and>* mpz_assn i sp)"
  proof -
    interpret llvm_prim_mem_setup .
    show ?thesis  
      unfolding mpz_assn_def
      apply (rule exI[where x="\<lambda>dp sp. doM { ds\<leftarrow>ll_load dp; ss\<leftarrow>ll_load sp; i\<leftarrow>internal_mpz_get ss; ds\<leftarrow>internal_mpz_make i; ll_store ds dp }"])
      supply [vcg_rules] = internal_mpz_get_rule internal_mpz_set_rule internal_mpz_make_rule
      by vcg
      
  qed  
  lemmas [llvm_code_raw] = LLVM_EXTERNALI[of raw_mpz_init_set "''__gmpz_init_set''"]
  
  consts raw_mpz_init_set_ui :: "mpz_t \<Rightarrow> gmp_long_t \<Rightarrow> unit llM"
  specification (raw_mpz_init_set_ui)
    mpz_init_set_ui_rl[vcg_rules]: "llvm_htriple 
      (\<upharpoonleft>ll_pto ds dp \<and>* uint_assn i ii) 
      (raw_mpz_init_set_ui dp ii) 
      (\<lambda>_. mpz_assn i dp)"
  proof -
    interpret llvm_prim_mem_setup .
    show ?thesis  
      unfolding mpz_assn_def
      apply (rule exI[where x="\<lambda>dp ii. doM { ds\<leftarrow>ll_load dp; ds\<leftarrow>internal_mpz_make (uint ii); ll_store ds dp }"])
      unfolding uint_rel_def uint.rel_def br_def pure_def
      supply [vcg_rules] = internal_mpz_get_rule internal_mpz_set_rule internal_mpz_make_rule
      by vcg
      
  qed  
  lemmas [llvm_code_raw] = LLVM_EXTERNALI[of raw_mpz_init_set_ui "''__gmpz_init_set_ui''"]

  consts raw_mpz_init_set_si :: "mpz_t \<Rightarrow> gmp_long_t \<Rightarrow> unit llM"
  specification (raw_mpz_init_set_si)
    mpz_init_set_si_rl[vcg_rules]: "llvm_htriple 
      (\<upharpoonleft>ll_pto ds dp \<and>* sint_assn i ii) 
      (raw_mpz_init_set_si dp ii) 
      (\<lambda>_. mpz_assn i dp)"
  proof -
    interpret llvm_prim_mem_setup .
    show ?thesis  
      unfolding mpz_assn_def
      apply (rule exI[where x="\<lambda>dp ii. doM { ds\<leftarrow>ll_load dp; ds\<leftarrow>internal_mpz_make (sint ii); ll_store ds dp }"])
      unfolding sint_rel_def sint.rel_def br_def pure_def
      supply [vcg_rules] = internal_mpz_get_rule internal_mpz_set_rule internal_mpz_make_rule
      by vcg
      
  qed  
  lemmas [llvm_code_raw] = LLVM_EXTERNALI[of raw_mpz_init_set_si "''__gmpz_init_set_si''"]
  
  context
  begin
    interpretation llvm_prim_mem_setup .
  
    definition [llvm_inline]: "mpzb_copy a \<equiv> doM {
      p\<leftarrow>ll_balloc' TYPE(gmp_mpz_struct);
      mpzb_open a;
      raw_mpz_init_set p a;
      mpzb_close a;
      mpzb_close p;
      Mreturn p
    }"
    
    lemma mpzb_copy_hnr[sepref_fr_rules]: "(mpzb_copy, RETURN o COPY) \<in> mpzb_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
      apply sepref_to_hoare
      unfolding mpzb_copy_def
      supply [simp] = ll_bpto_def mpzbr_assn_def
      by vcg

    definition mpz_from_int :: "int \<Rightarrow> int" where [simp]: "mpz_from_int x \<equiv> x"  
    sepref_register mpz_from_int
      
    definition [llvm_inline]: "mpzb_from_ui a \<equiv> doM {
      p\<leftarrow>ll_balloc' TYPE(gmp_mpz_struct);
      raw_mpz_init_set_ui p a;
      mpzb_close p;
      Mreturn p
    }"

    definition [llvm_inline]: "mpzb_from_si a \<equiv> doM {
      p\<leftarrow>ll_balloc' TYPE(gmp_mpz_struct);
      raw_mpz_init_set_si p a;
      mpzb_close p;
      Mreturn p
    }"

    lemma mpzb_from_ui_hnr[sepref_fr_rules]: "(mpzb_from_ui, RETURN o mpz_from_int) \<in> uint_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
      apply sepref_to_hoare unfolding mpzb_from_ui_def 
      supply [simp] = ll_bpto_def mpzbr_assn_def pure_def
      by vcg
            
    lemma mpzb_from_si_hnr[sepref_fr_rules]: "(mpzb_from_si, RETURN o mpz_from_int) \<in> sint_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
      apply sepref_to_hoare unfolding mpzb_from_si_def 
      supply [simp] = ll_bpto_def mpzbr_assn_def pure_def
      by vcg
      
    
    definition "mpz_from_uint_cast \<equiv> mpz_from_int o uint_uint_cast.op gmp_long_t"
    lemma mpz_from_uint_cast_refine: "(mpz_from_uint_cast, mpz_from_int)\<in>Id \<rightarrow> Id" unfolding mpz_from_uint_cast_def by auto 
    
    definition "mpz_from_sint_cast \<equiv> mpz_from_int o sint_sint_cast.op gmp_long_t"
    lemma mpz_from_sint_cast_refine: "(mpz_from_sint_cast, mpz_from_int)\<in>Id \<rightarrow> Id" unfolding mpz_from_sint_cast_def by auto 
      
    sepref_definition mpzb_from_ustd_int [llvm_inline] is "RETURN o mpz_from_uint_cast" :: "gmp_uint_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
      unfolding mpz_from_uint_cast_def by sepref
    
    sepref_definition mpzb_from_sstd_int [llvm_inline] is "RETURN o mpz_from_sint_cast" :: "gmp_sint_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
      unfolding mpz_from_sint_cast_def by sepref
    
    lemmas [sepref_fr_rules] = 
      mpzb_from_ustd_int.refine[FCOMP mpz_from_uint_cast_refine]
      mpzb_from_sstd_int.refine[FCOMP mpz_from_sint_cast_refine]
    
      
  end      
  
  
  subsubsection \<open>Conversion Functions\<close>  
  (*
    Function: unsigned long int mpz_get_ui (const mpz_t op)
    Function: signed long int mpz_get_si (const mpz_t op)
  *)
  
  text \<open>\<^bold>\<open>The binding states \<open>\<bar>i\<bar> mod 2\<^sup>6\<^sup>4\<close>.\<close> GMP's \<open>__gmpz_get_ui\<close> ignores the sign and returns the
    low limbs of the absolute value, so at \<open>i = -5\<close> it returns \<open>5\<close>; a contract \<open>r = i mod 2\<^sup>6\<^sup>4\<close>
    would claim \<open>2\<^sup>6\<^sup>4 - 5\<close>. A binding may state only facts true of the C function for every
    abstract input. \<open>mpz_to_uint\<close> carries the same \<open>\<bar>\<cdot>\<bar>\<close>; its non-negative corollary
    \<open>mpz_to_uint_correct'\<close> (below) is unaffected.\<close>
  consts raw_mpz_get_ui :: "mpz_t \<Rightarrow> gmp_long_t llM"
  specification (raw_mpz_get_ui)
    raw_mpz_get_ui_rl[vcg_rules]: "llvm_htriple
      (mpz_assn i ii)
      (raw_mpz_get_ui ii)
      (\<lambda>ri. EXS r. mpz_assn i ii \<and>* gmp_ulong_assn r ri \<and>* \<up>(r = \<bar>i\<bar> mod 2^LENGTH(gmp_long_len)))"
  proof -
    interpret llvm_prim_mem_setup .
    show ?thesis
      apply (rule exI[where x="\<lambda>ii. doM { i\<leftarrow>gmp_internals.mpz_ld_mpz ii; Mreturn (word_of_int \<bar>i\<bar>) }"])
      unfolding uint_rel_def uint.rel_def br_def pure_def
      supply [vcg_rules] = gmp_internals.mpz_ld_mpz[THEN gmp_internals.is_loaderD]
      supply [simp] = uint_word_of_int
      by vcg
      
  qed  
  lemmas [llvm_code_raw] = LLVM_EXTERNALI[of raw_mpz_get_ui "''__gmpz_get_ui''"]
  
  consts raw_mpz_get_si :: "mpz_t \<Rightarrow> gmp_long_t llM"
  specification (raw_mpz_get_si)
    raw_mpz_get_si_rl[vcg_rules]: "llvm_htriple 
      (mpz_assn i ii \<and>* \<up>(min_sint LENGTH(gmp_long_len)\<le>i \<and> i<max_sint LENGTH(gmp_long_len))) 
      (raw_mpz_get_si ii) 
      (\<lambda>ri. mpz_assn i ii \<and>* gmp_slong_assn i ri)"
  proof -
    interpret llvm_prim_mem_setup .
    show ?thesis  
      apply (rule exI[where x="\<lambda>ii. doM { i\<leftarrow>gmp_internals.mpz_ld_mpz ii; Mreturn (word_of_int i) }"])
      unfolding sint_rel_def sint.rel_def br_def pure_def
      supply [vcg_rules] = gmp_internals.mpz_ld_mpz[THEN gmp_internals.is_loaderD]
      supply [simp] = sint_of_int_eq min_sint_def max_sint_def
      by vcg
      
  qed  
  lemmas [llvm_code_raw] = LLVM_EXTERNALI[of raw_mpz_get_si "''__gmpz_get_si''"]
  
  (* TBD: conversion to double, string *)

  
  context
  begin
    interpretation llvm_prim_mem_setup .
  
    definition [llvm_inline]: "mpzb_get_ui a \<equiv> doM {
      mpzb_open a;
      r\<leftarrow>raw_mpz_get_ui a;
      mpzb_close a;
      Mreturn r
    }"

    definition [llvm_inline]: "mpzb_get_si a \<equiv> doM {
      mpzb_open a;
      r\<leftarrow>raw_mpz_get_si a;
      mpzb_close a;
      Mreturn r
    }"

    
    \<comment> \<open>\<open>\<bar>x\<bar>\<close>, not \<open>x\<close>: \<open>__gmpz_get_ui\<close> discards the sign (see the note at
       \<open>raw_mpz_get_ui\<close>). Agrees with the old definition on the whole nonneg range, which
       is all \<open>mpz_to_uint_correct'\<close> and every (currently zero) caller use.\<close>
    definition mpz_to_uint :: "int \<Rightarrow> int" where
      "mpz_to_uint x \<equiv> \<bar>x\<bar> mod max_uint LENGTH(gmp_long_len)"
      
    lemma mpz_to_uint_correct'[simp]: "\<lbrakk>0\<le>x; x<max_uint LENGTH(gmp_long_len)\<rbrakk> \<Longrightarrow> mpz_to_uint x = x"  
      unfolding mpz_to_uint_def by auto
      
    sepref_register mpz_to_uint
        
    lemma mpzb_get_ui_hnr[sepref_fr_rules]: "(mpzb_get_ui, RETURN o mpz_to_uint) \<in> mpzb_assn\<^sup>k \<rightarrow>\<^sub>a gmp_ulong_assn"
      apply sepref_to_hoare
      unfolding mpzb_get_ui_def mpz_to_uint_def
      supply [simp] = ll_bpto_def mpzbr_assn_def max_uint_def uint_rel_def uint.rel_def in_br_conv pure_def
      by vcg'

    definition mpz_to_sint :: "int \<Rightarrow> int nres" where 
      "mpz_to_sint x \<equiv> doN { 
        ASSERT (min_sint LENGTH(gmp_long_len) \<le> x \<and> x<max_sint LENGTH(gmp_long_len));
        RETURN x
      }"
      
    lemma mpz_to_sint_correct[refine_vcg]: 
      "\<lbrakk>min_sint LENGTH(gmp_long_len) \<le> x; x<max_sint LENGTH(gmp_long_len)\<rbrakk> 
      \<Longrightarrow> mpz_to_sint x \<le> SPEC (\<lambda>r. r = x)"  
      unfolding mpz_to_sint_def
      apply refine_vcg
      by auto
      
    sepref_register mpz_to_sint
        
    lemma mpzb_get_si_hnr[sepref_fr_rules]: "(mpzb_get_si, mpz_to_sint) \<in> mpzb_assn\<^sup>k \<rightarrow>\<^sub>a gmp_slong_assn"
      apply sepref_to_hoare
      unfolding mpzb_get_si_def mpz_to_sint_def
      supply [simp] = 
        ll_bpto_def mpzbr_assn_def min_sint_def max_sint_def sint_rel_def sint.rel_def 
        in_br_conv pure_def refine_pw_simps
      by vcg'
      
  end      
  
  
  
    
  
  subsubsection \<open>Arithmetic Functions\<close>
  
  (*  
  Function: void mpz_add (mpz_t rop, const mpz_t op1, const mpz_t op2)
  Function: void mpz_add_ui (mpz_t rop, const mpz_t op1, unsigned long int op2)
  Set rop to op1 + op2.
  *)
  
  global_interpretation mpz_add: mpz_binary_spec_mm_axiom Orderings.top "(+)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_add''" defines raw_mpz_add = mpz_add.op by (rule mpz_internal_realize)+
  global_interpretation mpz_add_ui: mpz_binary_spec_mx_axiom uint_assn gmp_internals.mpz_ld_ui Orderings.top "(+)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_add_ui''" defines raw_mpz_add_ui = mpz_add_ui.op by (rule mpz_internal_realize)+

  (*
  Function: void mpz_sub (mpz_t rop, const mpz_t op1, const mpz_t op2)
  Function: void mpz_sub_ui (mpz_t rop, const mpz_t op1, unsigned long int op2)
  Function: void mpz_ui_sub (mpz_t rop, unsigned long int op1, const mpz_t op2)
  Set rop to op1 − op2.
  *)
  
  global_interpretation mpz_sub: mpz_binary_spec_mm_axiom Orderings.top "(-)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_sub''" defines raw_mpz_sub = mpz_sub.op by (rule mpz_internal_realize)+
  global_interpretation mpz_sub_ui: mpz_binary_spec_mx_axiom uint_assn gmp_internals.mpz_ld_ui Orderings.top "(-)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_sub_ui''" defines raw_mpz_sub_ui = mpz_sub_ui.op by (rule mpz_internal_realize)+
  global_interpretation mpz_ui_sub: mpz_binary_spec_xm_axiom uint_assn gmp_internals.mpz_ld_ui Orderings.top "(-)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_ui_sub''" defines raw_mpz_ui_sub = mpz_ui_sub.op by (rule mpz_internal_realize)+

  (*
  Function: void mpz_mul (mpz_t rop, const mpz_t op1, const mpz_t op2)
  Function: void mpz_mul_si (mpz_t rop, const mpz_t op1, long int op2)
  Function: void mpz_mul_ui (mpz_t rop, const mpz_t op1, unsigned long int op2)  
  Set rop to op1 times op2.
  *)
  global_interpretation mpz_mul: mpz_binary_spec_mm_axiom Orderings.top "(*)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_mul''" defines raw_mpz_mul = mpz_mul.op by (rule mpz_internal_realize)+
  global_interpretation mpz_mul_si: mpz_binary_spec_mx_axiom sint_assn gmp_internals.mpz_ld_si Orderings.top "(*)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_mul_si''" defines raw_mpz_mul_si = mpz_mul_si.op by (rule mpz_internal_realize)+
  global_interpretation mpz_mul_ui: mpz_binary_spec_mx_axiom uint_assn gmp_internals.mpz_ld_ui Orderings.top "(*)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_mul_ui''" defines raw_mpz_mul_ui = mpz_mul_ui.op by (rule mpz_internal_realize)+
  
  
  
  
  (*
    Function: void mpz_mul_2exp (mpz_t rop, const mpz_t op1, mp_bitcnt_t op2)
    Set rop to op1 times 2 raised to op2. This operation can also be defined as a left shift by op2 bits.
  *)

  global_interpretation mpz_mul_2exp: mpz_binary_spec_mx_axiom unat_assn gmp_internals.mpz_ld_bitcnt Orderings.top "(<<)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_mul_2exp''" defines raw_mpz_mul_2exp = mpz_mul_2exp.op by (rule mpz_internal_realize)+

  (*
    Function: void mpz_neg (mpz_t rop, const mpz_t op)
    Set rop to −op.
  *)

  global_interpretation mpz_neg: mpz_unary_spec_m_axiom Orderings.top "uminus" "''__gmpz_neg''" defines raw_mpz_neg = mpz_neg.op by (rule mpz_internal_realize)+
      
  (*
    Function: void mpz_abs (mpz_t rop, const mpz_t op)
    Set rop to the absolute value of op.
  *)
  
  global_interpretation mpz_abs: mpz_unary_spec_m_axiom Orderings.top "abs" "''__gmpz_abs''" defines raw_mpz_abs = mpz_abs.op by (rule mpz_internal_realize)+


  subsubsection \<open>Division Functions\<close>
  
  find_theorems "_*_+_ = _"
  
  term "(div)" term "(mod)"
  term "(sdiv)" term "(smod)"
  
  find_theorems "_ mod _ \<ge> 0"
  
  thm floor_divide_of_int_eq
  
  lemma "a div b = \<lfloor>real_of_int a/real_of_int b\<rfloor>" for a b :: int
    by (metis floor_divide_of_int_eq)
  
  definition [simp]: "snd_notzero a b \<equiv> b\<noteq>0"  
    
  
  (*
    Division is undefined if the divisor is zero. Passing a zero divisor to the division or modulo functions (including the modular powering functions mpz_powm and mpz_powm_ui) will cause an intentional division by zero. This lets a program handle arithmetic exceptions in these functions the same way as for normal C int arithmetic.
    
    Function: void mpz_cdiv_q (mpz_t q, const mpz_t n, const mpz_t d)
    Function: void mpz_cdiv_r (mpz_t r, const mpz_t n, const mpz_t d)
    Function: void mpz_cdiv_qr (mpz_t q, mpz_t r, const mpz_t n, const mpz_t d)
    Function: unsigned long int mpz_cdiv_q_ui (mpz_t q, const mpz_t n, unsigned long int d)
    Function: unsigned long int mpz_cdiv_r_ui (mpz_t r, const mpz_t n, unsigned long int d)
    Function: unsigned long int mpz_cdiv_qr_ui (mpz_t q, mpz_t r, const mpz_t n, unsigned long int d)
    Function: unsigned long int mpz_cdiv_ui (const mpz_t n, unsigned long int d)
    Function: void mpz_cdiv_q_2exp (mpz_t q, const mpz_t n, mp_bitcnt_t b)
    Function: void mpz_cdiv_r_2exp (mpz_t r, const mpz_t n, mp_bitcnt_t b)
  *)
  (* tbd *)
    
  (*  
    Function: void mpz_fdiv_q (mpz_t q, const mpz_t n, const mpz_t d)
    Function: void mpz_fdiv_r (mpz_t r, const mpz_t n, const mpz_t d)
    
    Function: void mpz_fdiv_qr (mpz_t q, mpz_t r, const mpz_t n, const mpz_t d)
    Function: unsigned long int mpz_fdiv_q_ui (mpz_t q, const mpz_t n, unsigned long int d)
    Function: unsigned long int mpz_fdiv_r_ui (mpz_t r, const mpz_t n, unsigned long int d)
    Function: unsigned long int mpz_fdiv_qr_ui (mpz_t q, mpz_t r, const mpz_t n, unsigned long int d)
    Function: unsigned long int mpz_fdiv_ui (const mpz_t n, unsigned long int d)
    
    Function: void mpz_fdiv_q_2exp (mpz_t q, const mpz_t n, mp_bitcnt_t b)
    Function: void mpz_fdiv_r_2exp (mpz_t r, const mpz_t n, mp_bitcnt_t b)
  *)  
    
  global_interpretation mpz_fdiv_q: mpz_binary_spec_mm_axiom snd_notzero "(div)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_fdiv_q''" defines raw_mpz_fdiv_q = mpz_fdiv_q.op by (rule mpz_internal_realize)+
  global_interpretation mpz_fdiv_r: mpz_binary_spec_mm_axiom snd_notzero "(mod)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_fdiv_r''" defines raw_mpz_fdiv_r = mpz_fdiv_r.op by (rule mpz_internal_realize)+


  (*  
  lemma smod_mod_conv_aux: "\<lbrakk> 0<m; m<m' \<rbrakk> \<Longrightarrow> \<bar>a smod m\<bar> mod m' = \<bar>a smod m\<bar>" for a m m' :: int
    by (metis abs_ge_zero abs_of_pos abs_rem_rtz_lt dual_order.strict_trans less_int_code(1) zmod_trivial_iff)
  *)
    
  lemma mod_mod_aux: "\<lbrakk>rdomp (uint_assn' TYPE('l::len)) b; b\<noteq>0\<rbrakk> \<Longrightarrow> (word_of_int (a mod b) :: 'l word, a mod b) \<in> uint_rel"
    unfolding uint_rel_def uint.rel_def in_br_conv pure_def
    apply (clarsimp simp: uint_word_of_int rdomp_def sep_algebra_simps)
    by (metis dual_order.strict_trans int_sgn_cases m2pths(1) no_bintr_alt1 pos_mod_bound take_bit_int_eq_self uint_lt_0 uint_range')
    
  
  lemma mod_mod_aux_rl: "\<lbrakk>rdomp mpz_assn a; rdomp (uint_assn' TYPE('l::len)) b; b\<noteq>0\<rbrakk> \<Longrightarrow> llvm_htriple \<box> (return\<^sub>M ((word_of_int (a mod b))::'l word)) (uint_assn (a mod b))"
    unfolding uint_rel_def uint.rel_def in_br_conv pure_def
    apply vcg'
    apply (clarsimp simp: uint_word_of_int rdomp_def sep_algebra_simps)
    by (smt (verit, del_insts) mod_pos_pos_trivial pos_mod_bound pos_mod_sign uint_lt uint_lt_0)
  
  global_interpretation mpz_fdiv_q_ui: mpz_binary_spec_mx_axiom uint_assn gmp_internals.mpz_ld_ui snd_notzero "(div)" 
    gmp_ulong_assn "\<lambda>a b. a mod b" "\<lambda>a b. Mreturn (word_of_int (a mod b))" "''__gmpz_fdiv_q_ui''" defines raw_mpz_fdiv_q_ui = mpz_fdiv_q_ui.op 
    by (rule mpz_internal_realize mod_mod_aux_rl | assumption | simp)+

  global_interpretation mpz_fdiv_r_ui: mpz_binary_spec_mx_axiom uint_assn gmp_internals.mpz_ld_ui snd_notzero "(mod)" 
    gmp_ulong_assn "\<lambda>a b. a mod b" "\<lambda>a b. Mreturn (word_of_int (a mod b))" "''__gmpz_fdiv_r_ui''" defines raw_mpz_fdiv_r_ui = mpz_fdiv_r_ui.op 
    by (rule mpz_internal_realize mod_mod_aux_rl | assumption | simp)+


  definition fdiv_mod :: "int \<Rightarrow> int \<Rightarrow> int" where [simp]: "fdiv_mod a b \<equiv> a mod b"
  sepref_register fdiv_mod
        
  global_interpretation mpz_fdiv_ui: mpz_binary_spec_nores_mx_axiom gmp_ulong_assn gmp_internals.mpz_ld_ui snd_notzero gmp_ulong_rel "fdiv_mod" "\<lambda>a b. word_of_int (a mod b)" "''__gmpz_fdiv_ui''" defines raw_mpz_fdiv_ui = mpz_fdiv_ui.op
    by (rule mpz_internal_realize mod_mod_aux | assumption | simp)+
      
  definition fdiv_q_2exp :: "int \<Rightarrow> nat \<Rightarrow> int" where [simp]: "fdiv_q_2exp a n \<equiv> a div 2^n"
  definition fdiv_r_2exp :: "int \<Rightarrow> nat \<Rightarrow> int" where [simp]: "fdiv_r_2exp a n \<equiv> a mod 2^n"
  global_interpretation mpz_fdiv_q_2exp: mpz_binary_spec_mx_axiom unat_assn gmp_internals.mpz_ld_bitcnt snd_notzero fdiv_q_2exp unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_fdiv_q_2exp''" defines raw_mpz_fdiv_q_2exp = mpz_fdiv_q_2exp.op by (rule mpz_internal_realize)+
  global_interpretation mpz_fdiv_r_2exp: mpz_binary_spec_mx_axiom unat_assn gmp_internals.mpz_ld_bitcnt snd_notzero fdiv_r_2exp unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_fdiv_r_2exp''" defines raw_mpz_fdiv_r_2exp = mpz_fdiv_r_2exp.op by (rule mpz_internal_realize)+
  
    
  (*  
    Function: void mpz_tdiv_q (mpz_t q, const mpz_t n, const mpz_t d)
    Function: void mpz_tdiv_r (mpz_t r, const mpz_t n, const mpz_t d)
    
    Function: void mpz_tdiv_qr (mpz_t q, mpz_t r, const mpz_t n, const mpz_t d)
    Function: unsigned long int mpz_tdiv_q_ui (mpz_t q, const mpz_t n, unsigned long int d)
    Function: unsigned long int mpz_tdiv_r_ui (mpz_t r, const mpz_t n, unsigned long int d)
    Function: unsigned long int mpz_tdiv_qr_ui (mpz_t q, mpz_t r, const mpz_t n, unsigned long int d)
    Function: unsigned long int mpz_tdiv_ui (const mpz_t n, unsigned long int d)
    
    Function: void mpz_tdiv_q_2exp (mpz_t q, const mpz_t n, mp_bitcnt_t b)
    Function: void mpz_tdiv_r_2exp (mpz_t r, const mpz_t n, mp_bitcnt_t b)
  *)  
  global_interpretation mpz_tdiv_q: mpz_binary_spec_mm_axiom snd_notzero "(sdiv)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_tdiv_q''" defines raw_mpz_tdiv_q = mpz_tdiv_q.op by (rule mpz_internal_realize)+
  global_interpretation mpz_tdiv_r: mpz_binary_spec_mm_axiom snd_notzero "(smod)" unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_tdiv_r''" defines raw_mpz_tdiv_r = mpz_tdiv_r.op by (rule mpz_internal_realize)+

  lemma smod_mod_conv_aux: "\<lbrakk> 0<m; m<m' \<rbrakk> \<Longrightarrow> \<bar>a smod m\<bar> mod m' = \<bar>a smod m\<bar>" for a m m' :: int
    by (metis abs_ge_zero abs_of_pos abs_rem_rtz_lt dual_order.strict_trans less_int_code(1) zmod_trivial_iff)
  
  lemma smod_mod_aux: "\<lbrakk>rdomp (uint_assn' TYPE('l::len)) b; b \<noteq> 0\<rbrakk> \<Longrightarrow> (word_of_int \<bar>a smod b\<bar> :: 'l word, \<bar>a smod b\<bar>) \<in> uint_rel"  
    unfolding uint_rel_def uint.rel_def in_br_conv pure_def
    apply (clarsimp simp: uint_word_of_int rdomp_def sep_algebra_simps)
    apply (subst smod_mod_conv_aux)
    apply (simp add: less_le; fail)
    by auto
    
  lemma smod_mod_aux_rl: "\<lbrakk>rdomp mpz_assn a; rdomp (uint_assn' TYPE('l::len)) b; b\<noteq>0\<rbrakk> \<Longrightarrow> llvm_htriple \<box> (return\<^sub>M ((word_of_int \<bar>a smod b\<bar>)::'l word)) (uint_assn \<bar>a smod b\<bar>)"
    unfolding uint_rel_def uint.rel_def in_br_conv pure_def
    apply vcg'
    apply (clarsimp simp: uint_word_of_int rdomp_def sep_algebra_simps)
    apply (subst smod_mod_conv_aux)
    apply (simp add: less_le; fail)
    by (auto)
    
  
  definition tdiv_abs_smod :: "int \<Rightarrow> int \<Rightarrow> int" where [simp]: "tdiv_abs_smod a b \<equiv> \<bar>a smod b\<bar>"
  sepref_register tdiv_abs_smod
    
  global_interpretation mpz_tdiv_q_ui: mpz_binary_spec_mx_axiom uint_assn gmp_internals.mpz_ld_ui snd_notzero "(sdiv)" 
    "uint_assn' TYPE(gmp_long_len)" tdiv_abs_smod "\<lambda>a b. Mreturn (word_of_int \<bar>a smod b\<bar>)" "''__gmpz_tdiv_q_ui''" defines raw_mpz_tdiv_q_ui = mpz_tdiv_q_ui.op 
    by (rule mpz_internal_realize smod_mod_aux_rl | assumption | simp)+

  global_interpretation mpz_tdiv_r_ui: mpz_binary_spec_mx_axiom uint_assn gmp_internals.mpz_ld_ui snd_notzero "(smod)" 
    "uint_assn' TYPE(gmp_long_len)" tdiv_abs_smod "\<lambda>a b. Mreturn (word_of_int \<bar>a smod b\<bar>)" "''__gmpz_tdiv_r_ui''" defines raw_mpz_tdiv_r_ui = mpz_tdiv_r_ui.op 
    by (rule mpz_internal_realize smod_mod_aux_rl | assumption | simp)+
    
    
  global_interpretation mpz_tdiv_ui: mpz_binary_spec_nores_mx_axiom gmp_ulong_assn gmp_internals.mpz_ld_ui snd_notzero gmp_ulong_rel tdiv_abs_smod "\<lambda>a b. word_of_int (\<bar>a smod b\<bar>)" "''__gmpz_tdiv_ui''" defines raw_mpz_tdiv_ui = mpz_tdiv_ui.op
    by (rule mpz_internal_realize smod_mod_aux | assumption | simp)+
    
      
  
  definition tdiv_q_2exp :: "int \<Rightarrow> nat \<Rightarrow> int" where [simp]: "tdiv_q_2exp a n \<equiv> a sdiv 2^n"
  definition tdiv_r_2exp :: "int \<Rightarrow> nat \<Rightarrow> int" where [simp]: "tdiv_r_2exp a n \<equiv> a smod 2^n"
  global_interpretation mpz_tdiv_q_2exp: mpz_binary_spec_mx_axiom unat_assn gmp_internals.mpz_ld_bitcnt snd_notzero tdiv_q_2exp unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_tdiv_q_2exp''" defines raw_mpz_tdiv_q_2exp = mpz_tdiv_q_2exp.op by (rule mpz_internal_realize)+
  global_interpretation mpz_tdiv_r_2exp: mpz_binary_spec_mx_axiom unat_assn gmp_internals.mpz_ld_bitcnt snd_notzero tdiv_r_2exp unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_tdiv_r_2exp''" defines raw_mpz_tdiv_r_2exp = mpz_tdiv_r_2exp.op by (rule mpz_internal_realize)+
    
  
        

  subsubsection \<open>Miscellaneous\<close>
  (* GMP's size_t mpz_sizeinbase (const mpz_t op, int base): the number of digits of |op| in the
   given base (2 to 62). The result is exact when base is a power of 2 and may be one too big
   otherwise; for op = 0 it is 1. In base 2 it is the position of the most significant 1 bit,
   counting from 1. *)
  text \<open>Note: the base-agnostic rule over-approximates this function (any \<open>r \<ge> 1\<close>). A fully
    precise characterization is impossible as an UNCONDITIONAL total-correctness spec: the
    digit count must fit a \<open>size_t\<close>, but the abstract integer is unbounded — see the
    base-2 rule below, whose upper-bound conjunct is guarded for exactly this reason.\<close>

  text \<open>Pure model bit length, used ONLY as the specification witness for
    \<open>raw_mpz_sizeinbase\<close> below (it has no code role): the least \<open>r\<close> with
    \<open>\<bar>i\<bar> < 2 ^ r\<close> (with \<open>r = 1\<close> at \<open>i = 0\<close>, matching GMP), SATURATED to \<open>1\<close> outside the
    \<open>size_t\<close>-representable range so the witness is total and never word-wraps.\<close>
  definition sizeinbase2_wit :: "int \<Rightarrow> nat" where
    "sizeinbase2_wit i \<equiv>
       if \<bar>i\<bar> < 2 ^ (max_unat gmp_size_len - 1)
       then (if i = 0 then 1 else (LEAST r. \<bar>i\<bar> < 2 ^ r))
       else 1"

  text \<open>\<^bold>\<open>Numerals\<close>: \<open>max_unat_def\<close> must not be in a simp or auto set whose goal contains
    \<open>2 ^ (max_unat \<dots> - 1)\<close>, since the simplifier then tries to evaluate \<open>2^(2^64-1)\<close> as a
    numeral.\<close>

  lemma sizeinbase2_wit_ex:
    fixes i :: int
    shows "i \<noteq> 0 \<Longrightarrow> \<exists>r. \<bar>i\<bar> < 2 ^ r"
  proof -
    have "nat \<bar>i\<bar> < 2 ^ nat \<bar>i\<bar>" by (rule less_exp)
    hence "int (nat \<bar>i\<bar>) < int (2 ^ nat \<bar>i\<bar>)" by (simp only: of_nat_less_iff)
    moreover have "int (nat \<bar>i\<bar>) = \<bar>i\<bar>" by simp
    moreover have "int (2 ^ nat \<bar>i\<bar>) = 2 ^ nat \<bar>i\<bar>" by simp
    ultimately have "\<bar>i\<bar> < 2 ^ nat \<bar>i\<bar>" by simp
    thus ?thesis by blast
  qed

  lemma sizeinbase2_least_ne0:
    fixes i :: int
    assumes nz: "i \<noteq> 0"
    shows "(LEAST r. \<bar>i\<bar> < 2 ^ r) \<noteq> 0"
  proof -
    have PL: "\<bar>i\<bar> < 2 ^ (LEAST r. \<bar>i\<bar> < 2 ^ r)"
      using LeastI_ex[OF sizeinbase2_wit_ex[OF nz]] .
    have P0: "\<not> \<bar>i\<bar> < 2 ^ (0::nat)" using nz by simp
    show ?thesis using PL P0 by metis
  qed

  lemma sizeinbase2_wit_ge1: "1 \<le> sizeinbase2_wit i"
  proof (cases "\<bar>i\<bar> < 2 ^ (max_unat gmp_size_len - 1) \<and> i \<noteq> 0")
    case True
    hence "sizeinbase2_wit i = (LEAST r. \<bar>i\<bar> < 2 ^ r)"
      unfolding sizeinbase2_wit_def by simp
    thus ?thesis using sizeinbase2_least_ne0 True by (simp add: Suc_le_eq)
  next
    case False
    thus ?thesis unfolding sizeinbase2_wit_def by auto
  qed

  lemma sizeinbase2_wit_lt: "sizeinbase2_wit i < max_unat gmp_size_len"
  proof -
    have mu1: "(1::nat) < max_unat gmp_size_len"
      unfolding max_unat_def by simp
    show ?thesis
    proof (cases "\<bar>i\<bar> < 2 ^ (max_unat gmp_size_len - 1) \<and> i \<noteq> 0")
      case True
      hence "(LEAST r. \<bar>i\<bar> < 2 ^ r) \<le> max_unat gmp_size_len - 1"
        by (intro Least_le) simp
      moreover from True have "sizeinbase2_wit i = (LEAST r. \<bar>i\<bar> < 2 ^ r)"
        unfolding sizeinbase2_wit_def by simp
      ultimately show ?thesis using mu1 by linarith
    next
      case False
      hence "sizeinbase2_wit i = 1"
        unfolding sizeinbase2_wit_def by auto
      thus ?thesis using mu1 by simp
    qed
  qed

  lemma sizeinbase2_wit_lower:
    fixes i :: int
    assumes nz: "i \<noteq> 0"
    shows "2 ^ (sizeinbase2_wit i - 1) \<le> \<bar>i\<bar>"
  proof (cases "\<bar>i\<bar> < 2 ^ (max_unat gmp_size_len - 1)")
    case True
    let ?r = "LEAST r. \<bar>i\<bar> < 2 ^ r"
    have r1: "?r \<noteq> 0" by (rule sizeinbase2_least_ne0[OF nz])
    have "\<not> \<bar>i\<bar> < 2 ^ (?r - 1)"
      by (rule not_less_Least) (use r1 in simp)
    moreover from True nz have "sizeinbase2_wit i = ?r"
      unfolding sizeinbase2_wit_def by simp
    ultimately show ?thesis by simp
  next
    case False
    hence ge: "(2::int) ^ (max_unat gmp_size_len - 1) \<le> \<bar>i\<bar>" by simp
    have "(1::int) \<le> 2 ^ (max_unat gmp_size_len - 1)" by simp
    hence "(1::int) \<le> \<bar>i\<bar>" using ge by linarith
    moreover from False have "sizeinbase2_wit i = 1"
      unfolding sizeinbase2_wit_def by simp
    ultimately show ?thesis by simp
  qed

  lemma sizeinbase2_wit_zero: "i = 0 \<Longrightarrow> sizeinbase2_wit i = 1"
    unfolding sizeinbase2_wit_def by simp

  lemma sizeinbase2_wit_upper:
    fixes i :: int
    assumes g: "\<bar>i\<bar> < 2 ^ (max_unat gmp_size_len - 1)"
    shows "\<bar>i\<bar> < 2 ^ sizeinbase2_wit i"
  proof (cases "i = 0")
    case True
    thus ?thesis using g unfolding sizeinbase2_wit_def by simp
  next
    case False
    have "\<bar>i\<bar> < 2 ^ (LEAST r. \<bar>i\<bar> < 2 ^ r)"
      using LeastI_ex[OF sizeinbase2_wit_ex[OF False]] .
    thus ?thesis using g False unfolding sizeinbase2_wit_def by simp
  qed

  lemma sizeinbase2_wit_unat:
    "unat (word_of_nat (sizeinbase2_wit i) :: gmp_size_t) = sizeinbase2_wit i"
  proof -
    have "sizeinbase2_wit i < 2 ^ LENGTH(gmp_size_len)"
      using sizeinbase2_wit_lt unfolding max_unat_def .
    thus ?thesis by (rule unat_of_nat_eq)
  qed

  text \<open>The pure residual of the base-2 rule's \<open>vcg'\<close>, in the goal printer's \<open>Suc 0\<close>
    normal form (copied verbatim from the goal state).\<close>
  lemma sizeinbase2_wit_bundle:
    "Suc 0 \<le> sizeinbase2_wit i \<and>
     (i \<noteq> 0 \<longrightarrow> 2 ^ (sizeinbase2_wit i - Suc 0) \<le> \<bar>i\<bar>) \<and>
     (i = 0 \<longrightarrow> sizeinbase2_wit i = Suc 0) \<and>
     (\<bar>i\<bar> < 2 ^ (max_unat gmp_size_len - Suc 0) \<longrightarrow> \<bar>i\<bar> < 2 ^ sizeinbase2_wit i)"
  proof (intro conjI impI)
    show "Suc 0 \<le> sizeinbase2_wit i"
      by (metis One_nat_def sizeinbase2_wit_ge1)
    show "i \<noteq> 0 \<Longrightarrow> 2 ^ (sizeinbase2_wit i - Suc 0) \<le> \<bar>i\<bar>"
      by (metis One_nat_def sizeinbase2_wit_lower)
    show "i = 0 \<Longrightarrow> sizeinbase2_wit i = Suc 0"
      by (metis One_nat_def sizeinbase2_wit_zero)
    show "\<bar>i\<bar> < 2 ^ (max_unat gmp_size_len - Suc 0) \<Longrightarrow> \<bar>i\<bar> < 2 ^ sizeinbase2_wit i"
      by (metis One_nat_def sizeinbase2_wit_upper)
  qed

  consts raw_mpz_sizeinbase :: "mpz_t \<Rightarrow> gmp_int_t \<Rightarrow> gmp_size_t llM"
  specification (raw_mpz_sizeinbase)
    raw_mpz_sizeinbase_rl[vcg_rules]: "llvm_htriple
      (mpz_assn i ii \<and>* gmp_sint_assn b bi \<and>* \<up>(b\<in>{2..62}))
      (raw_mpz_sizeinbase ii bi)
      (\<lambda>ri. EXS r. mpz_assn i ii \<and>* gmp_size_assn r ri \<and>* \<up>(1\<le>r))"
    raw_mpz_sizeinbase2_rl: "llvm_htriple
      (mpz_assn i ii \<and>* gmp_sint_assn 2 bi)
      (raw_mpz_sizeinbase ii bi)
      (\<lambda>ri. EXS r. mpz_assn i ii \<and>* gmp_size_assn r ri
             \<and>* \<up>(1 \<le> r
                  \<and> (i \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>i\<bar>)
                  \<and> (i = 0 \<longrightarrow> r = 1)
                  \<and> (\<bar>i\<bar> < 2 ^ (max_unat gmp_size_len - 1) \<longrightarrow> \<bar>i\<bar> < 2 ^ r)))"
  proof -
    interpret llvm_prim_mem_setup .
    show ?thesis
      apply (rule exI[where x="\<lambda>ii bi. doM {
          s \<leftarrow> ll_load ii;
          i \<leftarrow> internal_mpz_get s;
          Mreturn (word_of_nat (sizeinbase2_wit i)) }"])
      apply (intro conjI allI)
      subgoal
        unfolding mpz_assn_def
        supply [vcg_rules] = internal_mpz_get_rule
        unfolding unat_rel_def unat.rel_def br_def pure_def
        supply [simp] = sizeinbase2_wit_unat sizeinbase2_wit_ge1
          sizeinbase2_wit_ge1[unfolded One_nat_def]
        by vcg'
      subgoal
        unfolding mpz_assn_def
        supply [vcg_rules] = internal_mpz_get_rule
        unfolding unat_rel_def unat.rel_def br_def pure_def
        supply [simp] = sizeinbase2_wit_unat sizeinbase2_wit_ge1
          sizeinbase2_wit_ge1[unfolded One_nat_def] sizeinbase2_wit_lower
          sizeinbase2_wit_zero sizeinbase2_wit_upper sizeinbase2_wit_bundle
        by vcg'
      done
  qed
  lemmas [llvm_code_raw] = LLVM_EXTERNALI[of raw_mpz_sizeinbase "''__gmpz_sizeinbase''"]

  text \<open>\<^bold>\<open>The base-2 rule \<open>raw_mpz_sizeinbase2_rl\<close> (above).\<close> GMP's \<open>__gmpz_sizeinbase(op, 2)\<close>
    returns the number of base-2 digits, the exact bit length
    (\<^url>\<open>https://gmplib.org/manual/Miscellaneous-Integer-Functions\<close>).

    \<^bold>\<open>Why the upper bound is guarded.\<close> An unconditional characterisation \<open>\<bar>i\<bar> < 2 ^ r \<and> \<dots>\<close> with
    the result under \<open>gmp_size_assn = unat_assn' TYPE(64)\<close> is false in the model: the result
    assertion forces \<open>r < 2\<^sup>6\<^sup>4\<close> while the model integer is unbounded
    (@{thm internal_mpz_make_rule} realises \<open>mpzs_assn i\<close> for every \<open>i\<close>), so for
    \<open>\<bar>i\<bar> \<ge> 2 ^ (2\<^sup>6\<^sup>4 - 1)\<close> the postcondition would be unsatisfiable under a satisfiable
    precondition, which with \<open>llvm_htriple\<close> total correctness is an inconsistency. The result type
    carries \<open>r < 2\<^sup>6\<^sup>4\<close> implicitly.

    So only the upper-bound conjunct is guarded, by the representability premise
    \<open>\<bar>i\<bar> < 2 ^ (max_unat 64 - 1)\<close>:
      \<^item> the lower bound \<open>2 ^ (r - 1) \<le> \<bar>i\<bar>\<close>, the zero case, and \<open>1 \<le> r\<close> are unconditional: they are
        witnessable for every input (out of range, every representable \<open>r\<close> satisfies the lower
        bound), and they alone carry the soundness of the truncation kernels' trust test
        (trusted \<Longrightarrow> sign correct);
      \<^item> the upper bound \<open>\<bar>i\<bar> < 2 ^ r\<close> holds whenever the bit length is \<open>size_t\<close>-representable,
        which excludes only integers of at least two exbibytes and is implied by every caller-side
        magnitude hypothesis (the \<open>\<bar>m\<bar> < 2 ^ (max_snat 64 - 1)\<close> pattern of
        \<open>mpz_bitlen2_monadic_snat_bound\<close> in \<open>Array\<close>).
    Witness: \<open>ll_load\<close>, @{const internal_mpz_get} and the pure saturating @{const sizeinbase2_wit},
    so the rule is a conservative extension. The trust at the foreign-function boundary is that the
    linked \<open>__gmpz_sizeinbase\<close> behaves as a function satisfying this specification, as for every
    other binding in this theory.\<close>

  context
  begin
    interpretation llvm_prim_mem_setup .
  
    definition [llvm_inline]: "mpzb_sizeinbase a b \<equiv> doM {
      mpzb_open a;
      r\<leftarrow>raw_mpz_sizeinbase a b;
      mpzb_close a;
      Mreturn r
    }"
    
    definition mpz_sizeinbase :: "int \<Rightarrow> int \<Rightarrow> nat nres" where 
      "mpz_sizeinbase a b \<equiv> doN { ASSERT (b\<in>{2..62}); SPEC (\<lambda>r. 1\<le>r) }"
      
    lemma mpz_sizeinbase_correct[refine_vcg]: "\<lbrakk>b\<in>{2..62}\<rbrakk> \<Longrightarrow> mpz_sizeinbase a b \<le> SPEC (\<lambda>r. 1\<le>r)"  
      unfolding mpz_sizeinbase_def by auto
      
    sepref_register mpz_sizeinbase
        
    lemma mpzb_sizeinbase_hnr[sepref_fr_rules]: "(uncurry mpzb_sizeinbase, uncurry mpz_sizeinbase) \<in> mpzb_assn\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k \<rightarrow>\<^sub>a gmp_size_assn"
      apply sepref_to_hoare
      unfolding mpzb_sizeinbase_def mpz_sizeinbase_def
      supply [simp] = pure_def refine_pw_simps
      apply vcg'
      done
      
  end      
  
  
  subsection \<open>Arrays of Values\<close>  
  
  
  term eoarray_slice_assn
  
  
  
  term "eoarray_slice_assn mpzs_assn"
  
  definition "mop_init_gmp_array xs i \<equiv> mop_eo_set xs i (0::int)"
  
  definition "init_gmp_array_impl (p::gmp_mpz_struct ptr) i \<equiv> doM {
    p' \<leftarrow> ll_ofs_ptr p i;
    raw_mpz_init p';
    Mreturn p
  }"

  
  
  subsection \<open>Examples\<close>

  definition "bigfac n \<equiv> for 0 n (\<lambda>i s. doN {ASSERT(i+1\<le>n); RETURN (s * (int i+1))}) 1"
  lemma "bigfac n \<le> SPEC (\<lambda>r. r = fact n)"
    unfolding bigfac_def 
    apply (refine_vcg for_rule[where I="\<lambda>j s. s = fact j"])
    by simp_all
    
  definition "bigfac2 n \<equiv> doN {
    for 0 n (\<lambda>i s. doN {
      ASSERT(i+1\<le>n); 
      RETURN (mpz_mul_ui.aop_r1 s (int i+1))
    }) (mpz_from_int 1)
  }"  

  lemma "bigfac2 n \<le>\<Down>Id (bigfac n)"
    unfolding bigfac2_def bigfac_def
    apply refine_vcg
    by simp_all
      
    
  sepref_def bigfac_impl is bigfac2 :: "[\<lambda>n. n+1<max_unat LENGTH(gmp_long_len)]\<^sub>a (unat_assn' TYPE('l::len))\<^sup>k \<rightarrow> mpzb_assn"
    unfolding bigfac2_def 
    apply (subst for_by_while_unat[where 'l='l])
    apply (annot_unat_const "TYPE('l)")
    (*apply (rewrite at "mpz_from_int \<hole>" fold_uint[where 'a=gmp_long_len])*)
    apply (annot_uint_const "TYPE(gmp_long_len)")
    apply (subst unat_uint_cast.annot[where T="TYPE(gmp_long_len)"])
    by sepref

  thm ll_identified_structures  
    


  thm llvm_code_raw
  find_in_thms LLVM_EXTERNAL in llvm_code_raw
    


end
