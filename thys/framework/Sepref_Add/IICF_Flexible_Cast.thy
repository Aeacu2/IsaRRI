section \<open>Flexible Integer type Casting\<close>
theory IICF_Flexible_Cast
imports IICF_Uint_Ops
begin

  text \<open>Type-casting operators between all Isabelle-LLVM integer types (snat,unat,sint,uint).
    The direction of the cast (up/down/none) is determined at code generation time by the preprocessor.
  \<close>

  subsection \<open>Preprocessor Setup\<close>

  (* Enable comparison of numeral LENGTH in LLVM code generator preprocessor *)  
  lemmas [llvm_pre_simp] = len_of_numeral_defs less_numeral_simps less_num_simps
  

  subsection \<open>LLVM operations\<close>    
  definition ll_ucast :: "'a::len word \<Rightarrow> 'b::len word llM" where
    "ll_ucast a \<equiv> 
      if LENGTH('a)<LENGTH('b) then ll_zext a TYPE('b word) 
      else if LENGTH('b)<LENGTH('a) then ll_trunc a TYPE('b word)
      else Mreturn (ucast a)"
      
  lemma ll_ucast_same[llvm_pre_simp]: "ll_ucast x = Mreturn x"
    unfolding ll_ucast_def by simp    
  lemma ll_ucast_up[llvm_pre_simp]: "LENGTH('a::len) < LENGTH('b::len) \<Longrightarrow> ll_ucast (x::'a word) = ll_zext x TYPE('b word)"  
    unfolding ll_ucast_def by simp    
  lemma ll_ucast_down[llvm_pre_simp]: "LENGTH('a::len) > LENGTH('b::len) \<Longrightarrow> ll_ucast (x::'a word) = ll_trunc x TYPE('b word)"  
    unfolding ll_ucast_def by simp    

    
  definition ll_scast :: "'a::len word \<Rightarrow> 'b::len word llM" where
    "ll_scast a \<equiv> 
      if LENGTH('a)<LENGTH('b) then ll_sext a TYPE('b word) 
      else if LENGTH('b)<LENGTH('a) then ll_trunc a TYPE('b word)
      else Mreturn (scast a)"
      
  lemma ll_scast_same[llvm_pre_simp]: "ll_scast x = Mreturn x"
    unfolding ll_scast_def by simp    
  lemma ll_scast_up[llvm_pre_simp]: "LENGTH('a::len) < LENGTH('b::len) \<Longrightarrow> ll_scast (x::'a word) = ll_sext x TYPE('b word)"  
    unfolding ll_scast_def by simp    
  lemma ll_scast_down[llvm_pre_simp]: "LENGTH('a::len) > LENGTH('b::len) \<Longrightarrow> ll_scast (x::'a word) = ll_trunc x TYPE('b word)"  
    unfolding ll_scast_def by simp    
    

  subsection \<open>VCG Setup\<close>      
  lemma is_up'_lenI: "LENGTH('a::len)<LENGTH('b::len) \<Longrightarrow> is_up' (f::('a word \<Rightarrow> 'b word))"
    unfolding is_up' .  

  lemma is_down'_lenI: "LENGTH('a::len)>LENGTH('b::len) \<Longrightarrow> is_down' (f::('a word \<Rightarrow> 'b word))"
    unfolding is_down' .  
    
    
  lemma uint_ucast_eq: "uint ni < max_uint LENGTH('b::len) \<Longrightarrow> uint (UCAST('a::len \<rightarrow> 'b) ni) = uint ni"  
    by (simp add: max_uint_def take_bit_int_eq_self_iff unsigned_ucast_eq)

  lemma unat_ucast_eq: "unat ni < max_unat LENGTH('b::len) \<Longrightarrow> unat (UCAST('a::len \<rightarrow> 'b) ni) = unat ni"  
    by (simp add: max_unat_def of_nat_inverse)

  lemma sint_scast_eq: "\<lbrakk>min_sint LENGTH('b) \<le> sint ni; sint ni < max_sint LENGTH('b::len)\<rbrakk> 
    \<Longrightarrow> sint (SCAST('a::len \<rightarrow> 'b) ni) = sint ni"  
    using word_sint.Abs_inverse by fastforce

  lemma snat_cast_eq: "\<lbrakk>snat_invar ni; snat ni < max_snat LENGTH('b)\<rbrakk>
          \<Longrightarrow> snat_invar (SCAST('a::len2 \<rightarrow> 'b::len2) ni) \<and> snat (SCAST('a \<rightarrow> 'b) ni) = snat ni"
    by (metis One_nat_def cnv_snat_to_uint(2) le_def max_snat_def max_unat_def msb_unat_big nat_uint_eq scast_def snat_eq_unat_aux2 snat_in_bounds_aux snat_invar_def uint_word_of_int_eq unat_ucast_eq unsigned_ucast_eq)          
    
    
  lemma uint_sint_cast_eq: "uint ni < max_sint LENGTH('b) \<Longrightarrow> sint (UCAST('a::len \<rightarrow> 'b::len) ni) = uint ni" 
    by (metis One_nat_def array_cast_index(1) max_sint_def max_uint_def nat_less_numeral_power_cancel_iff snat_in_bounds_aux uint_ucast_eq) 
    
  lemma sint_uint_cast_eq: "\<lbrakk>0 \<le> sint ni; sint ni < max_uint LENGTH('b::len)\<rbrakk> \<Longrightarrow> uint (UCAST('a::len \<rightarrow> 'b) ni) = sint ni"  
    by (metis pos_sint_to_uint uint_ucast_eq) 
    
  lemma unat_snat_cast_eq: "\<lbrakk>unat ni < max_snat LENGTH('b::len2)\<rbrakk>
          \<Longrightarrow> snat_invar (UCAST('a::len \<rightarrow> 'b) ni) \<and> snat (UCAST('a \<rightarrow> 'b) ni) = unat ni"  
    by (metis One_nat_def dual_order.strict_iff_not max_snat_def max_unat_def msb_unat_big snat_eq_unat_aux2 snat_in_bounds_aux snat_invar_def unat_ucast_eq)

  lemma snat_unat_cast_eq: "\<lbrakk>snat_invar ni; snat ni < max_unat LENGTH('b)\<rbrakk>
          \<Longrightarrow> unat (UCAST('a::len2 \<rightarrow> 'b::len) ni) = snat ni"  
    by (simp add: snat_eq_unat_aux2 unat_ucast_eq)    
    
  lemma snat_sint_cast_eq: "\<lbrakk>0 \<le> sint ni; nat (sint ni) < max_unat LENGTH('b)\<rbrakk>
          \<Longrightarrow> unat (UCAST('a::len \<rightarrow> 'b::len) ni) = nat (sint ni)"      
    by (metis nat_uint_eq pos_sint_to_uint unat_ucast_eq)          
    
  lemma sint_snat_cast_eq: "\<lbrakk>0 \<le> sint ni; nat (sint ni) < max_snat LENGTH('b)\<rbrakk>
          \<Longrightarrow> snat_invar (UCAST('a \<rightarrow> 'b) ni) \<and> unat (UCAST('a::len \<rightarrow> 'b::len2) ni) = nat (sint ni)"  
    by (metis nat_uint_eq pos_sint_to_uint snat_eq_unat_aux2 unat_snat_cast_eq)            
    
    
  locale cast_rule =
    fixes af src_assn tgt_assn minn maxx op
    assumes rl[vcg_rules]:
    "llvm_htriple 
      (\<upharpoonleft>src_assn n (ni::'a::len word) ** \<up>(minn LENGTH('b::len)\<le>n \<and> af n<maxx LENGTH('b))) 
      (op ni :: 'b word llM) 
      (\<lambda>r. \<upharpoonleft>tgt_assn (af n) r)"
        
  locale cast_rule_pos =
    fixes af src_assn tgt_assn maxx op
    assumes rl[vcg_rules]:
    "llvm_htriple 
      (\<upharpoonleft>src_assn n (ni::'a::len word) ** \<up>(af n<maxx LENGTH('b::len))) 
      (op ni :: 'b word llM) 
      (\<lambda>r. \<upharpoonleft>tgt_assn (af n) r)"
        
  context 
    notes [intro] = is_up'_lenI is_down'_lenI
    (*notes [fri_rules] = snat_ucast_fri_aux unat_snat_ucast_fri_aux*)
    notes [simp] = uint_ucast_eq uint.assn_def ll_ucast_def
    notes [simp] = sint.assn_def ll_scast_def sint_scast_eq snat_cast_eq
    notes [simp] = unat.assn_def unat_ucast_eq 
    notes [simp] = snat.assn_def 
    notes ASYM_CAST_EQS[simp] 
      = sint_uint_cast_eq uint_sint_cast_eq unat_snat_cast_eq snat_unat_cast_eq
        snat_sint_cast_eq sint_snat_cast_eq
    notes [split!] = if_split

  begin
    interpretation llvm_prim_arith_setup .

    global_interpretation uint_uint_cast: cast_rule_pos "\<lambda>x. x" uint.assn uint.assn max_uint ll_ucast by unfold_locales vcg
    global_interpretation uint_sint_cast: cast_rule_pos "\<lambda>x. x" uint.assn sint.assn max_sint ll_ucast by unfold_locales vcg
    
    global_interpretation sint_sint_cast: cast_rule "\<lambda>x. x" sint.assn sint.assn min_sint max_sint ll_scast 
      supply [simp] = scast_ucast_down_same[symmetric] by unfold_locales vcg
    global_interpretation sint_uint_cast: cast_rule "\<lambda>x. x" sint.assn uint.assn "\<lambda>_. 0" max_uint ll_ucast by unfold_locales vcg
      
    global_interpretation unat_unat_cast: cast_rule_pos "\<lambda>x. x" unat.assn unat.assn max_unat ll_ucast by unfold_locales vcg
    global_interpretation unat_snat_cast: cast_rule_pos "\<lambda>x. x" unat.assn snat.assn max_snat ll_ucast by unfold_locales vcg'
    
    global_interpretation snat_snat_cast: cast_rule_pos "\<lambda>x. x" snat.assn snat.assn max_snat ll_scast 
      supply [simp] = scast_ucast_down_same[symmetric] by unfold_locales vcg
    global_interpretation snat_unat_cast: cast_rule_pos "\<lambda>x. x" snat.assn unat.assn max_unat ll_ucast 
      by unfold_locales vcg'
      

    global_interpretation unat_uint_cast: cast_rule_pos int unat.assn uint.assn max_uint ll_ucast by unfold_locales vcg
    global_interpretation unat_sint_cast: cast_rule_pos int unat.assn sint.assn max_sint ll_ucast by unfold_locales vcg

    global_interpretation uint_unat_cast: cast_rule_pos nat uint.assn unat.assn max_unat ll_ucast by unfold_locales vcg
    global_interpretation uint_snat_cast: cast_rule_pos nat uint.assn snat.assn max_snat ll_ucast by unfold_locales vcg
    
    global_interpretation snat_uint_cast: cast_rule_pos int snat.assn uint.assn max_uint ll_ucast 
      supply [simp] = snat_eq_unat_aux2 by unfold_locales vcg 
    global_interpretation snat_sint_cast: cast_rule_pos int snat.assn sint.assn max_sint ll_ucast 
      supply [simp] = snat_eq_unat_aux2 by unfold_locales vcg 

    global_interpretation sint_unat_cast: cast_rule nat sint.assn unat.assn "\<lambda>_. 0" max_unat ll_ucast 
      by unfold_locales vcg
    global_interpretation sint_snat_cast: cast_rule nat sint.assn snat.assn "\<lambda>_. 0" max_snat ll_ucast 
      supply [simp] = snat_eq_unat_aux2
      by unfold_locales vcg'
      
      
  end  

  

  subsection \<open>Sepref Setup\<close>

  locale sepref_cast_loc =
    fixes disamb :: string (* HACK: Used to disambiguate operators of 
        different locale instantiations. Otherwise, several instantiations 
        will generate the same operations, causing confusion and making things harder to debug. *)
    fixes f :: "'a\<Rightarrow>'b" and fi :: "'s::len word \<Rightarrow> 't::len word llM" 
      and P :: "'a \<Rightarrow> bool"
      and src_assn :: "'a \<Rightarrow> 's word \<Rightarrow> assn" and tgt_assn :: "'b \<Rightarrow> 't word \<Rightarrow> assn"
    assumes hoare_rule: "llvm_htriple (src_assn x xi ** \<up>(P x)) (fi xi) (\<lambda>r. src_assn x xi ** tgt_assn (f x) r)"
  begin  

    definition op where "op (_::'t itself) \<equiv> let _=disamb in f"
    definition mop where "mop (T::'t itself) x \<equiv> doN {let _=disamb; ASSERT (P x); RETURN (f x)}"

    lemma annot: "f x = op T x" unfolding op_def by simp
        
    lemma op_hnr[sepref_fr_rules]: 
      "(fi, RETURN o PR_CONST (op T)) \<in> [P]\<^sub>a src_assn\<^sup>k \<rightarrow> tgt_assn"
      apply sepref_to_hoare
      unfolding in_snat_rel_conv_assn op_def Let_def PR_CONST_def
      supply [vcg_rules] = hoare_rule
      by vcg
  
    lemma mop_hnr[sepref_fr_rules]:
      "(fi, PR_CONST (mop T)) \<in> src_assn\<^sup>k \<rightarrow>\<^sub>a tgt_assn"
      apply sepref_to_hoare
      unfolding in_snat_rel_conv_assn mop_def Let_def PR_CONST_def
      apply (simp add: refine_pw_simps)
      supply [vcg_rules] = hoare_rule
      by vcg

      
    (* Refinement VCG Setup *)  
    
    lemma op_unfold[simp]: "op T x = f x" unfolding op_def by simp
    
    lemma mop_refine[refine]: "P x \<Longrightarrow> mop T x \<le> RETURN (f x)"
      unfolding mop_def by simp
      
    lemma mop_correct[refine_vcg]: "P x \<Longrightarrow> mop T x \<le> SPEC (\<lambda>r. r = f x)"
      unfolding mop_def by simp
      
  end      

  context fixes d::string and T :: "'t::len itself" and f::"'a\<Rightarrow>'b" and P :: "'a\<Rightarrow>bool" begin
    sepref_register "sepref_cast_loc.op d f T" "sepref_cast_loc.mop d f P T"
  end
  

  context begin  
  
    private method fc_prove = 
      unfold_locales; 
      unfold pure_def 
             in_snat_rel_conv_assn in_unat_rel_conv_assn in_uint_rel_conv_assn in_sint_rel_conv_assn;
      vcg

    private abbreviation (input) "pre_snat TYPE('t::len2) n \<equiv> n<max_snat LENGTH('t)"  
    private abbreviation (input) "pre_unat TYPE('t::len) n \<equiv> n<max_unat LENGTH('t)"  
    private abbreviation (input) "pre_uint TYPE('t::len) n \<equiv> 0\<le>n \<and> n<max_uint LENGTH('t)"  
    private abbreviation (input) "pre_sint TYPE('t::len) n \<equiv> min_sint LENGTH('t)\<le>n \<and> n<max_sint LENGTH('t)"  

    private abbreviation (input) "pre_snatc TYPE('t::len2) n \<equiv> 0\<le>n \<and> nat n<max_snat LENGTH('t)"  
    private abbreviation (input) "pre_unatc TYPE('t::len) n \<equiv> 0\<le>n \<and> nat n<max_unat LENGTH('t)"  
    private abbreviation (input) "pre_uintc TYPE('t::len) n \<equiv> int n<max_uint LENGTH('t)"  
    private abbreviation (input) "pre_sintc TYPE('t::len) n \<equiv> int n<max_sint LENGTH('t)"  
    
            
    global_interpretation snat_snat_cast: sepref_cast_loc "''snat_snat''" "\<lambda>x. x" ll_scast "pre_snat TYPE('t)" snat_assn "snat_assn' TYPE('t::len2)" by fc_prove
    global_interpretation snat_unat_cast: sepref_cast_loc "''snat_unat''" "\<lambda>x. x" ll_ucast "pre_unat TYPE('t)" snat_assn "unat_assn' TYPE('t::len)" by fc_prove
    global_interpretation snat_uint_cast: sepref_cast_loc "''snat_uint''" int     ll_ucast "pre_uintc TYPE('t)" snat_assn "uint_assn' TYPE('t::len)" by fc_prove      
    global_interpretation snat_sint_cast: sepref_cast_loc "''snat_sint''" int     ll_ucast "pre_sintc TYPE('t)" snat_assn "sint_assn' TYPE('t::len)" by fc_prove      
    
    global_interpretation unat_snat_cast: sepref_cast_loc "''unat_snat''" "\<lambda>x. x" ll_ucast "pre_snat TYPE('t)" unat_assn "snat_assn' TYPE('t::len2)" by fc_prove
    global_interpretation unat_unat_cast: sepref_cast_loc "''unat_unat''" "\<lambda>x. x" ll_ucast "pre_unat TYPE('t)" unat_assn "unat_assn' TYPE('t::len)" by fc_prove
    global_interpretation unat_uint_cast: sepref_cast_loc "''unat_uint''" int     ll_ucast "pre_uintc TYPE('t)" unat_assn "uint_assn' TYPE('t::len)" by fc_prove      
    global_interpretation unat_sint_cast: sepref_cast_loc "''unat_sint''" int     ll_ucast "pre_sintc TYPE('t)" unat_assn "sint_assn' TYPE('t::len)" by fc_prove      

    global_interpretation uint_snat_cast: sepref_cast_loc "''uint_snat''" nat     ll_ucast "pre_snatc TYPE('t)" uint_assn "snat_assn' TYPE('t::len2)" by fc_prove
    global_interpretation uint_unat_cast: sepref_cast_loc "''uint_unat''" nat     ll_ucast "pre_unatc TYPE('t)" uint_assn "unat_assn' TYPE('t::len)" by fc_prove
    global_interpretation uint_uint_cast: sepref_cast_loc "''uint_uint''" "\<lambda>x. x" ll_ucast "pre_uint TYPE('t)" uint_assn "uint_assn' TYPE('t::len)" by fc_prove      
    global_interpretation uint_sint_cast: sepref_cast_loc "''uint_sint''" "\<lambda>x. x" ll_ucast "pre_sint TYPE('t)" uint_assn "sint_assn' TYPE('t::len)" by fc_prove      
    
    global_interpretation sint_snat_cast: sepref_cast_loc "''sint_snat''" nat     ll_ucast "pre_snatc TYPE('t)" sint_assn "snat_assn' TYPE('t::len2)" by fc_prove
    global_interpretation sint_unat_cast: sepref_cast_loc "''sint_unat''" nat     ll_ucast "pre_unatc TYPE('t)" sint_assn "unat_assn' TYPE('t::len)" by fc_prove
    global_interpretation sint_uint_cast: sepref_cast_loc "''sint_uint''" "\<lambda>x. x" ll_ucast "pre_uint TYPE('t)" sint_assn "uint_assn' TYPE('t::len)" by fc_prove      
    global_interpretation sint_sint_cast: sepref_cast_loc "''sint_sint''" "\<lambda>x. x" ll_scast "pre_sint TYPE('t)" sint_assn "sint_assn' TYPE('t::len)" by fc_prove      
        
  end  

  subsection \<open>Regression Test\<close>
  
  experiment
  begin
  
    abbreviation "T_small \<equiv> TYPE(16)"
    abbreviation "T_big \<equiv> TYPE(64)"
  
    definition "\<And>op mop. test op mop T x \<equiv> doN {
      a \<leftarrow> mop T x;
      ASSERT(0<x \<and> x<42);
      RETURN (a = op T x)
    }"

    (* snat \<rightarrow> * *)
    sepref_definition test_sn_sn_up [llvm_code] is "test snat_snat_cast.op snat_snat_cast.mop T_small" :: "(snat_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_sn_sn_eq [llvm_code] is "test snat_snat_cast.op snat_snat_cast.mop T_small" :: "(snat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_sn_sn_dw [llvm_code] is "test snat_snat_cast.op snat_snat_cast.mop T_big"   :: "(snat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_sn_un_up [llvm_code] is "test snat_unat_cast.op snat_unat_cast.mop T_small" :: "(snat_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_sn_un_eq [llvm_code] is "test snat_unat_cast.op snat_unat_cast.mop T_small" :: "(snat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_sn_un_dw [llvm_code] is "test snat_unat_cast.op snat_unat_cast.mop T_big"   :: "(snat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_sn_ui_up [llvm_code] is "test snat_uint_cast.op snat_uint_cast.mop T_small" :: "(snat_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_sn_ui_eq [llvm_code] is "test snat_uint_cast.op snat_uint_cast.mop T_small" :: "(snat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_sn_ui_dw [llvm_code] is "test snat_uint_cast.op snat_uint_cast.mop T_big"   :: "(snat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_sn_si_up [llvm_code] is "test snat_sint_cast.op snat_sint_cast.mop T_small" :: "(snat_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_sn_si_eq [llvm_code] is "test snat_sint_cast.op snat_sint_cast.mop T_small" :: "(snat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_sn_si_dw [llvm_code] is "test snat_sint_cast.op snat_sint_cast.mop T_big"   :: "(snat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref

    (* unat \<rightarrow> * *)
    sepref_definition test_un_sn_up [llvm_code] is "test unat_snat_cast.op unat_snat_cast.mop T_small" :: "(unat_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_un_sn_eq [llvm_code] is "test unat_snat_cast.op unat_snat_cast.mop T_small" :: "(unat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_un_sn_dw [llvm_code] is "test unat_snat_cast.op unat_snat_cast.mop T_big"   :: "(unat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_un_un_up [llvm_code] is "test unat_unat_cast.op unat_unat_cast.mop T_small" :: "(unat_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_un_un_eq [llvm_code] is "test unat_unat_cast.op unat_unat_cast.mop T_small" :: "(unat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_un_un_dw [llvm_code] is "test unat_unat_cast.op unat_unat_cast.mop T_big"   :: "(unat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_un_ui_up [llvm_code] is "test unat_uint_cast.op unat_uint_cast.mop T_small" :: "(unat_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_un_ui_eq [llvm_code] is "test unat_uint_cast.op unat_uint_cast.mop T_small" :: "(unat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_un_ui_dw [llvm_code] is "test unat_uint_cast.op unat_uint_cast.mop T_big"   :: "(unat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_un_si_up [llvm_code] is "test unat_sint_cast.op unat_sint_cast.mop T_small" :: "(unat_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_un_si_eq [llvm_code] is "test unat_sint_cast.op unat_sint_cast.mop T_small" :: "(unat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_un_si_dw [llvm_code] is "test unat_sint_cast.op unat_sint_cast.mop T_big"   :: "(unat_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref

    (* uint \<rightarrow> * *)
    sepref_definition test_ui_sn_up [llvm_code] is "test uint_snat_cast.op uint_snat_cast.mop T_small" :: "(uint_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_ui_sn_eq [llvm_code] is "test uint_snat_cast.op uint_snat_cast.mop T_small" :: "(uint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_ui_sn_dw [llvm_code] is "test uint_snat_cast.op uint_snat_cast.mop T_big"   :: "(uint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_ui_un_up [llvm_code] is "test uint_unat_cast.op uint_unat_cast.mop T_small" :: "(uint_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_ui_un_eq [llvm_code] is "test uint_unat_cast.op uint_unat_cast.mop T_small" :: "(uint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_ui_un_dw [llvm_code] is "test uint_unat_cast.op uint_unat_cast.mop T_big"   :: "(uint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_ui_ui_up [llvm_code] is "test uint_uint_cast.op uint_uint_cast.mop T_small" :: "(uint_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_ui_ui_eq [llvm_code] is "test uint_uint_cast.op uint_uint_cast.mop T_small" :: "(uint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_ui_ui_dw [llvm_code] is "test uint_uint_cast.op uint_uint_cast.mop T_big"   :: "(uint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_ui_si_up [llvm_code] is "test uint_sint_cast.op uint_sint_cast.mop T_small" :: "(uint_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_ui_si_eq [llvm_code] is "test uint_sint_cast.op uint_sint_cast.mop T_small" :: "(uint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_ui_si_dw [llvm_code] is "test uint_sint_cast.op uint_sint_cast.mop T_big"   :: "(uint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    
    (* sint \<rightarrow> * *)
    sepref_definition test_si_sn_up [llvm_code] is "test sint_snat_cast.op sint_snat_cast.mop T_small" :: "(sint_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_si_sn_eq [llvm_code] is "test sint_snat_cast.op sint_snat_cast.mop T_small" :: "(sint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_si_sn_dw [llvm_code] is "test sint_snat_cast.op sint_snat_cast.mop T_big"   :: "(sint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_si_un_up [llvm_code] is "test sint_unat_cast.op sint_unat_cast.mop T_small" :: "(sint_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_si_un_eq [llvm_code] is "test sint_unat_cast.op sint_unat_cast.mop T_small" :: "(sint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_si_un_dw [llvm_code] is "test sint_unat_cast.op sint_unat_cast.mop T_big"   :: "(sint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_si_ui_up [llvm_code] is "test sint_uint_cast.op sint_uint_cast.mop T_small" :: "(sint_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_si_ui_eq [llvm_code] is "test sint_uint_cast.op sint_uint_cast.mop T_small" :: "(sint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_si_ui_dw [llvm_code] is "test sint_uint_cast.op sint_uint_cast.mop T_big"   :: "(sint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_si_si_up [llvm_code] is "test sint_sint_cast.op sint_sint_cast.mop T_small" :: "(sint_assn' T_big)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_si_si_eq [llvm_code] is "test sint_sint_cast.op sint_sint_cast.mop T_small" :: "(sint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
    sepref_definition test_si_si_dw [llvm_code] is "test sint_sint_cast.op sint_sint_cast.mop T_big"   :: "(sint_assn' T_small)\<^sup>k \<rightarrow>\<^sub>a bool1_assn" unfolding test_def by sepref
            

    
    export_llvm test_sn_sn_up               
    export_llvm test_sn_sn_eq
    export_llvm test_sn_sn_dw
    export_llvm test_sn_un_up
    export_llvm test_sn_un_eq
    export_llvm test_sn_un_dw
    export_llvm test_sn_ui_up
    export_llvm test_sn_ui_eq
    export_llvm test_sn_ui_dw
    export_llvm test_sn_si_up
    export_llvm test_sn_si_eq
    export_llvm test_sn_si_dw
    
    
    export_llvm test_un_sn_up
    export_llvm test_un_sn_eq
    export_llvm test_un_sn_dw
    export_llvm test_un_un_up
    export_llvm test_un_un_eq
    export_llvm test_un_un_dw
    export_llvm test_un_ui_up
    export_llvm test_un_ui_eq
    export_llvm test_un_ui_dw
    export_llvm test_un_si_up
    export_llvm test_un_si_eq
    export_llvm test_un_si_dw
    
    
    export_llvm test_ui_sn_up
    export_llvm test_ui_sn_eq
    export_llvm test_ui_sn_dw
    export_llvm test_ui_un_up
    export_llvm test_ui_un_eq
    export_llvm test_ui_un_dw
    export_llvm test_ui_ui_up
    export_llvm test_ui_ui_eq
    export_llvm test_ui_ui_dw
    export_llvm test_ui_si_up
    export_llvm test_ui_si_eq
    export_llvm test_ui_si_dw
    
    
    export_llvm test_si_sn_up
    export_llvm test_si_sn_eq
    export_llvm test_si_sn_dw
    export_llvm test_si_un_up
    export_llvm test_si_un_eq
    export_llvm test_si_un_dw
    export_llvm test_si_ui_up
    export_llvm test_si_ui_eq
    export_llvm test_si_ui_dw
    export_llvm test_si_si_up
    export_llvm test_si_si_eq
    export_llvm test_si_si_dw
                  
  end
  
  


end
