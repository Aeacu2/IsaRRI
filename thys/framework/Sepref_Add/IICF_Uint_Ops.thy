theory IICF_Uint_Ops
imports "Isabelle_LLVM.IICF"
begin
no_syntax (ASCII)  
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixl ">>" 54)


  
  
  lemma uints_ss_sintsSuc: "uints W \<subseteq> sints (Suc W)"
    unfolding uints_num sints_num
    by (clarsimp)
        
  lemma uints_ss_sints2x: "W\<noteq>0 \<Longrightarrow> uints W \<subseteq> sints (2*W)"
    apply (rule order_trans[OF uints_ss_sintsSuc])
    apply (rule sints_subset)
    by simp
    
  

  lemma sint_eq_uint_2pl':
    "\<lbrakk> uint (a :: 'a :: len word) < 2 ^ (LENGTH('a) - 1) \<rbrakk>
     \<Longrightarrow> sint a = uint a"
    by (simp add: not_msb_from_less sint_eq_uint word_2p_lem word_size)
  

  lemma in_snat_rel_conv: "(w,n)\<in>snat_rel \<longleftrightarrow> nat (sint w) = n \<and> \<not>msb w"
    apply (simp add: snat_rel_def snat.rel_def in_br_conv)
    by (auto simp: snat_invar_def snat_def)
    
  lemma snat_rel0[simp]: "(0,0)\<in>snat_rel"
    and snat_rel1[simp]: "(1,1)\<in>snat_rel"
    by (simp_all add: in_snat_rel_conv)  

text \<open>\<open>snat_rel_numeral'\<close> is proved by a structured Isar argument and \<open>snat_rel_numeral\<close> is derived
  from it, so this theory needs no external SMT solver.\<close>

  lemma snat_rel_numeral'[simp]:
    assumes "(numeral n :: nat) < 2^(LENGTH('l::len2)-1)"
    shows "(numeral n::'l word,numeral n)\<in>snat_rel"
  proof -
    have inv: "snat_invar (numeral n::'l word)"
      unfolding snat_invar_def
      apply (rule ll_const_signed_nat_aux2)
      using assms by (simp add: One_nat_def)
    have len_bound: "(numeral n::nat) < 2 ^ LENGTH('l)"
      using assms nat_power_minus_less by blast
    have unat_eq_of_nat: "unat (of_nat (numeral n) :: 'l word) = numeral n"
      using len_bound by (rule unat_of_nat_len)
    have unat_eq: "unat (numeral n::'l word) = numeral n"
      using unat_eq_of_nat by simp
    have snat_eq: "snat (numeral n::'l word) = numeral n"
      using inv unat_eq by (simp add: snat_eq_unat_aux2)
    show ?thesis
      unfolding snat_rel_def snat.rel_def in_br_conv
      using inv snat_eq by simp
  qed

  lemma snat_rel_numeral[simp]:
    assumes "(numeral n :: int) < 2^(LENGTH('l::len2)-1)" 
    shows "(numeral n::'l word,numeral n)\<in>snat_rel"
  proof (rule snat_rel_numeral')
    show "(numeral n :: nat) < 2^(LENGTH('l)-1)"
      using assms
      by (metis One_nat_def of_nat_less_iff of_nat_numeral semiring_1_class.of_nat_power)
  qed
    
        
  lemma snat_relI: "nat (sint w) = n \<Longrightarrow> \<not>msb w \<Longrightarrow> (w,n)\<in>snat_rel"
    apply (simp add: snat_rel_def snat.rel_def in_br_conv)
    by (simp add: snat_invar_def snat_def)
  
    
  lemma in_unat_rel_conv: "(w,n)\<in>unat_rel \<longleftrightarrow> unat w = n"
    apply (simp add: unat_rel_def unat.rel_def in_br_conv)
    by auto
    
  lemma unat_relI: "unat w = n \<Longrightarrow> (w,n)\<in>unat_rel"
    by (simp add: in_unat_rel_conv)
  
  lemma unat_rel0[simp]: "(0,0)\<in>unat_rel"
    and unat_rel1[simp]: "(1,1)\<in>unat_rel"
    by (simp_all add: in_unat_rel_conv)  
  
  lemma unat_rel_numeral[simp]:
    assumes "(numeral n :: nat) < 2^(LENGTH('l::len2))" 
    shows "(numeral n::'l word,numeral n)\<in>unat_rel"
    unfolding in_unat_rel_conv
    by (metis assms mod_less unat_numeral)
  
  
      
  
  sepref_register "(div)" "(mod)"  
  
  
  
subsubsection \<open>Unsigned Integer by Word\<close>
  
definition "uint_rel \<equiv> uint.rel"
abbreviation "uint_assn \<equiv> pure uint_rel"  

abbreviation (input) "uint_rel' TYPE('a::len) \<equiv> uint_rel :: ('a word \<times> _) set"
abbreviation (input) "uint_assn' TYPE('a::len) \<equiv> uint_assn :: _ \<Rightarrow> 'a word \<Rightarrow> _"


definition [simp]: "uint_const TYPE('a::len) c \<equiv> (c::int)"
context fixes c::int begin
  sepref_register "uint_const TYPE('a::len) c" :: "int"
end

lemma in_uint_rel_conv: "(w,n)\<in>uint_rel \<longleftrightarrow> uint w = n"
  by (auto simp: uint_rel_def uint.rel_def in_br_conv)


  
  
lemma fold_uint:
  "0 = uint_const TYPE('a::len) 0"  
  "1 = uint_const TYPE('a::len) 1"  
  "-1 \<equiv> (uint_const TYPE('a::len) (-1))"  
  "numeral n \<equiv> (uint_const TYPE('a::len) (numeral n))"
  "-(numeral n) \<equiv> (uint_const TYPE('a::len) (-numeral n))"
  by simp_all


lemma hn_uint_0[sepref_import_param]:
  "(0,uint_const TYPE('a) 0) \<in> uint_rel' TYPE('a::len)"
  by (auto simp: uint_rel_def uint.rel_def in_br_conv)

lemma hn_uint_1[sepref_fr_rules]:
  "hn_refine \<box> (Mreturn 1) \<box> (uint_assn' TYPE('a::len)) (\<lambda>_. True) (RETURN$PR_CONST (uint_const TYPE('a) 1))"
  apply sepref_to_hoare unfolding uint_rel_def uint.rel_def in_br_conv by vcg
  
lemma hn_uint_numeral[sepref_fr_rules]:
  "\<lbrakk>numeral n \<in> uints LENGTH('a)\<rbrakk> \<Longrightarrow> 
    hn_refine \<box> (Mreturn (numeral n)) \<box> (uint_assn' TYPE('a::len)) (\<lambda>_. True) (RETURN$(PR_CONST (uint_const TYPE('a) (numeral n))))"
  apply sepref_to_hoare unfolding uint_rel_def uint.rel_def in_br_conv 
  apply vcg'
  by (metis max_uint_def of_nat_numeral uint_bintrunc uint_numeral_eq_aux unsigned_numeral)

thm uint_cmp_ops[THEN uint.hn_cmp_op, folded uint_rel_def, unfolded to_hfref_post]  
thm uint_bin_ops[THEN uint.hn_bin_op, folded uint_rel_def, unfolded to_hfref_post]  
  
lemma hn_uint_ops[sepref_fr_rules]:
  "(uncurry ll_add, uncurry (RETURN \<circ>\<circ> (+)))
    \<in> [\<lambda>(a, b). a + b < max_uint LENGTH('a)]\<^sub>a uint_assn\<^sup>k *\<^sub>a uint_assn\<^sup>k \<rightarrow> uint_assn' TYPE('a::len)"
  "(uncurry ll_sub, uncurry (RETURN \<circ>\<circ> (-)))
    \<in> [\<lambda>(a, b). b\<le>a]\<^sub>a uint_assn\<^sup>k *\<^sub>a uint_assn\<^sup>k \<rightarrow> uint_assn' TYPE('a::len)"
  "(uncurry ll_mul, uncurry (RETURN \<circ>\<circ> (*)))
    \<in> [\<lambda>(a, b). a * b < max_uint LENGTH('a)]\<^sub>a uint_assn\<^sup>k *\<^sub>a uint_assn\<^sup>k \<rightarrow> uint_assn' TYPE('a::len)"
  "(uncurry ll_udiv, uncurry (RETURN \<circ>\<circ> (div)))
    \<in> [\<lambda>(a, b). b \<noteq> 0]\<^sub>a uint_assn\<^sup>k *\<^sub>a uint_assn\<^sup>k \<rightarrow> uint_assn' TYPE('a::len)"
  "(uncurry ll_urem, uncurry (RETURN \<circ>\<circ> (mod)))
    \<in> [\<lambda>(a, b). b \<noteq> 0]\<^sub>a uint_assn\<^sup>k *\<^sub>a uint_assn\<^sup>k \<rightarrow> uint_assn' TYPE('a::len)"
    
    
  "(uncurry ll_and, uncurry (RETURN \<circ>\<circ> (AND))) \<in> uint_assn\<^sup>k *\<^sub>a uint_assn\<^sup>k \<rightarrow>\<^sub>a uint_assn"
  "(uncurry ll_or, uncurry (RETURN \<circ>\<circ> (OR))) \<in> uint_assn\<^sup>k *\<^sub>a uint_assn\<^sup>k \<rightarrow>\<^sub>a uint_assn"
  "(uncurry ll_xor, uncurry (RETURN \<circ>\<circ> (XOR))) \<in> uint_assn\<^sup>k *\<^sub>a uint_assn\<^sup>k \<rightarrow>\<^sub>a uint_assn"
    
    
  "(uncurry ll_icmp_eq, uncurry (RETURN \<circ>\<circ> (=))) \<in> uint_assn\<^sup>k *\<^sub>a uint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ne, uncurry (RETURN \<circ>\<circ> (op_neq))) \<in> uint_assn\<^sup>k *\<^sub>a uint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ule, uncurry (RETURN \<circ>\<circ> (\<le>))) \<in> uint_assn\<^sup>k *\<^sub>a uint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ult, uncurry (RETURN \<circ>\<circ> (<))) \<in> uint_assn\<^sup>k *\<^sub>a uint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding op_neq_def
  using uint_bin_ops[THEN uint.hn_bin_op, folded uint_rel_def, unfolded to_hfref_post]
    and uint_cmp_ops[THEN uint.hn_cmp_op, folded uint_rel_def bool1_rel_def, unfolded to_hfref_post]
  apply simp_all
  done

definition [simp]: "uint_init TYPE('a::len) \<equiv> 0::int"

lemma is_init_uint[sepref_gen_algo_rules]:
  "GEN_ALGO (uint_init TYPE('a::len)) (is_init (uint_assn' TYPE('a)))"
  unfolding GEN_ALGO_def uint_init_def is_init_def
  unfolding uint_rel_def uint.rel_def
  by (simp add: in_br_conv)
  
lemma is_init_uint0[sepref_gen_algo_rules]: 
  "GEN_ALGO (uint_const TYPE('a::len) 0) (is_init (uint_assn' TYPE('a)))"
  using is_init_uint[where 'a='a]
  by simp


  
context begin
  interpretation llvm_prim_arith_setup .


  definition [llvm_inline]: "uint_uint_upcast TYPE('a::len) x \<equiv> ll_zext x TYPE('a word)"
  definition [llvm_inline]: "uint_uint_downcast TYPE('a::len) x \<equiv> ll_trunc x TYPE('a word)"
  definition [llvm_inline]: "uint_uint_trunc TYPE('a::len) x \<equiv> ll_trunc x TYPE('a word)"

  definition [llvm_inline]: "uint_sint_upcast TYPE('a::len2) x \<equiv> ll_zext x TYPE('a word)"
  definition [llvm_inline]: "sint_uint_downcast TYPE('a::len) x \<equiv> ll_trunc x TYPE('a word)"
    
  
  definition [llvm_inline]: "uint_snat_upcast TYPE('a::len2) x \<equiv> ll_zext x TYPE('a word)"
  definition [llvm_inline]: "uint_snat_downcast TYPE('a::len) x \<equiv> ll_trunc x TYPE('a word)"
  
  definition [llvm_inline]: "snat_uint_upcast TYPE('a::len2) x \<equiv> ll_zext x TYPE('a word)"
  definition [llvm_inline]: "snat_uint_downcast TYPE('a::len) x \<equiv> ll_trunc x TYPE('a word)"
  
  lemma uint_uint_upcast_rule[vcg_rules]:
  "llvm_htriple 
    (\<up>(is_up' UCAST('small \<rightarrow> 'big)) ** \<upharpoonleft>uint.assn n (ni::'small::len word)) 
    (uint_uint_upcast TYPE('big::len) ni) 
    (\<lambda>r. \<upharpoonleft>uint.assn n r)"
  unfolding uint.assn_def snat.assn_def uint_uint_upcast_def
  apply vcg'
  apply (simp add: Word_Lemmas.cast_simps(23))
  done
  
  lemma uint_uint_downcast_rule[vcg_rules]:
  "llvm_htriple 
    (\<up>(is_down' UCAST('big \<rightarrow> 'small)) ** \<upharpoonleft>uint.assn n (ni::'big::len word) ** \<up>(n<max_uint LENGTH('small))) 
    (uint_uint_downcast TYPE('small::len) ni) 
    (\<lambda>r. \<upharpoonleft>uint.assn n r)"
  unfolding uint.assn_def uint.assn_def uint_uint_downcast_def
  apply vcg'
  by (simp add: max_uint_def take_bit_int_eq_self unsigned_ucast_eq)
  
  lemma uint_uint_trunc_rule[vcg_rules]:
  "llvm_htriple 
    (\<up>(is_down' UCAST('big \<rightarrow> 'small)) ** \<upharpoonleft>uint.assn n (ni::'big::len word)) 
    (uint_uint_trunc TYPE('small::len) ni) 
    (\<lambda>r. \<upharpoonleft>uint.assn (n mod 2^LENGTH('small)) r)"
  unfolding uint.assn_def uint.assn_def uint_uint_trunc_def
  apply vcg'
  by (metis Word.of_int_uint int_word_uint)

  lemma uint_sint_upcast_rule[vcg_rules]:
    "llvm_htriple 
      (\<up>(is_up' UCAST('small \<rightarrow> 'big)) ** \<upharpoonleft>uint.assn n (ni::'small::len word)) 
      (uint_sint_upcast TYPE('big::len2) ni) 
      (\<lambda>r. \<upharpoonleft>sint.assn n r)"
    unfolding uint.assn_def sint.assn_def uint_sint_upcast_def
    apply vcg'
    by (simp add: is_up' bintr_uint sint_eq_uint unsigned_ucast_eq)

  lemma sint_uint_downcast_rule[vcg_rules]:
    "llvm_htriple 
      (\<up>(is_down' UCAST('big \<rightarrow> 'small)) ** \<upharpoonleft>sint.assn n (ni::'big::len2 word) ** \<up>(0\<le>n \<and> n<max_uint LENGTH('small))) 
      (sint_uint_downcast TYPE('small::len) ni) 
      (\<lambda>r. \<upharpoonleft>uint.assn n r)"
    unfolding uint.assn_def sint.assn_def sint_uint_downcast_def
    apply vcg'
    by (simp add: is_down' max_uint_def pos_sint_to_uint take_bit_int_eq_self unsigned_ucast_eq)
    
  
  lemma uint_snat_upcast_rule[vcg_rules]:
    "llvm_htriple 
      (\<up>(is_up' UCAST('small \<rightarrow> 'big)) ** \<upharpoonleft>uint.assn i (ii::'small::len word)) 
      (uint_snat_upcast TYPE('big::len2) ii) 
      (\<lambda>r. \<upharpoonleft>snat.assn (nat i) r)"
    unfolding uint.assn_def snat.assn_def uint_snat_upcast_def
    apply vcg'
    by (simp add: is_up' snat_eq_unat_aux2 snat_invar_def unat_ucast_up_simp)

    
  lemma uint_snat_downcast_rule[vcg_rules]:
    "llvm_htriple 
      (\<up>(is_down' UCAST('big \<rightarrow> 'small)) ** \<upharpoonleft>uint.assn i (ii::'big::len2 word) ** \<up>(nat i<max_snat LENGTH('small))) 
      (uint_snat_downcast TYPE('small::len2) ii) 
      (\<lambda>r. \<upharpoonleft>snat.assn (nat i) r)"
    unfolding uint.assn_def snat.assn_def uint_snat_downcast_def
    apply vcg'
    apply (simp add: is_down' max_snat_def snat_invar_alt)
    by (metis One_nat_def Suc_diff_1 Word.of_nat_unat len_gt_0 nat_power_minus_less snat_eq_unat_aux1 unat_of_nat_len)

    
  lemma snat_uint_upcast_rule[vcg_rules]:
    "llvm_htriple 
      (\<up>(is_up' UCAST('small \<rightarrow> 'big)) ** \<upharpoonleft>snat.assn i (ii::'small::len2 word)) 
      (snat_uint_upcast TYPE('big::len2) ii) 
      (\<lambda>r. \<upharpoonleft>uint.assn (int i) r)"
    unfolding uint.assn_def snat.assn_def snat_uint_upcast_def
    apply vcg'
    apply (simp add: is_up' snat_eq_unat_aux2 snat_invar_def )
    by (metis Word.of_nat_unat less_le_not_le unat_ucast_up_simp)

    
  lemma snat_uint_downcast_rule[vcg_rules]:
    "llvm_htriple 
      (\<up>(is_down' UCAST('big \<rightarrow> 'small)) ** \<upharpoonleft>snat.assn i (ii::'big::len2 word) ** \<up>(int i<max_uint LENGTH('small))) 
      (snat_uint_downcast TYPE('small::len2) ii) 
      (\<lambda>r. \<upharpoonleft>uint.assn (int i) r)"
    unfolding uint.assn_def snat.assn_def snat_uint_downcast_def
    apply vcg'
    apply (simp add: is_down' max_snat_def snat_invar_alt)
    by (metis Word.of_int_uint Word.of_nat_unat max_uint_def snat_eq_unat_aux2 snat_invar_alt uint_range' word_of_int_inverse)    
    
      
end



context fixes T :: "'a::len itself" begin
  definition [simp]: "uint_uint_upcast_aux \<equiv> let _=TYPE('a::len) in id::int\<Rightarrow>int"
  definition [simp]: "uint_uint_downcast_aux \<equiv> let _=TYPE('a::len) in id::int\<Rightarrow>int"
  definition [simp]: "uint_uint_trunc_aux \<equiv> \<lambda>w::int. w mod 2^LENGTH('a)"

  definition [simp]: "uint_sint_upcast_aux \<equiv> let _=TYPE('a::len) in id::int\<Rightarrow>int"
  definition [simp]: "sint_uint_downcast_aux \<equiv> let _=TYPE('a::len) in id::int\<Rightarrow>int"

  definition [simp]: "uint_snat_upcast_aux \<equiv> let _=TYPE('a::len) in nat::int\<Rightarrow>nat"
  definition [simp]: "uint_snat_downcast_aux \<equiv> let _=TYPE('a::len) in nat::int\<Rightarrow>nat"
  
  definition [simp]: "snat_uint_upcast_aux \<equiv> let _=TYPE('a::len) in int::nat\<Rightarrow>int"
  definition [simp]: "snat_uint_downcast_aux \<equiv> let _=TYPE('a::len) in int::nat\<Rightarrow>int"
    
  sepref_decl_op uint_uint_upcast: "uint_uint_upcast_aux" :: "int_rel \<rightarrow> int_rel" .
  sepref_decl_op uint_uint_downcast: "uint_uint_downcast_aux" :: "int_rel \<rightarrow> int_rel" .
  sepref_decl_op uint_uint_trunc: "uint_uint_trunc_aux" :: "int_rel \<rightarrow> int_rel" .

  
  sepref_decl_op uint_sint_upcast: "uint_sint_upcast_aux" :: "int_rel \<rightarrow> int_rel" .
  sepref_decl_op sint_uint_downcast: "sint_uint_downcast_aux" :: "int_rel \<rightarrow> int_rel" .
    
  sepref_decl_op uint_snat_upcast: "uint_snat_upcast_aux" :: "int_rel \<rightarrow> nat_rel" .
  sepref_decl_op uint_snat_downcast: "uint_snat_downcast_aux" :: "int_rel \<rightarrow> nat_rel" .

  sepref_decl_op snat_uint_upcast: "snat_uint_upcast_aux" :: "nat_rel \<rightarrow> int_rel" .
  sepref_decl_op snat_uint_downcast: "snat_uint_downcast_aux" :: "nat_rel \<rightarrow> int_rel" .
  
    
  sepref_decl_op uint_sint_conv: "id::int\<Rightarrow>_" :: "int_rel \<rightarrow> int_rel" .
  sepref_decl_op sint_uint_conv: "id::int\<Rightarrow>_" :: "int_rel \<rightarrow> int_rel" .
  sepref_decl_op unat_uint_conv: "int" :: "nat_rel \<rightarrow> int_rel" .
  sepref_decl_op uint_unat_conv: "nat" :: "int_rel \<rightarrow> nat_rel" .
  
  
  
  sepref_decl_op uint_add_mod: "\<lambda>a b :: int. (a+b) mod 2^LENGTH('a)" :: "int_rel \<rightarrow> int_rel \<rightarrow> int_rel" .
  sepref_decl_op uint_sub_mod: "\<lambda>a b :: int. (a-b) mod 2^LENGTH('a)" :: "int_rel \<rightarrow> int_rel \<rightarrow> int_rel" .
  sepref_decl_op uint_mul_mod: "\<lambda>a b :: int. (a*b) mod 2^LENGTH('a)" :: "int_rel \<rightarrow> int_rel \<rightarrow> int_rel" .
  

  sepref_decl_op snat_uint_conv: "int" :: "nat_rel \<rightarrow> int_rel" .
  sepref_decl_op uint_snat_conv: "nat" :: "int_rel \<rightarrow> nat_rel" .
  
    
end

lemma annot_uint_uint_upcast: "x = op_uint_uint_upcast TYPE('l::len) x" by simp 
lemma annot_uint_uint_downcast: "x = op_uint_uint_downcast TYPE('l::len) x" by simp 

lemma annot_uint_sint_upcast: "x = op_uint_sint_upcast TYPE('l::len) x" by simp 
lemma annot_sint_uint_downcast: "x = op_sint_uint_downcast TYPE('l::len) x" by simp 

lemma annot_uint_snat_upcast: "nat x = op_uint_snat_upcast TYPE('l::len) x" by simp 
lemma annot_uint_snat_downcast: "nat x = op_uint_snat_downcast TYPE('l::len) x" by simp 

lemma annot_snat_uint_upcast: "int x = op_snat_uint_upcast TYPE('l::len) x" by simp 
lemma annot_snat_uint_downcast: "int x = op_snat_uint_downcast TYPE('l::len) x" by simp 

lemma annot_uint_sint_conv: "x = op_uint_sint_conv x" by simp 
lemma annot_sint_uint_conv: "x = op_sint_uint_conv x" by simp  
lemma annot_unat_uint_conv: "int x = op_unat_uint_conv x" by simp  
lemma annot_uint_unat_conv: "nat x = op_uint_unat_conv x" by simp  

lemma annot_snat_uint_conv: "int x = op_snat_uint_conv x" by simp  
lemma annot_uint_snat_conv: "nat x = op_uint_snat_conv x" by simp  


lemma in_uint_rel_conv_assn: "\<up>((xi, x) \<in> uint_rel) = \<upharpoonleft>uint.assn x xi"
  by (auto simp: uint_rel_def uint.assn_is_rel pure_app_eq)

lemma in_sint_rel_conv_assn: "\<up>((xi, x) \<in> sint_rel) = \<upharpoonleft>sint.assn x xi"
  by (auto simp: sint_rel_def sint.assn_is_rel pure_app_eq)
  
thm in_snat_rel_conv  

context fixes BIG :: "'big::len" and SMALL :: "'small::len" begin  
  lemma uint_uint_upcast_refine: 
    "(uint_uint_upcast TYPE('big), PR_CONST (mop_uint_uint_upcast TYPE('big))) \<in> [\<lambda>_. is_up' UCAST('small \<rightarrow> 'big)]\<^sub>a (uint_assn' TYPE('small::len))\<^sup>k \<rightarrow> uint_assn"
    supply [simp] = in_uint_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) uint_uint_upcast_refine fixes 'big 'small by simp
  
  lemma uint_uint_downcast_refine: 
    "(uint_uint_downcast TYPE('small), PR_CONST (mop_uint_uint_downcast TYPE('small))) 
      \<in> [\<lambda>x. is_down' UCAST('big \<rightarrow> 'small) \<and> x<max_uint LENGTH('small)]\<^sub>a (uint_assn' TYPE('big::len))\<^sup>k \<rightarrow> uint_assn"
    supply [simp] = in_uint_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) uint_uint_downcast_refine fixes 'big 'small by simp
  
  
  lemma uint_uint_trunc_refine: 
    "(uint_uint_trunc TYPE('small), PR_CONST (mop_uint_uint_trunc TYPE('small))) 
      \<in> [\<lambda>x. is_down' UCAST('big \<rightarrow> 'small)]\<^sub>a (uint_assn' TYPE('big::len))\<^sup>k \<rightarrow> uint_assn"
    supply [simp] = in_uint_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'

  sepref_decl_impl (ismop) uint_uint_trunc_refine fixes 'big 'small by simp
    
end
  
context fixes BIG :: "'big::len2" and SMALL :: "'small::len" begin  

  lemma uint_sint_upcast_refine: 
    "(uint_sint_upcast TYPE('big), PR_CONST (mop_uint_sint_upcast TYPE('big))) \<in> [\<lambda>_. is_up' UCAST('small \<rightarrow> 'big)]\<^sub>a (uint_assn' TYPE('small::len))\<^sup>k \<rightarrow> sint_assn"
    supply [simp] = in_uint_rel_conv_assn in_sint_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) uint_sint_upcast_refine fixes 'big 'small by simp
  
  lemma sint_uint_downcast_refine: 
    "(sint_uint_downcast TYPE('small), PR_CONST (mop_sint_uint_downcast TYPE('small))) 
      \<in> [\<lambda>x. is_down' UCAST('big \<rightarrow> 'small) \<and> 0\<le>x \<and> x<max_uint LENGTH('small)]\<^sub>a (sint_assn' TYPE('big))\<^sup>k \<rightarrow> uint_assn"
    supply [simp] = in_uint_rel_conv_assn in_sint_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) sint_uint_downcast_refine fixes 'big 'small by simp
        
end


context fixes BIG :: "'big::len2" and SMALL :: "'small::len2" begin  

  lemma uint_snat_upcast_refine: 
    "(uint_snat_upcast TYPE('big), PR_CONST (mop_uint_snat_upcast TYPE('big))) \<in> [\<lambda>_. is_up' UCAST('small \<rightarrow> 'big)]\<^sub>a (uint_assn' TYPE('small))\<^sup>k \<rightarrow> snat_assn"
    supply [simp] = in_uint_rel_conv_assn in_snat_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) uint_snat_upcast_refine fixes 'big 'small by simp
  
  lemma uint_snat_downcast_refine: 
    "(uint_snat_downcast TYPE('small), PR_CONST (mop_uint_snat_downcast TYPE('small))) 
      \<in> [\<lambda>x. is_down' UCAST('big \<rightarrow> 'small) \<and> nat x<max_snat LENGTH('small)]\<^sub>a (uint_assn' TYPE('big))\<^sup>k \<rightarrow> snat_assn"
    supply [simp] = in_uint_rel_conv_assn in_snat_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) uint_snat_downcast_refine fixes 'big 'small by simp
        
end

context fixes BIG :: "'big::len2" and SMALL :: "'small::len2" begin  

  lemma snat_uint_upcast_refine: 
    "(snat_uint_upcast TYPE('big), PR_CONST (mop_snat_uint_upcast TYPE('big))) \<in> [\<lambda>_. is_up' UCAST('small \<rightarrow> 'big)]\<^sub>a (snat_assn' TYPE('small))\<^sup>k \<rightarrow> uint_assn"
    supply [simp] = in_uint_rel_conv_assn in_snat_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) snat_uint_upcast_refine fixes 'big 'small by simp
  
  lemma snat_uint_downcast_refine: 
    "(snat_uint_downcast TYPE('small), PR_CONST (mop_snat_uint_downcast TYPE('small))) 
      \<in> [\<lambda>x. is_down' UCAST('big \<rightarrow> 'small) \<and> int x<max_uint LENGTH('small)]\<^sub>a (snat_assn' TYPE('big))\<^sup>k \<rightarrow> uint_assn"
    supply [simp] = in_uint_rel_conv_assn in_snat_rel_conv_assn
    apply sepref_to_hoare
    apply simp
    by vcg'
  
  sepref_decl_impl (ismop) snat_uint_downcast_refine fixes 'big 'small by simp
        
end


context fixes L :: "'l::len" begin  

  lemma add_mod_refine: "((+), ((op_uint_add_mod TYPE('l)))) \<in> uint_rel' TYPE('l) \<rightarrow> uint_rel \<rightarrow> uint_rel"
    by (auto simp: uint_rel_def uint.rel_def in_br_conv uint_word_ariths)
  
  sepref_decl_impl add_mod_refine[sepref_dbg_import_rl_only, unfolded arith_inlines, to_hfref] .  

  lemma sub_mod_refine: "((-), ((op_uint_sub_mod TYPE('l)))) \<in> uint_rel' TYPE('l) \<rightarrow> uint_rel \<rightarrow> uint_rel"
    by (auto simp: uint_rel_def uint.rel_def in_br_conv uint_word_ariths)
  
  sepref_decl_impl sub_mod_refine[sepref_dbg_import_rl_only, unfolded arith_inlines, to_hfref] .  
  
      
  lemma mul_mod_refine: "((*), ((op_uint_mul_mod TYPE('l)))) \<in> uint_rel' TYPE('l) \<rightarrow> uint_rel \<rightarrow> uint_rel"
    by (auto simp: uint_rel_def uint.rel_def in_br_conv uint_word_ariths)
  
  sepref_decl_impl mul_mod_refine[sepref_dbg_import_rl_only, unfolded arith_inlines, to_hfref] .  

end


context fixes T::"'l::len2" begin
  lemma uint_sint_conv_refine: "(\<lambda>x. x, op_uint_sint_conv) 
    \<in> [\<lambda>x. x<max_sint LENGTH('l::len2)]\<^sub>f uint_rel' TYPE('l) \<rightarrow> sint_rel' TYPE('l)"
    by (auto 
      intro!: frefI 
      simp: sint_rel_def uint_rel_def sint.rel_def uint.rel_def
      simp: in_br_conv max_sint_def 
      simp: sint_eq_uint_2pl'
      )
      
  sepref_decl_impl uint_sint_conv_refine[sepref_param] fixes 'l by auto
  
  lemma sint_uint_conv_refine: "(\<lambda>x. x, op_sint_uint_conv)
    \<in> [\<lambda>x. 0\<le>x]\<^sub>f sint_rel' TYPE('l) \<rightarrow> uint_rel' TYPE('l)"
    by (auto
      intro!: frefI
      simp: sint_rel_def uint_rel_def sint.rel_def uint.rel_def
      simp: in_br_conv max_sint_def 
      simp: pos_sint_to_uint
      )
      

  sepref_decl_impl sint_uint_conv_refine[sepref_param] fixes 'l .
  

  lemma uint_unat_conv_refine: "(\<lambda>x. x, op_uint_unat_conv) 
    \<in> uint_rel' TYPE('l) \<rightarrow> unat_rel' TYPE('l)"
    by (auto simp: unat_rel_def uint_rel_def unat.rel_def uint.rel_def in_br_conv)
      
  sepref_decl_impl uint_unat_conv_refine[sepref_param] fixes 'l .
  
  lemma unat_uint_conv_refine: "(\<lambda>x. x, op_unat_uint_conv) 
    \<in> unat_rel' TYPE('l) \<rightarrow> uint_rel' TYPE('l)"
    by (auto simp: unat_rel_def uint_rel_def unat.rel_def uint.rel_def in_br_conv)
      
  sepref_decl_impl unat_uint_conv_refine[sepref_param] fixes 'l .
  
  
  
  
  
    
  
  lemma snat_uint_conv_refine: "(\<lambda>x. x, op_snat_uint_conv)
    \<in> snat_rel' TYPE('l) \<rightarrow> uint_rel' TYPE('l)"
    apply (clarsimp simp: in_snat_rel_conv in_uint_rel_conv)
    by (simp add: sint_eq_uint)
      

  sepref_decl_impl snat_uint_conv_refine[sepref_param] fixes 'l .

  lemma uint_snat_conv_refine: "(\<lambda>x. x, op_uint_snat_conv)
    \<in> [\<lambda>x. nat x < max_snat LENGTH('l)]\<^sub>f uint_rel' TYPE('l) \<rightarrow> snat_rel' TYPE('l)"
    apply (clarsimp simp: in_snat_rel_conv in_uint_rel_conv intro!: frefI)
    by (simp add: max_snat_def msb_unat_big sint_eq_uint)

  sepref_decl_impl uint_snat_conv_refine[sepref_param] fixes 'l by blast
  
    
  
end





lemma in_uint_rel_boundsD[sepref_bounds_dest]: 
  "(w,i)\<in>uint_rel' TYPE('l::len) \<Longrightarrow> 0 \<le> i \<and> i < max_uint LENGTH('l)"
  by (auto simp: uint_rel_def uint.rel_def in_br_conv)
  
lemmas [sepref_bounds_simps] = max_uint_def


lemma uint_distr_lshr: "uint (w >> n) = uint w >> n"
  by (metis shiftr_div_2n shiftr_eq_div)


lemma bit_lshift_uint_assn[sepref_fr_rules]:
  \<open>(uncurry ll_lshr, uncurry (RETURN oo (>>))) \<in> [\<lambda>(a,b). b < LENGTH('a)]\<^sub>a
    (uint_assn' TYPE('a::len2))\<^sup>k *\<^sub>a (snat_assn)\<^sup>k \<rightarrow> (uint_assn)\<close>
  apply sepref_to_hoare
  unfolding ll_lshr_def op_lift_arith2_def Let_def
  apply (vcg)
  subgoal 
    by (auto simp: shift_ovf_def uint_rel_def uint.rel_def word_to_lint_to_uint_conv in_br_conv snat_rel_def snat.rel_def snat_eq_unat)
  subgoal 
    by (simp add: sep_algebra_simps bitLSHR'_def word_to_lint_to_uint_conv
        uint_rel_def uint.rel_def in_br_conv POSTCOND_def  exists_pure_conv
        snat_rel_def snat.rel_def snat_eq_unat uint_distr_lshr
        flip: word_to_lint_lshr)
        
  done

lemma uint_distr_shl:
  "uint a << k < max_uint LENGTH('l) \<Longrightarrow> k < LENGTH('l)  \<Longrightarrow> uint (a << k) = uint (a::'l::len word) << k"
  apply (auto simp: shiftl_def push_bit_eq_mult)
  by (metis max_uint_def uint_mult_lem uint_power_lower)

lemma bit_shiftl_uint_assn[sepref_fr_rules]:
  \<open>(uncurry ll_shl, uncurry (RETURN oo (<<))) \<in> [\<lambda>(a,b). b < LENGTH('a) \<and> (a << b) < max_uint LENGTH('a)]\<^sub>a
    (uint_assn' TYPE('a::len2))\<^sup>k *\<^sub>a (snat_assn)\<^sup>k \<rightarrow> (uint_assn)\<close>
proof -
  show ?thesis
    apply sepref_to_hoare
    unfolding ll_shl_def op_lift_arith2_def Let_def
    apply (vcg)
    subgoal 
      by (auto simp: shift_ovf_def uint_rel_def uint.rel_def word_to_lint_to_uint_conv in_br_conv snat_rel_def snat.rel_def snat_eq_unat)
    subgoal by (simp add: sep_algebra_simps bitSHL'_def word_to_lint_to_uint_conv
          uint_rel_def uint.rel_def in_br_conv POSTCOND_def uint_distr_shl exists_pure_conv snat_rel_def snat.rel_def snat_eq_unat
          flip: word_to_lint_shl)
    done
qed


lemma sint_distr_ashr: "sint (w >>> n) = sint w >> n"
  by (simp add: shiftr_eq_div sshiftr_div_2n)


lemma bit_ashift_sint_assn[sepref_fr_rules]:
  \<open>(uncurry ll_ashr, uncurry (RETURN oo (>>))) \<in> [\<lambda>(a,b). b < LENGTH('a)]\<^sub>a
    (sint_assn' TYPE('a::len2))\<^sup>k *\<^sub>a (snat_assn)\<^sup>k \<rightarrow> (sint_assn)\<close>
  apply sepref_to_hoare
  unfolding ll_ashr_def op_lift_arith2_def Let_def
  apply (vcg)
  subgoal 
    by (auto simp: shift_ovf_def uint_rel_def uint.rel_def word_to_lint_to_uint_conv in_br_conv snat_rel_def snat.rel_def snat_eq_unat)
  subgoal 
    by (simp add: sep_algebra_simps bitASHR'_def word_to_lint_to_uint_conv
        sint_rel_def sint.rel_def in_br_conv POSTCOND_def  exists_pure_conv
        snat_rel_def snat.rel_def snat_eq_unat sint_distr_ashr
        flip: word_to_lint_ashr)
  done

lemma uint_const_fold: 
  "0 = uint_const TYPE('a::len) 0"
  "1 = uint_const TYPE('a::len) 1"
  "numeral n = uint_const TYPE('a::len) (numeral n)"
  by simp_all
  
lemma annot_num_const_cong_add:  
  "\<And>a b. uint_const a b = uint_const a b" 
  ..
  
method annot_uint_const for T::"'a::len itself" = 
  (rule hfref_absfun_convI),
  (simp only: uint_const_fold[where 'a='a] cong: annot_num_const_cong annot_num_const_cong_add),
  (rule CNV_I)
  


definition snat_const' :: "'l::len2 itself \<Rightarrow> nat \<Rightarrow> nat" where
  [simp,sepref_preproc]: "snat_const' T n \<equiv> snat_const TYPE('l) n"

lemma snat_const_fold': "n = snat_const' T n" by simp

definition uint_const' :: "'l::len2 itself \<Rightarrow> int \<Rightarrow> int" where
  [simp,sepref_preproc]: "uint_const' T n \<equiv> uint_const TYPE('l) n"

lemma uint_const_fold': "n = uint_const' T n" by simp

definition unat_const' :: "'l::len2 itself \<Rightarrow> nat \<Rightarrow> nat" where
  [simp,sepref_preproc]: "unat_const' T n \<equiv> unat_const TYPE('l) n"

lemma unat_const_fold': "n = unat_const' T n" by simp
  
definition sint_const' :: "'l::len2 itself \<Rightarrow> int \<Rightarrow> int" where
  [simp,sepref_preproc]: "sint_const' T n \<equiv> sint_const TYPE('l) n"

lemma sint_const_fold': "n = sint_const' T n" by simp
  

  
  
  
    
subsection \<open>Word operations with Assertions\<close>  
  
  lemma power2_2times_split: "(2::int)^(2*W) = 2^W * 2^W"
    by (simp_all add: algebra_simps power2_eq_square power_mult)

    
  lemma minus_power_le_nonneg[simp]: "0\<le>y \<Longrightarrow> -(2^w) \<le> y" for y::int
    by (smt (verit) zero_le_power) 
  
  

  locale bounded_binop_abs =
    fixes B :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
    fixes absB :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  begin
    context fixes W :: nat begin
  
      definition "op a b \<equiv> doN { ASSERT(absB a b \<and> B W (f a b)); RETURN (f a b ) }"
    
      lemma op_correct[refine_vcg]: "absB a b \<Longrightarrow> B W (f a b) \<Longrightarrow> op a b \<le> SPEC (\<lambda>r. r = f a b \<and> B W r)"
        unfolding op_def by auto
  
      sepref_register "op"
    end  
    
    
  end  
    
  locale bounded_binop = bounded_binop_abs +
    fixes fi :: "'c \<Rightarrow> 'c \<Rightarrow> 'c llM"
    fixes A :: "'a \<Rightarrow> 'c \<Rightarrow> assn"
    fixes L :: "'l::len itself"
    
    assumes refine: "(uncurry fi,uncurry (RETURN oo f))\<in>[\<lambda>(a,b). absB a b \<and> B LENGTH('l) (f a b)]\<^sub>a A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow> A"
    
  begin

    context
      notes [[sepref_register_adhoc f]]
      notes [sepref_fr_rules] = refine
    begin
      
      lemma hnr[sepref_fr_rules]: "(uncurry fi, uncurry (PR_CONST (op LENGTH('l)))) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a A"
        unfolding op_def PR_CONST_def 
        by sepref
      
    end      
  
  end

  
  locale bounded_cast_abs =
    fixes Bdst :: "nat \<Rightarrow> 'b \<Rightarrow> bool"
    fixes f :: "'a \<Rightarrow> 'b"
  begin
    context fixes W :: nat begin
  
      definition "op a \<equiv> doN { ASSERT(Bdst W (f a)); RETURN (f a ) }"
    
      lemma op_correct[refine_vcg]: "Bdst W (f a) \<Longrightarrow> op a \<le> SPEC (\<lambda>r. r = f a \<and> Bdst W r)"
        unfolding op_def by auto
  
      sepref_register "op"
    end  
    
  end  
    
  locale bounded_cast = bounded_cast_abs Bdst f for Bdst and f :: "'a \<Rightarrow> 'b" +
    fixes fi :: "'c \<Rightarrow> 'd llM"
    fixes Asrc :: "'a \<Rightarrow> 'c \<Rightarrow> assn"
    fixes Adst :: "'b \<Rightarrow> 'd \<Rightarrow> assn"
    fixes Rcond :: "bool"
    fixes L :: "'l::len itself"
    
    assumes refine: "(fi, (RETURN o f))\<in>[\<lambda>a. Rcond \<and> Bdst LENGTH('l) (f a)]\<^sub>a Asrc\<^sup>k \<rightarrow> Adst"
    
  begin

  
    context
      notes [[sepref_register_adhoc "(f)"]]
      notes [sepref_fr_rules] = refine
    begin
      
      lemma hnr[sepref_fr_rules]: "(fi, (PR_CONST (op LENGTH('l)))) \<in> [\<lambda>_. Rcond]\<^sub>a Asrc\<^sup>k \<rightarrow> Adst"
        unfolding op_def PR_CONST_def 
        by sepref
      
    end      
  
  end

  
  subsubsection \<open>Bounds\<close>
  
  
  definition "bnd_u W x \<equiv> x\<in>uints W"
  definition "bnd_s W x \<equiv> x\<in>sints W"
  definition "bnd_n W x \<equiv> x\<in>snats W"
    
  lemma bnd_u_numeral_simps[simp]:
    "bnd_u l 0"
    "bnd_u l 1 \<longleftrightarrow> l\<noteq>0"
    "bnd_u l (numeral n) \<longleftrightarrow> 0\<le>(numeral n::int) \<and> (numeral n::int) < 2^l"
    unfolding bnd_u_def uints_num 
    subgoal by auto
    subgoal by (cases "l=0") auto
    subgoal by auto
    done  
  
  lemma bnd_s_numeral_simps[simp]:
    "bnd_s l 0"
    "bnd_s l 1 \<longleftrightarrow> 1<l"
    "bnd_s l (-1)"
    "bnd_s l (numeral n) \<longleftrightarrow> -(2^(l-1)) \<le> (numeral n::int) \<and> (numeral n::int) < 2^(l-1)"
    "bnd_s l (-numeral n) \<longleftrightarrow> -(2^(l-1)) \<le> (-numeral n::int) \<and> (-numeral n::int) < 2^(l-1)"
    unfolding bnd_s_def sints_num 
    subgoal by auto
    subgoal 
      apply clarsimp
      by (smt (verit, ccfv_threshold) diff_is_0_eq not_less one_less_power power_0 zero_less_diff)
    subgoal
      apply (cases l; clarsimp)
      by (smt (verit) zero_le_power) 
    subgoal by (clarsimp)
    subgoal by clarsimp
    done  

  lemma bnd_n_numeral_simps[simp]:
    "bnd_n l 0"
    "bnd_n l 1 \<longleftrightarrow> 1<l"
    "bnd_n l (numeral n) \<longleftrightarrow> (numeral n::nat) < 2^(l-1)"
    unfolding bnd_n_def snats_def  
    subgoal by auto
    subgoal 
      apply (cases l; clarsimp)
      using Suc_le_eq pow_mono_leq_imp_lt by fastforce
    subgoal by auto
    done  
    
    
  subsubsection \<open>Casts\<close>
      
  interpretation cast_u: bounded_cast_abs "bnd_u" "id" .
  interpretation cast_s: bounded_cast_abs "bnd_s" "id" .
  interpretation cast_n: bounded_cast_abs "bnd_n" "id" .

  interpretation cast_nu: bounded_cast_abs "bnd_u" "int" .
  interpretation cast_un: bounded_cast_abs "bnd_n" "nat" .
  
    
  interpretation dcast_uu: bounded_cast "bnd_u" "id" "uint_uint_downcast TYPE('ld::len)" "uint_assn' TYPE('ls::len)" "uint_assn' TYPE('ld::len)" "is_down' (UCAST ('ls \<rightarrow> 'ld))" "TYPE('ld)"
    apply unfold_locales
    unfolding bnd_u_def id_def
    apply (rewrite in "RETURN o (\<hole>)" annot_uint_uint_downcast[where 'l='ld])
    by sepref
  
  interpretation ucast_uu: bounded_cast "bnd_u" "id" "uint_uint_upcast TYPE('ld::len)" "uint_assn' TYPE('ls::len)" "uint_assn' TYPE('ld::len)" "is_up' (UCAST ('ls \<rightarrow> 'ld))" "TYPE('ld)"
    apply unfold_locales
    unfolding id_def
    apply (rewrite in "RETURN o (\<hole>)" annot_uint_uint_upcast[where 'l='ld])
    by sepref
    
  interpretation dcast_su: bounded_cast "bnd_u" "id" "sint_uint_downcast TYPE('ld::len)" 
    "sint_assn' TYPE('ls::len2)" "uint_assn' TYPE('ld::len)" "is_down' (UCAST ('ls \<rightarrow> 'ld))" "TYPE('ld)"  
    apply unfold_locales
    unfolding bnd_u_def id_def
    apply (rewrite in "RETURN o (\<hole>)" annot_sint_uint_downcast[where 'l='ld])
    by sepref
    
  interpretation ucast_us: bounded_cast "bnd_s" "id" "uint_sint_upcast TYPE('ld::len2)" 
    "uint_assn' TYPE('ls::len)" "sint_assn' TYPE('ld)" "is_up' (UCAST ('ls \<rightarrow> 'ld))" "TYPE('ld)"  
    apply unfold_locales
    unfolding id_def
    apply (rewrite in "RETURN o (\<hole>)" annot_uint_sint_upcast[where 'l='ld])
    by sepref

    
  interpretation conv_us: bounded_cast "bnd_s" "id" "Mreturn" 
    "uint_assn' TYPE('l::len2)" "sint_assn' TYPE('l)" "True" "TYPE('l)"  
    apply unfold_locales
    unfolding bnd_s_def id_def
    apply (rewrite in "RETURN o (\<hole>)" annot_uint_sint_conv)
    by sepref
        
  interpretation conv_su: bounded_cast "bnd_u" "id" "Mreturn" 
    "sint_assn' TYPE('l::len2)" "uint_assn' TYPE('l)" "True" "TYPE('l)"  
    apply unfold_locales
    unfolding bnd_u_def id_def
    apply (rewrite in "RETURN o (\<hole>)" annot_sint_uint_conv)
    by sepref

  interpretation conv_nu: bounded_cast "bnd_u" "op_snat_uint_conv" "Mreturn" 
    "snat_assn' TYPE('l::len2)" "uint_assn' TYPE('l)" "True" "TYPE('l)"  
    apply unfold_locales
    unfolding bnd_u_def id_def
    by sepref

  interpretation conv_un: bounded_cast "bnd_n" "op_uint_snat_conv" "Mreturn" 
    "uint_assn' TYPE('l::len2)" "snat_assn' TYPE('l)" "True" "TYPE('l)"  
    apply unfold_locales
    unfolding bnd_n_def id_def
    by sepref
    
  interpretation dcast_nn: bounded_cast "bnd_n" "id" "snat_snat_downcast TYPE('ld)" "snat_assn' TYPE('ls::len2)" "snat_assn' TYPE('ld::len2)" "is_down' (UCAST ('ls \<rightarrow> 'ld))" "TYPE('ld)"
    apply unfold_locales
    unfolding bnd_n_def id_def
    apply (rewrite in "RETURN o (\<hole>)" annot_snat_snat_downcast[where 'l='ld])
    by sepref
  
  interpretation ucast_nn: bounded_cast "bnd_n" "id" "snat_snat_upcast TYPE('ld)" "snat_assn' TYPE('ls::len2)" "snat_assn' TYPE('ld::len2)" "is_up' (UCAST ('ls \<rightarrow> 'ld))" "TYPE('ld)"
    apply unfold_locales
    unfolding bnd_n_def id_def
    apply (rewrite in "RETURN o (\<hole>)" annot_snat_snat_upcast[where 'l='ld])
    by sepref

  interpretation ucast_un: bounded_cast "bnd_n" "nat" "uint_snat_upcast TYPE('ld)" "uint_assn' TYPE('ls::len2)" "snat_assn' TYPE('ld::len2)" "is_up' (UCAST ('ls \<rightarrow> 'ld))" "TYPE('ld)"
    apply unfold_locales
    unfolding bnd_n_def id_def 
    apply (rewrite in "RETURN o (\<hole>)" annot_uint_snat_upcast[where 'l='ld, abs_def])
    by sepref
    
  interpretation dcast_un: bounded_cast "bnd_n" "nat" "uint_snat_downcast TYPE('ld)" "uint_assn' TYPE('ls::len2)" "snat_assn' TYPE('ld::len2)" "is_down' (UCAST ('ls \<rightarrow> 'ld))" "TYPE('ld)"
    apply unfold_locales
    unfolding bnd_n_def id_def 
    apply (rewrite in "RETURN o (\<hole>)" annot_uint_snat_downcast[where 'l='ld, abs_def])
    by sepref
    

  interpretation ucast_nu: bounded_cast "bnd_u" "int" "snat_uint_upcast TYPE('ld)" "snat_assn' TYPE('ls::len2)" "uint_assn' TYPE('ld::len2)" "is_up' (UCAST ('ls \<rightarrow> 'ld))" "TYPE('ld)"
    apply unfold_locales
    unfolding bnd_u_def id_def 
    apply (rewrite in "RETURN o (\<hole>)" annot_snat_uint_upcast[where 'l='ld, abs_def])
    by sepref
    
  interpretation dcast_nu: bounded_cast "bnd_u" "int" "snat_uint_downcast TYPE('ld)" "snat_assn' TYPE('ls::len2)" "uint_assn' TYPE('ld::len2)" "is_down' (UCAST ('ls \<rightarrow> 'ld))" "TYPE('ld)"
    apply unfold_locales
    unfolding bnd_u_def id_def 
    apply (rewrite in "RETURN o (\<hole>)" annot_snat_uint_downcast[where 'l='ld, abs_def])
    by sepref    
        
        
  subsubsection \<open>Operations\<close>
      
  context fixes W :: nat begin
  
    sepref_decl_op mul_mod_u: "\<lambda>a b. (a*b::int) mod 2^W" :: "int_rel \<rightarrow> int_rel \<rightarrow> int_rel" .
    sepref_decl_op add_mod_u: "\<lambda>a b. (a+b::int) mod 2^W" :: "int_rel \<rightarrow> int_rel \<rightarrow> int_rel" .
    sepref_decl_op sub_mod_u: "\<lambda>a b. (a-b::int) mod 2^W" :: "int_rel \<rightarrow> int_rel \<rightarrow> int_rel" .
    sepref_decl_op trunc_u: "\<lambda>m. (m::int) mod 2^W" :: "int_rel \<rightarrow> int_rel" .

    definition "shr_u_op a b \<equiv> doN { ASSERT(b<W); RETURN ((a::int) >> b)}"  
    definition "shl_u_op a b \<equiv> doN { ASSERT(b<W \<and> a<<b < max_uint W); RETURN ((a::int) << b)}"  
    sepref_register shr_u_op shl_u_op
      
  end

  lemma op_mul_mod_u_alt: "op_mul_mod_u LENGTH('l::len) = op_uint_mul_mod TYPE('l)" by simp
  lemma op_add_mod_u_alt: "op_add_mod_u LENGTH('l::len) = op_uint_add_mod TYPE('l)" by simp
  lemma op_sub_mod_u_alt: "op_sub_mod_u LENGTH('l::len) = op_uint_sub_mod TYPE('l)" by simp
  lemma op_trunc_u_alt: "op_trunc_u LENGTH('l::len) = op_uint_uint_trunc TYPE('l)" by simp

  lemma shr_u_op_correct[refine_vcg]: "b<W \<Longrightarrow> shr_u_op W a b \<le> SPEC (\<lambda>r. r = a div (2^b))"
    unfolding shr_u_op_def
    by (simp add: shiftr_int_def)
    
  lemma shl_u_op_correct[refine_vcg]: "b<W \<Longrightarrow> bnd_u W (a*2^b) \<Longrightarrow> shl_u_op W a b \<le> SPEC (\<lambda>r. r = a * (2^b))"
    unfolding shl_u_op_def
    apply (refine_vcg)
    by (simp_all add: shiftl_int_def bnd_u_def)
  
  lemma op_mul_mod_u_hnr: "(uncurry ll_mul, uncurry (RETURN oo PR_CONST (op_mul_mod_u LENGTH('l::len)))) \<in> 
    (uint_assn' TYPE('l::len))\<^sup>k *\<^sub>a (uint_assn' TYPE('l::len))\<^sup>k \<rightarrow>\<^sub>a uint_assn' TYPE('l)"  
    unfolding PR_CONST_def op_mul_mod_u_alt
    by sepref

  sepref_decl_impl op_mul_mod_u_hnr . 
    
  lemma op_add_mod_u_hnr: "(uncurry ll_add, uncurry (RETURN oo PR_CONST (op_add_mod_u LENGTH('l::len)))) \<in> 
    (uint_assn' TYPE('l::len))\<^sup>k *\<^sub>a (uint_assn' TYPE('l::len))\<^sup>k \<rightarrow>\<^sub>a uint_assn' TYPE('l)"  
    unfolding PR_CONST_def op_add_mod_u_alt
    by sepref

  sepref_decl_impl op_add_mod_u_hnr . 
    
  lemma op_sub_mod_u_hnr: "(uncurry ll_sub, uncurry (RETURN oo PR_CONST (op_sub_mod_u LENGTH('l::len)))) \<in> 
    (uint_assn' TYPE('l::len))\<^sup>k *\<^sub>a (uint_assn' TYPE('l::len))\<^sup>k \<rightarrow>\<^sub>a uint_assn' TYPE('l)"  
    unfolding PR_CONST_def op_sub_mod_u_alt
    by sepref

  sepref_decl_impl op_sub_mod_u_hnr . 
            
  lemma op_trunc_u_hnr: "(uint_uint_trunc TYPE('ld), RETURN o PR_CONST (op_trunc_u LENGTH('ld::len))) \<in> 
    [\<lambda>_. is_down' (UCAST ('ls \<rightarrow> 'ld))]\<^sub>a (uint_assn' TYPE('ls::len))\<^sup>k \<rightarrow> uint_assn' TYPE('ld)"  
    unfolding PR_CONST_def op_trunc_u_alt
    by sepref

  context
    fixes LS :: "'ls::len itself" 
    fixes LD :: "'ld::len itself" 
  begin  
    sepref_decl_impl op_trunc_u_hnr[where 'ls='ls and 'ld='ld] fixes 'ld 'ls by blast 
  end  
          
  lemma shr_u_op_hnr[sepref_fr_rules]: "(uncurry ll_lshr, uncurry (PR_CONST (shr_u_op LENGTH('l)))) 
    \<in> (uint_assn' TYPE('l::len2))\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a uint_assn"  
    unfolding shr_u_op_def PR_CONST_def
    by sepref
  
  lemma shl_u_op_hnr[sepref_fr_rules]: "(uncurry ll_shl, uncurry (PR_CONST (shl_u_op LENGTH('l)))) 
    \<in> (uint_assn' TYPE('l::len2))\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow>\<^sub>a uint_assn"  
    unfolding shl_u_op_def PR_CONST_def
    by sepref
    
  definition [simp]: "abs_bound_triv a b \<equiv> True"
  
  
  interpretation add_uuu: bounded_binop_abs bnd_u abs_bound_triv  "(+)" .
  
  interpretation add_uuu: bounded_binop bnd_u abs_bound_triv "(+)" "ll_add" "uint_assn' TYPE('l::len)" "TYPE('l)" 
    apply unfold_locales
    unfolding bnd_u_def
    by sepref

  interpretation sub_uuu: bounded_binop_abs bnd_u abs_bound_triv "(-)" .
  interpretation sub_uuu: bounded_binop bnd_u abs_bound_triv "(-)" "ll_sub" "uint_assn' TYPE('l::len)" "TYPE('l)" 
    apply unfold_locales
    unfolding bnd_u_def
    by sepref
    
  interpretation mul_uuu: bounded_binop_abs bnd_u abs_bound_triv "(*)" .
  interpretation mul_uuu: bounded_binop bnd_u abs_bound_triv "(*)" "ll_mul" "uint_assn' TYPE('l::len)" "TYPE('l)" 
    apply unfold_locales
    unfolding bnd_u_def
    by sepref

    
  definition [simp]: "abs_bound_div a b \<equiv> b\<noteq>0"      
  interpretation div_uuu: bounded_binop_abs bnd_u abs_bound_div "(div)" .
  interpretation div_uuu: bounded_binop bnd_u abs_bound_div "(div)"  "ll_udiv" "uint_assn' TYPE('l::len)" "TYPE('l)" 
    apply unfold_locales
    unfolding bnd_u_def
    by sepref
    
  interpretation mod_uuu: bounded_binop_abs bnd_u abs_bound_div "(mod)" .
  interpretation mod_uuu: bounded_binop bnd_u abs_bound_div "(mod)"  "ll_urem" "uint_assn' TYPE('l::len)" "TYPE('l)" 
    apply unfold_locales
    unfolding bnd_u_def
    by sepref

  interpretation add_sss: bounded_binop_abs bnd_s abs_bound_triv  "(+)" .
  interpretation add_sss: bounded_binop bnd_s abs_bound_triv "(+)" "ll_add" "sint_assn' TYPE('l::len)" "TYPE('l)" 
    apply unfold_locales
    unfolding bnd_s_def
    by sepref

  interpretation sub_sss: bounded_binop_abs bnd_s abs_bound_triv "(-)" .
  interpretation sub_sss: bounded_binop bnd_s abs_bound_triv "(-)" "ll_sub" "sint_assn' TYPE('l::len)" "TYPE('l)" 
    apply unfold_locales
    unfolding bnd_s_def
    by sepref
    
  interpretation mul_sss: bounded_binop_abs bnd_s abs_bound_triv "(*)" .
  interpretation mul_sss: bounded_binop bnd_s abs_bound_triv "(*)" "ll_mul" "sint_assn' TYPE('l::len)" "TYPE('l)" 
    apply unfold_locales
    unfolding bnd_s_def
    by sepref

    
  interpretation div_sss: bounded_binop_abs bnd_s abs_bound_div "(sdiv)" .
  interpretation div_sss: bounded_binop bnd_s abs_bound_div "(sdiv)" "ll_sdiv" "sint_assn' TYPE('l::len)" "TYPE('l)" 
    apply unfold_locales
    unfolding bnd_s_def
    by sepref
    

  experiment
  begin

          
    definition "foo TYPE('l::len) TYPE('ll::len) a b \<equiv> doN {
      t\<leftarrow>add_uuu.op LENGTH('l) a a;
      t\<leftarrow>add_uuu.op LENGTH('l) t b;
      t\<leftarrow>div_uuu.op LENGTH('l) t b;
      t\<leftarrow>mul_uuu.op LENGTH('l) t a;
      t\<leftarrow>sub_uuu.op LENGTH('l) t b;
      t\<leftarrow>mod_uuu.op LENGTH('l) t b;
      
      t \<leftarrow> cast_u.op LENGTH('ll) t;
      
      t \<leftarrow> cast_u.op LENGTH('l) t;
      t \<leftarrow> cast_s.op LENGTH('l) t;
      
      RETURN t
    }"
    
      
    lemma "foo TYPE(32) TYPE(16) 1 2 \<le> RETURN 0"
      unfolding foo_def
      apply refine_vcg
      apply simp_all
      done
    
    sepref_def foo_impl is "uncurry (PR_CONST (foo TYPE(32) TYPE(16)))" 
      :: "(uint_assn' TYPE(32))\<^sup>k *\<^sub>a (uint_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a (sint_assn' TYPE(32))"
      unfolding foo_def PR_CONST_def
      supply [simp] = is_down' is_up'
      by sepref
      
      
    
    export_llvm foo_impl
    
  end     


  subsubsection \<open>Bounds Lemmas\<close>
  
  lemma max_snat_2x_self_bound: "4<W \<Longrightarrow> 2 * W < max_snat W"  
    unfolding max_snat_def
  proof -  
    assume "4<W"
    then obtain W' where W': "W=5+W'"
      apply (rule_tac that[of "W-5"]) by auto

    have A: "(1::nat) \<le> 2^x" for x by simp  
          
    have "(5::nat)<7*2^W'"
      apply (rule order.strict_trans2[OF _ mult_mono[OF order_refl A]])
      by auto
    from add_strict_mono[OF this less_exp[of W']] have "W < 8*2^W'"
      by (simp add: W')
    also have "\<dots> = 2^(W-2)"        
      by (simp add: power_add W')
    finally have "W < 2 ^ (W - 2)" .
    from add_strict_mono[OF this this]
    have "W + W < 2 ^ (W - 2) + 2 ^ (W - 2)" .
    also have "W+W = 2*W" by simp
    also have "(2::nat) ^ (W - 2) + 2 ^ (W - 2) = 2^(W-1)"
      by (simp add: W' power_add)
    finally show "2*W < 2^(W-1)" .
  qed    
    
  lemma uints_mul_bound: "a\<in>uints W \<Longrightarrow> b\<in>uints W \<Longrightarrow> a*b\<in>uints (2*W)"
    unfolding uints_num
    by (auto simp: power2_2times_split intro: mult_strict_mono)  
    
  lemma uints_add_bound: "a\<in>uints W \<Longrightarrow> b\<in>uints W \<Longrightarrow> a+b\<in>uints (Suc W)"
    unfolding uints_num
    by (auto simp: power2_2times_split intro: mult_strict_mono)  
        
  lemma uints_diff_sint_bound: "a\<in>uints W \<Longrightarrow> b\<in>uints W \<Longrightarrow> a-b \<in> sints (Suc W)"
    unfolding uints_num sints_num
    by auto
    
  lemma uints_diff_sint_bound': "W\<noteq>0 \<Longrightarrow> a\<in>uints W \<Longrightarrow> b\<in>uints W \<Longrightarrow> a-b \<in> sints (2*W)"
    apply (erule (1) set_rev_mp[OF uints_diff_sint_bound sints_subset])
    by auto

    
    
 
  lemma bnd_u_mono: "bnd_u W b \<Longrightarrow> a\<le>b \<Longrightarrow> 0\<le>a \<Longrightarrow> bnd_u W a"
    unfolding bnd_u_def uints_num 
    by auto
    
  lemma bnd_u_strict_mono: "a<b \<Longrightarrow> bnd_u W b \<Longrightarrow> 0\<le>a \<Longrightarrow> bnd_u W a"
    unfolding bnd_u_def uints_num 
    by auto
  
  lemma bnd_u_modI_self[intro!,simp]: "bnd_u W (x mod 2^W)"  
    unfolding bnd_u_def uints_num by auto
    
  lemma bnd_u_modI[simp,intro]: "bnd_u W n \<Longrightarrow> n\<noteq>0 \<Longrightarrow> bnd_u W (x mod n)"
    unfolding bnd_u_def uints_num  
    apply clarsimp
    using pos_mod_bound[of n x] 
    by linarith     
    
    
  lemma bnd_u_monoW: "bnd_u W x \<Longrightarrow> W\<le>W' \<Longrightarrow> bnd_u W' x"  
    unfolding bnd_u_def 
    using uints_monoI by blast
      
  lemma bnd_u_extend2[simp,intro]: "bnd_u W x \<Longrightarrow> bnd_u (2*W) x"
    apply (erule bnd_u_monoW)      
    by simp
    
  lemma bnd_u_mul[simp,intro]: "bnd_u W a \<Longrightarrow> bnd_u W b \<Longrightarrow> bnd_u (2*W) (a*b)"  
    by (meson bnd_u_def uints_mul_bound)

  lemma bnd_u_add[simp,intro]: "bnd_u W a \<Longrightarrow> bnd_u W b \<Longrightarrow> bnd_u (Suc W) (a+b)"  
    by (meson bnd_u_def uints_add_bound)
    
  lemma bnd_u_add2[simp,intro]: "W\<noteq>0 \<Longrightarrow> bnd_u W a \<Longrightarrow> bnd_u W b \<Longrightarrow> bnd_u (2*W) (a+b)"  
    apply (erule bnd_u_monoW[OF bnd_u_add])  
    by auto
        
  lemma bnd_s_div_pos_triv[simp,intro]: "b>0 \<Longrightarrow> bnd_s W a \<Longrightarrow> bnd_s W (a div b)"  
    unfolding bnd_s_def sints_num 
    apply (simp;safe)
    subgoal 
      by (smt (verit, ccfv_threshold) div_by_1 pos_imp_zdiv_nonneg_iff zdiv_mono2_neg) 
    subgoal 
      by (smt (verit) div_nonpos_pos_le0 zdiv_le_dividend) 
    done
    
    
  lemma bnd_uuu_sub_le[simp,intro]: "bnd_u W a \<Longrightarrow> 0\<le>b \<Longrightarrow> b\<le>a \<Longrightarrow> bnd_u W (a-b)"
    unfolding bnd_u_def by simp
    
  lemma bnd_uus_sub[simp,intro]: "bnd_u W a \<Longrightarrow> bnd_u W b \<Longrightarrow> bnd_s (Suc W) (a-b)"
    by (meson bnd_s_def bnd_u_def uints_diff_sint_bound)
  
  lemma bnd_uus_sub2[simp,intro]: "W\<noteq>0 \<Longrightarrow> bnd_u W a \<Longrightarrow> bnd_u W b \<Longrightarrow> bnd_s (2*W) (a-b)"
    by (meson bnd_s_def bnd_u_def uints_diff_sint_bound')
    
  lemma bnd_u_upper_half[simp,intro]: "bnd_u (2*W) a \<Longrightarrow> bnd_u W (a div 2^W)"  
    unfolding bnd_u_def uints_num
    apply (clarsimp simp: power2_2times_split nonneg_mod_div)
    by (smt (verit) mult_div_le nonzero_mult_div_cancel_right zdiv_mono1 zero_less_power)
    
  lemma bnd_ext_us[simp,intro]: "bnd_u W a \<Longrightarrow> bnd_s (2*W) a"  
    unfolding bnd_u_def bnd_s_def uints_num sints_num
    apply (clarsimp simp: power2_2times_split)
    by (smt (verit, ccfv_SIG) Suc_pred gt_or_eq_0 n_less_m_mult_n not_less_eq numeral_2_eq_2 pos2 power_less_imp_less_exp)
    

    
    
  lemma bnd_n_mono: "a\<le>b \<Longrightarrow> bnd_n W b \<Longrightarrow> 0\<le>a \<Longrightarrow> bnd_n W a"
    unfolding bnd_n_def 
    by auto
    
  lemma bnd_n_strict_mono: "a<b \<Longrightarrow> bnd_n W b \<Longrightarrow> 0\<le>a \<Longrightarrow> bnd_n W a"
    unfolding bnd_n_def 
    by auto
  
  lemma bnd_n_monoW: "bnd_n W x \<Longrightarrow> W\<le>W' \<Longrightarrow> bnd_n W' x"  
    unfolding bnd_n_def 
    apply (auto simp: max_snat_def)
    apply (cases "W'"; simp)
    by (metis Suc_to_right diff_le_mono one_less_numeral_iff order_less_le_trans power_increasing_iff semiring_norm(76))
        
  lemma bnd_n_self[simp, intro]: "2<W \<Longrightarrow> bnd_n W W"
    unfolding bnd_n_def in_snats_conv max_snat_def
    by (metis One_nat_def Suc_le_eq Suc_lessD Suc_pred nat_le_Suc_less_imp numeral_2_eq_2 suc_le_pow_2)

  lemma bnd_n_ext[simp,intro]: "bnd_n W a \<Longrightarrow> bnd_n (2*W) a"  
    by (simp add: bnd_n_monoW)
  
  lemma bnd_n_2x_self: "4<W \<Longrightarrow> bnd_n W (2*W)"
    by (simp add: bnd_n_def max_snat_2x_self_bound)
    
  lemma bnd_n_lessW: "n<W \<Longrightarrow> bnd_n W n"  
    unfolding bnd_n_def in_snats_conv
    by (simp add: max_snat_def pow_mono_leq_imp_lt)
  
    
  lemma bnd_u_exp2I[simp, intro]: "n<W \<Longrightarrow> bnd_u W (2^n)"  
    by (simp add: bnd_u_def uints_num)
    
    
  lemma bnd_u_int_self[simp,intro]: "bnd_u W (int W)"      
    unfolding bnd_u_def uints_num
    by simp  
  
    
    
    
    
      
    
  subsection \<open>Doubling the Length\<close>  
  lemma is_down'_half[simp, intro!]: "is_down' UCAST ('l::len bit0 \<rightarrow> 'l)"
    by (simp add: is_down')
    
  lemma is_up'_dbl[simp, intro!]: "is_up' UCAST ('l \<rightarrow> 'l::len bit0)"
    by (simp add: is_up')
  
  lemma fold_2xLEN: "2*LENGTH('l::len) = LENGTH('l bit0)" by simp
  lemma fold_4xLEN: "4*LENGTH('l::len) = LENGTH ('l bit0 bit0)" by simp
    

  (*  
  sepref_register "LENGTH('l::len)"
  *)
  
  
  


end
