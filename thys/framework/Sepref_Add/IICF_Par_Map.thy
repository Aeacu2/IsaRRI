theory IICF_Par_Map 
imports Isabelle_LLVM.IICF IICF_More_Array 
begin


locale parmap_abs = 
  fixes P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
    and f :: "'b \<Rightarrow> 'a \<Rightarrow> 'a nres"
    and spec :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes f_spec: "\<And>b x. P b x \<Longrightarrow> f b x \<le> SPEC (\<lambda>r. spec b x r)"
begin
  definition "mspec b xs xs' \<equiv> length xs'=length xs \<and> (\<forall>i<length xs. spec b (xs!i) (xs'!i))"
  
  lemma mspec_alt: "mspec b = list_all2 (spec b)"
    unfolding mspec_def 
    by (auto simp add: fun_eq_iff list_all2_conv_all_nth)
  
  definition pmap_seq :: "'b \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list nres" where
    "pmap_seq b xs n \<equiv> doN {
      ASSERT (n=length xs);
      for 0 n (\<lambda>i xs. doN {
        xs\<leftarrow>mop_to_eo_conv xs;
      
        (x,xs) \<leftarrow> mop_eo_extract xs i;
        x \<leftarrow> f b x;
        xs \<leftarrow> mop_eo_set xs i x;
        
        xs \<leftarrow>mop_to_wo_conv xs;
        RETURN xs
      }) xs
    }"
  
  lemma pmap_seq_correct[refine_vcg]: "\<lbrakk>n=length xs; \<forall>x\<in>set xs. P b x\<rbrakk> 
    \<Longrightarrow> pmap_seq b xs n 
      \<le> SPEC (\<lambda>xs'. mspec b xs xs')"
    unfolding pmap_seq_def
    apply simp
    apply (refine_vcg 
      f_spec
      for_rule[where 
        I="\<lambda>ib xs'. length xs'=length xs 
          \<and> (\<forall>i<ib. spec b (xs!i) (xs'!i))  
          \<and> (\<forall>i\<in>{ib..<length xs}. xs'!i=xs!i)
        "])
    by (auto simp: nth_list_update mspec_def elim: in_set_upd_cases)
    
  
  definition pmap_par :: "nat \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list nres"
  where "pmap_par thr d b xs n \<equiv> doN {
    ASSERT (n = length xs);
    RECT (\<lambda>pmap_par (thr,d,b,xs,n). doN {
      if n<thr \<or> d=0 then doN {
        pmap_seq b xs n
      } else doN {
        let n\<^sub>1 = n div 2;
        let n\<^sub>2 = n - n\<^sub>1;
        let d=d-1;
        (_,xs)\<leftarrow>WITH_SPLIT n\<^sub>1 xs (\<lambda>xs\<^sub>1 xs\<^sub>2. doN {
          let thr_copy = COPY thr;
          let d_copy = COPY d;
          let b_copy = COPY b;
          (xs\<^sub>1,xs\<^sub>2) \<leftarrow> 
            nres_par 
              (pmap_par)
              (pmap_par)
              (thr_copy,d_copy,b_copy,xs\<^sub>1,n\<^sub>1)
              (thr,d,b,xs\<^sub>2,n\<^sub>2)
              ;
          RETURN (True,xs\<^sub>1,xs\<^sub>2)
        });
        RETURN xs
      }
    }) (thr, d, b, xs, n)
  }"  

  lemma pmap_par_correct[refine_vcg]:
    "\<lbrakk>n = length xs; Suc 0<thr; \<forall>x\<in>set xs. P b x\<rbrakk> \<Longrightarrow> pmap_par thr d b xs n \<le> SPEC (\<lambda>xs'. mspec b xs xs')"
    unfolding pmap_par_def mop_free_def
    supply R = RECT_rule[where 
          pre="\<lambda>(thr',d,b',xs,n). thr'=thr \<and> b'=b \<and> n=length xs \<and> (\<forall>x\<in>set xs. P b x)"
      and M="\<lambda>(_,_,_,xs,n). SPEC (mspec b xs)"    
      and V = "Wellfounded.measure (\<lambda>(thr',d,b,xs,n). d)",
      THEN order_trans
    ]
    thm R
  
    apply (refine_vcg R)
    
    apply (simp;fail)+
    subgoal by force
    
    apply (rule order_trans, rprems)
    
    subgoal by simp
    subgoal by simp
    
    apply refine_vcg
    apply (rule order_trans, rprems)
    
    
    unfolding mspec_def 
    apply (auto simp: nth_append)
    done
  


        
  definition "pmap_par_array thr d b xs n \<equiv> doN {
    xs \<leftarrow> mop_array_to_woarray xs;
    (xs,tag) \<leftarrow> split_woarray xs;
    res \<leftarrow> pmap_par thr d b xs n;
    res \<leftarrow> combine_woarray res tag;
    res \<leftarrow> mop_woarray_to_array res;  
    RETURN res
  }"
  
  lemma pmap_par_array_correct[refine_vcg]: "\<lbrakk>n = length xs; Suc 0<thr; \<forall>x\<in>set xs. P b x\<rbrakk> \<Longrightarrow>pmap_par_array thr d b xs n \<le> SPEC (\<lambda>xs'. mspec b xs xs')"
    unfolding pmap_par_array_def split_woarray_def combine_woarray_def mop_array_to_woarray_def
    apply refine_vcg
    apply (simp_all add: mspec_def)
    done
    
    
    
    
    
      
end  

thm hn_MK_FREEI

locale parmap_impl = parmap_abs P f spec 
  for P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  and f :: "'b \<Rightarrow> 'a \<Rightarrow> 'a nres"
  and spec :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  + 
  fixes size_t :: "'size_t::len2 itself"
  assumes size_len: "5\<le>LENGTH('size_t)"
  fixes A :: "'a \<Rightarrow> 'ai::llvm_rep \<Rightarrow> assn" and B :: "'b \<Rightarrow> 'bi::llvm_rep \<Rightarrow> assn"
  fixes fi :: "'bi \<Rightarrow> 'ai \<Rightarrow> 'ai llM"
  fixes copyB :: "'bi \<Rightarrow> 'bi llM" and freeB :: "'bi \<Rightarrow> unit llM"
  assumes f_hnr[sepref_fr_rules]: 
    "(uncurry fi,uncurry f) \<in> B\<^sup>k *\<^sub>a A\<^sup>d \<rightarrow>\<^sub>a A"
  (*assumes AB_pure[safe_constraint_rules]: (*"is_pure A"*) "is_pure B"*)
  
  assumes copyB_hnr[sepref_fr_rules]: "(copyB,RETURN o COPY) \<in> B\<^sup>k \<rightarrow>\<^sub>a B"
  
  assumes freeB_rl[sepref_frame_free_rules]: "MK_FREE B freeB"
  
  notes [[sepref_register_adhoc f]]
  (*notes [sepref_frame_free_rules] = AB_pure[THEN mk_free_is_pure]*)
begin

  (*abbreviation "size_t \<equiv> TYPE(64)"*)  
  abbreviation "size_assn \<equiv> snat_assn' size_t"  
    
  sepref_register pmap_seq
  
  sepref_def pmap_seq_impl is "uncurry2 (PR_CONST pmap_seq)" 
    :: "[\<lambda>_. True]\<^sub>c B\<^sup>k *\<^sub>a (woarray_slice_assn A)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> woarray_slice_assn A [\<lambda>((_,p),_) p'. p'=p]\<^sub>c"  
    unfolding pmap_seq_def PR_CONST_def
    apply (subst for_by_while)
    apply (annot_snat_const size_t)
    apply sepref_dbg_keep
    done    
    
    

  lemma size_snat_bound: 
    fixes n :: nat assumes "n<2^4" shows "n < 2 ^ (LENGTH('size_t) - Suc 0)"      
  proof -
    from size_len have "4 \<le> LENGTH('size_t) - Suc 0" by simp
    hence "(2::nat)^4 \<le> 2^(LENGTH('size_t) - Suc 0)"
      by (simp add: numeral_2_eq_2)
    with assms show ?thesis by linarith
  qed    

  sepref_register pmap_par

  
  (*
    This is declared B\<^sup>d because there is no sub-tuple precise k/d: the parameters to nres-par are tuples
    containing both B and the array, and the array is changed, so the whole tuple is \<^sup>d.
  *)
  
  sepref_def pmap_par_impl is "uncurry4 (PR_CONST pmap_par)" 
    :: "[\<lambda>_. True]\<^sub>c size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a B\<^sup>d *\<^sub>a (woarray_slice_assn A)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> woarray_slice_assn A [\<lambda>(((_,_),p),_) p'. p'=p]\<^sub>c"
    unfolding pmap_par_def PR_CONST_def
  
    apply (rewrite RECT_cp_annot[where CP="\<lambda>(_,_,_,p,_) p'. p'= p"])
    supply [sepref_comb_rules] = hn_RECT_cp_annot_noframe
    
    supply [sepref_bounds_simps] = size_snat_bound
    
    supply [safe_constraint_rules] = CN_FALSEI[of is_pure B]
    
    (*supply [sepref_opt_simps] = fold_pmap_seq_impl_uncurried*)
    
    apply (annot_snat_const size_t)
    supply [[goals_limit = 1]]

    apply sepref    
    done    


  theorem pmap_par_impl_htriple:
    assumes "n = length xs"
      and "Suc 0 < thr"
      and "\<forall>x\<in>set xs. P b x"
    shows
    "llvm_htriple
      (snat_assn thr thri \<and>* snat_assn d di \<and>* B b bi \<and>* woarray_slice_assn A xs xsi \<and>* snat_assn (length xs) ni)
      (pmap_par_impl thri di bi xsi ni)
      (\<lambda>r. EXS x. \<up>(r = xsi) 
        ** snat_assn thr thri \<and>* snat_assn d di \<and>* woarray_slice_assn A x xsi ** snat_assn (length xs) ni 
        \<and>* \<up>mspec b xs x)"
  proof -    
    note A = pmap_par_impl.refine[to_hnr, unfolded autoref_tag_defs hn_ctxt_def, 
      of thr thri d di b bi xs xsi n ni]
    
    note R = hn_refine_ref[OF pmap_par_correct A, THEN hn_refineD, simplified] 
  
    from R[OF assms] show ?thesis
      apply (rule htriple_ent_post[rotated])
      apply (clarsimp simp add: sep_algebra_simps entails_def invalid_assn_def)
      subgoal for s x
        apply (rule exI[where x=x])
        apply (simp add: sep_conj_c)
        done
      done      
    
  qed
    
  

  sepref_register pmap_par_array
  
  find_in_thms mop_woarray_to_array in sepref_fr_rules   
  find_in_thms mop_array_to_woarray in sepref_fr_rules   
  sepref_def pmap_par_array_impl is "uncurry4 (PR_CONST pmap_par_array)" 
    :: "[\<lambda>_. is_pure A]\<^sub>a size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k *\<^sub>a B\<^sup>d *\<^sub>a (array_assn A)\<^sup>d *\<^sub>a size_assn\<^sup>k \<rightarrow> array_assn A"
    unfolding pmap_par_array_def PR_CONST_def
    by sepref
  
  
end  


find_theorems woarray_slice_assn array_slice_assn

find_theorems array_slice_assn array_assn










end
