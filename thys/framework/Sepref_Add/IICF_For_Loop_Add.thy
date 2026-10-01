theory IICF_For_Loop_Add
imports "Isabelle_LLVM.IICF"
begin

subsection \<open>Specialized Rules for Foreach-Loops\<close>
lemma nfoldli_upt_rule:
  assumes INTV: "lb\<le>ub"
  assumes I0: "I lb \<sigma>0"
  assumes IS: "\<And>i \<sigma>. \<lbrakk> lb\<le>i; i<ub; I i \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f i \<sigma> \<le> SPEC (I (i+1))"
  assumes FNC: "\<And>i \<sigma>. \<lbrakk> lb\<le>i; i\<le>ub; I i \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes FC: "\<And>\<sigma>. \<lbrakk> I ub \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "nfoldli [lb..<ub] c f \<sigma>0 \<le> SPEC P"
  apply (rule nfoldli_rule[where I="\<lambda>l _ \<sigma>. I (lb+length l) \<sigma>"])
  apply simp_all
  apply (simp add: I0)
  subgoal using IS
    by (metis Suc_eq_plus1 add_diff_cancel_left' eq_diff_iff le_add1 length_upt upt_eq_lel_conv)
  subgoal for l1 l2 \<sigma> 
    apply (rule FNC[where i="lb + length l1"])
    apply (auto simp: INTV)
    using INTV upt_eq_append_conv by auto
  apply (rule FC) using INTV 
  by auto  
  
  (* Specialized refinement rule for for-loop, that allows to establish refinement relation that depends
   on progress of loop. *)  
  lemma nfoldli_upt_refine_rel_induct:
    assumes ni_ref: "(ni,n)\<in>nat_rel"
    assumes si_ref: "(si,s) \<in> R 0"
    assumes fi_ref: "\<And>si s ii i. \<lbrakk> (ii,i)\<in>nat_rel; i<n; (si,s)\<in>R i \<rbrakk> \<Longrightarrow> fi ii si \<le>\<Down>(R (Suc i)) (f i s)"
    shows "nfoldli [0..<ni] (\<lambda>_. True) fi si \<le> \<Down>(R ni) (nfoldli [0..<n] (\<lambda>_. True) f s)"
  proof -  
  
    {
      fix i
      assume "i\<le>n" "(si,s)\<in>R i"
      hence "nfoldli [i..<n] (\<lambda>_. True) fi si \<le> \<Down>(R n) (nfoldli [i..<n] (\<lambda>_. True) f s)"
        apply (induction "(n-i)" arbitrary: i s si)
        subgoal for s si
          by (simp add: IdD[OF ni_ref])
        subgoal for x i s si
          apply (subgoal_tac "[i..<n] = i#[Suc i..<n]")
          apply simp
          apply (rule bind_refine) (* Controlled application of just one refine rule. 
            Just refine_rcg will use default nfoldli_refine, rather than IH! *)
          apply (rule fi_ref; simp)
          apply rprems
          apply (simp_all add: upt_conv_Cons)
          done
        done
    
    }
    from this[of 0] ni_ref si_ref show ?thesis by simp
  qed
  
  
  
  definition "for l h f s \<equiv> nfoldli [l..<h] (\<lambda>_. True) f s"

  definition "forI I l h f s \<equiv> nfoldli [l..<h] (\<lambda>_. True) (\<lambda>i s. doN { ASSERT (I i s); f i s}) s"
  
    
  lemma for_rule:   
    assumes INTV: "l\<le>h"
    assumes I0: "I l s"
    assumes IS: "\<And>i s. \<lbrakk> l\<le>i; i<h; I i s \<rbrakk> \<Longrightarrow> f i s \<le> SPEC (I (i+1))"
    assumes FC: "\<And>s. \<lbrakk> I h s \<rbrakk> \<Longrightarrow> P s"
    shows "for l h f s \<le> SPEC P"
    unfolding for_def
    apply (rule nfoldli_upt_rule[where I=I])
    using assms
    by auto
  
    
  lemma forI_rule[refine_vcg]:   
    assumes INTV: "l\<le>h"
    assumes I0: "I l s"
    assumes IS: "\<And>i s. \<lbrakk> l\<le>i; i<h; I i s \<rbrakk> \<Longrightarrow> f i s \<le> SPEC (I (i+1))"
    assumes FC: "\<And>s. \<lbrakk> I h s \<rbrakk> \<Longrightarrow> P s"
    shows "forI I l h f s \<le> SPEC P"
    unfolding forI_def
    apply (rule nfoldli_upt_rule[where I=I])
    using assms
    by auto
    

  lemma for_refine[refine]:
    assumes "(l',l)\<in>Id" "(h',h)\<in>Id" "(s',s)\<in>R"
    assumes [refine]: "\<And>i' i si s. \<lbrakk>(i', i) \<in> nat_rel; l\<le>i; i<h; (si, s) \<in> R \<rbrakk> \<Longrightarrow> f' i' si \<le> \<Down> R (f i s)"
    shows "for l' h' f' s' \<le>\<Down>R (for l h f s)"  
    unfolding for_def
    apply (refine_rcg nfoldli_invar_refine[where I="\<lambda>li ri _. set li \<union> set ri \<subseteq> {l..<h}"])
    apply refine_dref_type
    using assms by auto
    
  lemma forI_refine[refine]:
    assumes "(l',l)\<in>Id" "(h',h)\<in>Id" "(s',s)\<in>R"
    assumes [refine]: "\<And>i' i si s. \<lbrakk>(i', i) \<in> nat_rel; l\<le>i; i<h; (si, s) \<in> R; I i' s\<rbrakk> \<Longrightarrow> f' i' si \<le> \<Down> R (f i s)"
    shows "for l' h' f' s' \<le>\<Down>R (forI I l h f s)"  
    unfolding for_def forI_def 
    apply (refine_rcg nfoldli_invar_refine[where I="\<lambda>li ri _. set li \<union> set ri \<subseteq> {l..<h}"])
    apply refine_dref_type
    using assms by auto


  lemma for_refine_rel_induct:
    assumes ni_ref: "(ni,n)\<in>nat_rel"
    assumes si_ref: "(si,s) \<in> R 0"
    assumes fi_ref: "\<And>si s ii i. \<lbrakk> (ii,i)\<in>nat_rel; i<n; (si,s)\<in>R i \<rbrakk> \<Longrightarrow> fi ii si \<le>\<Down>(R (Suc i)) (f i s)"
    shows "for 0 ni fi si \<le> \<Down>(R ni) (for 0 n f s)"
    unfolding for_def
    using nfoldli_upt_refine_rel_induct[OF assms] .
    
  lemma forI_refine_rel_induct:
    assumes ni_ref: "(ni,n)\<in>nat_rel"
    assumes si_ref: "(si,s) \<in> R 0"
    assumes fi_ref: "\<And>si s ii i. \<lbrakk> (ii,i)\<in>nat_rel; i<n; (si,s)\<in>R i; I i s \<rbrakk> \<Longrightarrow> fi ii si \<le>\<Down>(R (Suc i)) (f i s)"
    shows "for 0 ni fi si \<le> \<Down>(R ni) (forI I 0 n f s)"
    unfolding for_def forI_def
    apply (rule nfoldli_upt_refine_rel_induct)
    apply fact+
    apply (refine_rcg fi_ref)
    done
    

  lemma for_by_while_gen: 
    assumes "\<And>n. conv_op n \<equiv> n"
    shows "for l h f s = do {
      let h = h; \<comment> \<open>HACK: should the upper bound be a fixed variable, 
        this ensures proper refinement with keeping the assertion for the bound, which is needed to
        prove bounds for index increment.\<close>
      (_, s) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, s). i < h \<and> True) (\<lambda>(i, s). do {
        s \<leftarrow> f i s;
        ASSERT (i < h);
        RETURN (i + conv_op 1, s)
      }) (l, s);
      Refine_Basic.RETURN s
    }"
    unfolding for_def nfoldli_upt_by_while by (simp add: assms)
    
        

  lemma for_by_while: "for l h f s = do {
      let h = h; \<comment> \<open>HACK: should the upper bound be a fixed variable, 
        this ensures proper refinement with keeping the assertion for the bound, which is needed to
        prove bounds for index increment.\<close>
      (_, s) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, s). i < h \<and> True) (\<lambda>(i, s). do {
        s \<leftarrow> f i s;
        ASSERT (i < h);
        RETURN (i + snat_const TYPE('l::len2) 1, s)
      }) (l, s);
      Refine_Basic.RETURN s
    }"
    using for_by_while_gen[of "snat_const TYPE('l::len2)"] by fastforce
    
  definition [simp]: "THE_TYPE (x::'a itself) \<equiv> True"  
  lemma THE_TYPEI: "THE_TYPE t" by simp

  lemma for_by_while': "THE_TYPE (t::'l::len2 itself) \<Longrightarrow> for l h f s = do {
      let h = h;
      (_, s) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, s). i < h \<and> True) (\<lambda>(i, s). do {
        s \<leftarrow> f i s;
        ASSERT (i < h);
        RETURN (i + snat_const TYPE('l) 1, s)
      }) (l, s);
      Refine_Basic.RETURN s
    }"
    by (rule for_by_while)

    
  lemmas for_by_while_unat = for_by_while_gen[OF unat_const_def[where 'a="'l::len"], zero_var_indexes]

  context
    fixes t
    assumes T: "THE_TYPE (t::'l::len itself)"
  begin  
    lemmas for_by_while_unat' = for_by_while_gen[OF unat_const_def[where 'a="'l"]]
  end
  
  lemma forI_as_for: "forI I l h f s = for l h (\<lambda>i s. doN { ASSERT (I i s); f i s}) s"
    unfolding for_def forI_def by blast

   
  
  
  
subsection \<open>For loop over range with custom increment\<close>
  
definition for_incrI :: "(nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres"
  where "for_incrI I l h \<delta> f s \<equiv> doN {
  if l<h then doN {
    ASSERT (I l s);
    s \<leftarrow> f l s;
    if (\<delta>\<le>h) then doN {
      (s,_)\<leftarrow>WHILET (\<lambda>(s,i). i < h-\<delta>) (\<lambda>(s,i). doN {
        ASSERT(i+\<delta><h);
        let i=i+\<delta>;
        ASSERT (l\<le>i \<and> i<h \<and> I i s);
        s \<leftarrow> f i s;
        RETURN (s,i)
      }) (s,l);
      RETURN s
    } else RETURN s
  } else RETURN s
}"

definition "for_incr = for_incrI (\<lambda>_ _. True)"


thm for_rule

lemma for_incrI_rule[refine_vcg]:
  assumes DPOS: "0<\<delta>"
  assumes I0: "I l s"
  assumes [refine_vcg]: "\<And>i s. \<lbrakk> l\<le>i; i<h; I i s \<rbrakk> \<Longrightarrow> f i s \<le> SPEC (\<lambda>s'. I (i+\<delta>) s')"
  assumes IF: "\<And>i s. \<lbrakk>h\<le>i; I i s \<rbrakk> \<Longrightarrow> Q s"
  shows "for_incrI I l h \<delta> f s \<le> SPEC Q"
  unfolding for_incrI_def
  apply (refine_vcg wf_measure[where f="(\<lambda>(_,i). h+\<delta>-i)"] WHILET_rule[where I="(\<lambda>(s,i). I (i+\<delta>) s \<and> l\<le>i)"])
  apply (simp_all add: I0 IF[of l] IF[of "l+\<delta>"])
  subgoal using DPOS by simp
  subgoal by (meson IF leI le_diff_conv)
  done
  
lemma for_incr_rule:
  assumes DPOS: "0<\<delta>"
  assumes I0: "I l s"
  assumes [refine_vcg]: "\<And>i s. \<lbrakk> l\<le>i; i<h; I i s \<rbrakk> \<Longrightarrow> f i s \<le> SPEC (\<lambda>s'. I (i+\<delta>) s')"
  assumes IF: "\<And>i s. \<lbrakk>h\<le>i; I i s \<rbrakk> \<Longrightarrow> Q s"
  shows "for_incr l h \<delta> f s \<le> SPEC Q"
  unfolding for_incr_def for_incrI_def
  apply (refine_vcg wf_measure[where f="(\<lambda>(_,i). h+\<delta>-i)"] WHILET_rule[where I="(\<lambda>(s,i). I (i+\<delta>) s \<and> l\<le>i)"])
  apply (simp_all add: I0 IF[of l] IF[of "l+\<delta>"])
  subgoal using DPOS by simp
  subgoal by (meson IF leI le_diff_conv)
  done
  

lemma for_incrI_refine[refine]:
  assumes "(l',l)\<in>Id" "(h',h)\<in>Id" "(incr,incr')\<in>Id" "(s',s)\<in>R"
  assumes [refine]: "\<And>i' i s' s. \<lbrakk>(i', i) \<in> nat_rel; I i s; l\<le>i; i<h; (s', s) \<in> R \<rbrakk> \<Longrightarrow> f' i' s' \<le> \<Down> R (f i s)"
  shows "for_incr l' h' incr f' s' \<le>\<Down>R (for_incrI I l h incr' f s)"  
  unfolding for_incrI_def for_incr_def
  apply (refine_vcg)
  supply [refine_dref_RELATES] = RELATESI[of R]
  apply refine_dref_type
  using assms by auto



lemma for_incr_refine[refine]:
  assumes "(l',l)\<in>Id" "(h',h)\<in>Id" "(incr,incr')\<in>Id" "(s',s)\<in>R"
  assumes [refine]: "\<And>i' i s' s. \<lbrakk>(i', i) \<in> nat_rel; l\<le>i; i<h; (s', s) \<in> R \<rbrakk> \<Longrightarrow> f' i' s' \<le> \<Down> R (f i s)"
  shows "for_incr l' h' incr f' s' \<le>\<Down>R (for_incr l h incr' f s)"  
  apply (rewrite in "_ \<le> \<hole>" for_incr_def)
  apply (refine_vcg)
  using assms by auto

lemmas for_incr_by_while = for_incr_def[unfolded for_incrI_def]  
lemmas for_incrI_by_while = for_incrI_def

  
  
   
end

