theory Sep_Generic_Wp
imports 
  "../lib/Sep_Algebra_Add" 
  "../lib/Frame_Infer"
begin

section \<open>General VCG Setup for Separation Logic\<close>

(* TODO: Move to Library *)

locale generic_wp_defs =
  fixes wp :: "'e \<Rightarrow> 'c \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool"
begin
  definition "htripleF e \<alpha> I F P c Q \<equiv> (\<forall>s. I s \<and> (P**F) (\<alpha> s) \<longrightarrow>
      wp e c (\<lambda>r s'. I s' \<and> (Q r ** F) (\<alpha> s')) s)"

  definition "htriple e \<alpha> I P c Q \<equiv> (\<forall>F s. I s \<and> (P**F) (\<alpha> s) \<longrightarrow>
      wp e c (\<lambda>r s'. I s' \<and> (Q r ** F) (\<alpha> s')) s)"

  lemma htriple_as_F_eq: "htriple e \<alpha> I P c Q = (\<forall>F. htripleF e \<alpha> I F P c Q)"    
    unfolding htriple_def htripleF_def by blast
      
end


locale generic_wp = generic_wp_defs wp
  for wp :: "'e \<Rightarrow> 'c \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" +
  assumes wp_comm_inf: "inf (wp e c Q) (wp e c Q') = wp e c (inf Q Q')"
begin

  lemma wp_comm_conj: "wp e c (\<lambda>r. Q r and Q' r) s \<longleftrightarrow> wp e c Q s \<and> wp e c Q' s"
    using wp_comm_inf[of e c Q Q']
    unfolding inf_fun_def inf_bool_def by metis

  lemma wp_comm_conjI: "\<lbrakk> wp e c Q s; wp e c Q' s \<rbrakk> \<Longrightarrow> wp e c (\<lambda>r s. Q r s \<and> Q' r s) s"
    using wp_comm_inf[of e c Q Q']
    unfolding inf_fun_def inf_bool_def by metis


  lemma wp_mono: "Q\<le>Q' \<Longrightarrow> wp e c Q \<le> wp e c Q'"
    by (metis (mono_tags) antisym_conv le_inf_iff order_refl wp_comm_inf)

  lemma wp_monoI:
    assumes "wp e c Q s"
    assumes "\<And>r x. Q r x \<Longrightarrow> Q' r x"
    shows "wp e c Q' s"
    using assms wp_mono[of Q Q' e c] by auto
      
  lemma htripleI:     
    assumes "\<And>F s. I s \<Longrightarrow> (P**F) (\<alpha> s) \<Longrightarrow> wp e c (\<lambda>r s'. I s' \<and> (Q r ** F) (\<alpha> s')) s"
    shows "htriple e \<alpha> I P c Q"
    using assms by (auto simp: htriple_def)

  lemma htripleFI:     
    assumes "\<And>s. I s \<Longrightarrow> (P**F) (\<alpha> s) \<Longrightarrow> wp e c (\<lambda>r s'. I s' \<and> (Q r ** F) (\<alpha> s')) s"
    shows "htripleF e \<alpha> I F P c Q"
    using assms by (auto simp: htripleF_def)
        
  lemma htripleD:  
    assumes "htriple e \<alpha> I P c Q"
    assumes "I s"
    assumes "(P**F) (\<alpha> s)"
    shows "wp e c (\<lambda>r s'. I s' \<and> (Q r ** F) (\<alpha> s')) s"
    using assms by (auto simp: htriple_def)
    
  lemma htriple_triv[simp, intro!]: "htriple e \<alpha> I sep_false c Q"
    by (auto simp: htriple_def)
      
  lemma frame_rule: "htriple e \<alpha> I P c Q \<Longrightarrow> htriple e \<alpha> I (P ** F) c (\<lambda>r. Q r ** F)"
    unfolding htriple_def
    by (fastforce)

  lemma cons_rule:
    assumes "htriple e \<alpha> I P c Q"
    assumes "\<And>s. P' s \<Longrightarrow> P s"
    assumes "\<And>r s. Q r s \<Longrightarrow> Q' r s"
    shows "htriple e \<alpha> I P' c Q'"
    unfolding htriple_def
  proof clarsimp
    fix F s
    assume I: "I s"
    assume "(P' \<and>* F) (\<alpha> s)"
    with assms(2) have "(P \<and>* F) (\<alpha> s)"
      using sep_conj_impl1 by blast
    with assms(1) have "wp e c (\<lambda>r s'. I s' \<and> (Q r \<and>* F) (\<alpha> s')) s"
      unfolding htriple_def using I by auto
    thus "wp e c (\<lambda>r s'. I s' \<and> (Q' r \<and>* F) (\<alpha> s')) s"
      apply (rule wp_monoI)
      using assms(3)
      using sep_conj_impl1 by blast
  qed

  lemma cons_post_rule:
    assumes "htriple e \<alpha> I P c Q"
    assumes "\<And>r s. Q r s \<Longrightarrow> Q' r s"
    shows "htriple e \<alpha> I P c Q'"
    using cons_rule assms by blast
  
  
  lemma htriple_alt:
    "htriple e \<alpha> I P c Q 
      = (\<forall>p s f. I s \<and> p##f \<and> \<alpha> s = p + f \<and> P p \<longrightarrow> wp e c (\<lambda>r s'. I s' \<and> (\<exists>p'. p'##f \<and> \<alpha> s'=p'+f \<and> Q r p')) s)"
  proof (rule iffI, goal_cases)
    case 1
    show ?case
      using htripleD[OF 1, where F="EXACT x" for x]
        by (auto simp: sep_conj_def)
    
  next
    case 2
    show ?case proof (rule htripleI)
      fix F s 
      assume I: "I s"
      assume "(P \<and>* F) (\<alpha> s)"
      then obtain p f where "p##f" "P p" "F f" "\<alpha> s = p+f"
        by (blast elim: sep_conjE)
      with 2 I have "wp e c (\<lambda>r s'. I s' \<and> (\<exists>p'. p' ## f \<and> \<alpha> s' = p' + f \<and> Q r p')) s" by blast
      then show "wp e c (\<lambda>r s'. I s' \<and> (Q r \<and>* F) (\<alpha> s')) s"
        apply (rule wp_monoI)
        using \<open>F f\<close> by (auto intro: sep_conjI)
    qed
  qed
  
  lemma htripleI': 
    assumes "\<And>p s f. \<lbrakk> p##f; I s; \<alpha> s = p + f; P p\<rbrakk> \<Longrightarrow> wp e c (\<lambda>r s'. I s' \<and> (\<exists>p'. p'##f \<and> \<alpha> s'=p'+f \<and> Q r p')) s"
    shows "htriple e \<alpha> I P c Q"
    using assms by (auto simp: htriple_alt)

  lemma htripleD': 
    assumes "htriple e \<alpha> I P c Q"
    assumes "p##f" "I s" "\<alpha> s = p + f" "P p"
    shows "wp e c (\<lambda>r s'. I s' \<and> (\<exists>p'. p'##f \<and> \<alpha> s'=p'+f \<and> Q r p')) s"
    using assms by (auto simp: htriple_alt)
        
    
    
  lemma htriple_extract_pre_pure: 
    "htriple e \<alpha> I (\<up>\<Phi>**P) c Q \<longleftrightarrow> \<Phi> \<longrightarrow> htriple e \<alpha> I P c Q"  
    by (cases \<Phi>) (auto simp: sep_algebra_simps)
    
  (*
  lemma htriple_extract_pre_EXS: 
    assumes "\<And>x s. \<Phi> x \<Longrightarrow> P s \<Longrightarrow> f x ## s"
    shows "htriple e \<alpha> (EXS x. \<up>\<Phi> x ** EXACT (f x) ** P) c Q \<longleftrightarrow> (\<exists>x. \<Phi> x \<and> htriple e \<alpha> (EXACT (f x) ** P) c Q)"
    apply rule
  *)  
    
  thm htripleD
  
  thm option.simps
  
  lemma sv_htripleD:
    assumes "htriple e \<alpha> I P c Q"
    assumes "I s"
    assumes "(P**F) (\<alpha> s)"
    assumes "\<And>r s. I s \<Longrightarrow> (Q r ** F) (\<alpha> s) \<Longrightarrow> Q' r s"
    shows "wp e c Q' s"
    using assms 
    by (force simp: htriple_def intro: wp_monoI)
  
  lemma sv_htripleFD:
    assumes "htripleF e \<alpha> I F P c Q"
    assumes "I s"
    assumes "(P**F) (\<alpha> s)"
    assumes "\<And>r s. I s \<Longrightarrow> (Q r ** F) (\<alpha> s) \<Longrightarrow> Q' r s"
    shows "wp e c Q' s"
    using assms 
    by (force simp: htripleF_def intro: wp_monoI)
    
    
  lemma htriple_conj_pure:
    fixes \<alpha>
    assumes "htriple e \<alpha> I P c Q"
    assumes "htriple e \<alpha> I P c (\<lambda>r. \<up>\<Phi> r ** sep_true)"
    shows "htriple e \<alpha> I P c (\<lambda>r. \<up>\<Phi> r ** Q r)"
  proof (rule htripleI)  
    fix F s
    assume I: "I s"
    assume "(P**F) (\<alpha> s)"
    from wp_comm_conjI[OF assms[THEN htripleD,OF I this]]
    show "wp e c (\<lambda>r s'. I s' \<and> ((\<up>\<Phi> r \<and>* Q r) \<and>* F) (\<alpha> s')) s"
      apply (rule wp_monoI)
      using and_pure_true I unfolding entails_def by blast
      
  qed    
    
end

(* experiment begin
  text \<open>Precondition defined by semantics relation:
    \<^item> \<open>T c s\<close> command terminates in state \<open>s\<close>
    \<^item> \<open>R c s r s'\<close> command yields result \<open>r\<close> and new state \<open>s'\<close>
  \<close>
  
  definition "my_wp T (R::_ \<Rightarrow> 's\<Rightarrow>_\<Rightarrow>'s\<Rightarrow>bool) c Q s \<equiv> T c s \<and> (\<forall>r s'. R c s r s' \<longrightarrow> Q r s')"
  

  interpretation generic_wp "my_wp T R"  
    apply unfold_locales
    unfolding my_wp_def
    by auto
  

end *)




definition STATE :: "('s \<Rightarrow> 'a::sep_algebra) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" 
  where "STATE \<alpha> I P s \<equiv> I s \<and> P (\<alpha> s)"

lemma STATE_assn_cong[fri_extract_congs]: "P\<equiv>P' \<Longrightarrow> STATE \<alpha> I P s \<equiv> STATE \<alpha> I P' s" by simp
  
lemma STATE_extract[vcg_normalize_simps]:
  "STATE \<alpha> I (\<up>\<Phi>) h \<longleftrightarrow> \<Phi> \<and> STATE \<alpha> I \<box> h"
  "STATE \<alpha> I (\<up>\<Phi> ** P) h \<longleftrightarrow> \<Phi> \<and> STATE \<alpha> I P h"
  "STATE \<alpha> I (EXS x. Q x) h \<longleftrightarrow> (\<exists>x. STATE \<alpha> I (Q x) h)"
  "STATE \<alpha> I (\<lambda>_. False) h \<longleftrightarrow> False"
  "STATE \<alpha> I ((\<lambda>_. False) ** P) h \<longleftrightarrow> False"
  by (auto simp: STATE_def sep_algebra_simps pred_lift_extract_simps)
 

definition POSTCOND :: "('s \<Rightarrow> 'a::sep_algebra) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" 
  where [vcg_tag_defs]: "POSTCOND \<alpha> I \<equiv> STATE \<alpha> I"
  
lemma POSTCONDI:
  "STATE \<alpha> I A h \<Longrightarrow> POSTCOND \<alpha> I A h"
  by (auto simp add: POSTCOND_def)
lemma POSTCOND_cong[vcg_normalize_congs]: "POSTCOND \<alpha> I A = POSTCOND \<alpha> I A" ..

lemma POSTCOND_triv_simps[vcg_normalize_simps]:
  "I h \<Longrightarrow> POSTCOND \<alpha> I sep_true h"
  "\<not>POSTCOND \<alpha> I sep_false h"
  unfolding POSTCOND_def STATE_def by auto

(* lemma STATE_imp_inv[vcg_normalize_simps]: "STATE \<alpha> I P h \<Longrightarrow> I h"
  unfolding STATE_def by simp *)
  
lemma start_entailsE:
  assumes "STATE \<alpha> I P h"
  assumes "ENTAILS P P'"
  shows "STATE \<alpha> I P' h"
  using assms unfolding STATE_def ENTAILS_def entails_def
  by auto

declaration \<open>
  K (Basic_VCG.add_xformer (@{thms POSTCONDI},@{binding postcond_xformer},
    fn ctxt => eresolve_tac ctxt @{thms start_entailsE}
  ))
\<close>


named_theorems htriple_vcg_intros
named_theorems htriple_vcg_intro_congs
definition [vcg_tag_defs]: "DECOMP_HTRIPLE \<phi> \<equiv> \<phi>"
lemma DECOMP_HTRIPLEI: "\<phi> \<Longrightarrow> DECOMP_HTRIPLE \<phi>" unfolding vcg_tag_defs by simp

 
context generic_wp begin
  thm frame_rule
  thm cons_rule  
    
  lemma htriple_vcg_frame_erule[vcg_frame_erules]:
    assumes S: "STATE \<alpha> I P' s"
    assumes F: "PRECOND (FRAME P' P F)"
    assumes HT: "htriple e \<alpha> I P c Q"  
    assumes P: "\<And>r s. STATE \<alpha> I (Q r ** F) s \<Longrightarrow> PRECOND (EXTRACT (Q' r s))"
    shows "wp e c Q' s"
  proof -
    from S have I: "I s"
      unfolding STATE_def by simp
    from S F have "(P \<and>* F) (\<alpha> s)"
      unfolding vcg_tag_defs
      by (metis (no_types) FRAME_def entails_def STATE_def)
    with P show ?thesis
      unfolding vcg_tag_defs
      by (metis (no_types) STATE_def sv_htripleD[OF HT I])
      
  qed

  lemma htripleF_vcg_frame_erule[vcg_frame_erules]:
    assumes S: "STATE \<alpha> I P' s"
    assumes F: "PRECOND (FRAME P' P F)"
    assumes HT: "htripleF e \<alpha> I F P c Q"  
    assumes P: "\<And>r s. STATE \<alpha> I (Q r ** F) s \<Longrightarrow> PRECOND (EXTRACT (Q' r s))"
    shows "wp e c Q' s"
  proof -
    from S have I: "I s"
      unfolding STATE_def by simp
    from S F have "(P \<and>* F) (\<alpha> s)"
      unfolding vcg_tag_defs
      by (metis (no_types) FRAME_def entails_def STATE_def)
    with P show ?thesis
      unfolding vcg_tag_defs
      by (metis (no_types) STATE_def sv_htripleFD[OF HT I])
      
  qed
  
  
  
  lemma htriple_vcgI': 
    assumes "\<And>F s. STATE \<alpha> I (P**F) s \<Longrightarrow> wp e c (\<lambda>r. POSTCOND \<alpha> I (Q r ** F)) s"
    shows "htriple e \<alpha> I P c Q"
    apply (rule htripleI)
    using assms unfolding vcg_tag_defs STATE_def by simp
  
  lemma htriple_vcgI[htriple_vcg_intros]: 
    assumes "\<And>F s. STATE \<alpha> I (P**F) s \<Longrightarrow> EXTRACT (wp e c (\<lambda>r. POSTCOND \<alpha> I (Q r ** F)) s)"
    shows "htriple e \<alpha> I P c Q"
    apply (rule htripleI)
    using assms unfolding vcg_tag_defs STATE_def by simp

  lemma htripleF_vcgI[htriple_vcg_intros]: 
    assumes "\<And>s. STATE \<alpha> I (P**F) s \<Longrightarrow> EXTRACT (wp e c (\<lambda>r. POSTCOND \<alpha> I (Q r ** F)) s)"
    shows "htripleF e \<alpha> I F P c Q"
    apply (rule htripleFI)
    using assms unfolding vcg_tag_defs STATE_def by simp
    
      
  lemma htriple_decompI[vcg_decomp_rules]: 
    "DECOMP_HTRIPLE (htriple e \<alpha> I P c Q) \<Longrightarrow> htriple e \<alpha> I P c Q"
    "DECOMP_HTRIPLE (htripleF e \<alpha> I F P c Q) \<Longrightarrow> htripleF e \<alpha> I F P c Q"
    unfolding vcg_tag_defs by auto

  lemma htriple_assn_cong[htriple_vcg_intro_congs]: 
    "P\<equiv>P' \<Longrightarrow> Q\<equiv>Q' \<Longrightarrow>  htriple e \<alpha> I P c Q \<equiv> htriple e \<alpha> I P' c Q'" by simp

  lemma htripleF_assn_cong[htriple_vcg_intro_congs]: 
    "P\<equiv>P' \<Longrightarrow> Q\<equiv>Q' \<Longrightarrow>  htripleF e \<alpha> I F P c Q \<equiv> htripleF e \<alpha> I F P' c Q'" by simp
            
  lemma htriple_ent_pre:
    "P\<turnstile>P' \<Longrightarrow> htriple e \<alpha> I P' c Q \<Longrightarrow> htriple e \<alpha> I P c Q"
    unfolding entails_def
    apply (erule cons_rule) by blast+
    
  lemma htriple_ent_post:
    "\<lbrakk>\<And>r. Q r \<turnstile> Q' r\<rbrakk> \<Longrightarrow> htriple e \<alpha> I P c Q \<Longrightarrow> htriple e \<alpha> I P c Q'"
    unfolding entails_def
    apply (erule cons_rule) by blast+
   
  lemma htriple_pure_preI: "\<lbrakk>pure_part P \<Longrightarrow> htriple e \<alpha> I P c Q\<rbrakk> \<Longrightarrow> htriple e \<alpha> I P c Q"  
    by (meson htriple_def pure_partI sep_conjE)
   
  lemma htripleF_pure_preI: "\<lbrakk>pure_part P \<Longrightarrow> htripleF e \<alpha> I F P c Q\<rbrakk> \<Longrightarrow> htripleF e \<alpha> I F P c Q"  
    by (meson htripleF_def pure_partI sep_conjE)

  lemma htriple_strengthen_inv:
    assumes "htriple e \<alpha> I P c Q"
    assumes "\<And>s. I' s \<Longrightarrow> I s"
    assumes "\<And>F s. I' s \<Longrightarrow> I s \<Longrightarrow> wp e c (\<lambda>r s'. I s' \<and> (Q r \<and>* F) (\<alpha> s')) s \<Longrightarrow> wp e c (\<lambda>_. I') s"
    shows "htriple e \<alpha> I' P c Q"
    using assms
    unfolding htriple_def
    apply clarify
    apply (rule wp_comm_conjI)
    using wp_monoI apply fastforce
    using assms(1) sv_htripleD by fastforce
  
end

declaration \<open>
  K (Basic_VCG.add_xformer (@{thms DECOMP_HTRIPLEI},@{binding decomp_htriple_xformer},
    fn ctxt => 
      (full_simp_tac (put_simpset HOL_basic_ss ctxt 
        addsimps (Named_Theorems.get ctxt @{named_theorems vcg_tag_defs})
        |> fold Simplifier.add_cong (Named_Theorems.get ctxt @{named_theorems htriple_vcg_intro_congs})
      ))
      THEN' resolve_tac ctxt (Named_Theorems.get ctxt @{named_theorems htriple_vcg_intros})
  ))
\<close>

section \<open>WP from inductive\<close>

locale wp_from_inductive =
  fixes rel :: "'e \<Rightarrow> 'c \<Rightarrow> 's \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> bool"
begin

definition valid :: "'e \<Rightarrow> 'c \<Rightarrow> 's \<Rightarrow> bool" where
  "valid e c s \<equiv> \<exists>r s'. rel e c s r s'"

definition wlp :: "'e \<Rightarrow> 'c \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" where
  "wlp e c Q s \<equiv> \<forall>r s'. rel e c s r s' \<longrightarrow> Q r s'"

definition wp :: "'e \<Rightarrow> 'c \<Rightarrow> ('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" where
  "wp e c Q s \<equiv> valid e c s \<and> wlp e c Q s"

sublocale generic_wp wp
  apply standard
  unfolding wp_def valid_def wlp_def
  by fastforce

lemma validI: "rel e c s r s' \<Longrightarrow> valid e c s"
  unfolding valid_def by auto
lemma validE:
  assumes "valid e c s"
  obtains r s' where "rel e c s r s'"
  using assms unfolding valid_def by auto

lemma wlpI: "(\<And>r s'. rel e c s r s' \<Longrightarrow> Q r s') \<Longrightarrow> wlp e c Q s"
  unfolding wlp_def by auto
lemma wlpD:
  assumes "wlp e c Q s"
  shows "\<And>r s'. rel e c s r s' \<Longrightarrow> Q r s'"
  using assms unfolding wlp_def by auto

lemma wpI: "rel e c s r s' \<Longrightarrow> (\<And>r s'. rel e c s r s' \<Longrightarrow> Q r s') \<Longrightarrow> wp e c Q s"
  unfolding wp_def by (auto intro: validI wlpI)
lemma wpD:
  assumes "wp e c Q s"
  shows "\<exists>r s'. rel e c s r s' \<and> Q r s'" "\<And>r s'. rel e c s r s' \<Longrightarrow> Q r s'"
  using assms unfolding wp_def by (auto dest: wlpD elim!: validE)
lemma wpE:
  assumes "wp e c Q s"
  obtains r s' where "rel e c s r s'"  "Q r s'" "\<And>r s'. rel e c s r s' \<Longrightarrow> Q r s'"
  using assms unfolding wp_def
  using valid_def wlpD by fastforce
lemma wpE_concrete:
  assumes "wp e c Q s"
  obtains r s' where "rel e c s r s'" "Q r s'"
  using assms by (rule wpE)

lemma wp_to_wp:
  assumes "wp e c Q s"
    "\<And>r s'. rel e c s r s' \<Longrightarrow> Q r s' \<Longrightarrow> \<exists> r' s''. rel e c' s r' s''"
    "(\<And>r s'. rel e c s r s' \<Longrightarrow> Q r s') \<Longrightarrow> (\<And>r' s''. rel e c' s r' s'' \<Longrightarrow> Q' r' s'')"
  shows "wp e c' Q' s"
  using assms
  by (metis wpE wpI)
end

subsection \<open>Deterministic inductives\<close>
locale wp_from_inductive_determ = wp_from_inductive +
  assumes determ: "rel e c s r s' \<Longrightarrow> rel e c s r' s'' \<Longrightarrow> r=r' \<and> s'=s''"
begin

lemma wlp_determI: "rel e c s r s' \<Longrightarrow> Q r s' \<Longrightarrow> wlp e c Q s"
  using determ wlpI by blast

lemma wp_determI: "rel e c s r s' \<Longrightarrow>  Q r s' \<Longrightarrow> wp e c Q s"
  unfolding wp_def by (auto intro: validI wlp_determI)

lemma wp_determE:
  assumes "wp e c Q s"
  obtains r s' where "rel e c s r s'" "Q r s'" "\<And>r' s''. rel e c s r' s'' \<Longrightarrow> (r' = r \<and> s'' = s')"
  by (metis assms determ wpD(1))
end


end
