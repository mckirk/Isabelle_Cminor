theory TSA_Map
  imports "../lib/Sep_Algebra_Add"
          Basic_Lens
begin

section \<open>TSA Map \<alpha>\<close>

type_synonym ('a, 'b) tsa_map = "'a \<Rightarrow> 'b tsa_opt"
definition "tsa_map_dom m \<equiv> {a. m a \<noteq> ZERO}"

locale tsa_map_\<alpha> = concrete: basic_ptr_lens concrete
  for concrete :: "'p \<Rightarrow> ('vc, 'c) basic_lens" +
  fixes embed_concrete :: "'v \<Rightarrow> 'vc"
  and unembed_concrete :: "'vc \<Rightarrow> 'v option"
  assumes unembed: "embed_concrete v = vc \<longleftrightarrow> unembed_concrete vc = Some v"
begin

definition \<alpha> :: "'c \<Rightarrow> ('p, 'v) tsa_map" where
  "\<alpha> c \<equiv> \<lambda>p. case unembed_concrete (concrete.get p c) of Some v \<Rightarrow> TRIV v | _ \<Rightarrow> ZERO"

sublocale lens_assertion concrete sep_algebra_func_lens embed_concrete TRIV \<alpha>
  "\<lambda>vc. unembed_concrete vc = None"
  unfolding lens_assertion_def
  apply safe
     apply (simp add: concrete.basic_ptr_lens_axioms)
    apply (simp add: sep_algebra_func_lens.sep_algebra_ptr_lens_axioms)
  unfolding basic_ptr_lens_equiv_def
   apply safe
     apply (simp add: concrete.basic_ptr_lens_axioms)
    apply (simp add: func_lens.basic_ptr_lens_axioms)
  unfolding basic_ptr_lens_equiv_axioms_def basic_lens_equiv_def basic_lens_equiv_axioms_def
  apply (simp add: func_lens.defs[symmetric] concrete.defs[symmetric])
   apply safe
  apply (simp add: concrete.is_lens)
      apply (simp add: func_lens.is_lens)
  unfolding \<alpha>_def
     apply (auto simp add: sep_algebra_func_lens_unfold concrete.ground_defs split: option.splits)
      apply (metis unembed)
  using unembed apply auto[1]
  apply (metis option.inject unembed)
   apply standard
   apply (auto)
    apply (metis basic_lens.get_put' concrete.is_lens option.simps(5) unembed)
   apply (auto split: option.splits simp add: concrete.put_focused')
  unfolding lens_assertion_axioms_def
  apply (auto)
     apply (metis tsa_opt.exhaust_sel zero_tsa_opt_def)
  apply (metis option.distinct(1) unembed)
  by (simp add: unembed)

end

end