theory Case_Study
imports Chunkval_Interface Serialize
begin

fun stmt_list :: "stmt list \<Rightarrow> stmt" where
  "stmt_list [] = Sskip"
| "stmt_list [s] = s"
| "stmt_list (s#ss) = Sseq s (stmt_list ss)"

section \<open>Case Study\<close>

definition Earray_offset where
  "Earray_offset var_name ofs \<equiv> (Ebinop Oaddl
          (Evar var_name)
          (Econst (Olongconst (word_of_int ofs))))"

definition "arr_name \<equiv> STR ''array''"
definition "var_name \<equiv> STR ''res''"

definition "case_study_stmts \<equiv> [
  Sbuiltin (Some arr_name) EF_malloc [Econst (Olongconst (word_of_nat 8))],
  Sstore Mint32 (Earray_offset arr_name 0) (Econst (Ointconst (Int.repr 21))),
  Sstore Mint32 (Earray_offset arr_name 4) (Econst (Ointconst (Int.repr 21))),
  Sassign var_name (Ebinop Oadd
    (Eload Mint32 (Earray_offset arr_name 0))
    (Eload Mint32 (Earray_offset arr_name 4))),
  Sbuiltin None EF_free [Evar arr_name],
  Sreturn (Some (Evar var_name))
  ]"

lemma [iff]: "arr_name \<noteq> var_name"
  unfolding arr_name_def var_name_def
  by simp

lemma case_study_proof:
  "stmt_ht ge f sp
   (env.assn_is arr_name Vundef ** env.assn_is var_name Vundef)
   (stmt_list case_study_stmts)
   (\<lambda>(t, out). \<up>((t, out) = (E0, Out_return (Some (Vint 42))))
    ** (EXS v1 v2. env.assn_is arr_name v1 ** env.assn_is var_name v2))"
  unfolding case_study_stmts_def Earray_offset_def
  apply simp
  apply vcg
  apply simp
  apply vcg
   apply (simp add: sep_algebra_simps)
   apply vcg_normalize
   apply vcg
  apply (simp add: mem.val_range_split[of 4 "replicate 8 Undef", simplified])
   apply (simp add: mem.range_to_chunk[of "replicate 4 Undef" Mint32])
   apply vcg
  unfolding mem.mem_chunk_def
   apply (simp add: sep_algebra_simps)
  supply [simp] = mem.val_range_split[of 4 "encode_val Mint32 (Vint 21) @ encode_val Mint32 (Vint 21)" _ 0, symmetric, simplified]
   apply (simp)
   apply vcg_rl
  sorry

definition "case_study_func \<equiv>
  (func.make signature_main [] [arr_name, var_name] 0 (stmt_list case_study_stmts))"

definition case_study_program :: Cminor_Syntax.program where
"case_study_program \<equiv> program.make
  [(STR ''main'', Gfun (Internal case_study_func)),
  (STR ''malloc'', Gfun (External EF_malloc)),
  (STR ''free'', Gfun (External EF_free))]
  [] (STR ''main'')"

definition "case_study_jsoned \<equiv> show_json (to_json case_study_program)"

(* declare case_study_program_def[code del]

schematic_goal [code]: "case_study_program \<equiv> ?x"
  unfolding case_study_program_def
  unfolding case_study_func_def
  unfolding case_study_stmts_def
  apply (subst malloc_fix)
  apply (subst free_fix)
  by simp

ML_val \<open>writeln @{code case_study_jsoned}\<close>

ML_val \<open>
val using_master_directory =
          File.full_path o Resources.master_directory o Proof_Context.theory_of;
val path = using_master_directory @{context} (Path.basic "case_study.cmj");
File.write path @{code case_study_jsoned}\<close> *)

section \<open>Array Case Study\<close>

definition "my_array \<equiv> cv_array_def.make (STR ''array'') 4 2"

schematic_goal my_array_simps[simp]:
  "array_name my_array = ?x"
  "array_elem_size my_array = ?y"
  "array_length my_array = ?z"
  unfolding my_array_def
  by (auto simp only: cv_array_def.defs cv_array_def.simps)

lemma my_array_valid[iff]: "array_def_valid my_array"
  unfolding my_array_def
  apply (rule array_def_valid.intros)
  by (auto simp: cv_array_def.defs array_size_def arch_max_size_def)

definition [simp]: "array_case_study_stmts \<equiv>
  [Sarray_alloc my_array,
  Sarray_store my_array 0 Mint32 (Econst (Ointconst 21)),
  Sarray_store my_array 1 Mint32 (Econst (Ointconst 21)),
  Sassign (STR ''res'') (Ebinop Oadd
    (Earray_load my_array 0 Mint32)
    (Earray_load my_array 1 Mint32)),
  Sarray_free my_array,
  Sreturn (Some (Evar (STR ''res'')))]"

lemma def_extend: "cv_array_def.extend \<lparr>array_name = an, array_elem_size = aes, array_length = al\<rparr>
         (cv_array.fields ab acvs)
    = \<lparr>array_name = an, array_elem_size = aes, array_length = al, array_block = ab, array_chunkvals = acvs\<rparr>"
  by (simp add: cv_array_def.defs cv_array.defs)

lemmas [simp] = cv_array_def.defs cv_array.defs
lemmas [simp] = chunk_fits_array_def array_set_val_def array_get_val_def sep_algebra_simps

notation stmt_ht ("_ _ _ \<Turnstile>\<^sub>s {_} _ {_}")
notation env.assn_is ("_ \<mapsto>\<^sub>v _")

lemma array_case_study_proof:
  "ge f sp \<Turnstile>\<^sub>s
   {EXS v1 v2. (STR ''array'') \<mapsto>\<^sub>v v1 \<and>* (STR ''res'') \<mapsto>\<^sub>v v2}
   (stmt_list array_case_study_stmts)
   {\<lambda>r. \<up>(r = (E0, Out_return (Some (Vint 42))))
    ** (EXS v1 v2. (STR ''array'') \<mapsto>\<^sub>v v1 \<and>* (STR ''res'') \<mapsto>\<^sub>v v2)}"
  by vcg


definition "array_case_study_func \<equiv>
  (func.make signature_main [] [STR ''array'', STR ''res''] 0 (stmt_list array_case_study_stmts))"

definition array_case_study_program :: Cminor_Syntax.program where
"array_case_study_program \<equiv> program.make
  [(STR ''malloc'', Gfun (External EF_malloc)),
  (STR ''free'', Gfun (External EF_free)),
  (STR ''main'', Gfun (Internal array_case_study_func))]
  [] (STR ''main'')"

definition "array_case_study_jsoned \<equiv> show_json (to_json array_case_study_program)"

declare array_case_study_program_def[code del]

(* horrible hack *)

lemma malloc_fix:
  "Sbuiltin r EF_malloc args = Scall r (ef_sig EF_malloc) (Econst (Oaddrsymbol (STR ''malloc'') 0)) args"
  sorry

lemma free_fix:
  "Sbuiltin r EF_free args = Scall r (ef_sig EF_malloc) (Econst (Oaddrsymbol (STR ''free'') 0)) args"
  sorry

(* don't prove anything after this point *)

schematic_goal [code]: "array_case_study_program \<equiv> ?x"
  unfolding array_case_study_program_def
  unfolding array_case_study_func_def
  unfolding array_case_study_stmts_def
  unfolding Sarray_alloc_def Sarray_free_def
  apply (subst malloc_fix)
  apply (subst free_fix)
  by simp

ML_val "writeln @{code array_case_study_jsoned}"

ML \<open>
val using_master_directory =
          File.full_path o Resources.master_directory o Proof_Context.theory_of;
val path = using_master_directory @{context} (Path.basic "array_case_study.cmj");
File.write path @{code array_case_study_jsoned}\<close>

end