theory Serialize
  imports Main "../compcert/Cminor"
    "Show.Show_Instances" "Show.Show_Real" "Show.Show_Real_Impl"
begin

section \<open>JSON Type\<close>

datatype JSON =
  Number int
| String String.literal
| Boolean bool
| List "JSON list"
| Object "(String.literal * JSON) list"
| Null

fun escape_quote' :: "string \<Rightarrow> string" where
 "escape_quote' [] = []"
| "escape_quote' (CHR 0x22 # cs) = (CHR 0x5C # CHR 0x22 # escape_quote' cs)"
| "escape_quote' (c # cs) = c # escape_quote' cs"

definition "escape_quote s \<equiv> String.implode (escape_quote' (String.explode s))"

fun show_list :: "JSON list \<Rightarrow> String.literal" and
    show_dict_elem :: "(String.literal * JSON) \<Rightarrow> String.literal" and
    show_dict :: "(String.literal * JSON) list \<Rightarrow> String.literal" and
    show_json :: "JSON \<Rightarrow> String.literal"
    where
  "show_list [] = STR ''''"
| "show_list [x] = show_json x"
| "show_list (x#xs) = show_json x + STR '', '' + show_list xs"
| "show_dict_elem (n, x) =
    STR ''\"'' + escape_quote n + STR ''\": '' + show_json x"
| "show_dict [] = STR ''''"
| "show_dict [e] = show_dict_elem e"
| "show_dict (e#es) = show_dict_elem e + STR '', '' + show_dict es"
| "show_json (Number i) = String.implode (show i)"
| "show_json (String s) = STR ''\"'' + escape_quote s + STR ''\"''"
| "show_json (Boolean True) = STR ''true''"
| "show_json (Boolean False) = STR ''false''"
| "show_json (List l) = STR ''['' + show_list l + STR '']''"
| "show_json (Object l) = STR ''{'' + show_dict l + STR ''}''"
| "show_json Null = STR ''null''"

section \<open>JSONable Definitions\<close>

class jsonable =
  fixes to_json :: "'a \<Rightarrow> JSON"

instantiation JSON :: jsonable
begin
fun to_json_JSON :: "JSON \<Rightarrow> JSON" where "to_json_JSON j = j"
instance ..
end

instantiation unit :: jsonable
begin
fun to_json_unit :: "unit \<Rightarrow> JSON" where "to_json_unit _ = Null"
instance ..
end

instantiation int :: jsonable
begin
fun to_json_int :: "int \<Rightarrow> JSON" where "to_json_int i = Number i"
instance ..
end

instantiation nat :: jsonable
begin
fun to_json_nat :: "nat \<Rightarrow> JSON" where "to_json_nat n = Number n"
instance ..
end

instantiation num :: jsonable
begin
fun to_json_num where "to_json_num p = to_json (nat_of_num p)"
instance ..
end

instantiation bool :: jsonable
begin
fun to_json_bool where "to_json_bool b = Boolean b"
instance ..
end

instantiation String.literal :: jsonable
begin
fun to_json_literal where "to_json_literal l = String l"
instance ..
end

instantiation list :: (jsonable) jsonable
begin
fun to_json_list where "to_json_list l = List (map to_json l)"
instance ..
end

instantiation prod :: (jsonable, jsonable) jsonable
begin
fun to_json_prod :: "'a \<times> 'b \<Rightarrow> JSON" where
  "to_json_prod (a,b) = List [to_json a, to_json b]"
instance ..
end

instantiation option :: (jsonable) jsonable
begin
fun to_json_option :: "'a option \<Rightarrow> JSON" where
  "to_json_option None = Null"
| "to_json_option (Some x) = List [to_json x]"
instance ..
end

subsection \<open>CompCert base types\<close>

instantiation word :: (len) jsonable
begin
fun to_json_word :: "'a word \<Rightarrow> JSON" where
  "to_json_word w = to_json (sint w)"
instance ..
end

instantiation IEEE.float :: (len, len) jsonable
begin
lift_definition to_json_float :: "('a, 'b) IEEE.float \<Rightarrow> JSON" is
  "(\<lambda>(s, e, f). Object [(STR ''sign'', to_json s), (STR ''exponent'', to_json e), (STR ''fraction'', to_json f)])"
  .
instance ..
end

subsection \<open>Generated\<close>

instantiation comparison :: jsonable
begin
fun to_json_comparison :: "comparison \<Rightarrow> JSON" where
  "to_json_comparison Ceq = String STR ''Ceq''"
| "to_json_comparison Cne = String STR ''Cne''"
| "to_json_comparison Clt = String STR ''Clt''"
| "to_json_comparison Cle = String STR ''Cle''"
| "to_json_comparison Cgt = String STR ''Cgt''"
| "to_json_comparison Cge = String STR ''Cge''"
instance ..
end

instantiation type :: jsonable
begin
fun to_json_type :: "type \<Rightarrow> JSON" where
  "to_json_type Tint = String STR ''Tint''"
| "to_json_type Tfloat = String STR ''Tfloat''"
| "to_json_type Tlong = String STR ''Tlong''"
| "to_json_type Tsingle = String STR ''Tsingle''"
| "to_json_type Tany32 = String STR ''Tany32''"
| "to_json_type Tany64 = String STR ''Tany64''"
instance ..
end

instantiation rettype :: jsonable
begin
fun to_json_rettype :: "rettype \<Rightarrow> JSON" where
  "to_json_rettype (Tret a0) = List [String STR ''Tret'', to_json a0]"
| "to_json_rettype Tint8signed = List [String STR ''Tint8signed'']"
| "to_json_rettype Tint8unsigned = List [String STR ''Tint8unsigned'']"
| "to_json_rettype Tint16signed = List [String STR ''Tint16signed'']"
| "to_json_rettype Tint16unsigned = List [String STR ''Tint16unsigned'']"
| "to_json_rettype Tvoid = List [String STR ''Tvoid'']"
instance ..
end

instantiation calling_convention_ext :: (_) jsonable
begin
fun to_json_calling_convention_ext :: "('a) calling_convention_scheme \<Rightarrow> JSON" where
  "to_json_calling_convention_ext v = Object [
    (STR ''cc_vararg'', to_json (cc_vararg v)),
    (STR ''cc_unproto'', to_json (cc_unproto v)),
    (STR ''cc_structret'', to_json (cc_structret v))]"
instance ..
end

instantiation signature_ext :: (_) jsonable
begin
fun to_json_signature_ext :: "('a) signature_scheme \<Rightarrow> JSON" where
  "to_json_signature_ext v = Object [
    (STR ''sig_args'', to_json (sig_args v)),
    (STR ''sig_res'', to_json (sig_res v)),
    (STR ''sig_cc'', to_json (sig_cc v))]"
instance ..
end

instantiation memory_chunk :: jsonable
begin
fun to_json_memory_chunk :: "memory_chunk \<Rightarrow> JSON" where
  "to_json_memory_chunk Mint8signed = String STR ''Mint8signed''"
| "to_json_memory_chunk Mint8unsigned = String STR ''Mint8unsigned''"
| "to_json_memory_chunk Mint16signed = String STR ''Mint16signed''"
| "to_json_memory_chunk Mint16unsigned = String STR ''Mint16unsigned''"
| "to_json_memory_chunk Mint32 = String STR ''Mint32''"
| "to_json_memory_chunk Mint64 = String STR ''Mint64''"
| "to_json_memory_chunk Mfloat32 = String STR ''Mfloat32''"
| "to_json_memory_chunk Mfloat64 = String STR ''Mfloat64''"
| "to_json_memory_chunk Many32 = String STR ''Many32''"
| "to_json_memory_chunk Many64 = String STR ''Many64''"
instance ..
end

instantiation init_data :: jsonable
begin
fun to_json_init_data :: "init_data \<Rightarrow> JSON" where
  "to_json_init_data (Init_int8 a0) = List [String STR ''Init_int8'', to_json a0]"
| "to_json_init_data (Init_int16 a0) = List [String STR ''Init_int16'', to_json a0]"
| "to_json_init_data (Init_int32 a0) = List [String STR ''Init_int32'', to_json a0]"
| "to_json_init_data (Init_int64 a0) = List [String STR ''Init_int64'', to_json a0]"
| "to_json_init_data (Init_float32 a0) = List [String STR ''Init_float32'', to_json a0]"
| "to_json_init_data (Init_float64 a0) = List [String STR ''Init_float64'', to_json a0]"
| "to_json_init_data (Init_space a0) = List [String STR ''Init_space'', to_json a0]"
| "to_json_init_data (Init_addrof a0 a1) = List [String STR ''Init_addrof'', to_json a0, to_json a1]"
instance ..
end

instantiation globvar_ext :: (jsonable, _) jsonable
begin
fun to_json_globvar_ext :: "('a, 'b) globvar_scheme \<Rightarrow> JSON" where
  "to_json_globvar_ext v = Object [
    (STR ''gvar_info'', to_json (gvar_info v)),
    (STR ''gvar_init'', to_json (gvar_init v)),
    (STR ''gvar_readonly'', to_json (gvar_readonly v)),
    (STR ''gvar_volatile'', to_json (gvar_volatile v))]"
instance ..
end

instantiation globdef :: (jsonable, jsonable) jsonable
begin
fun to_json_globdef :: "('a, 'b) globdef \<Rightarrow> JSON" where
  "to_json_globdef (Gfun a0) = List [String STR ''Gfun'', to_json a0]"
| "to_json_globdef (Gvar a0) = List [String STR ''Gvar'', to_json a0]"
instance ..
end

instantiation program_ext :: (jsonable, jsonable, _) jsonable
begin
fun to_json_program_ext :: "('a, 'b, 'c) program_scheme \<Rightarrow> JSON" where
  "to_json_program_ext v = Object [
    (STR ''prog_defs'', to_json (prog_defs v)),
    (STR ''prog_public'', to_json (prog_public v)),
    (STR ''prog_main'', to_json (prog_main v))]"
instance ..
end

instantiation external_function :: jsonable
begin
fun to_json_external_function :: "external_function \<Rightarrow> JSON" where
(*   "to_json_external_function (EF_external a0 a1) = List [String STR ''EF_external'', to_json a0, to_json a1]"
| "to_json_external_function (EF_builtin a0 a1) = List [String STR ''EF_builtin'', to_json a0, to_json a1]"
| "to_json_external_function (EF_runtime a0 a1) = List [String STR ''EF_runtime'', to_json a0, to_json a1]"
| "to_json_external_function (EF_vload a0) = List [String STR ''EF_vload'', to_json a0]"
| "to_json_external_function (EF_vstore a0) = List [String STR ''EF_vstore'', to_json a0]" *)
  "to_json_external_function EF_malloc = List [String STR ''EF_malloc'']"
| "to_json_external_function EF_free = List [String STR ''EF_free'']"
| "to_json_external_function (EF_memcpy a0 a1) = List [String STR ''EF_memcpy'', to_json a0, to_json a1]"
(* | "to_json_external_function (EF_annot a0 a1 a2) = List [String STR ''EF_annot'', to_json a0, to_json a1, to_json a2]"
| "to_json_external_function (EF_annot_val a0 a1 a2) = List [String STR ''EF_annot_val'', to_json a0, to_json a1, to_json a2]"
| "to_json_external_function (EF_inline_asm a0 a1 a2) = List [String STR ''EF_inline_asm'', to_json a0, to_json a1, to_json a2]"
| "to_json_external_function (EF_debug a0 a1 a2) = List [String STR ''EF_debug'', to_json a0, to_json a1, to_json a2]" *)
instance ..
end

instantiation AST.fundef :: (jsonable) jsonable
begin
fun to_json_fundef :: "'a AST.fundef \<Rightarrow> JSON" where
  "to_json_fundef (Internal a0) = List [String STR ''Internal'', to_json a0]"
| "to_json_fundef (External a0) = List [String STR ''External'', to_json a0]"
instance ..
end

instantiation const :: jsonable
begin
fun to_json_const :: "const \<Rightarrow> JSON" where
  "to_json_const (Ointconst a0) = List [String STR ''Ointconst'', to_json a0]"
| "to_json_const (Ofloatconst a0) = List [String STR ''Ofloatconst'', to_json a0]"
| "to_json_const (Osingleconst a0) = List [String STR ''Osingleconst'', to_json a0]"
| "to_json_const (Olongconst a0) = List [String STR ''Olongconst'', to_json a0]"
| "to_json_const (Oaddrsymbol a0 a1) = List [String STR ''Oaddrsymbol'', to_json a0, to_json a1]"
| "to_json_const (Oaddrstack a0) = List [String STR ''Oaddrstack'', to_json a0]"
instance ..
end

instantiation unary_operation :: jsonable
begin
fun to_json_unary_operation :: "unary_operation \<Rightarrow> JSON" where
  "to_json_unary_operation Ocast8unsigned = String STR ''Ocast8unsigned''"
| "to_json_unary_operation Ocast8signed = String STR ''Ocast8signed''"
| "to_json_unary_operation Ocast16unsigned = String STR ''Ocast16unsigned''"
| "to_json_unary_operation Ocast16signed = String STR ''Ocast16signed''"
| "to_json_unary_operation Onegint = String STR ''Onegint''"
| "to_json_unary_operation Onotint = String STR ''Onotint''"
| "to_json_unary_operation Onegf = String STR ''Onegf''"
| "to_json_unary_operation Oabsf = String STR ''Oabsf''"
| "to_json_unary_operation Onegfs = String STR ''Onegfs''"
| "to_json_unary_operation Oabsfs = String STR ''Oabsfs''"
| "to_json_unary_operation Osingleoffloat = String STR ''Osingleoffloat''"
| "to_json_unary_operation Ofloatofsingle = String STR ''Ofloatofsingle''"
| "to_json_unary_operation Ointoffloat = String STR ''Ointoffloat''"
| "to_json_unary_operation Ointuoffloat = String STR ''Ointuoffloat''"
| "to_json_unary_operation Ofloatofint = String STR ''Ofloatofint''"
| "to_json_unary_operation Ofloatofintu = String STR ''Ofloatofintu''"
| "to_json_unary_operation Ointofsingle = String STR ''Ointofsingle''"
| "to_json_unary_operation Ointuofsingle = String STR ''Ointuofsingle''"
| "to_json_unary_operation Osingleofint = String STR ''Osingleofint''"
| "to_json_unary_operation Osingleofintu = String STR ''Osingleofintu''"
| "to_json_unary_operation Onegl = String STR ''Onegl''"
| "to_json_unary_operation Onotl = String STR ''Onotl''"
| "to_json_unary_operation Ointoflong = String STR ''Ointoflong''"
| "to_json_unary_operation Olongofint = String STR ''Olongofint''"
| "to_json_unary_operation Olongofintu = String STR ''Olongofintu''"
| "to_json_unary_operation Olongoffloat = String STR ''Olongoffloat''"
| "to_json_unary_operation Olonguoffloat = String STR ''Olonguoffloat''"
| "to_json_unary_operation Ofloatoflong = String STR ''Ofloatoflong''"
| "to_json_unary_operation Ofloatoflongu = String STR ''Ofloatoflongu''"
| "to_json_unary_operation Olongofsingle = String STR ''Olongofsingle''"
| "to_json_unary_operation Olonguofsingle = String STR ''Olonguofsingle''"
| "to_json_unary_operation Osingleoflong = String STR ''Osingleoflong''"
| "to_json_unary_operation Osingleoflongu = String STR ''Osingleoflongu''"
instance ..
end

instantiation binary_operation :: jsonable
begin
fun to_json_binary_operation :: "binary_operation \<Rightarrow> JSON" where
  "to_json_binary_operation Oadd = List [String STR ''Oadd'']"
| "to_json_binary_operation Osub = List [String STR ''Osub'']"
| "to_json_binary_operation Omul = List [String STR ''Omul'']"
| "to_json_binary_operation Odiv = List [String STR ''Odiv'']"
| "to_json_binary_operation Odivu = List [String STR ''Odivu'']"
| "to_json_binary_operation Omod = List [String STR ''Omod'']"
| "to_json_binary_operation Omodu = List [String STR ''Omodu'']"
| "to_json_binary_operation Oand = List [String STR ''Oand'']"
| "to_json_binary_operation Oor = List [String STR ''Oor'']"
| "to_json_binary_operation Oxor = List [String STR ''Oxor'']"
| "to_json_binary_operation Oshl = List [String STR ''Oshl'']"
| "to_json_binary_operation Oshr = List [String STR ''Oshr'']"
| "to_json_binary_operation Oshru = List [String STR ''Oshru'']"
| "to_json_binary_operation Oaddf = List [String STR ''Oaddf'']"
| "to_json_binary_operation Osubf = List [String STR ''Osubf'']"
| "to_json_binary_operation Omulf = List [String STR ''Omulf'']"
| "to_json_binary_operation Odivf = List [String STR ''Odivf'']"
| "to_json_binary_operation Oaddfs = List [String STR ''Oaddfs'']"
| "to_json_binary_operation Osubfs = List [String STR ''Osubfs'']"
| "to_json_binary_operation Omulfs = List [String STR ''Omulfs'']"
| "to_json_binary_operation Odivfs = List [String STR ''Odivfs'']"
| "to_json_binary_operation Oaddl = List [String STR ''Oaddl'']"
| "to_json_binary_operation Osubl = List [String STR ''Osubl'']"
| "to_json_binary_operation Omull = List [String STR ''Omull'']"
| "to_json_binary_operation Odivl = List [String STR ''Odivl'']"
| "to_json_binary_operation Odivlu = List [String STR ''Odivlu'']"
| "to_json_binary_operation Omodl = List [String STR ''Omodl'']"
| "to_json_binary_operation Omodlu = List [String STR ''Omodlu'']"
| "to_json_binary_operation Oandl = List [String STR ''Oandl'']"
| "to_json_binary_operation Oorl = List [String STR ''Oorl'']"
| "to_json_binary_operation Oxorl = List [String STR ''Oxorl'']"
| "to_json_binary_operation Oshll = List [String STR ''Oshll'']"
| "to_json_binary_operation Oshrl = List [String STR ''Oshrl'']"
| "to_json_binary_operation Oshrlu = List [String STR ''Oshrlu'']"
| "to_json_binary_operation (Ocmp a0) = List [String STR ''Ocmp'', to_json a0]"
| "to_json_binary_operation (Ocmpu a0) = List [String STR ''Ocmpu'', to_json a0]"
| "to_json_binary_operation (Ocmpf a0) = List [String STR ''Ocmpf'', to_json a0]"
| "to_json_binary_operation (Ocmpfs a0) = List [String STR ''Ocmpfs'', to_json a0]"
| "to_json_binary_operation (Ocmpl a0) = List [String STR ''Ocmpl'', to_json a0]"
| "to_json_binary_operation (Ocmplu a0) = List [String STR ''Ocmplu'', to_json a0]"
instance ..
end

instantiation expr :: jsonable
begin
fun to_json_expr :: "expr \<Rightarrow> JSON" where
  "to_json_expr (Evar a0) = List [String STR ''Evar'', to_json a0]"
| "to_json_expr (Econst a0) = List [String STR ''Econst'', to_json a0]"
| "to_json_expr (Eunop a0 a1) = List [String STR ''Eunop'', to_json a0, to_json a1]"
| "to_json_expr (Ebinop a0 a1 a2) = List [String STR ''Ebinop'', to_json a0, to_json a1, to_json a2]"
| "to_json_expr (Eload a0 a1) = List [String STR ''Eload'', to_json a0, to_json a1]"
instance ..
end

instantiation stmt :: jsonable
begin
fun to_json_stmt :: "stmt \<Rightarrow> JSON" where
  "to_json_stmt Sskip = List [String STR ''Sskip'']"
| "to_json_stmt (Sassign a0 a1) = List [String STR ''Sassign'', to_json a0, to_json a1]"
| "to_json_stmt (Sstore a0 a1 a2) = List [String STR ''Sstore'', to_json a0, to_json a1, to_json a2]"
| "to_json_stmt (Scall a0 a1 a2 a3) = List [String STR ''Scall'', to_json a0, to_json a1, to_json a2, to_json a3]"
| "to_json_stmt (Stailcall a0 a1 a2) = List [String STR ''Stailcall'', to_json a0, to_json a1, to_json a2]"
| "to_json_stmt (Sbuiltin a0 a1 a2) = List [String STR ''Sbuiltin'', to_json a0, to_json a1, to_json a2]"
| "to_json_stmt (Sseq a0 a1) = List [String STR ''Sseq'', to_json a0, to_json a1]"
| "to_json_stmt (Sifthenelse a0 a1 a2) = List [String STR ''Sifthenelse'', to_json a0, to_json a1, to_json a2]"
| "to_json_stmt (Sloop a0) = List [String STR ''Sloop'', to_json a0]"
| "to_json_stmt (Sblock a0) = List [String STR ''Sblock'', to_json a0]"
| "to_json_stmt (Sexit a0) = List [String STR ''Sexit'', to_json a0]"
| "to_json_stmt (Sswitch a0 a1 a2 a3) = List [String STR ''Sswitch'', to_json a0, to_json a1, to_json a2, to_json a3]"
| "to_json_stmt (Sreturn a0) = List [String STR ''Sreturn'', to_json a0]"
| "to_json_stmt (Slabel a0 a1) = List [String STR ''Slabel'', to_json a0, to_json a1]"
| "to_json_stmt (Sgoto a0) = List [String STR ''Sgoto'', to_json a0]"
instance ..
end

instantiation func_ext :: (_) jsonable
begin
fun to_json_func_ext :: "('a) func_scheme \<Rightarrow> JSON" where
  "to_json_func_ext v = Object [
    (STR ''fn_sig'', to_json (fn_sig v)),
    (STR ''fn_params'', to_json (fn_params v)),
    (STR ''fn_vars'', to_json (fn_vars v)),
    (STR ''fn_stackspace'', to_json (fn_stackspace v)),
    (STR ''fn_body'', to_json (fn_body v))]"
instance ..
end


definition "test_func \<equiv>
  Internal (func.make signature_main [] [] 0 (Sreturn (Some (Econst (Ointconst 0x42)))))"

definition test_program :: program where 
  "test_program \<equiv> program.make [(STR ''main'', Gfun test_func)] [] (STR ''main'')"

ML_val \<open>open Term_XML.Encode\<close>
ML_val \<open>Term_XML.Encode.term (Proof_Context.consts_of @{context}) (@{term "test_program"})\<close>

value "test_program"
term "prog_defs test_program"
value "to_json test_program"
value "show_json (to_json test_program)"

definition "jsoned \<equiv> show_json (to_json test_program)"
                 
ML_val \<open>open Generated_Files\<close>
ML_val \<open>Generated_Files.with_compile_dir (writeln o Path.print)\<close>
ML_val "open Path"

(* ML_val \<open>
val using_master_directory =
          File.full_path o Resources.master_directory o Proof_Context.theory_of;
val path = using_master_directory @{context} (Path.basic "program.cmj");
File.write path @{code jsoned}\<close> *)

ML_val \<open>writeln @{code jsoned}\<close>
end