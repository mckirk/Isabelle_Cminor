theory Globalenvs
  imports Main
    Maps AST
    Integers Floats Values Memory
begin

(** Global environments are a component of the dynamic semantics of
  all languages involved in the compiler.  A global environment
  maps symbol names (names of functions and of global variables)
  to the corresponding memory addresses.  It also maps memory addresses
  of functions to the corresponding function descriptions.

  Global environments, along with the initial memory state at the beginning
  of program execution, are built from the program of interest, as follows:
- A distinct memory address is assigned to each function of the program.
  These function addresses use negative numbers to distinguish them from
  addresses of memory blocks.  The associations of function name to function
  address and function address to function description are recorded in
  the global environment.
- For each global variable, a memory block is allocated and associated to
  the name of the variable.

  These operations reflect (at a high level of abstraction) what takes
  place during program linking and program loading in a real operating
  system. *)

(** Auxiliary function for initialization of global variables. *)

fun store_zeros :: "mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> Z \<Rightarrow> (mem option)" where
  "store_zeros m b p n =
  (if n \<le> 0 then Some m else
    (case Mem.store Mint8unsigned m b p (Vint 0) of
      Some m' \<Rightarrow> store_zeros m' b (p + 1) (n - 1)
    | None \<Rightarrow> None
    ))"

section \<open>Symbol environments\<close>

(** Symbol environments are a restricted view of global environments,
  focusing on symbol names and their associated blocks.  They do not
  contain mappings from blocks to function or variable definitions. *)

record Senv_t =
  senv_find_symbol :: "ident \<Rightarrow> block option"
  senv_public_symbol :: "ident \<Rightarrow> bool"
  senv_invert_symbol :: "block \<Rightarrow> ident option"
  senv_block_is_volatile :: "block \<Rightarrow> bool"
  senv_nextblock :: block

locale Senv'
begin

(** Operations *)
abbreviation "find_symbol \<equiv> senv_find_symbol"
abbreviation "public_symbol \<equiv> senv_public_symbol"
abbreviation "invert_symbol \<equiv> senv_invert_symbol"
abbreviation "block_is_volatile \<equiv> senv_block_is_volatile"
abbreviation "nextblock \<equiv> senv_nextblock"

(** Properties *)

named_theorems inv_defs'

definition [inv_defs']: "find_symbol_injective se \<equiv>
  \<forall>id1 id2 b. find_symbol se id1 = Some b \<longrightarrow> find_symbol se id2 = Some b \<longrightarrow> id1 = id2"

definition [inv_defs']: "invert_find_symbol se \<equiv>
  \<forall>id b. invert_symbol se b = Some id \<longrightarrow> find_symbol se id = Some b"

definition [inv_defs']: "find_invert_symbol se \<equiv>
  \<forall>id b. find_symbol se id = Some b \<longrightarrow> invert_symbol se b = Some id"

definition [inv_defs']: "public_symbol_exists se \<equiv>
  \<forall>id. public_symbol se id \<longrightarrow> (\<exists> b. find_symbol se id = Some b)"

definition [inv_defs']: "find_symbol_below se \<equiv>
  \<forall>id b. find_symbol se id = Some b \<longrightarrow> b < nextblock se"

definition [inv_defs']: "block_is_volatile_below se \<equiv>
  \<forall>b. block_is_volatile se b \<longrightarrow> b < nextblock se"

inductive invariants where
  "\<lbrakk> find_symbol_injective se;
     invert_find_symbol se;
     find_invert_symbol se;
     public_symbol_exists se;
     find_symbol_below se;
     block_is_volatile_below se \<rbrakk> \<Longrightarrow>
  invariants se"

lemmas inv_def = inv_defs' invariants.simps[simplified]

definition equiv :: "Senv_t \<Rightarrow> Senv_t \<Rightarrow> bool" where
  "equiv se1 se2 =
     ((\<forall> ident. find_symbol se2 ident = find_symbol se1 ident)
  \<and> (\<forall> ident. public_symbol se2 ident = public_symbol se1 ident)
  \<and> (\<forall> b. block_is_volatile se2 b = block_is_volatile se1 b))"
end

interpretation Senv: Senv' .

section \<open>Global Environments\<close>

record ('f, 'v) Genv_t =
  genv_public :: "ident list" (* which symbol names are public *)
  genv_symb :: "block ITree" (* mapping symbol -> block *)
  genv_defs :: "(('f, 'v) globdef) PTree" (* mapping block -> definition *)
  genv_next :: block (* next symbol pointer *)

locale Genv' =
  fixes ft :: "'f itself"
  fixes vt :: "'v itself"
begin

named_theorems inv_defs'

definition [inv_defs']: "genv_symb_range ge \<equiv>
  \<forall>id b. ITree.get id (genv_symb ge) = Some b \<longrightarrow> b < (genv_next ge)"

definition [inv_defs']: "genv_defs_range ge \<equiv>
  \<forall>b g. PTree.get b (genv_defs ge) = Some g \<longrightarrow> b < (genv_next ge)"

definition [inv_defs']: "genv_vars_inj ge \<equiv>
  \<forall>id1 id2 b.
  ITree.get id1 (genv_symb ge) = Some b \<longrightarrow> ITree.get id2 (genv_symb ge) = Some b \<longrightarrow> id1 = id2"

inductive invariants where
  "\<lbrakk>genv_symb_range ge;
    genv_defs_range ge;
    genv_vars_inj ge\<rbrakk> \<Longrightarrow>
  invariants ge"

lemmas inv_def = inv_defs' invariants.simps[simplified]

subsection \<open>Lookup functions\<close>

context
  fixes ge :: "('f, 'v) Genv_t"
begin

(** [find_symbol ge id] returns the block associated with the given name, if any *)

fun find_symbol :: "ident \<Rightarrow> (block option)" where
  "find_symbol ident = ITree.get ident (genv_symb ge)"

(** [symbol_address ge id ofs] returns a pointer into the block associated
  with [id], at byte offset [ofs].  [Vundef] is returned if no block is associated
  to [id]. *)

fun symbol_address :: "ident \<Rightarrow> m_ptrofs \<Rightarrow> val" where
  "symbol_address ident ofs =
  (case find_symbol ident of
    Some b \<Rightarrow> Vptr b ofs
  | None \<Rightarrow> Vundef
  )"

(** [public_symbol ge id] says whether the name [id] is public and defined. *)

fun public_symbol :: "ident \<Rightarrow> bool" where
  "public_symbol ident =
  (case find_symbol ident of
    None \<Rightarrow> False
  | Some _ \<Rightarrow> ident \<in> set (genv_public ge)
  )"

(** [find_def ge b] returns the global definition associated with the given address. *)

fun find_def :: "block \<Rightarrow> (('f, 'v) globdef) option" where
  "find_def b = PTree.get b (genv_defs ge)"

(** [find_funct_ptr ge b] returns the function description associated with
    the given address. *)

fun find_funct_ptr :: "block \<Rightarrow> ('f option)" where
  "find_funct_ptr b = (case find_def b of Some (Gfun f) \<Rightarrow> Some f | _ \<Rightarrow> None )"

(** [find_funct] is similar to [find_funct_ptr], but the function address
    is given as a value, which must be a pointer with offset 0. *)

fun find_funct :: "val \<Rightarrow> ('f option)" where
  "find_funct v =
  (case v of
    Vptr b ofs \<Rightarrow> if ofs = 0 then find_funct_ptr b else None
  | _ \<Rightarrow> None
  )"

(** [invert_symbol ge b] returns the name associated with the given block, if any *)

(* CompCert uses 'PTree.fold' here, which we can't because our tree doesn't have a structure *)
fun invert_symbol :: "block \<Rightarrow> (ident option)" where
  "invert_symbol b =
    (if \<exists>id. (genv_symb ge) id = Some b
      then Some (THE id. (genv_symb ge) id = Some b)
      else None)"

(** [find_var_info ge b] returns the information attached to the variable
   at address [b]. *)

fun find_var_info :: "block \<Rightarrow> (('v globvar) option)" where
  "find_var_info b =
  (case find_def b of Some (Gvar v) \<Rightarrow> Some v | _ \<Rightarrow> None )"

(** [block_is_volatile ge b] returns [true] if [b] points to a global variable
  of volatile type, [false] otherwise. *)

fun block_is_volatile :: "block \<Rightarrow> bool" where
  "block_is_volatile b =
  (case find_var_info b of
    None \<Rightarrow> False
  | Some gv \<Rightarrow> (gvar_volatile gv)
  )"

subsection \<open>Constructing the global environment\<close>

fun add_global :: "(ident * ('f, 'v) globdef) \<Rightarrow> ('f, 'v) Genv_t" where
  "add_global (ident, gdef) =
  Genv_t.make
    (genv_public ge)
    (ITree.set ident (genv_next ge) (genv_symb ge))
    (PTree.set (genv_next ge) gdef (genv_defs ge))
    ((genv_next ge) + 1)"

end

fun add_globals :: "('f, 'v) Genv_t \<Rightarrow> ((ident * ('f, 'v) globdef) list) \<Rightarrow> ('f, 'v) Genv_t" where
  "add_globals ge gl = List.foldl add_global ge gl"

fun empty_genv :: "ident list \<Rightarrow> ('f, 'v) Genv_t" where
  "empty_genv pub = Genv_t.make pub ITree.empty PTree.empty 1"

fun globalenv :: "('f, 'v) program \<Rightarrow> ('f, 'v) Genv_t" where
  "globalenv p = add_globals (empty_genv (prog_public p)) (prog_defs p)"

subsection \<open>Coercing a global environment into a symbol environment\<close>

fun to_senv :: "('f, 'v) Genv_t \<Rightarrow> Senv_t" where
  "to_senv ge =
    Senv_t.make
    (Genv'.find_symbol ge)
    (Genv'.public_symbol ge)
    (Genv'.invert_symbol ge)
    (Genv'.block_is_volatile ge)
    (genv_next ge)"

lemma to_senv_invars:
  assumes "Genv'.invariants ge"
  shows "Senv.invariants (to_senv ge)"
  using assms
  unfolding Genv'.inv_def Senv.inv_def
  by (auto simp add: Senv_t.defs the_equality split: option.split)

section \<open>Construction of the initial memory state\<close>

context
  fixes ge :: "('f, 'v) Genv_t"
begin

fun store_init_data :: "mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> init_data \<Rightarrow> (mem option)" where
  "store_init_data m b p ident =
  (case ident of
    Init_int8 n \<Rightarrow> Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n \<Rightarrow> Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n \<Rightarrow> Mem.store Mint32 m b p (Vint n)
  | Init_int64 n \<Rightarrow> Mem.store Mint64 m b p (Vlong n)
  | Init_float32 n \<Rightarrow> Mem.store Mfloat32 m b p (Vsingle n)
  | Init_float64 n \<Rightarrow> Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof symb ofs \<Rightarrow>
      (case Genv'.find_symbol ge symb of
        None \<Rightarrow> None
      | Some b' \<Rightarrow> Mem.store Mptr m b p (Vptr b' ofs)
      )
  | Init_space n \<Rightarrow> Some m
  )"

fun store_init_data_list :: "mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> (init_data list) \<Rightarrow> (mem option)" where
  "store_init_data_list m b p idl =
  (case idl of
    [] \<Rightarrow> Some m
  | ident # idl' \<Rightarrow>
      (case store_init_data m b p ident of
        None \<Rightarrow> None
      | Some m' \<Rightarrow> store_init_data_list m' b (p + init_data_size ident) idl'
      )
  )"

fun perm_globvar :: "('v globvar) \<Rightarrow> permission" where
  "perm_globvar gv =
  (if (gvar_volatile gv) then Nonempty
  else if (gvar_readonly gv) then Readable
  else Writable)"

fun alloc_global :: "mem \<Rightarrow> (ident * ('f, 'v) globdef) \<Rightarrow> (mem option)" where
  "alloc_global m idg =
  (case idg of
    (ident, Gfun f) \<Rightarrow>
      let (m1, b) = Mem.alloc m 0 1 in
      Mem.drop_perm m1 b 0 1 Nonempty
  | (ident, Gvar v) \<Rightarrow>
      let init = (gvar_init v) in
      let sz = init_data_list_size init in
      let (m1, b) = Mem.alloc m 0 sz in
      (case store_zeros m1 b 0 sz of
        None \<Rightarrow> None
      | Some m2 \<Rightarrow>
          (case store_init_data_list m2 b 0 init of
            None \<Rightarrow> None
          | Some m3 \<Rightarrow> Mem.drop_perm m3 b 0 sz (perm_globvar v)
          )
      )
  )"

fun alloc_globals :: "mem \<Rightarrow> ((ident * ('f, 'v) globdef) list) \<Rightarrow> (mem option)" where
  "alloc_globals m gl =
  (case gl of
    [] \<Rightarrow> Some m
  | g # gl' \<Rightarrow>
      (case alloc_global m g of
        None \<Rightarrow> None
      | Some m' \<Rightarrow> alloc_globals m' gl'
      )
  )"
end

fun init_mem :: "('f, 'v) program \<Rightarrow> (mem option)" where
  "init_mem p = alloc_globals (Genv'.globalenv p) Mem.empty (prog_defs p)"

lemmas simps = find_symbol.simps symbol_address.simps public_symbol.simps find_def.simps
  find_funct_ptr.simps find_funct.simps invert_symbol.simps find_var_info.simps
  block_is_volatile.simps add_global.simps add_globals.simps empty_genv.simps globalenv.simps
  to_senv.simps store_init_data.simps store_init_data_list.simps perm_globvar.simps
  alloc_global.simps alloc_globals.simps init_mem.simps

section \<open>Check invariants\<close>

context
  notes [simp] = Genv'.inv_def Genv_t.defs
begin

lemma empty_inv: "invariants (empty_genv pub)"
  by auto

lemma add_global_inv:
  "invariants ge \<Longrightarrow> add_global ge (ident, gdef) = ge' \<Longrightarrow> invariants ge'"
proof (goal_cases)
  case 1

  let ?nb = "genv_next ge"

  {
    fix id b

    have "ITree.get id (genv_symb ge') = Some b \<longrightarrow> b < (genv_next ge')"
      apply (cases "id = ident")
      using 1 pos_less_trans
      by auto
  }

  note all = this

  {
    fix b g

    have "PTree.get b (genv_defs ge') = Some g \<longrightarrow> b < (genv_next ge')"
      apply (cases "b = ?nb")
      using 1 pos_less_trans
      by auto
  }

  note all = all this

  {
    fix id1 id2 b

    have "ITree.get id1 (genv_symb ge') = Some b \<longrightarrow> ITree.get id2 (genv_symb ge') = Some b \<longrightarrow> id1 = id2"
      apply (cases "id1 = ident"; cases "id2 = ident")
      using 1 apply auto
      by blast+
  }

  note all = all this

  then show ?case
    by simp
qed

lemma add_globals_inv:
  "invariants ge \<Longrightarrow> add_globals ge gl = ge' \<Longrightarrow> invariants ge'"
  apply (induction gl arbitrary: ge ge')
  apply simp
  using add_global_inv
  by (metis add_global.cases add_globals.simps foldl_Cons)

lemma globalenv_inv:
  "invariants ge \<Longrightarrow> globalenv p = ge' \<Longrightarrow> invariants ge'"
  by (metis empty_inv add_globals_inv globalenv.simps)

end
end

end