theory AST
  imports Main
    BinNums Integers Floats
begin

(** This file defines a number of data types and operations used in
  the abstract syntax trees of many of the intermediate languages. *)

(** * Syntactic elements *)

(** Identifiers (names of local variables, of global symbols and functions,
  etc) are represented by strings in this formalization, but with the
  type [positive] in CompCert. Conversion is done at deserialization. *)

type_synonym ident = String.literal

(** The intermediate languages are weakly typed, using the following types: *)

datatype type =
    Tint (* 32-bit integers or pointers *)
  | Tfloat (* 64-bit double-precision floats *)
  | Tlong (* 64-bit integers *)
  | Tsingle (* 32-bit single-precision floats *)
  | Tany32 (* any 32-bit value *)
  | Tany64 (* any 64-bit value, i.e. any value *)

definition Tptr :: type where 
"Tptr \<equiv> if ptr64 then Tlong else Tint"

lemma Tptr64[simp]: "Tptr = Tlong" unfolding Tptr_def ptr64_def by simp

(** To describe the values returned by functions, we use the more precise
    types below. *)

datatype rettype =
    Tret type (* like type t *)
  | Tint8signed (* 8-bit signed integer *)
  | Tint8unsigned (* 8-bit unsigned integer *)
  | Tint16signed (* 16-bit signed integer *)
  | Tint16unsigned (* 16-bit unsigned integer *)
  | Tvoid (* no value returned *)

(** Additionally, function definitions and function calls are annotated
  by function signatures indicating:
- the number and types of arguments;
- the type of the returned value;
- additional information on which calling convention to use.

These signatures are used in particular to determine appropriate
calling conventions for the function. *)

record calling_convention =
  cc_vararg :: bool (* variable-arity function *)
  cc_unproto :: bool (* old-style unprototyped function *)
  cc_structret :: bool (* function returning a struct *)

definition cc_default :: calling_convention where
"cc_default \<equiv> (| cc_vararg = False, cc_unproto = False, cc_structret = False |)"

record signature =
  sig_args :: "type list"
  sig_res :: rettype
  sig_cc :: calling_convention

abbreviation "mksignature \<equiv> signature.make"

definition signature_dummy :: signature where
  "signature_dummy \<equiv> (| sig_args = [], sig_res = Tvoid, sig_cc = cc_default |)"

definition signature_main :: signature where
  "signature_main \<equiv> (| sig_args = [], sig_res = (Tret Tint), sig_cc = cc_default |)"

(** Memory accesses (load and store instructions) are annotated by
  a ``memory chunk'' indicating the type, size and signedness of the
  chunk of memory being accessed. *)

datatype memory_chunk =
    Mint8signed (* 8-bit signed integer *)
  | Mint8unsigned (* 8-bit unsigned integer *)
  | Mint16signed (* 16-bit signed integer *)
  | Mint16unsigned (* 16-bit unsigned integer *)
  | Mint32 (* 32-bit integer, or pointer *)
  | Mint64 (* 64-bit integer *)
  | Mfloat32 (* 32-bit single-precision float *)
  | Mfloat64 (* 64-bit double-precision float *)
  | Many32 (* any value that fits in 32 bits *)
  | Many64 (* any value *)

definition Mptr :: memory_chunk where "Mptr \<equiv> if Archi.ptr64 then Mint64 else Mint32"

(** The type (integer/pointer or float) of a chunk. *)

fun type_of_chunk :: "memory_chunk \<Rightarrow> type" where
  "type_of_chunk Mint8signed = Tint"
| "type_of_chunk Mint8unsigned = Tint"
| "type_of_chunk Mint16signed = Tint"
| "type_of_chunk Mint16unsigned = Tint"
| "type_of_chunk Mint32 = Tint"
| "type_of_chunk Mint64 = Tlong"
| "type_of_chunk Mfloat32 = Tsingle"
| "type_of_chunk Mfloat64 = Tfloat"
| "type_of_chunk Many32 = Tany32"
| "type_of_chunk Many64 = Tany64"

(** Same, as a return type. *)

fun rettype_of_chunk :: "memory_chunk \<Rightarrow> rettype" where
  "rettype_of_chunk Mint8signed = Tint8signed"
| "rettype_of_chunk Mint8unsigned = Tint8unsigned"
| "rettype_of_chunk Mint16signed = Tint16signed"
| "rettype_of_chunk Mint16unsigned = Tint16unsigned"
| "rettype_of_chunk Mint32 = Tret Tint"
| "rettype_of_chunk Mint64 = Tret Tlong"
| "rettype_of_chunk Mfloat32 = Tret Tsingle"
| "rettype_of_chunk Mfloat64 = Tret Tfloat"
| "rettype_of_chunk Many32 = Tret Tany32"
| "rettype_of_chunk Many64 = Tret Tany64"

(** Initialization data for global variables. *)

datatype init_data =
  Init_int8 m_int
| Init_int16 m_int
| Init_int32 m_int
| Init_int64 m_int64
| Init_float32 float32
| Init_float64 float64
| Init_space Z
| Init_addrof ident m_ptrofs (* address of symbol + offset *)

fun init_data_size :: "init_data \<Rightarrow> Z" where
  "init_data_size (Init_int8 _) = 1"
| "init_data_size (Init_int16 _) = 2"
| "init_data_size (Init_int32 _) = 4"
| "init_data_size (Init_int64 _) = 8"
| "init_data_size (Init_float32 _) = 4"
| "init_data_size (Init_float64 _) = 8"
| "init_data_size (Init_addrof _ _) = (if Archi.ptr64 then 8 else 4)"
| "init_data_size (Init_space n) = max n 0"

fun init_data_list_size :: "(init_data list) \<Rightarrow> Z" where
  "init_data_list_size [] = 0"
| "init_data_list_size (i # il') = init_data_size i + init_data_list_size il'"

(** Information attached to global variables. *)

record 'v globvar =
  gvar_info :: 'v (* language-dependent info, e.g. a type *)
  gvar_init :: "init_data list" (* initialization data *)
  gvar_readonly :: bool (* read-only variable? (const) *)
  gvar_volatile :: bool (* volatile variable? *)

(** Whole programs consist of:
- a collection of global definitions (name and description);
- a set of public names (the names that are visible outside
  this compilation unit);
- the name of the ``main'' function that serves as entry point in the program.

A global definition is either a global function or a global variable.
The type of function descriptions and that of additional information
for variables vary among the various intermediate languages and are
taken as parameters to the [program] type.  The other parts of whole
programs are common to all languages. *)

datatype ('f, 'v) globdef =
    Gfun 'f
  | Gvar "'v globvar"

record ('f, 'v) program =
  prog_defs :: "(ident * ('f, 'v) globdef) list"
  prog_public :: "ident list"
  prog_main :: ident

(** * External functions *)

(** For most languages, the functions composing the program are either
  internal functions, defined within the language, or external functions,
  defined outside.  External functions include system calls but also
  compiler built-in functions.  We define a type for external functions
  and associated operations. *)

datatype external_function =
(* TODO: not implemented for now
    EF_external (ef_name: String.literal) (ef_sg: signature)
     (** A system call or library function.  Produces an event
         in the trace. *)
  | EF_builtin (ef_name: String.literal) (ef_sg: signature)
     (** A compiler built-in function.  Behaves like an external, but
         can be inlined by the compiler. *)
  | EF_runtime (ef_name: String.literal) (ef_sg: signature)
     (** A function from the run-time library.  Behaves like an
         external, but must not be redefined. *)
  | EF_vload (ef_chunk: memory_chunk)
     (** A volatile read operation.  If the address given as first argument
         points within a volatile global variable, generate an
         event and return the value found in this event.  Otherwise,
         produce no event and behave like a regular memory load. *)
  | EF_vstore (ef_chunk: memory_chunk)
     (** A volatile store operation.   If the address given as first argument
         points within a volatile global variable, generate an event.
         Otherwise, produce no event and behave like a regular memory store. *)
*)
    EF_malloc
     (** Dynamic memory allocation.  Takes the requested size in bytes
         as argument; returns a pointer to a fresh block of the given size.
         Produces no observable event. *)
  | EF_free
     (** Dynamic memory deallocation.  Takes a pointer to a block
         allocated by an [EF_malloc] external call and frees the
         corresponding block.
         Produces no observable event. *)
  | EF_memcpy (ef_sz: Z) (ef_al: Z)
     (** Block copy, of [sz] bytes, between addresses that are [al]-aligned. *)
(* TODO: not implemented for now
  | EF_annot (ef_kind: positive) (ef_text_str: String.literal) (ef_targs: "type list")
     (** A programmer-supplied annotation.  Takes zero, one or several arguments,
         produces an event carrying the text and the values of these arguments,
         and returns no value. *)
  | EF_annot_val (ef_kind: positive) (ef_text_str: String.literal) (ef_targ: type)
     (** Another form of annotation that takes one argument, produces
         an event carrying the text and the value of this argument,
         and returns the value of the argument. *)
  | EF_inline_asm (ef_text_str: String.literal) (ef_sg: signature) (ef_clobbers: "String.literal list")
     (** Inline [asm] statements.  Semantically, treated like an
         annotation with no parameters ([EF_annot text nil]).  To be
         used with caution, as it can invalidate the semantic
         preservation theorem.  Generated only if [-finline-asm] is
         given. *)
  | EF_debug (ef_kind: positive) (ef_text_id: ident) (ef_targs: "type list")
     (** Transport debugging information from the front-end to the generated
         assembly.  Takes zero, one or several arguments like [EF_annot].
         Unlike [EF_annot], produces no observable event. *)
*)

(** The type signature of an external function. *)

fun ef_sig :: "external_function \<Rightarrow> signature" where
(* TODO: not implemented for now
  "ef_sig (EF_external name sg) = sg"
| "ef_sig (EF_builtin name sg) = sg"
| "ef_sig (EF_runtime name sg) = sg"
| "ef_sig (EF_vload chunk) = mksignature (Tptr # []) (rettype_of_chunk chunk) cc_default"
| "ef_sig (EF_vstore chunk) = mksignature (Tptr # type_of_chunk chunk # []) Tvoid cc_default"
*)
  "ef_sig EF_malloc = mksignature (Tptr # []) (Tret Tptr) cc_default"
| "ef_sig EF_free = mksignature (Tptr # []) Tvoid cc_default"
| "ef_sig (EF_memcpy sz al) = mksignature (Tptr # Tptr # []) Tvoid cc_default"
(* TODO: not implemented for now
| "ef_sig (EF_annot kind text targs) = mksignature targs Tvoid cc_default"
| "ef_sig (EF_annot_val kind text targ) = mksignature (targ # []) targ cc_default"
| "ef_sig (EF_inline_asm text sg clob) = sg"
| "ef_sig (EF_debug kind text targs) = mksignature targs Tvoid cc_default"
*)

(** Function definitions are the union of internal and external functions. *)

datatype 'a fundef = Internal 'a | External external_function

end