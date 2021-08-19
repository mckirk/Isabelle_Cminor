theory Cminor_Syntax
  imports
    Main
    Integers
    Floats
    Memdata
begin

(*
  The syntax is kept separate here because the datatype declarations below take such a long time
  to process.
*)

section \<open>Abstract Syntax\<close>

(** Cminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  We first define the constants
  and operators that occur within expressions. *)

datatype const =
    Ointconst m_int
  | Ofloatconst float64 (**r double-precision floating-point constant *)
  | Osingleconst float32 (**r single-precision floating-point constant *)
  | Olongconst m_int64  (**r long integer constant *)
  | Oaddrsymbol ident m_ptrofs (**r address of the symbol plus the offset *)
  | Oaddrstack m_ptrofs   (**r stack pointer plus the given offset *)

datatype unary_operation =
    Ocast8unsigned (* 8-bit zero extension *)
  | Ocast8signed (* 8-bit sign extension *)
  | Ocast16unsigned (* 16-bit zero extension *)
  | Ocast16signed (* 16-bit sign extension *)
  | Onegint (* integer opposite *)
  | Onotint (* bitwise complement *)
  | Onegf (* float64 opposite *)
  | Oabsf (* float64 absolute value *)
  | Onegfs (* float32 opposite *)
  | Oabsfs (* float32 absolute value *)
  | Osingleoffloat (* float truncation to float32 *)
  | Ofloatofsingle (* float extension to float64 *)
  | Ointoffloat (* signed integer to float64 *)
  | Ointuoffloat (* unsigned integer to float64 *)
  | Ofloatofint (* float64 to signed integer *)
  | Ofloatofintu (* float64 to unsigned integer *)
  | Ointofsingle (* signed integer to float32 *)
  | Ointuofsingle (* unsigned integer to float32 *)
  | Osingleofint (* float32 to signed integer *)
  | Osingleofintu (* float32 to unsigned integer *)
  | Onegl (* long integer opposite *)
  | Onotl (* long bitwise complement *)
  | Ointoflong (* long to int *)
  | Olongofint (* signed int to long *)
  | Olongofintu (* unsigned int to long *)
  | Olongoffloat (* float64 to signed long *)
  | Olonguoffloat (* float64 to unsigned long *)
  | Ofloatoflong (* signed long to float64 *)
  | Ofloatoflongu (* unsigned long to float64 *)
  | Olongofsingle (* float32 to signed long *)
  | Olonguofsingle (* float32 to unsigned long *)
  | Osingleoflong (* signed long to float32 *)
  | Osingleoflongu (* unsigned long to float32 *)

datatype binary_operation =
    Oadd (* integer addition *)
  | Osub (* integer subtraction *)
  | Omul (* integer multiplication *)
  | Odiv (* integer signed division *)
  | Odivu (* integer unsigned division *)
  | Omod (* integer signed modulus *)
  | Omodu (* integer unsigned modulus *)
  | Oand (* integer bitwise ``and'' *)
  | Oor (* integer bitwise ``or'' *)
  | Oxor (* integer bitwise ``xor'' *)
  | Oshl (* integer left shift *)
  | Oshr (* integer right signed shift *)
  | Oshru (* integer right unsigned shift *)
  | Oaddf (* float64 addition *)
  | Osubf (* float64 subtraction *)
  | Omulf (* float64 multiplication *)
  | Odivf (* float64 division *)
  | Oaddfs (* float32 addition *)
  | Osubfs (* float32 subtraction *)
  | Omulfs (* float32 multiplication *)
  | Odivfs (* float32 division *)
  | Oaddl (* long addition *)
  | Osubl (* long subtraction *)
  | Omull (* long multiplication *)
  | Odivl (* long signed division *)
  | Odivlu (* long unsigned division *)
  | Omodl (* long signed modulus *)
  | Omodlu (* long unsigned modulus *)
  | Oandl (* long bitwise ``and'' *)
  | Oorl (* long bitwise ``or'' *)
  | Oxorl (* long bitwise ``xor'' *)
  | Oshll (* long left shift *)
  | Oshrl (* long right signed shift *)
  | Oshrlu (* long right unsigned shift *)
  | Ocmp comparison (* integer signed comparison *)
  | Ocmpu comparison (* integer unsigned comparison *)
  | Ocmpf comparison (* float64 comparison *)
  | Ocmpfs comparison (* float32 comparison *)
  | Ocmpl comparison (* long signed comparison *)
  | Ocmplu comparison (* long unsigned comparison *)

(** Expressions include reading local variables, constants,
  arithmetic operations, and memory loads. *)

datatype expr =
    Evar ident
  | Econst const
  | Eunop unary_operation expr
  | Ebinop binary_operation expr expr
  | Eload memory_chunk expr

(** Statements include expression evaluation, assignment to local variables,
  memory stores, function calls, an if/then/else conditional, infinite
  loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1]
  enclosing [Sblock] statements. *)

type_synonym label = ident

datatype stmt =
    Sskip
  | Sassign ident expr
  | Sstore memory_chunk expr expr
  | Scall "ident option" signature expr "expr list"
  | Stailcall signature expr "expr list"
  | Sbuiltin "ident option" external_function "expr list"
  | Sseq stmt stmt
  | Sifthenelse expr stmt stmt
  | Sloop stmt
  | Sblock stmt
  | Sexit nat
  | Sswitch bool expr "(Z * nat) list" nat
  | Sreturn "expr option"
  | Slabel label stmt
  | Sgoto label

(** Functions are composed of a signature, a list of parameter names,
  a list of local variables, and a  statement representing
  the function body.  Each function can allocate a memory block of
  size [fn_stackspace] on entrance.  This block will be deallocated
  automatically before the function returns.  Pointers into this block
  can be taken with the [Oaddrstack] operator. *)

record func =
  fn_sig :: signature
  fn_params :: "ident list"
  fn_vars :: "ident list"
  fn_stackspace :: Z
  fn_body :: stmt

type_synonym fundef = "func AST.fundef"
type_synonym program = "(fundef, unit) AST.program"

fun funsig where
  "funsig (Internal f) = fn_sig f"
| "funsig (External ef) = ef_sig ef"

end