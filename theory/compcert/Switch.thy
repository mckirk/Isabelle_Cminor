theory Switch
imports
Main
Maps
Integers
Values
begin

(** Multi-way branches (``switch'' statements) and their compilation
    to comparison trees. *)

(** A multi-way branch is composed of a list of (key, action) pairs,
  plus a default action.  *)

type_synonym table = "(Z * nat) list"

fun switch_target :: "Z \<Rightarrow> nat \<Rightarrow> table \<Rightarrow> nat" where
  "switch_target n dfl [] = dfl"
| "switch_target n dfl ((key, action) # r) = (if n = key then action else switch_target n dfl r)"

inductive switch_argument :: "bool \<Rightarrow> val \<Rightarrow> Z \<Rightarrow> bool" where
    switch_argument_32:
      "switch_argument False (Vint i) (Int.unsigned i)"
  | switch_argument_64:
      "switch_argument True (Vlong i) (Int64.unsigned i)"

fun switch_argument_fun :: "bool \<Rightarrow> val \<Rightarrow> Z option" where
  "switch_argument_fun False (Vint i) = Some (Int.unsigned i)"
| "switch_argument_fun True (Vlong i) = Some (Int64.unsigned i)"
| "switch_argument_fun _ _ = None"

end