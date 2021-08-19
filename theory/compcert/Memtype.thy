theory Memtype imports Main
begin

(** This file defines the interface for the memory model that
  is used in the dynamic semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

(** Memory states are accessed by addresses [b, ofs]: pairs of a block
  identifier [b] and a byte offset [ofs] within that block.
  Each address is associated to permissions, also known as access rights.
  The following permissions are expressible:
- Freeable (exclusive access): all operations permitted
- Writable: load, store and pointer comparison operations are permitted,
  but freeing is not.
- Readable: only load and pointer comparison operations are permitted.
- Nonempty: valid, but only pointer comparisons are permitted.
- Empty: not yet allocated or previously freed; no operation permitted.

The first four cases are represented by the following type of permissions.
Being empty is represented by the absence of any permission.
*)

datatype permission =
    Freeable
  | Writable
  | Readable
  | Nonempty

(** In the list, each permission implies the other permissions further down the
    list.  We reflect this fact by the following order over permissions. *)

inductive perm_order :: "permission \<Rightarrow> permission \<Rightarrow> bool" where
    perm_refl: "perm_order p p"
  | perm_F_any: "perm_order Freeable p"
  | perm_W_R: "perm_order Writable Readable"
  | perm_any_N: "perm_order p Nonempty"

declare perm_order.intros[intro!]

lemma perm_order_code[code]: "perm_order p1 p2 =
  (if p1 = p2 then True else
  case (p1, p2) of
    (Freeable, _) \<Rightarrow> True
  | (Writable, Readable) \<Rightarrow> True
  | (_, Nonempty) \<Rightarrow> True
  | _ \<Rightarrow> False)"
  apply (simp add: perm_order.simps)
  by (metis permission.exhaust permission.simps(13) permission.simps(14) permission.simps(15) permission.simps(16))

lemma perm_order_trans:
  "perm_order p1 p2 \<Longrightarrow> perm_order p2 p3 \<Longrightarrow> perm_order p1 p3"
  using perm_order.simps by auto

(** Each address has not one, but two permissions associated
  with it.  The first is the current permission.  It governs whether
  operations (load, store, free, etc) over this address succeed or
  not.  The other is the maximal permission.  It is always at least as
  strong as the current permission.  Once a block is allocated, the
  maximal permission of an address within this block can only
  decrease, as a result of [free] or [drop_perm] operations, or of
  external calls.  In contrast, the current permission of an address
  can be temporarily lowered by an external call, then raised again by
  another external call. *)

datatype perm_kind = Max | Cur

end