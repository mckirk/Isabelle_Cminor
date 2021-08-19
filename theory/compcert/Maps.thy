theory Maps
  imports Main BinNums AST
begin

(** Applicative finite maps are the main data structure used in this
  project.  A finite map associates data to keys.  The two main operations
  are [set k d m], which returns a map identical to [m] except that [d]
  is associated to [k], and [get k m] which returns the data associated
  to key [k] in map [m].  In this library, we distinguish two kinds of maps:
- Trees: the [get] operation returns an option type, either [None]
  if no data is associated to the key, or [Some d] otherwise.
- Maps: the [get] operation always returns a data.  If no data was explicitly
  associated with the key, a default data provided at map initialization time
  is returned.

  In this library, we provide efficient implementations of trees and
  maps whose keys range over the type [positive] of binary positive
  integers or any type that can be injected into [positive].  The
  implementation is based on radix-2 search trees (uncompressed
  Patricia trees) and guarantees logarithmic-time operations.  An
  inefficient implementation of maps as functions is also provided.
*)

(*
  CompCert defines here 'efficient implementations of trees and
  maps whose keys range over the type [positive]'. But since we aren't
  interested in efficiency at this point, we simply model these trees and
  maps abstractly -- keeping the interface similar to CompCert's however.
*)

(** * The abstract signatures of trees *)

locale TREE =
  fixes empty :: 't
  and get :: "'a \<Rightarrow> 't \<Rightarrow> 'b option"
  and set :: "'a \<Rightarrow> 'b \<Rightarrow> 't \<Rightarrow> 't"
  and remove :: "'a \<Rightarrow> 't \<Rightarrow> 't"

  (** The ``good variables'' properties for trees, expressing
    commutations between [get], [set] and [remove]. *)

  assumes gempty: "get i empty = None"
  and gss: "get i (set i x m) = Some x"
  and gso: "i \<noteq> j \<Longrightarrow> get i (set j x m) = get i m"
  and gsspec: "get i (set j x m) = (if i = j then Some x else get i m)"
  and grs: "get i (remove i m) = None"
  and gro: "i \<noteq> j \<Longrightarrow> get i (remove j m) = get i m"
  and grspec: "get i (remove j m) = (if i = j then None else get i m)"
begin
lemmas laws = gempty gss gso gsspec grs gro grspec
end

(** * The abstract signatures of maps *)

locale MAP =
  fixes init :: "'b \<Rightarrow> 'm"
  and get :: "'a \<Rightarrow> 'm \<Rightarrow> 'b"
  and set :: "'a \<Rightarrow> 'b \<Rightarrow> 'm \<Rightarrow> 'm"

  assumes gi: "get i (init x) = x"
  and gss: "get i (set i x m) = x"
  and gso: "i \<noteq> j \<Longrightarrow> get i (set j x m) = get i m"
  and gsspec: "get i (set j x m) = (if i = j then x else get i m)"
  and gsident: "get j (set i (get i m) m ) = get j m"
begin
lemmas laws = gi gss gso gsspec gsident
end

(* we model Trees as a regular map *)

locale regular_map =
  fixes type :: "'t itself"
begin
abbreviation empty :: "('t, 'a) map" where "empty \<equiv> Map.empty"
fun get :: "'t \<Rightarrow> ('t, 'a) map \<Rightarrow> 'a option" where "get k t = t k"
fun set :: "'t \<Rightarrow> 'a \<Rightarrow> ('t, 'a) map \<Rightarrow> ('t, 'a) map" where "set k e t = t(k \<mapsto> e)"
fun remove :: "'t \<Rightarrow> ('t, 'a) map \<Rightarrow> ('t, 'a) map"  where "remove k t = t(k := None)"

sublocale TREE empty get set remove
  apply unfold_locales
  by (auto simp add: empty_def)
end

type_synonym 'a PTree = "(positive, 'a) map"
interpretation PTree: regular_map "TYPE(positive)" .

type_synonym 'a ITree = "(ident, 'a) map"
interpretation ITree: regular_map "TYPE(ident)" .

(* this would be closer to CompCert's Map implementation: *)

(* type_synonym ('a, 'b) "DefaultMap" = "'b \<times> (('a, 'b) Map.map)"

locale DefaultMap =
  fixes type :: "'t itself"
begin
fun init :: "'b \<Rightarrow> ('t, 'b) DefaultMap" where
"init d = (d, Map.empty)"
fun get :: "'t \<Rightarrow> ('t, 'b) DefaultMap \<Rightarrow> 'b" where
"get k (d, m) = (case m k of Some y \<Rightarrow> y | _ \<Rightarrow> d)"
fun set :: "'t \<Rightarrow> 'b \<Rightarrow> ('t, 'b) DefaultMap \<Rightarrow> ('t, 'b) DefaultMap" where
"set k e (d, m) = (d, (m(k \<mapsto>e)))"

sublocale MAP init get set
  apply unfold_locales
  by (auto)

lemmas simps = init.simps get.simps set.simps
end *)

(* instead, we simply model Maps as a total function *)

type_synonym ('a, 'b) "DefaultMap" = "'a \<Rightarrow> 'b"

locale DefaultMap =
  fixes type :: "'t itself"
begin
fun init :: "'b \<Rightarrow> ('t, 'b) DefaultMap" where
  "init d = (\<lambda>_. d)"
fun get :: "'t \<Rightarrow> ('t, 'b) DefaultMap \<Rightarrow> 'b" where
  "get k = (\<lambda>m. m k)"
fun set :: "'t \<Rightarrow> 'b \<Rightarrow> ('t, 'b) DefaultMap \<Rightarrow> ('t, 'b) DefaultMap" where
  "set k e = (\<lambda>m. m(k := e))"
fun update :: "'t \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('t, 'b) DefaultMap \<Rightarrow> ('t, 'b) DefaultMap" where
  "update k f = (\<lambda>m. m(k := f (m k)))"

sublocale MAP init get set
  apply unfold_locales
  by (auto)

lemmas simps = init.simps get.simps set.simps update.simps
end

declare DefaultMap.simps[code]

type_synonym 'a PMap = "(positive, 'a) DefaultMap"
interpretation PMap: DefaultMap "TYPE(positive)" .
type_synonym 'a IMap = "(ident, 'a) DefaultMap"
interpretation IMap: DefaultMap "TYPE(ident)" .
type_synonym 'a ZMap = "(Z, 'a) DefaultMap"
interpretation ZMap: DefaultMap "TYPE(Z)" .

end
