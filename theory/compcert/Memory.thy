theory Memory
  imports Main Memdata Memtype Maps AST
begin

(** This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

type_synonym mem_contents_type = "(memval ZMap) PMap" (* block -> offset -> memval *)
type_synonym mem_access_type = "(Z \<Rightarrow> perm_kind \<Rightarrow> permission option) PMap"

record mem =
  mem_contents :: mem_contents_type
  mem_access :: mem_access_type
  mem_nextblock :: block (* called just 'nextblock' in CompCert, but that would lead to collisions *)

lemma mem_update_id:
  "mem_contents_update (\<lambda>x. x) = id"
  "mem_access_update (\<lambda>x. x) = id"
  "mem_nextblock_update (\<lambda>x. x) = id"
  by auto

locale Mem'
begin

abbreviation "nextblock \<equiv> mem_nextblock"

inductive perm_order' where
  "perm_order p' p \<Longrightarrow> perm_order' (Some p') p"

inductive perm_order'' where
  "perm_order p1 p2 \<Longrightarrow> perm_order'' (Some p1) (Some p2)"
| "perm_order'' _ None"

declare perm_order'.intros[intro] perm_order''.intros[intro]
declare perm_order'.cases[elim] perm_order''.cases[elim]

lemma perm_order'_code[code]:
  "perm_order' po p =
  (case po of
    Some p' \<Rightarrow> perm_order p' p
  | None \<Rightarrow> False)"
  using Mem'.perm_order'.simps case_optionE by fastforce

lemma perm_order''_code[code]:
  "perm_order'' po1 po2 =
  (case (po1, po2) of
    (Some p1, Some p2) \<Rightarrow> perm_order p1 p2
  | (_, None) \<Rightarrow> True
  | (None, Some _) \<Rightarrow> False)"
  by (auto split: option.splits)

lemma [iff]: "perm_order'' p p"
  using Mem'.perm_order''.simps by auto

section \<open>Memory invariants\<close>

named_theorems mem_invariants_defs

definition [mem_invariants_defs]:
  "access_max m \<equiv> (\<forall>b ofs. perm_order'' ((mem_access m) b ofs Max) ((mem_access m) b ofs Cur))"

definition [mem_invariants_defs]:
  "nextblock_noaccess m \<equiv> (\<forall>b ofs k. b \<ge> (nextblock m) \<longrightarrow> (mem_access m) b ofs k = None)"

definition [mem_invariants_defs]:
  "contents_default m \<equiv> (\<forall>b. finite {ofs. (mem_contents m) b ofs \<noteq> Undef})"

definition [mem_invariants_defs]:
  "nextblock_undef m \<equiv> (\<forall>b ofs. b \<ge> (nextblock m) \<longrightarrow> (mem_contents m) b ofs = Undef)"

inductive mem_invariants where
  "\<lbrakk> access_max m; nextblock_noaccess m; contents_default m; nextblock_undef m \<rbrakk> \<Longrightarrow> mem_invariants m"

lemmas mem_invariants_def = mem_invariants_defs mem_invariants.simps[simplified]


section \<open>Validity of blocks and accesses\<close>

(** A block address is valid if it was previously allocated. It remains valid
  even after being freed. *)

definition "valid_block m b \<equiv> b < (nextblock m)"

(* Permissions *)

fun perm :: "'a mem_scheme \<Rightarrow> positive \<Rightarrow> int \<Rightarrow> perm_kind \<Rightarrow> permission \<Rightarrow> bool" where
"perm m b ofs k p = perm_order' ((PMap.get b (mem_access m)) ofs k) p"

lemma perm_perm_order:
  assumes "perm_order p p'"
  shows "perm m b ofs k p \<Longrightarrow> perm m b ofs k p'"
  using Mem'.perm_order'.simps assms perm_order.simps by auto

definition range_perm :: "'a mem_scheme \<Rightarrow> positive \<Rightarrow> int \<Rightarrow> int \<Rightarrow> perm_kind \<Rightarrow> permission \<Rightarrow> bool" where
"range_perm m b lo hi k p = (\<forall>ofs \<in> {lo..<hi}. perm m b ofs k p)"

lemma range_perm_0[iff]: "range_perm m b lo lo k p"
  unfolding range_perm_def by simp

lemma range_perm_order:
  assumes "range_perm m b lo hi k p"
  assumes "perm_order p p'"
  shows "range_perm m b lo hi k p'"
  unfolding range_perm_def
  apply (rule ballI)
  subgoal for ofs
  using assms(1) unfolding range_perm_def
  apply (rule ballE[of _ _ ofs])
  using assms(2) perm_perm_order
   apply blast
  by simp
  done

lemma range_perm_subrange:
  assumes "range_perm m b lo hi k p"
  assumes "lo' \<ge> lo" "hi' \<le> hi"
  shows "range_perm m b lo' hi' k p"
  using assms unfolding range_perm_def by auto

(** [valid_access m chunk b ofs p] holds if a memory access
    of the given chunk is possible in [m] at address [b, ofs]
    with current permissions [p].
    This means:
- The range of bytes accessed all have current permission [p].
- The offset [ofs] is aligned.
*)

fun valid_access :: "mem \<Rightarrow> memory_chunk \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> permission \<Rightarrow> bool" where
  "valid_access m chunk b ofs p =
    (range_perm m b ofs (ofs + size_chunk chunk) Cur p
    \<and> ((align_chunk chunk) dvd ofs))"

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)
fun valid_pointer :: "mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> bool" where
  "valid_pointer m b ofs = perm m b ofs Cur Nonempty"

section \<open>Operations over memory stores\<close>

(** The initial store *)

definition empty :: mem where
  "empty = mem.make
        (PMap.init (ZMap.init Undef))
        (PMap.init (\<lambda>ofs k. None))
        1"

(** Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the address of the fresh block, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. *)

fun alloc :: "mem \<Rightarrow> Z \<Rightarrow> Z \<Rightarrow> (mem \<times> block)" where
  "alloc m lo hi =
  ((mem_contents_update (PMap.set (nextblock m) (ZMap.init Undef)) o
    mem_access_update (PMap.set (nextblock m) (\<lambda> ofs k. if lo \<le> ofs \<and> ofs < hi then Some Freeable else None)) o
    mem_nextblock_update ((+) 1)) m, nextblock m)"

lemma alloc_valid_block[iff]:
  assumes "alloc m lo hi = (m', b)"
  shows "valid_block m' b' \<longleftrightarrow> b' = b \<or> valid_block m b'" "\<not>valid_block m b"
  unfolding valid_block_def
  using assms
   apply (auto simp add: mem.defs)
  by (metis add.commute pos_less_pos_plus1)+

lemma alloc_max_perm:
  assumes "alloc m lo hi = (m', b)"
  assumes "valid_block m b'"
  shows "Mem'.perm m' b' ofs perm_kind.Max p \<longleftrightarrow> Mem'.perm m b' ofs perm_kind.Max p"
  using assms
  by (auto simp: mem.defs valid_block_def less_imp_neq)

lemma alloc_range_perm:
  assumes "alloc m lo hi = (m', b)"
  shows "range_perm m' b lo hi k Freeable"
  unfolding range_perm_def using assms
  by (auto simp: mem.defs)

(** Freeing a block between the given bounds.
  Return the updated memory state where the given range of the given block
  has been invalidated: future reads and writes to this
  range will fail.  Requires freeable permission on the given range. *)

fun unchecked_free :: "mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> Z \<Rightarrow> mem" where
"unchecked_free m b lo hi = mem_access_update
  (PMap.update b (\<lambda> prev ofs k. (if lo \<le> ofs \<and> ofs < hi then None else (prev ofs k)))) m"

fun free :: "mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> Z \<Rightarrow> mem option" where
"free m b lo hi =
  (if range_perm m b lo hi Cur Freeable
  then Some (unchecked_free m b lo hi)
  else None)"

(** Memory reads. *)

(** Reading N adjacent bytes in a block content. *)

fun getN :: "nat \<Rightarrow> Z \<Rightarrow> (memval ZMap) \<Rightarrow> (memval list)" where
  "getN 0 p c = []"
| "getN (Suc n) p c = ZMap.get p c # getN n (p + 1) c"

lemma getN_len[simp]: "length (getN n p c) = n"
  by (induction n arbitrary: p) auto

lemma getN_same:
  assumes "\<And>ofs. ofs \<ge> p \<Longrightarrow> c ofs = c' ofs"
  assumes "\<And>ofs. ofs < p + sz \<Longrightarrow> c ofs = c' ofs"
  shows "getN sz p c = getN sz p c'"
  using assms apply (induction sz p c rule: getN.induct)
  by auto

(** [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  It returns the value of the memory chunk
  at that address.  [None] is returned if the accessed bytes
  are not readable. *)

fun load :: "memory_chunk \<Rightarrow> mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> val option" where 
  "load chunk m b ofs =
    (if valid_access m chunk b ofs Readable
    then Some(decode_val chunk (getN (size_chunk_nat chunk) ofs (PMap.get b (mem_contents m))))
    else None)"

(** [loadv chunk m addr] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

fun loadv :: "memory_chunk \<Rightarrow> mem \<Rightarrow> val \<Rightarrow> (val option)" where
  "loadv chunk m (Vptr b ofs) = load chunk m b (uint ofs)"
| "loadv chunk m _ = None"

(** [loadbytes m b ofs n] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. *)

fun loadbytes :: "mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> Z \<Rightarrow> ((memval list) option)" where
  "loadbytes m b ofs n =
  (if range_perm m b ofs (ofs + n) Cur Readable
  then Some (getN (nat n) ofs ((mem_contents m) b))
  else None)"

lemma loadbytes_0[simp]:
  "loadbytes m b ofs 0 = Some []"
  by auto

lemma loadbytes_len[simp]:
  assumes "loadbytes m b ofs n = Some bytes"
  shows "length bytes = nat n"
  using assms by (auto split: if_splits)

(* Memory stores *)

(** Writing N adjacent bytes in a block content. *)

fun setN :: "(memval list) \<Rightarrow> Z \<Rightarrow> (memval ZMap) \<Rightarrow> (memval ZMap)" where
  "setN [] p c = c"
| "setN (v # vl') p c = setN vl' (p + 1) (ZMap.set p v c)"

lemma setN_same:
  fixes p :: int
  shows "(ofs < p \<or> ofs \<ge> p + length vl) \<Longrightarrow> (setN vl p c) ofs = c ofs"
  apply (induction vl p c rule: setN.induct)
  by auto

lemma setN_one:
  assumes "offset < length vl"
  shows "setN vl p c (p+offset) = vl ! offset"
  using assms
  proof (induction vl p c arbitrary: offset rule: setN.induct)
    case (1 p c)
    then show ?case by simp
  next
    case (2 v vl' p c)
    show ?case
    proof (cases offset)
      case 0
      then show ?thesis
        using setN_same by auto
    next
      case (Suc offset')
      with 2 have "setN vl' (p + 1) (ZMap.set p v c) (p + 1 + int offset') = vl' ! offset'"
        by fastforce

      with Suc show ?thesis
        by (simp add: add.assoc)
    qed
  qed

lemmas setN_one' = setN_one[of 0, simplified]

lemma setN_finite_vals:
  fixes ofs vl
  assumes "finite {ofs. b ofs \<noteq> Undef}"
  defines "b' \<equiv> setN vl ofs b"
  shows "finite {ofs. b' ofs \<noteq> Undef}"
  using assms
proof (induction vl arbitrary: ofs b b')
  case Nil
  then show ?case 
    by simp
next
  case (Cons v vl ofs' b)

  have "finite {ofs. (b(ofs' := v)) ofs \<noteq> Undef}"
    apply (cases "v = Undef"; cases "b ofs' = Undef")
  proof (goal_cases)
    case 1

    then have "{ofs. (b(ofs' := v)) ofs \<noteq> Undef} = {ofs. b ofs \<noteq> Undef}"
      by auto

    then show ?case using Cons(2) by auto
  next
    case 2

    then have "insert ofs' {ofs. (b(ofs' := v)) ofs \<noteq> Undef} = {ofs. b ofs \<noteq> Undef}"
      by auto

    then show ?case using Cons(2)
      by (metis finite_insert)
  next
    case 3

    then have "{ofs. (b(ofs' := v)) ofs \<noteq> Undef} = insert ofs' {ofs. b ofs \<noteq> Undef}"
      by auto

    then show ?case using Cons(2)
      by simp
  next
    case 4

    then have "{ofs. (b(ofs' := v)) ofs \<noteq> Undef} = {ofs. b ofs \<noteq> Undef}"
      by auto

    then show ?case using Cons(2) by auto
  qed

  note IH = Cons(1)[OF this]

  show ?case
    apply simp
    by (rule IH)
qed

lemma getN_setN:
  assumes "setN vl p c = c'"
  shows "getN (length vl) p c' = vl"
  using assms proof (induction vl p c arbitrary: c' rule: setN.induct)
  case (1 p c)
  then show ?case by simp
next
  case (2 v vl' p c)
  then obtain c'' where c'': "setN vl' (p + 1) (ZMap.set p v c) = c''" by simp
  with 2 have l: "getN (length vl') (p + 1) c'' = vl'"
    by blast

  {
    fix p'
    have "c'' p' = c' p'" if "p \<noteq> p'"
      using that c'' 2
      by simp
  }
  note cs_same = this

  note getN_same = getN_same[of "p+1" c' c'' "length vl'"]

  show ?case
    apply auto
    using setN_one'[of "v # vl'"] 2(2) apply force
    using "2.prems" c'' l by auto
qed

(** [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. *)

fun store :: "memory_chunk \<Rightarrow> mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> val \<Rightarrow> (mem option)" where
  "store chunk m b ofs v =
  (if valid_access m chunk b ofs Writable then
    Some (mem_contents_update (PMap.update b (setN (encode_val chunk v) ofs)) m)
  else
    None)"

lemma store_valid_block[iff]:
  assumes "store chunk m b ofs v = Some m'"
  shows "valid_block m' b' \<longleftrightarrow> valid_block m b'"
  unfolding valid_block_def
  using assms
  by (auto split: if_splits)

lemma store_max_perm:
  assumes "store chunk m b ofs v = Some m'"
  shows "Mem'.perm m' b' ofs' perm_kind.Max p \<longleftrightarrow> Mem'.perm m b' ofs' perm_kind.Max p"
  using assms
  by (auto simp: mem.defs split: if_splits)

lemma store_after_alloc:
  assumes "alloc m lo hi = (m', b)"
  assumes "ofs \<ge> lo" "ofs + size_chunk_nat chunk \<le> hi"
  assumes "align_chunk chunk dvd ofs"
  shows "\<exists>m''. store chunk m' b ofs v = Some m''"
  using assms
  apply (auto simp del: size_chunk_nat.simps alloc.simps simp: mem.defs)
  using range_perm_subrange[OF alloc_range_perm[OF assms(1)] assms(2,3)] range_perm_order
  by blast

(** [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

fun storev :: "memory_chunk \<Rightarrow> mem \<Rightarrow> val \<Rightarrow> val \<Rightarrow> (mem option)" where
  "storev chunk m (Vptr b ofs) v = store chunk m b (uint ofs) v"
| "storev chunk m _ v = None"

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)

fun storebytes :: "mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> (memval list) \<Rightarrow> (mem option)" where
  "storebytes m b ofs bytes =
  (if range_perm m b ofs (ofs + (length bytes)) Cur Writable then
    Some (mem_contents_update (PMap.update b (setN bytes ofs)) m)
  else
    None)"

lemma storebytes_0[simp]:
  "storebytes m b ofs [] = Some m"
  by auto

(** [drop_perm m b lo hi p] sets the max permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have current permissions
    [Freeable] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

fun drop_perm :: "mem \<Rightarrow> block \<Rightarrow> Z \<Rightarrow> Z \<Rightarrow> permission \<Rightarrow> (mem option)" where
  "drop_perm m b lo hi p =
  (if range_perm m b lo hi Cur Freeable then
    Some (mem.make (mem_contents m)
                (PMap.set b
                        (\<lambda>ofs k. if lo \<le> ofs \<and> ofs < hi then Some p else PMap.get b (mem_access m) ofs k)
                        (mem_access m))
                (nextblock m))
  else None)"

section \<open>Check invariants\<close>

context notes [simp] = mem_invariants_def mem.defs
begin

lemma empty_inv: "mem_invariants empty"
  unfolding empty_def
  by (auto)

lemma alloc_inv: "mem_invariants m \<Longrightarrow> alloc m lo hi = (m', b) \<Longrightarrow> mem_invariants m'"
  apply (auto)
  by (metis add.commute pos_larger)+

lemma unchecked_free_inv: "mem_invariants m \<Longrightarrow> unchecked_free m b lo hi = m' \<Longrightarrow> mem_invariants m'"
  by (auto split: option.split)

lemma free_inv: "mem_invariants m \<Longrightarrow> free m b lo hi = Some m' \<Longrightarrow> mem_invariants m'"
  using unchecked_free_inv
  by (auto split: if_splits simp del: unchecked_free.simps mem_invariants_def)

lemma store_inv: "mem_invariants m \<Longrightarrow> store chunk m b ofs v = Some m' \<Longrightarrow> mem_invariants m'"
  apply (simp del: valid_access.simps encode_val.simps split: if_splits)
  apply safe
proof (goal_cases)
  case (1 b ofs)
  then show ?case
    by simp
next
  case (2 b ofs k)
  then show ?case
    by fastforce
next
  case (3 b)
  then show ?case
    by (simp add: Mem'.setN_finite_vals)
next
  case (4 b' ofs)

  have "b' \<ge> mem_nextblock m"
    using "4"(7) by auto

  then have "\<And>ofs k. mem_access m b' ofs k = None"
    using "4"(3) by simp

  then have "b \<noteq> b'"
    using "4"(1)
    apply (cases chunk)
    apply (auto simp: range_perm_def)
    by auto

  then have "(mem_contents m') b' ofs = (mem_contents m) b' ofs"
    using "4"(6)
    by auto

  then show ?case
    by (simp add: "4"(5) "4"(6) \<open>mem_nextblock m \<le> b'\<close>)
qed

lemma storev_inv: "mem_invariants m \<Longrightarrow> storev chunk m addr v = Some m' \<Longrightarrow> mem_invariants m'"
  apply (erule storev.elims)
  apply (auto split: val.splits simp del: mem_invariants_def store.simps)
  apply (rule store_inv)
  by auto

lemma storebytes_inv: "mem_invariants m \<Longrightarrow> storebytes m b ofs bytes = Some m' \<Longrightarrow> mem_invariants m'"
  apply (simp split: if_splits)
  apply (cases "bytes = []")
  apply (simp add: setN.simps[abs_def] mem_update_id)
  apply safe
proof (goal_cases)
  case (1 b ofs)
  then show ?case by simp
next
  case (2 b ofs k)
  then show ?case by auto
next
  case (3 b)
  then show ?case
    by (simp add: Mem'.setN_finite_vals)
next
  case (4 b' ofs)

  have "b' \<ge> mem_nextblock m"
    using "4"(8) by fastforce

  then have "\<And>ofs k. mem_access m b' ofs k = None"
    using "4"(3) by simp

  then have "b \<noteq> b'"
    using "4"(1,6)
    apply (auto simp: range_perm_def split: option.splits memory_chunk.splits)
    by auto

  then have "(mem_contents m') b' ofs = (mem_contents m) b' ofs"
    using "4"(7)
    by auto

  then show ?case
    by (simp add: "4"(5) "4"(7) \<open>mem_nextblock m \<le> b'\<close>)
qed

lemma drop_perm_inv: "mem_invariants m \<Longrightarrow> drop_perm m b lo hi p = Some m' \<Longrightarrow> mem_invariants m'"
  apply simp
  apply (split if_splits; standard; simp)
proof (goal_cases)
  case 1

  {
    fix b' ofs

    from 1 have perm_m: "perm_order'' (mem_access m b' ofs perm_kind.Max) (mem_access m b' ofs Cur)" by blast

    have "perm_order'' (mem_access m' b' ofs perm_kind.Max) (mem_access m' b' ofs Cur)"
    proof (cases "b = b' \<and> lo \<le> ofs \<and> ofs < hi")
      case True
      then have "\<And>k. mem_access m' b' ofs k = Some p"
        using 1 by auto
      then show ?thesis
        by auto
    next
      case False
      then have "mem_access m' b' ofs = mem_access m b' ofs"
        using 1 by auto
      then show ?thesis using perm_m
        by simp
    qed
  }

  then show ?case by simp
next
  case 2

  {
    assume lo_hi: "lo < hi"
  
    from 2(1,3) have b: "b < nextblock m"
      unfolding range_perm_def perm.simps
      apply clarsimp
    proof (goal_cases)
      case 1
      {
        assume "b \<ge> nextblock m"
        with 1 have p1: "\<And>ofs k. mem_access m b ofs k = None" by simp
  
        fix ofs
        assume "ofs \<in> {lo..<hi}"
        with 1 have p2: "\<exists>y. mem_access m b ofs Cur = Some y"
          by (metis Mem'.perm_order'.cases)
  
        from p1 p2 have "False"
          by simp
      }
      then show ?case using lo_hi by fastforce
    qed

    fix b' ofs k
    assume "b' \<ge> nextblock m'"
    then have "mem_access m' b' ofs k = None"
      using 2 b by auto
  }

  then show ?case
    apply (cases "lo < hi")
    using 2 by auto
qed
end

section \<open>Generic injections\<close>

(** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
*)

definition mem_inj :: "meminj \<Rightarrow> mem \<Rightarrow> mem \<Rightarrow> bool" where
  "mem_inj f m1 m2 \<equiv>
      (\<forall> b1 b2 delta ofs k p.
      f b1 = Some(b2, delta) \<longrightarrow>
      perm m1 b1 ofs k p \<longrightarrow>
      perm m2 b2 (ofs + delta) k p) \<and>

      (\<forall> b1 b2 delta chunk ofs p.
      f b1 = Some(b2, delta) \<longrightarrow>
      range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p \<longrightarrow>
      (align_chunk chunk dvd delta)) \<and>

      (\<forall> b1 ofs b2 delta.
      f b1 = Some(b2, delta) \<longrightarrow>
      perm m1 b1 ofs Cur Readable \<longrightarrow>
      memval_inject f (ZMap.get ofs ((mem_contents m1) b1)) (ZMap.get (ofs+delta) ((mem_contents m2) b2)))"

(** Preservation of stores. *)

definition meminj_no_overlap :: "meminj \<Rightarrow> mem \<Rightarrow> bool" where
  "meminj_no_overlap f m \<equiv>
  \<forall> b1 b1' delta1 b2 b2' delta2 ofs1 ofs2.
  b1 \<noteq> b2 \<longrightarrow>
  f b1 = Some (b1', delta1) \<longrightarrow>
  f b2 = Some (b2', delta2) \<longrightarrow>
  perm m b1 ofs1 Max Nonempty \<longrightarrow>
  perm m b2 ofs2 Max Nonempty \<longrightarrow>
  b1' \<noteq> b2' \<or> ofs1 + delta1 \<noteq> ofs2 + delta2"

section \<open>Memory extensions\<close>

definition extends :: "mem \<Rightarrow> mem \<Rightarrow> bool" where
  "extends m1 m2 \<equiv>
    (nextblock m1 = nextblock m2) \<and>
    (mem_inj inject_id m1 m2) \<and>
    (\<forall> b ofs k p.
      perm m2 b ofs k p \<longrightarrow>
      perm m1 b ofs k p \<or> ~perm m1 b ofs Max Nonempty)"

section \<open>Memory injections\<close>

(** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with unsigned machine integers;
- pointers that could be represented using unsigned machine integers remain
  representable after the injection.
*)

named_theorems inject_defs

definition [inject_defs]: "mi_inj f m1 m2 \<equiv>
      Mem'.mem_inj f m1 m2"

definition [inject_defs]: "mi_freeblocks f m1 m2 \<equiv>
      \<forall> b. ~(Mem'.valid_block m1 b) \<longrightarrow> f b = None"

definition [inject_defs]: "mi_mappedblocks f m1 m2 \<equiv>
      \<forall> b b' delta. f b = Some(b', delta) \<longrightarrow> Mem'.valid_block m2 b'"

definition [inject_defs]: "mi_no_overlap f m1 m2 \<equiv>
      Mem'.meminj_no_overlap f m1"

definition [inject_defs]: "mi_representable f m1 m2 \<equiv>
      \<forall> b b' delta ofs.
      f b = Some(b', delta) \<longrightarrow>
      Mem'.perm m1 b (Int64.unsigned ofs) Max Nonempty \<or> Mem'.perm m1 b (Int64.unsigned ofs - 1) Max Nonempty \<longrightarrow>
      delta \<ge> 0 \<and> 0 \<le> Int64.unsigned ofs + delta \<and> Int64.unsigned ofs + delta \<le> Int64.max_unsigned"

definition [inject_defs]: "mi_perm_inv f m1 m2 \<equiv>
      \<forall> b1 ofs b2 delta k p.
      f b1 = Some(b2, delta) \<longrightarrow>
      Mem'.perm m2 b2 (ofs + delta) k p \<longrightarrow>
      Mem'.perm m1 b1 ofs k p \<or> ~Mem'.perm m1 b1 ofs Max Nonempty"

inductive inject where
  "\<lbrakk> mi_inj f m1 m2; mi_freeblocks f m1 m2; mi_mappedblocks f m1 m2; mi_no_overlap f m1 m2;
    mi_representable f m1 m2; mi_perm_inv f m1 m2 \<rbrakk> \<Longrightarrow> inject f m1 m2"

lemmas inject_def = inject_defs inject.simps[simplified]

section \<open>Invariance properties between two memory states\<close>

context
  fixes P :: "block \<Rightarrow> Z \<Rightarrow> bool"
begin
named_theorems unchanged_on_defs'

definition [unchanged_on_defs']: "unchanged_on_nextblock m_before m_after \<equiv>
    (Mem'.nextblock m_before) \<le> (Mem'.nextblock m_after)"
definition [unchanged_on_defs']: "unchanged_on_perm m_before m_after \<equiv>
    \<forall> b ofs k p.
    P b ofs \<longrightarrow> Mem'.valid_block m_before b \<longrightarrow>
    (Mem'.perm m_before b ofs k p \<longleftrightarrow> Mem'.perm m_after b ofs k p)"
definition [unchanged_on_defs']: "unchanged_on_contents m_before m_after \<equiv>
    \<forall> b ofs.
    P b ofs \<longrightarrow> Mem'.perm m_before b ofs Cur Readable \<longrightarrow>
    ZMap.get ofs (PMap.get b (mem_contents m_after)) =
    ZMap.get ofs (PMap.get b (mem_contents m_before))"

inductive unchanged_on :: "mem \<Rightarrow> mem \<Rightarrow> bool" where
  unchanged_on_intro: 
  "\<lbrakk>unchanged_on_nextblock m_before m_after;
    unchanged_on_perm m_before m_after;
    unchanged_on_contents m_before m_after \<rbrakk>
  \<Longrightarrow> unchanged_on m_before m_after"

lemmas unchanged_on_def = unchanged_on_defs' unchanged_on.simps[simplified]

lemma unchanged_on_refl:
  "unchanged_on m m"
  by (simp add: unchanged_on_nextblock_def unchanged_on_contents_def unchanged_on_perm_def unchanged_on_intro)


lemma alloc_unchanged_on:
  assumes "alloc m lo hi = (m', b)"
  assumes "mem_invariants m"
  shows "unchanged_on m m'"
  using assms
  unfolding unchanged_on_def valid_block_def mem_invariants_def
  by (auto simp: add.commute pos_larger less_imp_neq)

lemma store_unchanged_on:
  assumes "store chunk m b ofs v = Some m'"
  assumes "\<And>b' ofs'. P b' ofs' \<Longrightarrow> b' \<noteq> b \<or> ofs' < ofs \<or> ofs' \<ge> ofs + size_chunk_nat chunk"
  shows "unchanged_on m m'"
  unfolding unchanged_on_def valid_block_def
  using assms
    apply (auto simp del: align_chunk.simps size_chunk_nat.simps encode_val.simps split: if_splits)
  using setN_same encode_val_length by auto

end (* context *)

lemma unchanged_on_trans:
  assumes "mem_invariants m"
  assumes "unchanged_on P m m'"
  assumes "unchanged_on (\<lambda>b ofs. P b ofs \<and> valid_block m b) m' m''"
  shows "unchanged_on P m m''"
  using assms
  unfolding mem_invariants_def unchanged_on_def
  apply safe
     apply (metis dual_order.trans)
    apply (meson Mem'.valid_block_def dual_order.strict_trans1)
   apply (meson Mem'.valid_block_def le_less_trans not_less)
  by (metis Mem'.perm.elims(2) Mem'.perm_order'.simps Mem'.valid_block_def PMap.get.simps option.distinct(1) verit_comp_simplify1(3))

end (* locale Mem' *)

interpretation Mem: Mem' .

lemmas mem_simps = Mem.perm.simps Mem.valid_access.simps Mem.valid_pointer.simps Mem.alloc.simps
  Mem.unchecked_free.simps Mem.free.simps Mem.getN.simps Mem.load.simps Mem.loadv.simps
  Mem.loadbytes.simps Mem.setN.simps Mem.store.simps Mem.storev.simps Mem.storebytes.simps
  Mem.drop_perm.simps

(* Mem funcs should generally be blackboxes from here on out *)
declare mem_simps[simp del]

end