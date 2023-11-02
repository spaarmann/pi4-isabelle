theory Syntax
  imports Nominal2.Nominal2 "HOL-Library.AList"
begin

section\<open>General Definitions\<close>

atom_decl var
text\<open>There is a special variable called "heap":\<close>
definition "var_heap" :: var where "var_heap = undefined"

text\<open>Instances don't appear in binders, so we can just model these as string names.\<close>
type_synonym instanc = string
type_synonym field_name = string

text\<open>Bit vectors are mostly boolean lists.
 There is an additional option of including bit variables. This is used by the chomp operation.
 Variables only appear internally, never in the surface syntax.\<close>
datatype bit = Zero | One | BitVar
type_synonym bv = "bit list"
instantiation bit :: pure begin
  definition permute_bit :: "perm \<Rightarrow> bit \<Rightarrow> bit" where
    "permute_bit _ b = b"
  instance by standard (auto simp add: permute_bit_def)
end
fun bit_from_bool :: "bool \<Rightarrow> bit" where
  "bit_from_bool False = Zero" |
  "bit_from_bool True = One"
fun bool_from_bit :: "bit \<Rightarrow> bool option" where
  "bool_from_bit Zero = Some False" |
  "bool_from_bit One = Some True" |
  "bool_from_bit BitVar = None"

definition bv_to_bools :: "bv \<Rightarrow> bool list option" where
  "bv_to_bools bv = those (map bool_from_bit bv)"
declare bv_to_bools_def[simp]

typedef slice_range = "{(n::nat, m::nat). n < m}"
  by auto
setup_lifting type_definition_slice_range
lift_definition left :: "slice_range \<Rightarrow> nat" is fst.
lift_definition right :: "slice_range \<Rightarrow> nat" is snd.
lemma slice_range_valid[simp]: "left rng < right rng" by (transfer) (auto)

lift_definition slice_range_one :: "nat \<Rightarrow> slice_range" is "\<lambda>n. (n, n + 1)"
  by (auto)
lift_definition slice_range :: "nat \<Rightarrow> nat \<Rightarrow> slice_range"
  is "\<lambda>n m. if n < m then (n, m) else (undefined, undefined + 1)"
  by (auto)
lemma left_range_one[simp]: "left (slice_range_one n) = n" by (transfer) (auto)
lemma right_range_one[simp]: "right (slice_range_one n) = n + 1" by (transfer) (auto)
lemma left_range[simp]: "n < m \<Longrightarrow> left (slice_range n m) = n" by (transfer) (auto)
lemma right_range[simp]: "n < m \<Longrightarrow> right (slice_range n m) = m" by (transfer) (auto)
lemma right_range_left_0[simp]: "left rng = 0 \<Longrightarrow> rng = slice_range 0 (right rng)" by (transfer) (auto)
lift_definition slice_range_sub :: "slice_range \<Rightarrow> nat \<Rightarrow> slice_range"
  is "\<lambda>(n, m) k. if k \<le> n then (n - k, m - k) else (undefined, undefined + 1)"
  apply (auto)
  by (metis Pair_inject diff_less_mono less_add_one)

instantiation slice_range :: pure begin
  definition permute_slice_range :: "perm \<Rightarrow> slice_range \<Rightarrow> slice_range" where
    "permute_slice_range p rng = rng"
  instance by (standard) (auto simp add: permute_slice_range_def)
end

datatype packet = PktIn | PktOut
instantiation packet :: pure begin
  definition permute_packet :: "perm \<Rightarrow> packet \<Rightarrow> packet" where
    "permute_packet _ pkt = pkt"
  instance by standard (auto simp add: permute_packet_def)
end

record field =
  field_name :: field_name
  field_length :: nat
instantiation field_ext :: (type) pure begin
  definition permute_field_ext :: "perm \<Rightarrow> 'a field_ext \<Rightarrow> 'a field_ext" where
    "permute_field_ext p f = f"
  instance by standard (auto simp add: permute_field_ext_def)
end

record header_type =
  header_name :: string
  header_fields :: "field list"
type_synonym header_table = "(instanc \<times> header_type) list"
instantiation header_type_ext :: (type) pure begin
  definition permute_header_type_ext :: "perm \<Rightarrow> 'a header_type_ext \<Rightarrow> 'a header_type_ext" where
    "permute_header_type_ext p \<eta> = \<eta>"
  instance by standard (auto simp add: permute_header_type_ext_def)
end

type_synonym headers = "instanc \<Rightarrow> bv option"
                              
definition empty_headers :: headers where "empty_headers = Map.empty"
declare empty_headers_def[simp]

record heap = 
  heap_pkt_in :: bv
  heap_pkt_out :: bv
  heap_headers :: headers
instantiation heap_ext :: (type) pure begin
  definition permute_heap_ext :: "perm \<Rightarrow> 'a heap_ext \<Rightarrow> 'a heap_ext" where
    "permute_heap_ext p h = h"
  instance by standard (auto simp add: permute_heap_ext_def)
end

definition empty_heap :: "heap" where
  "empty_heap = \<lparr> heap_pkt_in = [], heap_pkt_out = [], headers = empty_headers \<rparr>"
declare empty_heap_def[simp]

record env =
  heaps :: "(var \<times> heap) list"
instantiation env_ext :: (pt) pt begin
  definition permute_env_ext :: "perm \<Rightarrow> 'a env_ext \<Rightarrow> 'a env_ext" where
    "p \<bullet> \<E> = \<E>\<lparr>heaps := p \<bullet> (heaps \<E>), more := p \<bullet> (more \<E>)\<rparr>"
  instance by (standard) (auto simp add: permute_env_ext_def)
end

lemma permute_env_eq: "(p \<bullet> \<E> = \<E>) = (p \<bullet> (heaps \<E>) = heaps \<E> \<and> p \<bullet> (more \<E>) = more \<E>)"
  apply (cases \<E>)
  apply (auto simp add: permute_env_ext_def)
done

lemma env_supp_helper: "{b. (a \<rightleftharpoons> b) \<bullet> \<E> \<noteq> \<E>} =
  ({b. (a \<rightleftharpoons> b) \<bullet> (heaps \<E>) \<noteq> (heaps \<E>)} \<union> {b. (a \<rightleftharpoons> b) \<bullet> (more \<E>) \<noteq> (more \<E>)})"
  by (auto simp add: permute_env_eq)

lemma env_supp: "supp \<E> = supp (heaps \<E>) \<union> supp (more \<E>)"
  by (standard) (auto simp add: supp_def env_supp_helper)

instantiation env_ext :: (fs) fs begin
  instance by (standard) (auto simp add: env_supp finite_supp)
end

definition env_update :: "env \<Rightarrow> var \<Rightarrow> heap \<Rightarrow> env" ("_[_ \<rightarrow> _]" [1000, 49, 49] 1000)
where
  "\<E>[x \<rightarrow> h] = \<E>\<lparr>heaps := AList.update x h (heaps \<E>)\<rparr>"

lemma alist_update_other: "x \<noteq> y \<Longrightarrow> map_of al x = map_of (AList.update y v al) x"
  by (auto simp add: update_conv)

lemma env_update_other[simp]: "x \<noteq> y \<Longrightarrow> map_of (heaps \<E>[y \<rightarrow> h']) x = map_of (heaps \<E>) x"
  by (auto simp add: env_update_def simp flip: alist_update_other)
lemma env_update_same[simp]: "map_of (heaps \<E>[x \<rightarrow> h]) x = Some h"
  by (auto simp add: env_update_def update_conv)


section\<open>Expressions and Formulas\<close>

datatype sliceable = SlPacket var packet | SlInstance var instanc
instantiation sliceable :: pt begin
  fun permute_sliceable :: "perm \<Rightarrow> sliceable \<Rightarrow> sliceable" where
    "p \<bullet> (SlPacket x pkt) = SlPacket (p \<bullet> x) pkt" |
    "p \<bullet> (SlInstance x \<iota>) = SlInstance (p \<bullet> x) \<iota>"
  instance apply (standard)
    subgoal for x by (cases x) (auto)
    subgoal for p q x by (cases x) (auto)
  done
end
instantiation sliceable :: fs begin
  instance proof
    fix x::sliceable
    show "finite (supp x)" proof (cases x)
      case (SlPacket y pkt) then have "supp x = supp y" by (auto simp add: supp_def)
        then show "finite (supp x)" by (auto simp add: finite_supp)
      next
      case (SlInstance y \<iota>) then have "supp x = supp y" by (auto simp add: supp_def)
        then show "finite (supp x)" by (auto simp add: finite_supp)
    qed
  qed
end
lemma SlPacket_eqvt[eqvt]: "p \<bullet> (SlPacket x pkt) = SlPacket (p \<bullet> x) (p \<bullet> pkt)"
  by (auto simp add: permute_pure)
lemma SlInstance_eqvt[eqvt]: "p \<bullet> (SlInstance x \<iota>) = SlInstance (p \<bullet> x) (p \<bullet> \<iota>)"
  by (auto simp add: permute_pure)
lemma supp_SlPacket: "supp (SlPacket x pkt) = supp x"
  by (auto simp add: supp_def)
lemma supp_SlInstance: "supp (SlInstance x \<iota>) = supp x"
  by (auto simp add: supp_def)

datatype val = VNum nat | VBv bv
instantiation val :: pure begin
  definition permute_val :: "perm \<Rightarrow> val \<Rightarrow> val" where
    "permute_val _ v = v"
  instance by standard (auto simp add: permute_val_def)
end

definition bv_to_val :: "bv \<Rightarrow> val option" where
  "bv_to_val bv = (if BitVar \<in> set bv then None else Some (VBv bv))"

datatype exp =
  Num nat | Bv bv |
  Plus exp exp | Concat exp exp |
  Packet var packet | Len var packet |
  Slice sliceable slice_range
instantiation exp :: pt begin
  fun permute_exp :: "perm \<Rightarrow> exp \<Rightarrow> exp" where
    "p \<bullet> (Num n) = Num n" |
    "p \<bullet> (Bv bv) = Bv bv" |
    "p \<bullet> (Plus e\<^sub>1 e\<^sub>2) = Plus (p \<bullet> e\<^sub>1) (p \<bullet> e\<^sub>2)" |
    "p \<bullet> (Concat e\<^sub>1 e\<^sub>2) = Concat (p \<bullet> e\<^sub>1) (p \<bullet> e\<^sub>2)" |
    "p \<bullet> (Packet x pkt) = Packet (p \<bullet> x) pkt" |
    "p \<bullet> (Len x pkt) = Len (p \<bullet> x) pkt" |
    "p \<bullet> (Slice sl rng) = Slice (p \<bullet> sl) rng"
  instance apply (standard)
    subgoal for e by (induction e) (auto)
    subgoal for p q e by (induction e) (auto)
   done
end
declare permute_exp.simps(3)[eqvt]
declare permute_exp.simps(4)[eqvt]

lemma supp_Plus: "supp (Plus e\<^sub>1 e\<^sub>2) = supp e\<^sub>1 \<union> supp e\<^sub>2"
proof -
  have "\<forall>a. {b. (a \<rightleftharpoons> b) \<bullet> (Plus e\<^sub>1 e\<^sub>2) \<noteq> (Plus e\<^sub>1 e\<^sub>2)}
    = {b. (a \<rightleftharpoons> b) \<bullet> e\<^sub>1 \<noteq> e\<^sub>1} \<union> {b. (a \<rightleftharpoons> b) \<bullet> e\<^sub>2 \<noteq> e\<^sub>2}" by (auto)
  then show ?thesis by (auto simp add: supp_def)
qed
lemma supp_Concat: "supp (Concat e\<^sub>1 e\<^sub>2) = supp e\<^sub>1 \<union> supp e\<^sub>2"
proof -
  have "\<forall>a. {b. (a \<rightleftharpoons> b) \<bullet> (Concat e\<^sub>1 e\<^sub>2) \<noteq> (Concat e\<^sub>1 e\<^sub>2)}
    = {b. (a \<rightleftharpoons> b) \<bullet> e\<^sub>1 \<noteq> e\<^sub>1} \<union> {b. (a \<rightleftharpoons> b) \<bullet> e\<^sub>2 \<noteq> e\<^sub>2}" by (auto)
  then show ?thesis by (auto simp add: supp_def)
qed
lemma supp_Packet: "supp (Packet x pkt) = supp x"
proof -
  have "\<forall>a. {b. (a \<rightleftharpoons> b) \<bullet> (Packet x pkt) \<noteq> (Packet x pkt)} = {b. (a \<rightleftharpoons> b) \<bullet> x \<noteq> x}" by (auto)
  then show ?thesis by (auto simp add: supp_def)
qed
lemma supp_Len: "supp (Len x pkt) = supp x"
proof -
  have "\<forall>a. {b. (a \<rightleftharpoons> b) \<bullet> (Len x pkt) \<noteq> (Len x pkt)} = {b. (a \<rightleftharpoons> b) \<bullet> x \<noteq> x}" by (auto)
  then show ?thesis by (auto simp add: supp_def)
qed
lemma supp_Slice: "supp (Slice sl rng) = supp sl"
proof -
  have "\<forall>a. {b. (a \<rightleftharpoons> b) \<bullet> (Slice sl rng) \<noteq> (Slice sl rng)} = {b. (a \<rightleftharpoons> b) \<bullet> sl \<noteq> sl}" by (auto)
  then show ?thesis by (auto simp add: supp_def)
qed

instantiation exp :: fs begin
  instance proof
    fix e::exp
    show "finite (supp e)" proof (induction e)
        case (Num n) have "supp (Num n) = {}" by (auto simp add: supp_def)
        thus "finite (supp (Num n))" by (simp)
      next
        case (Bv bv) have "supp (Bv bv) = {}" by (auto simp add: supp_def)
        thus "finite (supp (Bv bv))" by (simp)
      next
        case (Plus e\<^sub>1 e\<^sub>2)
        thus "finite (supp (Plus e\<^sub>1 e\<^sub>2))" by (auto simp add: supp_Plus)
      next
        case (Concat e\<^sub>1 e\<^sub>2)
        thus "finite (supp (Concat e\<^sub>1 e\<^sub>2))" by (auto simp add: supp_Concat)
      next
        case (Packet x pkt) have "supp (Packet x pkt) = supp x" by (auto simp add: supp_Packet)
        thus "finite (supp (Packet x pkt))" by (auto simp add: finite_supp)
      next
        case (Len x pkt) have "supp (Len x pkt) = supp x" by (auto simp add: supp_Len)
        thus "finite (supp (Len x pkt))" by (auto simp add: finite_supp)
      next
        case (Slice sl rng) have "supp (Slice sl rng) = supp sl" by (auto simp add: supp_Slice)
        thus "finite (supp (Slice sl rng))" by (auto simp add: finite_supp)
    qed
  qed
end
lemma Num_eqvt[eqvt]: "p \<bullet> (Num n) = Num (p \<bullet> n)" by (simp add: permute_pure)
lemma Bv_eqvt[eqvt]: "p \<bullet> (Bv bv) = Bv (p \<bullet> bv)" by (simp add: permute_pure)
lemma Packet_eqvt[eqvt]: "p \<bullet> (Packet x pkt) = Packet (p \<bullet> x) (p \<bullet> pkt)" by (simp add: permute_pure)
lemma Len_eqvt[eqvt]: "p \<bullet> (Len x pkt) = Len (p \<bullet> x) (p \<bullet> pkt)" by (simp add: permute_pure)
lemma Slice_eqvt[eqvt]: "p \<bullet> (Slice sl rng) = Slice (p \<bullet> sl) (p \<bullet> rng)"
  by (cases sl) (auto simp add: permute_pure)


datatype formula =
  FTrue | FFalse |
  Eq exp exp | Gt exp exp | And formula formula | Not formula |
  IsValid var instanc
instantiation formula :: pt begin
  fun permute_formula :: "perm \<Rightarrow> formula \<Rightarrow> formula" where
    "p \<bullet> FTrue = FTrue" |
    "p \<bullet> FFalse = FFalse" |
    "p \<bullet> (Eq e\<^sub>1 e\<^sub>2) = Eq (p \<bullet> e\<^sub>1) (p \<bullet> e\<^sub>2)" |
    "p \<bullet> (Gt e\<^sub>1 e\<^sub>2) = Gt (p \<bullet> e\<^sub>1) (p \<bullet> e\<^sub>2)" |
    "p \<bullet> (And \<phi>\<^sub>1 \<phi>\<^sub>2) = And (p \<bullet> \<phi>\<^sub>1) (p \<bullet> \<phi>\<^sub>2)" |
    "p \<bullet> (Not \<phi>) = Not (p \<bullet> \<phi>)" |
    "p \<bullet> (IsValid x \<iota>) = IsValid (p \<bullet> x) \<iota>"
  instance apply (standard)
    subgoal for \<phi> by (induction \<phi>) (auto)
    subgoal for p q \<phi> by (induction \<phi>) (auto)
  done
end
declare permute_formula.simps(3)[eqvt]
declare permute_formula.simps(4)[eqvt]
declare permute_formula.simps(5)[eqvt]
declare permute_formula.simps(6)[eqvt]
lemma IsValid_eqvt[eqvt]: "p \<bullet> (IsValid x \<iota>) = IsValid (p \<bullet> x) (p \<bullet> \<iota>)" by (auto simp add: permute_pure)

lemma supp_Eq: "supp (Eq e\<^sub>1 e\<^sub>2) = supp e\<^sub>1 \<union> supp e\<^sub>2"
proof -
  have "\<forall>a. {b. (a \<rightleftharpoons> b) \<bullet> (Eq e\<^sub>1 e\<^sub>2) \<noteq> (Eq e\<^sub>1 e\<^sub>2)}
    = {b. (a \<rightleftharpoons> b) \<bullet> e\<^sub>1 \<noteq> e\<^sub>1} \<union> {b. (a \<rightleftharpoons> b) \<bullet> e\<^sub>2 \<noteq> e\<^sub>2}" by (auto)
  then show ?thesis by (auto simp add: supp_def)
qed
lemma supp_Gt: "supp (Gt e\<^sub>1 e\<^sub>2) = supp e\<^sub>1 \<union> supp e\<^sub>2"
proof -
  have "\<forall>a. {b. (a \<rightleftharpoons> b) \<bullet> (Gt e\<^sub>1 e\<^sub>2) \<noteq> (Gt e\<^sub>1 e\<^sub>2)}
    = {b. (a \<rightleftharpoons> b) \<bullet> e\<^sub>1 \<noteq> e\<^sub>1} \<union> {b. (a \<rightleftharpoons> b) \<bullet> e\<^sub>2 \<noteq> e\<^sub>2}" by (auto)
  then show ?thesis by (auto simp add: supp_def)
qed
lemma supp_And: "supp (And \<phi>\<^sub>1 \<phi>\<^sub>2) = supp \<phi>\<^sub>1 \<union> supp \<phi>\<^sub>2"
proof -
  have "\<forall>a. {b. (a \<rightleftharpoons> b) \<bullet> (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<noteq> (And \<phi>\<^sub>1 \<phi>\<^sub>2)}
    = {b. (a \<rightleftharpoons> b) \<bullet> \<phi>\<^sub>1 \<noteq> \<phi>\<^sub>1} \<union> {b. (a \<rightleftharpoons> b) \<bullet> \<phi>\<^sub>2 \<noteq> \<phi>\<^sub>2}" by (auto)
  then show ?thesis by (auto simp add: supp_def)
qed
lemma supp_Not: "supp (Not \<phi>) = supp \<phi>" by (auto simp add: supp_def)
lemma supp_IsValid: "supp (IsValid x \<iota>) = supp x" by (auto simp add: supp_def)

instantiation formula :: fs begin
  instance proof
    fix \<phi>::formula
    show "finite (supp \<phi>)" proof (induction \<phi>)
      case FTrue show ?case by (auto simp add: supp_def) next
      case FFalse show ?case by (auto simp add: supp_def) next
      case (Eq e\<^sub>1 e\<^sub>2) show ?case by (auto simp add: supp_Eq finite_supp) next
      case (Gt e\<^sub>1 e\<^sub>2) show ?case by (auto simp add: supp_Gt finite_supp) next
      case (And \<phi>\<^sub>1 \<phi>\<^sub>2) then show ?case by (auto simp add: supp_And) next
      case (Not \<phi>) then show ?case by (auto simp add: supp_Not) next
      case (IsValid x \<iota>) then show ?case by (auto simp add: supp_IsValid finite_supp)
    qed
  qed
end

inductive "value\<^sub>e" :: "exp \<Rightarrow> bool" where
  "value\<^sub>e (Num _)" |
  "value\<^sub>e (Bv _)"
declare value\<^sub>e.intros[simp]
declare value\<^sub>e.intros[intro]
(*equivariance "value\<^sub>e"*)

inductive "value\<^sub>f" :: "formula \<Rightarrow> bool" where
  "value\<^sub>f FTrue" |
  "value\<^sub>f FFalse"
declare value\<^sub>f.intros[simp]
declare value\<^sub>f.intros[intro]
(*equivariance "value\<^sub>f"*)

section\<open>Types\<close>

nominal_datatype heap_ty =
  Nothing | Top |
  Sigma x::var \<tau>\<^sub>1::heap_ty \<tau>\<^sub>2::heap_ty binds x in \<tau>\<^sub>2 |
  Choice heap_ty heap_ty |
  Refinement x::var heap_ty \<phi>::formula binds x in \<phi> |
  Substitution \<tau>\<^sub>1::heap_ty x::var \<tau>\<^sub>2::heap_ty binds x in \<tau>\<^sub>1

nominal_datatype pi_ty = PiTy x::var \<tau>\<^sub>1::heap_ty \<tau>\<^sub>2::heap_ty binds x in \<tau>\<^sub>2
  ("'(_ : _') \<rightarrow> _" [50,50,50] 50)

nominal_datatype base_ty = Nat | Bool | BV | Pi pi_ty

type_synonym ty_env = "(var \<times> heap_ty) list"

definition ty_env_update :: "ty_env \<Rightarrow> var \<Rightarrow> heap_ty \<Rightarrow> ty_env"
  ("_\<^bold>, _ : _" [1000, 51, 51] 50)
where
  "\<Gamma>\<^bold>, x : \<tau> = AList.update x \<tau> \<Gamma>"

definition ty_env_add_heap :: "ty_env \<Rightarrow> heap_ty \<Rightarrow> ty_env"
  ("_\<^bold>; _" [50,51] 50)
where
  "(\<Gamma>\<^bold>; \<tau>) = AList.update var_heap \<tau> \<Gamma>"

section\<open>Commands\<close>

datatype cmd =
  Skip | Seq cmd cmd | If formula cmd cmd | Assign instanc string exp |
  Extract instanc | Remit instanc | Add instanc |
  Reset | Ascribe cmd pi_ty

end