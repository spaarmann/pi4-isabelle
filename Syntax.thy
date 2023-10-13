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
                                   
record heap = 
  heap_pkt_in :: bv
  heap_pkt_out :: bv
  heap_headers :: headers
instantiation heap_ext :: (type) pure begin
  definition permute_heap_ext :: "perm \<Rightarrow> 'a heap_ext \<Rightarrow> 'a heap_ext" where
    "permute_heap_ext p h = h"
  instance by standard (auto simp add: permute_heap_ext_def)
end

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


section\<open>Expressions and Formulas\<close>

nominal_datatype sliceable = SlPacket var packet | SlInstance var instanc

datatype val = VNum nat | VBv "bool list"
instantiation val :: pure begin
  definition permute_val :: "perm \<Rightarrow> val \<Rightarrow> val" where
    "permute_val _ v = v"
  instance by standard (auto simp add: permute_val_def)
end

nominal_datatype exp =
  Num nat | Bv bv |
  Plus exp exp | Concat exp exp |
  Packet var packet | Len var packet |
  Slice sliceable nat nat

nominal_datatype formula =
  FTrue | FFalse |
  Eq exp exp | Gt exp exp | And formula formula | Not formula |
  IsValid var instanc

inductive "value\<^sub>e" :: "exp \<Rightarrow> bool" where
  "value\<^sub>e (Num _)" |
  "value\<^sub>e (Bv _)"
declare value\<^sub>e.intros[simp]
declare value\<^sub>e.intros[intro]
equivariance "value\<^sub>e"

inductive "value\<^sub>f" :: "formula \<Rightarrow> bool" where
  "value\<^sub>f FTrue" |
  "value\<^sub>f FFalse"
declare value\<^sub>f.intros[simp]
declare value\<^sub>f.intros[intro]
equivariance "value\<^sub>f"

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