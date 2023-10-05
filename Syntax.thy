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
datatype bit = Zero | One | BitVar nat
type_synonym bv = "bit list"
instantiation bit :: pure begin
  definition permute_bit :: "perm \<Rightarrow> bit \<Rightarrow> bit" where
    "permute_bit _ b = b"
  instance by standard (auto simp add: permute_bit_def)
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
                                   
record heap = 
  heap_pkt_in :: bv
  heap_pkt_out :: bv
  heap_headers :: headers
instantiation heap_ext :: (type) pure begin
  definition permute_heap_ext :: "perm \<Rightarrow> 'a heap_ext \<Rightarrow> 'a heap_ext" where
    "permute_heap_ext p h = h"
  instance by standard (auto simp add: permute_heap_ext_def)
end

(* Easier to work with than "var \<Rightarrow> heap" with Nominal2 because it has a finite support (I think) *)
type_synonym env = "(var \<times> heap) list"

definition env_update :: "env \<Rightarrow> var \<Rightarrow> heap \<Rightarrow> env" ("_[_ \<rightarrow> _]" [1000, 49, 49] 1000)
where
  "\<E>[x \<rightarrow> h] = AList.update x h \<E>"

section\<open>Expressions and Formulas\<close>

nominal_datatype sliceable = SlPacket var packet | SlInstance var instanc

datatype val = VNum nat | VBv bv
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