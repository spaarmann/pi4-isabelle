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

text\<open>Bit vectors are essentially boolean lists.
  The paper and implementation have an additional concept of bit variables, but I haven't seen a
  a place where they're actually needed yet.\<close>
type_synonym bv = "bool list"

datatype packet = PktIn | PktOut

instantiation packet :: pure begin
  definition permute_packet :: "perm \<Rightarrow> packet \<Rightarrow> packet" where
    "permute_packet _ pkt = pkt"
  instance by standard (auto simp add: permute_packet_def)
end

datatype field = Field field_name nat
datatype header_type = HeaderType string "field list"
type_synonym header_table = "(instanc \<times> header_type) list"

instantiation field :: pure begin
  definition permute_field :: "perm \<Rightarrow> field \<Rightarrow> field" where
    "permute_field _ f = f"
  instance by standard (auto simp add: permute_field_def)
end
instantiation header_type :: pure begin
  definition permute_header_type :: "perm \<Rightarrow> header_type \<Rightarrow> header_type" where
    "permute_header_type _ ht = ht"
  instance by standard (auto simp add: permute_header_type_def)
end

datatype headers = Headers "instanc \<Rightarrow> bv option"
datatype heap = Heap bv bv headers

(* Easier to work with than "var \<Rightarrow> heap" with Nominal2 because it has a finite support (I think) *)
type_synonym env = "(var \<times> heap) list"

definition env_update :: "env \<Rightarrow> var \<Rightarrow> heap \<Rightarrow> env" ("_[_ \<rightarrow> _]" [1000, 49, 49] 1000)
where
  "\<epsilon>[x \<rightarrow> h] = AList.update x h \<epsilon>"

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
  ("_, _ : _" [1000, 51, 51] 50)
where
  "\<Gamma>, x : \<tau> = AList.update x \<tau> \<Gamma>"

definition ty_env_add_heap :: "ty_env \<Rightarrow> heap_ty \<Rightarrow> ty_env"
  ("_; _" [50,51] 0)
where
  "(\<Gamma>; \<tau>) = AList.update var_heap \<tau> \<Gamma>"

section\<open>Commands\<close>

datatype cmd =
  Skip | Seq cmd cmd | If formula cmd cmd | Assign instanc field_name exp |
  Extract instanc | Remit instanc | Add instanc |
  Reset | Ascribe cmd pi_ty

end