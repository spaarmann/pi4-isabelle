theory Syntax imports Nominal2.Nominal2 begin

section\<open>General Definitions\<close>

atom_decl var

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

datatype field = Field field_name int
datatype header_type = HeaderType string "field list"
type_synonym header_table = "instanc \<Rightarrow> header_type" (* Should we have header_type option here? *)

datatype headers = Headers "instanc \<Rightarrow> bv option"
datatype heap = Heap bv bv headers

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
  Slice sliceable int int

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
  Substitution heap_ty var heap_ty

nominal_datatype pi_ty = PiTy x::var \<tau>\<^sub>1::heap_ty \<tau>\<^sub>2::heap_ty binds x in \<tau>\<^sub>2

nominal_datatype base_ty = Nat | Bool | BV | Pi pi_ty


section\<open>Commands\<close>

datatype cmd =
  Skip | Seq cmd cmd | If formula cmd cmd | Assign instanc field_name exp |
  Extract instanc | Remit instanc | Add instanc |
  Reset | Ascribe cmd pi_ty

end