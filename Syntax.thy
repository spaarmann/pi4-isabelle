theory Syntax imports Nominal2.Nominal2 begin

section\<open>General Definitions\<close>

atom_decl var

text\<open>Instances don't appear in binders, so we can just model these as string names.\<close>
type_synonym instanc = string

text\<open>Bit vectors are essentially boolean lists.
  The paper and implementation have an additional concept of bit\<close>
type_synonym bv = "bool list"

nominal_datatype packet = PktIn | PktOut

datatype field = Field string int
datatype header_type = HeaderType var "field list"
type_synonym header_table = "instanc \<Rightarrow> header_type" (* Should we have header_type option here? *)

type_synonym header_instance = "string \<Rightarrow> bv"
type_synonym headers = "instanc \<Rightarrow> header_instance"


section\<open>Expressions and Formulas\<close>

nominal_datatype sliceable = SlPacket var packet | SlInstance var instanc

(* TODO: The implementation indicates that slicing bounds can only be constants, not expressions.
         Do we want to keep it like that? *)
nominal_datatype exp =
  Num nat | Bv bv | Len var packet |
  Plus exp exp | Concat exp exp | Slice sliceable int int |
  Packet var packet

nominal_datatype formula =
  Eq exp exp | Gt exp exp | And formula formula | Not formula |
  FTrue | FFalse | IsValid var instanc

inductive "value" :: "exp \<Rightarrow> bool" where
  "value (Num _)" |
  "value (Bv _)"

declare value.intros[simp]
declare value.intros[intro]

equivariance "value"


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
  Extract instanc | Remit instanc | Add instanc |
  If formula cmd cmd | Seq cmd cmd | Assign instanc string exp |
  Skip | Reset | Ascribe cmd pi_ty

end