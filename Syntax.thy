theory Syntax imports Nominal2.Nominal2 begin

text\<open>Questions:
  - To make binding x in a formula for refinement types work, I made all the datatypes into
    nominal_datatypes even when they're theoretically simple on their own. Is that correct / the
    only way?
  - Defining functions on nominal_datatypes?
  - Op sem for expressions and especially formulas
  - Typing for expressions and formulas\<close>

text\<open>From last meeting:
  - I think there really are no other binders than the three for types, if we model instances
    without them.
  - It doesn't seem that dependent function types can occur in \<tau> based on the implementation.\<close>

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

nominal_datatype sliceable = SlPacket var packet | SlInstance var instanc

nominal_datatype exp =
  Num nat | Bv bv | Len var packet |
  Plus exp exp | Concat exp exp | Slice sliceable int int |
  Packet var packet

nominal_datatype formula =
  FEq exp exp | FGt exp exp | FAnd formula formula | FNot formula |
  FTrue | FFalse | FIsValid var instanc

nominal_datatype heap_ty =
  Nothing | Top |
  Sigma x::var \<tau>\<^sub>1::heap_ty \<tau>\<^sub>2::heap_ty binds x in \<tau>\<^sub>2 |
  Choice heap_ty heap_ty |
  Refinement x::var heap_ty \<phi>::formula binds x in \<phi> |
  Substitution heap_ty var heap_ty

nominal_datatype pi_ty = PiTy x::var \<tau>\<^sub>1::heap_ty \<tau>\<^sub>2::heap_ty binds x in \<tau>\<^sub>2

nominal_datatype base_ty = Nat | Bool | BV | Pi pi_ty

datatype cmd =
  Extract instanc | Remit instanc | Add instanc |
  If formula cmd cmd | Seq cmd cmd | Assign instanc string exp |
  Skip | Reset | Ascribe cmd pi_ty

end