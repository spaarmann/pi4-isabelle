theory Semantics imports Syntax "HOL-Library.AList" begin

text\<open>For next meeting:
Questions/Help:
- Nominal2 proof for lookup_instance. Can't get the first goal to be solved.
  Figured it was more productive to keep going for now.
- Heaps, see text block below.
To talk about:
- Think I figured out what's going on with expression and formula semantics, see below.
- See TODOs on the exp small-step semantics.
- See TODO on exp.\<close>

datatype headers = Instances "instanc \<Rightarrow> bv option"
datatype heap = Heap bv bv headers

text\<open>This is necessary to use heaps in nominal_functions. It basically states that
no variables actually appear in the type.\<close>
instantiation headers :: pure begin
  definition permute_headers :: "perm \<Rightarrow> headers \<Rightarrow> headers" where
    "permute_headers _ x = x"
  instance by standard (auto simp add: permute_headers_def)
end
instantiation heap :: pure begin
  definition permute_heap :: "perm \<Rightarrow> heap \<Rightarrow> heap"  where
    "permute_heap _ x = x"
  instance by standard (auto simp add: permute_heap_def)
end

fun triple_to_heap :: "bv \<Rightarrow> bv \<Rightarrow> headers \<Rightarrow> heap" where
  "triple_to_heap In Out H = Heap In Out H"

(* doesn't work because of nominal_datatype vs datatype right now I think.
   But Dmitriy had some way of making these constructors? *)
fun heap_lookup_packet :: "heap \<Rightarrow> packet \<Rightarrow> bv" where
  "heap_lookup_packet (Heap In Out _) PktIn = In" |
  "heap_lookup_packet (Heap In Out _) PktOut = Out" 

fun heap_lookup_instance :: "heap \<Rightarrow> instanc \<Rightarrow> bv option" where
  "heap_lookup_instance (Heap _ (Instances insts)) i = insts i"

(* Easier to work with than "var \<Rightarrow> heap" with Nominal2 because it has a finite support (I think) *)
type_synonym env = "(var \<times> heap) list"

(* These are declared in the LambdaAuth session, so I thought it might help *)
declare
  fresh_star_Pair[simp] fresh_star_insert[simp] fresh_Nil[simp]
  pure_supp[simp] pure_fresh[simp]

fun lookup_packet :: "env \<Rightarrow> var \<Rightarrow> packet \<Rightarrow> bv option" where
  "lookup_packet \<epsilon> x p = map_option (\<lambda>h. heap_lookup_packet h p) (map_of \<epsilon> x)"
fun lookup_instance :: "env \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> bv option" where
  "lookup_instance \<epsilon> x i = Option.bind (map_of \<epsilon> x) (\<lambda>h. heap_lookup_instance h i)"
nominal_function lookup_sliceable :: "sliceable \<Rightarrow> env \<Rightarrow> bv option" where
  "lookup_sliceable (SlPacket x p) \<epsilon> = lookup_packet \<epsilon> x p" |
  "lookup_sliceable (SlInstance x i) \<epsilon> = lookup_instance \<epsilon> x i"
sorry
(*  using [[simproc del: alpha_lst defined_all]]
  subgoal by (simp add: eqvt_def lookup_sliceable_graph_aux_def)
  subgoal by (erule lookup_sliceable_graph.induct) (auto simp: fresh_star_def fresh_at_base)
                      apply clarify
  subgoal for P t s y
    by (rule term.strong_exhaust[of t P "(s, y)"]) (auto simp: fresh_star_def fresh_Pair)
                      apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal for x' y' s' t' x t
    apply (erule Abs_lst1_fcb2'[where c = "(s', y')"])
       apply (simp_all add: eqvt_at_def fresh_star_def)
       apply (simp_all add: perm_supp_eq Abs_fresh_iff fresh_Pair)
    apply (metis fresh_star_def fresh_star_supp_conv supp_perm_eq_test)
    apply (metis fresh_star_def fresh_star_supp_conv supp_perm_eq_test)
    done
  done*)
nominal_termination (eqvt)
  by lexicographic_order

term lookup_sliceable_graph_aux

fun slice :: "'a list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a list" where
  "slice xs n m = take (nat (m - n)) (drop (nat n) xs)"


text\<open>About the semantics for expressions and formulas...
The paper references, but never defines, small-step semantics for formulas and expressions, which
are used to define the command small-step semantics and prove the corresponding type safety theorems.
These are shown to be of the form "(I, O, H, e) -> e'", basically the same form as for commands. H
here is "a map that relates instance names to records containing the field values". Expressions
referring to a variable always refer to an implicit variable "heap" when used in commands, which
corresponds with the H parameter for the small-step semantics.

What the paper does present are denotational-style semantics for a subset of expressions. It also
defines them for formulas (in the text below Fig. 5). These are both defined in terms of an
environment \<epsilon> that maps variable names to heaps, that is also used to define the semantics of
heap *types*.

So, right now my assumption is that we'll need both: small-step semantics to define small-step
command semantics and ideally denotational semantics / a function to define the semantics of heap
types (especially refinement types). Unless we can use of them for both? (e.g. use the small-step
ones for types too?) Probably not because of the different environments I think.
\<close>

text\<open>Relatedly, let's talk about heaps.
Section 3.3 says "We model heaps as maps from names to bit vectors".

Section 3.4 says "H is a map that relates instance names to records containing the field values"
(where H is one of the arguments for the small-step judgement). Later (in appendix B) (I, O, H) is
defined to mean H[PktIn -> I, PktOut -> O] which is a heap, as defined above. This seems to apply
that H really maps instance names to bit vectors too?
I suppose technically there is a 1-to-1 correspondence between a full instance bit vector and a
"record containing the field values" for an instance. But do we really have to model it like this,
converting back and forth when needed?

What forms do we actually have?
 - In types: Heaps with PktIn PktOut instance, all mapping to bvs
 - In semantics: H with instance, mapping to names to bvs
 - In semantics: (I, O, H), being PktIn PktOut and an H as above

So let's model the last two as mapping to bvs as well, with names just desugaring into slices? We
have the HT that gives us types for each instanc, so can just look up the range corresponding to a
name.
\<close>

(* TODO: At the moment, we just ignore variables here and assume they must be "heap". Should we
   explicitly encode that in the rule assumptions? *)
(* TODO: Which of these is preferable?
    E_PktIn:      "(In, Out, H, Packet x PktIn) \<rightarrow> Bv In" |
    E_PktIn:      "\<lbrakk> p = PktIn \<rbrakk> \<Longrightarrow> (In, Out, H, Packet x p) \<rightarrow> Bv In" |
  and similarly, keep len call in the rule or make it a premise in E_Pkt*Len?
*)
inductive
  exp_small_step :: "(bv \<times> bv \<times> headers \<times> exp) \<Rightarrow> exp \<Rightarrow> bool" ("_ \<rightarrow>/ _" [0,50] 50)
where
  E_Plus1:      "\<lbrakk> (In, Out, H, e\<^sub>1) \<rightarrow> e\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Plus e\<^sub>1 e\<^sub>2) \<rightarrow> Plus e\<^sub>1' e\<^sub>2" |
  E_Plus2:      "\<lbrakk> value v\<^sub>1; (In, Out, H, e\<^sub>2) \<rightarrow> e\<^sub>2' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Plus v\<^sub>1 e\<^sub>2) \<rightarrow> Plus v\<^sub>1 e\<^sub>2'" |
  E_Plus:       "\<lbrakk> v\<^sub>1 = Num n\<^sub>1; v\<^sub>2 = Num n\<^sub>2 \<rbrakk>
                \<Longrightarrow> (In, Out, H, Plus v\<^sub>1 v\<^sub>2) \<rightarrow> Num (n\<^sub>1 + n\<^sub>2)" |
  E_Concat1:    "\<lbrakk> (In, Out, H, e\<^sub>1) \<rightarrow> e\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Concat e\<^sub>1 e\<^sub>2) \<rightarrow> Concat e\<^sub>1 e\<^sub>2" |
  E_Concat2:    "\<lbrakk> value v\<^sub>1; (In, Out, H, e\<^sub>2) \<rightarrow> e\<^sub>2' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Concat v\<^sub>1 e\<^sub>2) \<rightarrow> Concat v\<^sub>1 e\<^sub>2'" |
  E_Concat:     "\<lbrakk> v\<^sub>1 = Bv b\<^sub>1; v\<^sub>2 = Bv b\<^sub>2 \<rbrakk>
                \<Longrightarrow> (In, Out, H, Concat v\<^sub>1 v\<^sub>2) \<rightarrow> Bv (b\<^sub>1 @ b\<^sub>2)" |
  E_PktIn:      "(In, Out, H, Packet x PktIn) \<rightarrow> Bv In" |
  E_PktOut:     "(In, Out, H, Packet x PktOut) \<rightarrow> Bv Out" |
  E_PktInLen:   "(In, Out, H, Len x PktIn) \<rightarrow> Num (len In)" |
  E_PktOutLen:  "(In, Out, H, Len x PktOut) \<rightarrow> Num (len Out)" |
  (*E_Slice1:     "\<lbrakk> (In, Out, H, e\<^sub>1) \<rightarrow> e\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice sl e\<^sub>1 e\<^sub>2) \<rightarrow> Slice sl e\<^sub>1' e\<^sub>2" |
  E_Slice2:     "\<lbrakk> value v\<^sub>1; (In, Out, H, e\<^sub>2) \<rightarrow> e\<^sub>2' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice sl v\<^sub>1 e\<^sub>2) \<rightarrow> Slice sl v\<^sub>1 e\<^sub>2'" | *)
  E_SlicePktIn: "\<lbrakk> 0 \<le> n \<and> n < m \<and> m \<le> (len In + 1); slice In n m = bs \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlPacket x PktIn) n m) \<rightarrow> Bv bs" |
  E_SlicePktOut:"\<lbrakk> 0 \<le> n \<and> n < m \<and> m \<le> (len Out + 1); slice Out n m = bs \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlPacket x PktOut) n m) \<rightarrow> Bv bs" |
  E_SliceInst:  "\<lbrakk> H \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlInstance x i) n m) \<rightarrow> Num 0"

inductive exp_sem :: "exp \<Rightarrow> env \<Rightarrow> val \<Rightarrow> bool" where
  "exp_sem (Syntax.Num n) _ (Num n)" |
  "exp_sem (Bv bs) _ (BV bs)" |
  "\<lbrakk> lookup_packet \<epsilon> x p = Some bs; len bs = n \<rbrakk> \<Longrightarrow> exp_sem (Len x p) \<epsilon> (Num n)" |
  "\<lbrakk> exp_sem e\<^sub>1 \<epsilon> (Num n\<^sub>1); exp_sem e\<^sub>2 \<epsilon> (Num n\<^sub>2) \<rbrakk> \<Longrightarrow> exp_sem (Plus e\<^sub>1 e\<^sub>2) \<epsilon> (Num (n\<^sub>1 + n\<^sub>2))" |
  "\<lbrakk> exp_sem e\<^sub>1 \<epsilon> (BV b\<^sub>1); exp_sem e\<^sub>2 \<epsilon> (BV b\<^sub>2) \<rbrakk> \<Longrightarrow> exp_sem (Concat e\<^sub>1 e\<^sub>2) \<epsilon> (BV (b\<^sub>1 @ b\<^sub>2))" |
  "\<lbrakk> lookup_packet \<epsilon> x p = Some bs \<rbrakk> \<Longrightarrow> exp_sem (Packet x p) \<epsilon> (BV bs)" |
  "\<lbrakk> lookup_packet \<epsilon> x p = Some bs;  0 \<le> n \<and> n < m \<and> m \<le> (len bs + 1); slice bs n m = bs' \<rbrakk>
    \<Longrightarrow> exp_sem (Slice (SlPacket x p) n m) \<epsilon> (BV bs')"

(* Should I make these small-step instead? Both form_sem and exp_sem *)

inductive form_sem :: "formula \<Rightarrow> env \<Rightarrow> bool \<Rightarrow> bool" where
  "\<lbrakk> exp_sem e\<^sub>1 \<epsilon> v; exp_sem e\<^sub>2 \<epsilon> v \<rbrakk> \<Longrightarrow> form_sem (Eq e\<^sub>1 e\<^sub>2) \<epsilon> true" |
  "\<lbrakk> exp_sem e\<^sub>1 \<epsilon> v\<^sub>1; exp_sem e\<^sub>2 \<epsilon> v\<^sub>2; v\<^sub>1 \<noteq> v\<^sub>2 \<rbrakk> \<Longrightarrow> form_sem (Eq e\<^sub>1 e\<^sub>2) \<epsilon> false" |
  "\<lbrakk> exp_sem e\<^sub>1 \<epsilon> (Num n\<^sub>1); exp_sem e\<^sub>2 \<epsilon> (Num n\<^sub>2); n\<^sub>1 > n\<^sub>2 \<rbrakk> \<Longrightarrow> form_sem (Gt e\<^sub>1 e\<^sub>2) \<epsilon> true" |
  "\<lbrakk> exp_sem e\<^sub>1 \<epsilon> (Num n\<^sub>1); exp_sem e\<^sub>2 \<epsilon> (Num n\<^sub>2); n\<^sub>1 \<le> n\<^sub>2 \<rbrakk> \<Longrightarrow> form_sem (Gt e\<^sub>1 e\<^sub>2) \<epsilon> false"
  (*"\<lbrakk> exp_sem e\<^sub>1 \<epsilon> (Num n\<^sub>1); exp_sem e\<^sub>2 \<epsilon> (Num n\<^sub>2); n\<^sub>1 \<le> n\<^sub>2 \<rbrakk> \<Longrightarrow> form_sem (And e\<^sub>1 e\<^sub>2) \<epsilon> false"*)

(*datatype cmd =
  Extract instanc | Remit instanc | Add instanc |
  If formula cmd cmd | Seq cmd cmd | Assign instanc string exp |
  Skip | Reset | Ascribe cmd pi_ty
*)

(* I added HT as the extra ambient/global context explicitly here. *)
inductive
  small_step :: "header_table \<Rightarrow> (bv \<times> bv \<times> headers \<times> cmd) \<Rightarrow> (bv \<times> bv \<times> headers \<times> cmd) \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ \<rightarrow>/ _))" [50,0,50] 50)
where
  E_Seq1: "\<lbrakk> HT \<turnstile> (I, Out, H, c\<^sub>1) \<rightarrow> (I', Out', H', c\<^sub>1') \<rbrakk>
    \<Longrightarrow> HT \<turnstile> (I, Out, H, Seq c\<^sub>1 c\<^sub>2) \<rightarrow> (I', Out', H', Seq c\<^sub>1' c\<^sub>2)" |
  E_Seq: "HT \<turnstile> (I, Out, H, Seq Skip c) \<rightarrow> (I, Out, H, c)" |
  
  E_Ascribe: "HT \<turnstile> (I, Out, H, Ascribe c ty) \<rightarrow> (I, Out, H, c)"

end