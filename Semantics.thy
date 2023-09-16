theory Semantics imports Syntax "HOL-Library.AList" begin

text\<open>For next meeting:
Questions/Help:
- Nominal2 proof for lookup_instance. Can't get the first goal to be solved.
  Figured it was more productive to keep going for now.
- See free_constructors packet below.
- Heaps, see text block below.
To talk about:
- Think I figured out what's going on with expression and formula semantics, see below.
- See TODOs on the exp small-step semantics.
- See TODO on exp.\<close>

datatype headers = Headers "instanc \<Rightarrow> bv option"
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

free_constructors packet for PktIn | PktOut
using packet.strong_exhaust apply auto done
(* TODO: Are these warnings bad? Can I do something about them? *)
(* TODO: Is it preferable to do this, or make every function matching on packets
         a nominal_function? *)
(* TODO: This works when done here but not when done in Syntax? *)

fun triple_to_heap :: "bv \<Rightarrow> bv \<Rightarrow> headers \<Rightarrow> heap" where
  "triple_to_heap In Out H = Heap In Out H"

fun header_lookup :: "headers \<Rightarrow> instanc \<Rightarrow> bv option" where
  "header_lookup (Headers h) i = h i" 

fun heap_lookup_packet :: "heap \<Rightarrow> packet \<Rightarrow> bv" where
  "heap_lookup_packet (Heap In Out _) PktIn = In" |
  "heap_lookup_packet (Heap In Out _) PktOut = Out"

fun heap_lookup_instance :: "heap \<Rightarrow> instanc \<Rightarrow> bv option" where
  "heap_lookup_instance (Heap _ _ (Headers insts)) i = insts i"

(* Easier to work with than "var \<Rightarrow> heap" with Nominal2 because it has a finite support (I think) *)
type_synonym env = "(var \<times> heap) list"

(* These are declared in the LambdaAuth session, so I thought it might help *)
declare
  fresh_star_Pair[simp] fresh_star_insert[simp] fresh_Nil[simp]
  pure_supp[simp] pure_fresh[simp]

fun env_lookup_packet :: "env \<Rightarrow> var \<Rightarrow> packet \<Rightarrow> bv option" where
  "env_lookup_packet \<epsilon> x p = map_option (\<lambda>h. heap_lookup_packet h p) (map_of \<epsilon> x)"
fun env_lookup_instance :: "env \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> bv option" where
  "env_lookup_instance \<epsilon> x i = Option.bind (map_of \<epsilon> x) (\<lambda>h. heap_lookup_instance h i)"
nominal_function env_lookup_sliceable :: "env \<Rightarrow> sliceable \<Rightarrow> bv option" where
  "env_lookup_sliceable \<epsilon> (SlPacket x p) = env_lookup_packet \<epsilon> x p" |
  "env_lookup_sliceable \<epsilon> (SlInstance x i) = env_lookup_instance \<epsilon> x i"
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

fun slice :: "'a list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a list" where
  "slice xs n m = take (nat (m - n)) (drop (nat n) xs)"

section\<open>Expressions and Formulas\<close>

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

subsection\<open>Small-step semantics\<close>

(* TODO: At the moment, we just ignore variables here and assume they must be "heap". Should we
   explicitly encode that somehow, perhaps in the rule assumptions? *)
(* TODO: Which of these is preferable?
    E_PktIn:      "(In, Out, H, Packet x PktIn) \<rightarrow> Bv In" |
    E_PktIn:      "\<lbrakk> p = PktIn \<rbrakk> \<Longrightarrow> (In, Out, H, Packet x p) \<rightarrow> Bv In" |
  and similarly, keep len call in the rule or make it a premise in E_Pkt*Len?
*)
inductive
  exp_small_step :: "(bv \<times> bv \<times> headers \<times> exp) \<Rightarrow> exp \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>e _" [0,50] 50)
where
  E_Plus1:      "\<lbrakk> (In, Out, H, e\<^sub>1) \<rightarrow>\<^sub>e e\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Plus e\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>e Plus e\<^sub>1' e\<^sub>2" |
  E_Plus2:      "\<lbrakk> value\<^sub>e v\<^sub>1; (In, Out, H, e\<^sub>2) \<rightarrow>\<^sub>e e\<^sub>2' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Plus v\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>e Plus v\<^sub>1 e\<^sub>2'" |
  E_Plus:       "\<lbrakk> v\<^sub>1 = Num n\<^sub>1; v\<^sub>2 = Num n\<^sub>2 \<rbrakk>
                \<Longrightarrow> (In, Out, H, Plus v\<^sub>1 v\<^sub>2) \<rightarrow>\<^sub>e Num (n\<^sub>1 + n\<^sub>2)" |
  E_Concat1:    "\<lbrakk> (In, Out, H, e\<^sub>1) \<rightarrow>\<^sub>e e\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Concat e\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>e Concat e\<^sub>1 e\<^sub>2" |
  E_Concat2:    "\<lbrakk> value\<^sub>e v\<^sub>1; (In, Out, H, e\<^sub>2) \<rightarrow>\<^sub>e e\<^sub>2' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Concat v\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>e Concat v\<^sub>1 e\<^sub>2'" |
  E_Concat:     "\<lbrakk> v\<^sub>1 = Bv b\<^sub>1; v\<^sub>2 = Bv b\<^sub>2 \<rbrakk>
                \<Longrightarrow> (In, Out, H, Concat v\<^sub>1 v\<^sub>2) \<rightarrow>\<^sub>e Bv (b\<^sub>1 @ b\<^sub>2)" |
  E_PktIn:      "(In, Out, H, Packet x PktIn) \<rightarrow>\<^sub>e Bv In" |
  E_PktOut:     "(In, Out, H, Packet x PktOut) \<rightarrow>\<^sub>e Bv Out" |
  E_PktInLen:   "(In, Out, H, Len x PktIn) \<rightarrow>\<^sub>e Num (len In)" |
  E_PktOutLen:  "(In, Out, H, Len x PktOut) \<rightarrow>\<^sub>e Num (len Out)" |
  (*E_Slice1:     "\<lbrakk> (In, Out, H, e\<^sub>1) \<rightarrow>\<^sub>e e\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice sl e\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>e Slice sl e\<^sub>1' e\<^sub>2" |
  E_Slice2:     "\<lbrakk> value\<^sub>e v\<^sub>1; (In, Out, H, e\<^sub>2) \<rightarrow>\<^sub>e e\<^sub>2' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice sl v\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>e Slice sl v\<^sub>1 e\<^sub>2'" | *)
  E_SlicePktIn: "\<lbrakk> 0 \<le> n \<and> n < m \<and> m \<le> (len In + 1); slice In n m = bs \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlPacket x PktIn) n m) \<rightarrow>\<^sub>e Bv bs" |
  E_SlicePktOut:"\<lbrakk> 0 \<le> n \<and> n < m \<and> m \<le> (len Out + 1); slice Out n m = bs \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlPacket x PktOut) n m) \<rightarrow>\<^sub>e Bv bs" |
  E_SliceInst:  "\<lbrakk> header_lookup H i = Some bv; 0 \<le> n \<and> n < m \<and> m \<le> (len bv + 1); slice bv n m = bs \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlInstance x i) n m) \<rightarrow>\<^sub>e Bv bs"

inductive formula_small_step :: "(bv \<times> bv \<times> headers \<times> formula) \<Rightarrow> formula \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>f _" [0,50] 50)
where
  F_Eq1:        "\<lbrakk> (In, Out, H, e\<^sub>1) \<rightarrow>\<^sub>e e\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Eq e\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>f Eq e\<^sub>1' e\<^sub>2" |
  F_Eq2:        "\<lbrakk> value\<^sub>e v\<^sub>1; (In, Out, H, e\<^sub>2) \<rightarrow>\<^sub>e e\<^sub>2' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Eq v\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>f Eq v\<^sub>1 e\<^sub>2'" |
  F_EqTrue:     "\<lbrakk> value\<^sub>e v\<^sub>1; value\<^sub>e v\<^sub>2; v\<^sub>1 = v\<^sub>2 \<rbrakk>
                \<Longrightarrow> (In, Out, H, Eq v\<^sub>1 v\<^sub>2) \<rightarrow>\<^sub>f FTrue" |
  F_EqFalse:    "\<lbrakk> value\<^sub>e v\<^sub>1; value\<^sub>e v\<^sub>2; v\<^sub>1 \<noteq> v\<^sub>2 \<rbrakk>
                \<Longrightarrow> (In, Out, H, Eq v\<^sub>1 v\<^sub>2) \<rightarrow>\<^sub>f FFalse" |
  F_Gt1:        "\<lbrakk> (In, Out, H, e\<^sub>1) \<rightarrow>\<^sub>e e\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Gt e\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>f Gt e\<^sub>1' e\<^sub>2" |
  F_Gt2:        "\<lbrakk> value\<^sub>e v\<^sub>1; (In, Out, H, e\<^sub>2) \<rightarrow>\<^sub>e e\<^sub>2' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Gt v\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>f Gt v\<^sub>1 e\<^sub>2'" |
  F_GtTrue:     "\<lbrakk> v\<^sub>1 = Num n\<^sub>1; v\<^sub>2 = Num n\<^sub>2; n\<^sub>1 > n\<^sub>2 \<rbrakk>
                \<Longrightarrow> (In, Out, H, Gt v\<^sub>1 v\<^sub>2) \<rightarrow>\<^sub>f FTrue" |
  F_GtFalse:    "\<lbrakk> v\<^sub>1 = Num n\<^sub>1; v\<^sub>2 = Num n\<^sub>2; n\<^sub>1 \<le> n\<^sub>2 \<rbrakk>
                \<Longrightarrow> (In, Out, H, Gt v\<^sub>1 v\<^sub>2) \<rightarrow>\<^sub>f FFalse" |
  F_And1:       "\<lbrakk> (In, Out, H, f\<^sub>1) \<rightarrow>\<^sub>f f\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, And f\<^sub>1 f\<^sub>2) \<rightarrow>\<^sub>f And f\<^sub>1' f\<^sub>2" |
  F_AndTrue:    "\<lbrakk> t\<^sub>1 = FTrue \<rbrakk>
                \<Longrightarrow> (In, Out, H, And t\<^sub>1 f\<^sub>2) \<rightarrow>\<^sub>f f\<^sub>2" |
  F_AndFalse:   "\<lbrakk> t\<^sub>1 = FFalse \<rbrakk>
                \<Longrightarrow> (In, Out, H, And t\<^sub>1 f\<^sub>2) \<rightarrow>\<^sub>f FFalse" |
  F_Not1:       "\<lbrakk> (In, Out, H, f\<^sub>1) \<rightarrow>\<^sub>f f\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Not f\<^sub>1) \<rightarrow>\<^sub>f f\<^sub>1'" |
  F_NotTrue:    "\<lbrakk> t\<^sub>1 = FTrue \<rbrakk>
                \<Longrightarrow> (In, Out, H, Not t\<^sub>1) \<rightarrow>\<^sub>f FFalse" |
  F_NotFalse:   "\<lbrakk> t\<^sub>1 = FFalse \<rbrakk>
                \<Longrightarrow> (In, Out, H, Not t\<^sub>1) \<rightarrow>\<^sub>f FTrue" |
  F_IsValidTrue:"\<lbrakk> header_lookup H i = Some _ \<rbrakk>
                \<Longrightarrow> (In, Out, H, IsValid x i) \<rightarrow>\<^sub>f FTrue" |
  F_IsValidFalse:"\<lbrakk> header_lookup H i = None \<rbrakk>
                \<Longrightarrow> (In, Out, H, IsValid x i) \<rightarrow>\<^sub>f FFalse"

subsection\<open>Denotational semantics\<close>

nominal_function exp_sem :: "exp \<Rightarrow> env \<Rightarrow> val option" ("\<lbrakk>_ in _\<rbrakk>\<^sub>e" [50,60] 50)
where
  "\<lbrakk>Num n in \<epsilon>\<rbrakk>\<^sub>e = Some (VNum n)" |
  "\<lbrakk>Bv bv in \<epsilon>\<rbrakk>\<^sub>e = Some (VBv bv)" |
  "\<lbrakk>Plus e\<^sub>1 e\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>e = (case (\<lbrakk>e\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>e, \<lbrakk>e\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>e) of
    (Some (VNum n\<^sub>1), Some (VNum n\<^sub>2)) \<Rightarrow> Some (VNum (n\<^sub>1 + n\<^sub>2)) | _ \<Rightarrow> None)" |
  "\<lbrakk>Concat e\<^sub>1 e\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>e = (case (\<lbrakk>e\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>e, \<lbrakk>e\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>e) of
    (Some (VBv bv\<^sub>1), Some (VBv bv\<^sub>2)) \<Rightarrow> Some (VBv (bv\<^sub>1 @ bv\<^sub>2)) | _ \<Rightarrow> None)" |
  "\<lbrakk>Packet x p in \<epsilon>\<rbrakk>\<^sub>e = map_option (\<lambda>bv. VBv bv) (env_lookup_packet \<epsilon> x p)" |
  "\<lbrakk>Len x p in \<epsilon>\<rbrakk>\<^sub>e = map_option (\<lambda>bv. VNum (len bv)) (env_lookup_packet \<epsilon> x p)" |
  "\<lbrakk>Slice sl n m in \<epsilon>\<rbrakk>\<^sub>e = Option.bind (env_lookup_sliceable \<epsilon> sl)
    (\<lambda>bv. if 0 \<le> n \<and> n < m \<and> m \<le> (len bv + 1) then Some (VBv (slice bv n m)) else None)"
sorry

nominal_termination (eqvt)
  by lexicographic_order

nominal_function formula_sem :: "formula \<Rightarrow> env \<Rightarrow> bool option" ("\<lbrakk>_ in _\<rbrakk>\<^sub>f" [50,60] 50)
where
  "\<lbrakk>FTrue in \<epsilon>\<rbrakk>\<^sub>f = Some True" |
  "\<lbrakk>FFalse in \<epsilon>\<rbrakk>\<^sub>f = Some False" |
  "\<lbrakk>Eq e\<^sub>1 e\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>f = (case (\<lbrakk>e\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>e, \<lbrakk>e\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>e) of
    (Some v\<^sub>1, Some v\<^sub>2) \<Rightarrow> Some (v\<^sub>1 = v\<^sub>2) | _ \<Rightarrow> None)" |
  "\<lbrakk>Gt e\<^sub>1 e\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>f = (case (\<lbrakk>e\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>e, \<lbrakk>e\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>e) of
    (Some (VNum n\<^sub>1), Some (VNum n\<^sub>2)) \<Rightarrow> Some (n\<^sub>1 > n\<^sub>2) | _ \<Rightarrow> None)" |
  "\<lbrakk>And f\<^sub>1 f\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>f = (case \<lbrakk>f\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>f of None \<Rightarrow> None | Some False \<Rightarrow> Some False |
    Some True \<Rightarrow> \<lbrakk>f\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>f)" |
  "\<lbrakk>Not f\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>f = map_option (\<lambda>b. \<not>b) (\<lbrakk>f\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>f)" |
  "\<lbrakk>IsValid x i in \<epsilon>\<rbrakk>\<^sub>f = map_option (\<lambda>bv. True) (env_lookup_instance \<epsilon> x i)"
sorry

nominal_termination (eqvt)
  by lexicographic_order

section\<open>Commands\<close>

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