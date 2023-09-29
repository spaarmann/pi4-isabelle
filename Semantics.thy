theory Semantics imports Syntax Utils begin

no_notation inverse_divide (infixl "'/" 70) \<comment> \<open>avoid clash with division notation\<close>

text\<open>For next meeting:
Questions/Help:
- If "\<Gamma>;\<tau>" is just syntax for extending \<Gamma>, can I define it without making the grammar abiguous?
To talk about:
- Exp/formula typing as judgement with extra parameter or "\<Gamma>;\<tau>" as \<Gamma>[var_heap -> \<tau>]?
- Well-formedness predicates from section 5.4 of the thesis.
- In the thesis, "env" also maps bit variables to single bits. This is mentioned off-hand in one
  place in the paper too I think.
\<close>

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

inductive
  exp_small_step :: "(bv \<times> bv \<times> headers \<times> exp) \<Rightarrow> exp \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>e _" [50,50] 50)
where
  E_Plus1:      "\<lbrakk> (In, Out, H, e\<^sub>1) \<rightarrow>\<^sub>e e\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Plus e\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>e Plus e\<^sub>1' e\<^sub>2" |
  E_Plus2:      "\<lbrakk> value\<^sub>e v\<^sub>1; (In, Out, H, e\<^sub>2) \<rightarrow>\<^sub>e e\<^sub>2' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Plus v\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>e Plus v\<^sub>1 e\<^sub>2'" |
  E_Plus:       "(In, Out, H, Plus (Num n\<^sub>1) (Num n\<^sub>2)) \<rightarrow>\<^sub>e Num (n\<^sub>1 + n\<^sub>2)" |
  E_Concat1:    "\<lbrakk> (In, Out, H, e\<^sub>1) \<rightarrow>\<^sub>e e\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Concat e\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>e Concat e\<^sub>1 e\<^sub>2" |
  E_Concat2:    "\<lbrakk> value\<^sub>e v\<^sub>1; (In, Out, H, e\<^sub>2) \<rightarrow>\<^sub>e e\<^sub>2' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Concat v\<^sub>1 e\<^sub>2) \<rightarrow>\<^sub>e Concat v\<^sub>1 e\<^sub>2'" |
  E_Concat:     "(In, Out, H, Concat (Bv b\<^sub>1) (Bv b\<^sub>2)) \<rightarrow>\<^sub>e Bv (b\<^sub>1 @ b\<^sub>2)" |
  E_PktIn:      "(In, Out, H, Packet var_heap PktIn) \<rightarrow>\<^sub>e Bv In" |
  E_PktOut:     "(In, Out, H, Packet var_heap PktOut) \<rightarrow>\<^sub>e Bv Out" |
  E_PktInLen:   "(In, Out, H, Len var_heap PktIn) \<rightarrow>\<^sub>e Num (length In)" |
  E_PktOutLen:  "(In, Out, H, Len var_heap PktOut) \<rightarrow>\<^sub>e Num (length Out)" |
  E_SlicePktIn: "\<lbrakk> 0 \<le> n \<and> n < m \<and> m \<le> length In + 1; slice In n m = bs \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlPacket var_heap PktIn) n m) \<rightarrow>\<^sub>e Bv bs" |
  E_SlicePktOut:"\<lbrakk> 0 \<le> n \<and> n < m \<and> m \<le> length Out + 1; slice Out n m = bs \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlPacket var_heap PktOut) n m) \<rightarrow>\<^sub>e Bv bs" |
  E_SliceInst:  "\<lbrakk> header_lookup H i = Some bv; 0 \<le> n \<and> n < m \<and> m \<le> length bv + 1;
                   slice bv n m = bs \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlInstance var_heap i) n m) \<rightarrow>\<^sub>e Bv bs"

inductive exp_small_steps :: "(bv \<times> bv \<times> headers \<times> exp) \<Rightarrow> exp \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>e* _" [50,50] 50)
where
  ES_Id:     "(In, Out, H, e) \<rightarrow>\<^sub>e* e" |
  ES_Step:   "\<lbrakk> (In, Out, H, e) \<rightarrow>\<^sub>e e''; (In, Out, H, e'') \<rightarrow>\<^sub>e* e' \<rbrakk>
             \<Longrightarrow> (In, Out, H, e) \<rightarrow>\<^sub>e* e'"

inductive formula_small_step :: "(bv \<times> bv \<times> headers \<times> formula) \<Rightarrow> formula \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>f _" [50,50] 50)
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
  F_GtTrue:     "\<lbrakk> n\<^sub>1 > n\<^sub>2 \<rbrakk>
                \<Longrightarrow> (In, Out, H, Gt (Num n\<^sub>1) (Num n\<^sub>2)) \<rightarrow>\<^sub>f FTrue" |
  F_GtFalse:    "\<lbrakk> n\<^sub>1 \<le> n\<^sub>2 \<rbrakk>
                \<Longrightarrow> (In, Out, H, Gt (Num n\<^sub>1) (Num n\<^sub>2)) \<rightarrow>\<^sub>f FFalse" |
  F_And1:       "\<lbrakk> (In, Out, H, f\<^sub>1) \<rightarrow>\<^sub>f f\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, And f\<^sub>1 f\<^sub>2) \<rightarrow>\<^sub>f And f\<^sub>1' f\<^sub>2" |
  F_AndTrue:    "\<lbrakk> t\<^sub>1 = FTrue \<rbrakk>
                \<Longrightarrow> (In, Out, H, And t\<^sub>1 f\<^sub>2) \<rightarrow>\<^sub>f f\<^sub>2" |
  F_AndFalse:   "\<lbrakk> t\<^sub>1 = FFalse \<rbrakk>
                \<Longrightarrow> (In, Out, H, And t\<^sub>1 f\<^sub>2) \<rightarrow>\<^sub>f FFalse" |
  F_Not1:       "\<lbrakk> (In, Out, H, f\<^sub>1) \<rightarrow>\<^sub>f f\<^sub>1' \<rbrakk>
                \<Longrightarrow> (In, Out, H, Not f\<^sub>1) \<rightarrow>\<^sub>f f\<^sub>1'" |
  F_NotTrue:    "(In, Out, H, Not FTrue) \<rightarrow>\<^sub>f FFalse" |
  F_NotFalse:   "(In, Out, H, Not FFalse) \<rightarrow>\<^sub>f FTrue" |
  F_IsValidTrue:"\<lbrakk> header_lookup H i = Some _ \<rbrakk>
                \<Longrightarrow> (In, Out, H, IsValid x i) \<rightarrow>\<^sub>f FTrue" |
  F_IsValidFalse:"\<lbrakk> header_lookup H i = None \<rbrakk>
                \<Longrightarrow> (In, Out, H, IsValid var_heap i) \<rightarrow>\<^sub>f FFalse"

inductive formula_small_steps :: "(bv \<times> bv \<times> headers \<times> formula) \<Rightarrow> formula \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>f* _" [0,50] 50)
where
  FS_Id:     "(In, Out, H, f) \<rightarrow>\<^sub>f* f" |
  FS_Step:   "\<lbrakk> (In, Out, H, f) \<rightarrow>\<^sub>f f''; (In, Out, H, f'') \<rightarrow>\<^sub>f* f' \<rbrakk>
             \<Longrightarrow> (In, Out, H, f) \<rightarrow>\<^sub>f* f'"

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
  "\<lbrakk>Len x p in \<epsilon>\<rbrakk>\<^sub>e = map_option (\<lambda>bv. VNum (length bv)) (env_lookup_packet \<epsilon> x p)" |
  "\<lbrakk>Slice sl n m in \<epsilon>\<rbrakk>\<^sub>e = Option.bind (env_lookup_sliceable \<epsilon> sl)
    (\<lambda>bv. if 0 \<le> n \<and> n < m \<and> m \<le> length bv + 1 then Some (VBv (slice bv n m)) else None)"
  subgoal by (simp add: eqvt_def exp_sem_graph_aux_def)
  subgoal by (erule exp_sem_graph.induct) (auto)
  apply clarify
  subgoal for P x e
    by (rule exp.strong_exhaust[of x P]) (auto)
  apply (simp_all)
done
nominal_termination (eqvt)
  by lexicographic_order

text\<open>Unlike for the small-step semantics, semantic expression equality and comparison is explicitly
defined to be False when the semantics of either operand are undefined. (See section 3.3, p. 9)\<close>
nominal_function formula_sem :: "formula \<Rightarrow> env \<Rightarrow> bool option" ("\<lbrakk>_ in _\<rbrakk>\<^sub>f" [50,60] 50)
where
  "\<lbrakk>FTrue in \<epsilon>\<rbrakk>\<^sub>f = Some True" |
  "\<lbrakk>FFalse in \<epsilon>\<rbrakk>\<^sub>f = Some False" |
  "\<lbrakk>Eq e\<^sub>1 e\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>f = (case (\<lbrakk>e\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>e, \<lbrakk>e\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>e) of
    (Some v\<^sub>1, Some v\<^sub>2) \<Rightarrow> Some (v\<^sub>1 = v\<^sub>2) | _ \<Rightarrow> Some False)" |
  "\<lbrakk>Gt e\<^sub>1 e\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>f = (case (\<lbrakk>e\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>e, \<lbrakk>e\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>e) of
    (Some (VNum n\<^sub>1), Some (VNum n\<^sub>2)) \<Rightarrow> Some (n\<^sub>1 > n\<^sub>2) | _ \<Rightarrow> Some False)" |
  "\<lbrakk>And f\<^sub>1 f\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>f = (case \<lbrakk>f\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>f of None \<Rightarrow> None | Some False \<Rightarrow> Some False |
    Some True \<Rightarrow> \<lbrakk>f\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>f)" |
  "\<lbrakk>Not f\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>f = map_option (\<lambda>b. \<not>b) (\<lbrakk>f\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>f)" |
  "\<lbrakk>IsValid x i in \<epsilon>\<rbrakk>\<^sub>f = map_option (\<lambda>bv. True) (env_lookup_instance \<epsilon> x i)"
  subgoal by (simp add: eqvt_def formula_sem_graph_aux_def)
  subgoal by (erule formula_sem_graph.induct) (auto)
  apply clarify
  subgoal for P x e
    by (rule formula.strong_exhaust[of x P]) (auto)
  apply (simp_all)
done
nominal_termination (eqvt)
  by lexicographic_order

section\<open>Commands\<close>

(* I added HT as the extra ambient/global context explicitly here. *)
inductive
  small_step :: "header_table \<Rightarrow> (bv \<times> bv \<times> headers \<times> cmd) \<Rightarrow> (bv \<times> bv \<times> headers \<times> cmd) \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ \<rightarrow>/ _))" [50,0,50] 50)
where
  C_Seq1:     "\<lbrakk> HT \<turnstile> (In, Out, H, c\<^sub>1) \<rightarrow> (In', Out', H', c\<^sub>1') \<rbrakk>
              \<Longrightarrow> HT \<turnstile> (In, Out, H, Seq c\<^sub>1 c\<^sub>2) \<rightarrow> (In', Out', H', Seq c\<^sub>1' c\<^sub>2)" |
  C_Seq:      "HT \<turnstile> (In, Out, H, Seq Skip c) \<rightarrow> (In, Out, H, c)" |
  C_If1:      "\<lbrakk> (In, Out, H, f) \<rightarrow>\<^sub>f f' \<rbrakk>
              \<Longrightarrow> HT \<turnstile> (In, Out, H, If f c\<^sub>1 c\<^sub>2) \<rightarrow> (In, Out, H, If f' c\<^sub>1 c\<^sub>2)" |
  C_IfTrue:   "HT \<turnstile> (In, Out, H, If FTrue c\<^sub>1 c\<^sub>2) \<rightarrow> (In, Out, H, c\<^sub>1)" |
  C_IfFalse:  "HT \<turnstile> (In, Out, H, If FFalse c\<^sub>1 c\<^sub>2) \<rightarrow> (In, Out, H, c\<^sub>2)" |
  C_Assign1:  "\<lbrakk> (In, Out, H, e) \<rightarrow>\<^sub>e e' \<rbrakk>
              \<Longrightarrow> HT \<turnstile> (In, Out, H, Assign i f e) \<rightarrow> (In, Out, H, Assign i f e')" |
  C_Assign:   "\<lbrakk> header_lookup H i = Some inst; HT i = Some \<eta>;
                 header_field_to_range \<eta> f = (n, m); splice inst n m bv = bv';
                 H' = header_update H i bv' \<rbrakk>
              \<Longrightarrow> HT \<turnstile> (In, Out, H, Assign i f (Bv bv)) \<rightarrow> (In, Out, H', Skip)" |
  C_Extract:  "\<lbrakk> HT i = Some \<eta>; deserialize_header \<eta> In = (In', bv); H' = header_update H i bv \<rbrakk>
              \<Longrightarrow> HT \<turnstile> (In, Out, H, Extract i) \<rightarrow> (In', Out, H', Skip)" |
  C_Remit:    "\<lbrakk> HT i = Some \<eta>; serialize_header H i = Some bv \<rbrakk>
              \<Longrightarrow> HT \<turnstile> (In, Out, H, Remit i) \<rightarrow> (In, Out @ bv, H, Skip)" |
  C_Add:      "\<lbrakk> HT i = Some \<eta>; header_lookup H i = None; init_header \<eta> = bv; H' = header_update H i bv \<rbrakk>
              \<Longrightarrow> HT \<turnstile> (In, Out, H, Add i) \<rightarrow> (In, Out, H', Skip)" |
  C_Reset:    "\<lbrakk> In' = Out @ In \<rbrakk>
              \<Longrightarrow> HT \<turnstile> (In, Out, H, Reset) \<rightarrow> (In', [], empty_headers, Skip)" |
  C_Ascribe:  "HT \<turnstile> (In, Out, H, Ascribe c ty) \<rightarrow> (In, Out, H, c)"

inductive
  small_steps :: "header_table \<Rightarrow> (bv \<times> bv \<times> headers \<times> cmd) \<Rightarrow> (bv \<times> bv \<times> headers \<times> cmd) \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ \<rightarrow>*/ _))" [50,0,50] 50)
where
  CS_Id:     "HT \<turnstile> (In, Out, H, c) \<rightarrow>* (In, Out, H, c)" |
  CS_Step:   "\<lbrakk> HT \<turnstile> t \<rightarrow> t''; HT \<turnstile> t'' \<rightarrow>* t' \<rbrakk>
             \<Longrightarrow> HT \<turnstile> t \<rightarrow>* t'"


section\<open>Types\<close>

nominal_function heap_ty_sem :: "heap_ty \<Rightarrow> env \<Rightarrow> heap set" ("\<lbrakk>_ in _\<rbrakk>\<^sub>t" [50,60] 100)
where
  "\<lbrakk>Nothing in \<epsilon>\<rbrakk>\<^sub>t = {}" |
  "\<lbrakk>Top in \<epsilon>\<rbrakk>\<^sub>t = UNIV" |
  "atom x \<sharp> (\<tau>\<^sub>1, \<epsilon>)
   \<Longrightarrow>\<lbrakk>Sigma x \<tau>\<^sub>1 \<tau>\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>t = {h\<^sub>1 ++ h\<^sub>2 | h\<^sub>1 h\<^sub>2. h\<^sub>1 \<in> \<lbrakk>\<tau>\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>t \<and> h\<^sub>2 \<in> \<lbrakk>\<tau>\<^sub>2 in \<epsilon>[x \<rightarrow> h\<^sub>1]\<rbrakk>\<^sub>t}" |
  "\<lbrakk>Choice \<tau>\<^sub>1 \<tau>\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>t = \<lbrakk>\<tau>\<^sub>1 in \<epsilon>\<rbrakk>\<^sub>t \<union> \<lbrakk>\<tau>\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>t" |
  "atom x \<sharp> (\<tau>, \<epsilon>)
   \<Longrightarrow> \<lbrakk>Refinement x \<tau> \<phi> in \<epsilon>\<rbrakk>\<^sub>t = {h. h \<in> \<lbrakk>\<tau> in \<epsilon>\<rbrakk>\<^sub>t \<and> \<lbrakk>\<phi> in \<epsilon>[x \<rightarrow> h]\<rbrakk>\<^sub>f = Some True}" |
  "atom x \<sharp> (\<tau>\<^sub>2, \<epsilon>)
   \<Longrightarrow> \<lbrakk>Substitution \<tau>\<^sub>1 x \<tau>\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>t = {h. \<exists> h\<^sub>2. (h\<^sub>2 \<in> \<lbrakk>\<tau>\<^sub>2 in \<epsilon>\<rbrakk>\<^sub>t) \<and> (h \<in> \<lbrakk>\<tau>\<^sub>1 in \<epsilon>[x \<rightarrow> h\<^sub>2]\<rbrakk>\<^sub>t)}"
  using [[simproc del: alpha_lst]]
  subgoal by (auto simp add: eqvt_def heap_ty_sem_graph_aux_def)
  subgoal by (erule heap_ty_sem_graph.induct) (auto)
  apply clarify
  subgoal for P \<tau> \<epsilon>
    apply (rule heap_ty.strong_exhaust[of \<tau> P "(\<tau>, \<epsilon>)"])
    apply (auto simp add: fresh_star_def fresh_Pair)
    done
  apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal for x \<tau>\<^sub>1 \<epsilon> \<tau>\<^sub>2 x' \<tau>\<^sub>2'
    apply (erule Abs_lst1_fcb2'[where c = "(\<tau>\<^sub>1, \<epsilon>)"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_Pair pure_fresh fresh_star_insert)
  done
  subgoal for x \<tau> \<epsilon> \<phi> x' \<phi>'
    apply (erule Abs_lst1_fcb2'[where c = "(\<tau>, \<epsilon>)"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_Pair pure_fresh fresh_star_insert)
  done
  subgoal for x \<tau>\<^sub>2 \<epsilon> \<tau>\<^sub>1 x' \<tau>\<^sub>1'
    apply (erule Abs_lst1_fcb2'[where c = "(\<tau>\<^sub>2, \<epsilon>)"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_Pair pure_fresh fresh_star_insert)
  done
done
nominal_termination (eqvt)
  by lexicographic_order

inductive heap_entails_ty :: "heap \<Rightarrow> env \<Rightarrow> heap_ty \<Rightarrow> bool" ("_ \<Turnstile>_ _" [50,50,50] 500)
where
  Ent_Top:      "h \<Turnstile>\<epsilon> Top" |
  Ent_ChoiceL:  "\<lbrakk> h \<Turnstile>\<epsilon> \<tau>\<^sub>1 \<rbrakk>
                \<Longrightarrow> h \<Turnstile>\<epsilon> (Choice \<tau>\<^sub>1 \<tau>\<^sub>2)" |
  Ent_ChoiceR:  "\<lbrakk> h \<Turnstile>\<epsilon> \<tau>\<^sub>2 \<rbrakk>
                \<Longrightarrow> h \<Turnstile>\<epsilon> (Choice \<tau>\<^sub>1 \<tau>\<^sub>2)" |
  Ent_Refine:   "\<lbrakk> h \<Turnstile>\<epsilon> \<tau>; \<lbrakk>\<phi> in \<epsilon>[x \<rightarrow> h]\<rbrakk>\<^sub>f = Some True \<rbrakk>
                \<Longrightarrow> h \<Turnstile>\<epsilon> (Refinement x \<tau> \<phi>)" |
  Ent_Sigma:    "\<lbrakk> In = In\<^sub>1 @ In\<^sub>2; Out = Out\<^sub>1 @ Out\<^sub>2; H = join_headers H\<^sub>1 H\<^sub>2;
                   (Heap In\<^sub>1 Out\<^sub>1 H\<^sub>1) \<Turnstile>\<epsilon> \<tau>\<^sub>1; (Heap In\<^sub>2 Out\<^sub>2 H\<^sub>2) \<Turnstile>(\<epsilon>[x \<rightarrow> (Heap In\<^sub>1 Out\<^sub>1 H\<^sub>1)]) \<tau>\<^sub>2\<rbrakk>
                \<Longrightarrow> (Heap In Out H) \<Turnstile>\<epsilon> (Sigma x \<tau>\<^sub>1 \<tau>\<^sub>2)" |
  Ent_Subst:    "\<lbrakk> (Heap In\<^sub>2 Out\<^sub>2 H\<^sub>2) \<Turnstile>\<epsilon> \<tau>\<^sub>2; h \<Turnstile>(\<epsilon>[x \<rightarrow> (Heap In\<^sub>2 Out\<^sub>2 H\<^sub>2)]) \<tau>\<^sub>1 \<rbrakk>
                \<Longrightarrow> h \<Turnstile>\<epsilon> (Substitution \<tau>\<^sub>1 x \<tau>\<^sub>2)"

definition env_entails_ty_env :: "env \<Rightarrow> ty_env \<Rightarrow> bool" ("_ \<TTurnstile> _" [50,50] 500)
where
  "(\<epsilon> \<TTurnstile> \<Gamma>) = (\<forall>x. x \<in> (fst ` set \<Gamma>)
    \<longrightarrow> (\<exists>h \<tau>. (map_of \<epsilon> x = Some h) \<and> (map_of \<Gamma> x = Some \<tau>) \<and> (h \<Turnstile>\<epsilon> \<tau>)))"

definition ty_includes :: "ty_env \<Rightarrow> heap_ty \<Rightarrow> instanc \<Rightarrow> bool" where
  "ty_includes \<Gamma> \<tau> i = (\<forall>\<epsilon>. \<epsilon> \<TTurnstile> \<Gamma> \<longrightarrow> (\<forall>h \<in> \<lbrakk>\<tau> in \<epsilon>\<rbrakk>\<^sub>t. i \<in> heap_dom h))"

definition ty_excludes :: "ty_env \<Rightarrow> heap_ty \<Rightarrow> instanc \<Rightarrow> bool" where
  "ty_excludes \<Gamma> \<tau> i = (\<forall>\<epsilon>. \<epsilon> \<TTurnstile> \<Gamma> \<longrightarrow> (\<forall>h \<in> \<lbrakk>\<tau> in \<epsilon>\<rbrakk>\<^sub>t. i \<notin> heap_dom h))"

(* TODO: I can't get the prios for this and ty_env_add_heap (";") such that this is not ambigious *)
inductive exp_typing :: "ty_env \<Rightarrow> exp \<Rightarrow> base_ty \<Rightarrow> bool"
  ("_ \<turnstile>\<^sub>e _ : _" [51,60,60] 60)
where
  TE_Num:       "\<Gamma> \<turnstile>\<^sub>e (Num n) : Nat" |
  TE_Bv:        "\<Gamma> \<turnstile>\<^sub>e (Bv bv) : BV" |
  TE_Plus:      "\<lbrakk> \<Gamma> \<turnstile>\<^sub>e e\<^sub>1 : Nat; \<Gamma> \<turnstile>\<^sub>e e\<^sub>2 : Nat \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e (Plus e\<^sub>1 e\<^sub>2) : Nat" |
  TE_Concat:    "\<lbrakk> \<Gamma> \<turnstile>\<^sub>e e\<^sub>1 : BV; \<Gamma> \<turnstile>\<^sub>e e\<^sub>2 : BV \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e (Concat e\<^sub>1 e\<^sub>2) : BV" |
  TE_Packet:    "\<lbrakk> map_of \<Gamma> x = Some _ \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e (Packet x p) : BV" |
  TE_Len:       "\<lbrakk> map_of \<Gamma> x = Some _ \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e (Len x p) : Nat" |
  (* TODO: Do these assumptions here make sense? These could be handled by well-formedness instead
           maybe.*)
  TE_SlicePkt:  "\<lbrakk> map_of \<Gamma> x = Some _; 0 \<le> n \<and> n < m \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e (Slice (SlPacket x p) n m) : BV" |
  TE_SliceInst: "\<lbrakk> map_of \<Gamma> x = Some \<tau>; ty_includes \<Gamma> \<tau> i; 0 \<le> n \<and> n < m \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e (Slice (SlInstance x i) n m) : BV"

inductive formula_typing :: "ty_env \<Rightarrow> formula \<Rightarrow> base_ty \<Rightarrow> bool"
  ("_ \<turnstile>\<^sub>f _ : _" [50,50,50] 60)
where
  TF_True:      "\<Gamma> \<turnstile>\<^sub>f FTrue : Bool" |
  TF_False:     "\<Gamma> \<turnstile>\<^sub>f FFalse : Bool" |
  TF_EqNum:     "\<lbrakk> \<Gamma> \<turnstile>\<^sub>e e\<^sub>1 : Nat; \<Gamma> \<turnstile>\<^sub>e e\<^sub>2 : Nat \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f (Eq e\<^sub>1 e\<^sub>2) : Bool" |
  TF_EqBv:      "\<lbrakk> \<Gamma> \<turnstile>\<^sub>e e\<^sub>1 : BV; \<Gamma> \<turnstile>\<^sub>e e\<^sub>2 : BV \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f (Eq e\<^sub>1 e\<^sub>2) : Bool" |
  TF_Gt:        "\<lbrakk> \<Gamma> \<turnstile>\<^sub>e e\<^sub>1 : Nat; \<Gamma> \<turnstile>\<^sub>e e\<^sub>2 : Nat \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f (Gt e\<^sub>1 e\<^sub>2) : Bool" |
  TF_And:       "\<lbrakk> \<Gamma> \<turnstile>\<^sub>f \<phi>\<^sub>1 : Bool; \<Gamma> \<turnstile>\<^sub>f \<phi>\<^sub>2 : Bool \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f (And \<phi>\<^sub>1 \<phi>\<^sub>2) : Bool" |
  TF_Not:       "\<lbrakk> \<Gamma> \<turnstile>\<^sub>f \<phi> : Bool \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f (Not \<phi>) : Bool" |
  TF_IsValid:   "\<lbrakk> map_of \<Gamma> x = Some _ \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f (IsValid x i) : Bool"

inductive command_typing :: "ty_env \<Rightarrow> cmd \<Rightarrow> pi_ty \<Rightarrow> bool"
  ("_ \<turnstile> _ : _" [50,50,50] 60)
(* TODO *)

end