theory Semantics imports Syntax Utils begin

no_notation inverse_divide (infixl "'/" 70) \<comment> \<open>avoid clash with division notation\<close>

text\<open>For next meeting:
Questions/Help:
- heap_ty_empty definition
- Chomping... Especially whether heapRef(..., b_n, n) is meant to have "two" n's or whether they're
  the same. Thesis has a "b_n fresh" but paper has the line at the top of page 14.
  The impl does seem to distinguish them. It also seems to potentially do some binder things
  differently, see TODOs in Chomp.thy.
  https://github.com/stg-tud/pi4/blob/main/lib/chomp.ml
  The only place these are introduced is in the actual `chomp` definition in the thesis (p. 68/79).
  From that, two things:
  - It seems like using b_n = n would work fine here.
  - It also seems like there could only ever possibly be a single variable in any given type?
    And like types with variables only ever exist temporarily to be passed from chomp1 to heapRef1?
    Oh, unless the b_0 literals are not a mistake and really are meant to be the 0th. But then at
    least that definitely means bit variables are id'd by the number I think.
    But the b0 literals do seem to be a mistake as far as I can tell.
    Maybe they even intend b_n specifically to be the only bit variable that exists? But then the
    references to having them in env don't seem to make any sense.
To talk about:
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

text\<open>The substitution functions for expressions and formulas just need to support replacing one
variable with another.\<close>
nominal_function subst_var_exp :: "exp \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp" ("_[_ '/ _]\<^sub>e" [1000, 49, 49] 1000)
where
  "(Num n)[s/y]\<^sub>e = Num n" |
  "(Bv bv)[s/y]\<^sub>e = Bv bv" |
  "(Plus e\<^sub>1 e\<^sub>2)[s/y]\<^sub>e = Plus e\<^sub>1[s/y]\<^sub>e e\<^sub>2[s/y]\<^sub>e" |
  "(Concat e\<^sub>1 e\<^sub>2)[s/y]\<^sub>e = Concat e\<^sub>1[s/y]\<^sub>e e\<^sub>2[s/y]\<^sub>e" |
  "(Packet x p)[s/y]\<^sub>e = (if x = y then Packet s p else Packet x p)" |
  "(Len x p)[s/y]\<^sub>e = (if x = y then Len s p else Len x p)" |
  "(Slice (SlPacket x p) n m)[s/y]\<^sub>e = Slice (SlPacket (if x = y then s else x) p) n m" |
  "(Slice (SlInstance x \<iota>) n m)[s/y]\<^sub>e = Slice (SlInstance (if x = y then s else x) \<iota>) n m"
  subgoal by (simp add: eqvt_def subst_var_exp_graph_aux_def)
  subgoal by (simp)
  apply (clarify)
  subgoal for P e s y
    apply (rule exp.strong_exhaust[of e P]) apply (auto)
    apply (rule sliceable.strong_exhaust) apply (auto)
  done
  apply (auto)
done
nominal_termination (eqvt)
  by lexicographic_order

nominal_function subst_var_formula :: "formula \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula"
  ("_[_ '/ _]\<^sub>f" [1000, 49, 49] 1000)
where
  "FTrue[s/y]\<^sub>f = FTrue" |
  "FFalse[s/y]\<^sub>f = FFalse" |
  "(Eq e\<^sub>1 e\<^sub>2)[s/y]\<^sub>f = Eq e\<^sub>1[s/y]\<^sub>e e\<^sub>2[s/y]\<^sub>e" |
  "(Gt e\<^sub>1 e\<^sub>2)[s/y]\<^sub>f = Gt e\<^sub>1[s/y]\<^sub>e e\<^sub>2[s/y]\<^sub>e" |
  "(And \<phi>\<^sub>1 \<phi>\<^sub>2)[s/y]\<^sub>f = And \<phi>\<^sub>1[s/y]\<^sub>f \<phi>\<^sub>2[s/y]\<^sub>f" |
  "(Not \<phi>)[s/y]\<^sub>f = Not \<phi>[s/y]\<^sub>f" |
  "(IsValid x \<iota>)[s/y]\<^sub>f = IsValid (if x = y then s else x) \<iota>"
  subgoal by (simp add: eqvt_def subst_var_formula_graph_aux_def)
  subgoal by (simp)
  apply (clarify)
  subgoal for P \<phi> s y by (rule formula.strong_exhaust[of \<phi> P]) (auto)
  apply (auto)
done
nominal_termination (eqvt)
  by lexicographic_order


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
  E_SliceInst:  "\<lbrakk> H \<iota> = Some bv; 0 \<le> n \<and> n < m \<and> m \<le> length bv + 1;
                   slice bv n m = bs \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlInstance var_heap \<iota>) n m) \<rightarrow>\<^sub>e Bv bs"

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
  F_IsValidTrue:"\<lbrakk> H \<iota> = Some _ \<rbrakk>
                \<Longrightarrow> (In, Out, H, IsValid x \<iota>) \<rightarrow>\<^sub>f FTrue" |
  F_IsValidFalse:"\<lbrakk> H \<iota> = None \<rbrakk>
                \<Longrightarrow> (In, Out, H, IsValid var_heap \<iota>) \<rightarrow>\<^sub>f FFalse"

inductive formula_small_steps :: "(bv \<times> bv \<times> headers \<times> formula) \<Rightarrow> formula \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>f* _" [0,50] 50)
where
  FS_Id:     "(In, Out, H, f) \<rightarrow>\<^sub>f* f" |
  FS_Step:   "\<lbrakk> (In, Out, H, f) \<rightarrow>\<^sub>f f''; (In, Out, H, f'') \<rightarrow>\<^sub>f* f' \<rbrakk>
             \<Longrightarrow> (In, Out, H, f) \<rightarrow>\<^sub>f* f'"


subsection\<open>Denotational semantics\<close>

nominal_function exp_sem :: "exp \<Rightarrow> env \<Rightarrow> val option" ("\<lbrakk>_ in _\<rbrakk>\<^sub>e" [50,60] 50)
where
  "\<lbrakk>Num n in \<E>\<rbrakk>\<^sub>e = Some (VNum n)" |
  "\<lbrakk>Bv bv in \<E>\<rbrakk>\<^sub>e = map_option VBv (bv_to_bools bv)" |
  "\<lbrakk>Plus e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = (case (\<lbrakk>e\<^sub>1 in \<E>\<rbrakk>\<^sub>e, \<lbrakk>e\<^sub>2 in \<E>\<rbrakk>\<^sub>e) of
    (Some (VNum n\<^sub>1), Some (VNum n\<^sub>2)) \<Rightarrow> Some (VNum (n\<^sub>1 + n\<^sub>2)) | _ \<Rightarrow> None)" |
  "\<lbrakk>Concat e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = (case (\<lbrakk>e\<^sub>1 in \<E>\<rbrakk>\<^sub>e, \<lbrakk>e\<^sub>2 in \<E>\<rbrakk>\<^sub>e) of
    (Some (VBv bv\<^sub>1), Some (VBv bv\<^sub>2)) \<Rightarrow> Some (VBv (bv\<^sub>1 @ bv\<^sub>2)) | _ \<Rightarrow> None)" |
  "\<lbrakk>Packet x p in \<E>\<rbrakk>\<^sub>e = map_option VBv (Option.bind (env_lookup_packet \<E> x p) bv_to_bools)" |
  "\<lbrakk>Len x p in \<E>\<rbrakk>\<^sub>e = map_option (\<lambda>bv. VNum (length bv)) (env_lookup_packet \<E> x p)" |
  "\<lbrakk>Slice sl n m in \<E>\<rbrakk>\<^sub>e = Option.bind (env_lookup_sliceable \<E> sl)
    (\<lambda>bv. if 0 \<le> n \<and> n < m \<and> m \<le> length bv + 1
          then map_option VBv (bv_to_bools (slice bv n m)) else None)"
  subgoal by (simp add: eqvt_def exp_sem_graph_aux_def)
  subgoal by (erule exp_sem_graph.induct) (auto)
  apply clarify
  subgoal for P e \<E>
    by (rule exp.strong_exhaust[of e P]) (auto)
  apply (simp_all)
done
nominal_termination (eqvt)
  by lexicographic_order

text\<open>Unlike for the small-step semantics, semantic expression equality and comparison is explicitly
defined to be False when the semantics of either operand are undefined. (See section 3.3, p. 9)\<close>
nominal_function formula_sem :: "formula \<Rightarrow> env \<Rightarrow> bool option" ("\<lbrakk>_ in _\<rbrakk>\<^sub>f" [50,60] 50)
where
  "\<lbrakk>FTrue in \<E>\<rbrakk>\<^sub>f = Some True" |
  "\<lbrakk>FFalse in \<E>\<rbrakk>\<^sub>f = Some False" |
  "\<lbrakk>Eq e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>f = (case (\<lbrakk>e\<^sub>1 in \<E>\<rbrakk>\<^sub>e, \<lbrakk>e\<^sub>2 in \<E>\<rbrakk>\<^sub>e) of
    (Some v\<^sub>1, Some v\<^sub>2) \<Rightarrow> Some (v\<^sub>1 = v\<^sub>2) | _ \<Rightarrow> Some False)" |
  "\<lbrakk>Gt e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>f = (case (\<lbrakk>e\<^sub>1 in \<E>\<rbrakk>\<^sub>e, \<lbrakk>e\<^sub>2 in \<E>\<rbrakk>\<^sub>e) of
    (Some (VNum n\<^sub>1), Some (VNum n\<^sub>2)) \<Rightarrow> Some (n\<^sub>1 > n\<^sub>2) | _ \<Rightarrow> Some False)" |
  "\<lbrakk>And f\<^sub>1 f\<^sub>2 in \<E>\<rbrakk>\<^sub>f = (case \<lbrakk>f\<^sub>1 in \<E>\<rbrakk>\<^sub>f of None \<Rightarrow> None | Some False \<Rightarrow> Some False |
    Some True \<Rightarrow> \<lbrakk>f\<^sub>2 in \<E>\<rbrakk>\<^sub>f)" |
  "\<lbrakk>Not f\<^sub>1 in \<E>\<rbrakk>\<^sub>f = map_option (\<lambda>b. \<not>b) (\<lbrakk>f\<^sub>1 in \<E>\<rbrakk>\<^sub>f)" |
  "\<lbrakk>IsValid x \<iota> in \<E>\<rbrakk>\<^sub>f = map_option (\<lambda>bv. True) (env_lookup_instance \<E> x \<iota>)"
  subgoal by (simp add: eqvt_def formula_sem_graph_aux_def)
  subgoal by (erule formula_sem_graph.induct) (auto)
  apply clarify
  subgoal for P \<phi> \<E>
    by (rule formula.strong_exhaust[of \<phi> P]) (auto)
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
              \<Longrightarrow> HT \<turnstile> (In, Out, H, Assign \<iota> f e) \<rightarrow> (In, Out, H, Assign \<iota> f e')" |
  C_Assign:   "\<lbrakk> H \<iota> = Some orig_bv; map_of HT \<iota> = Some \<eta>;
                 header_field_to_range \<eta> f = (n, m); splice orig_bv n m bv = bv';
                 H' = header_update H \<iota> bv' \<rbrakk>
              \<Longrightarrow> HT \<turnstile> (In, Out, H, Assign \<iota> f (Bv bv)) \<rightarrow> (In, Out, H', Skip)" |
  C_Extract:  "\<lbrakk> map_of HT \<iota> = Some \<eta>; deserialize_header \<eta> In = (In', bv); H' = header_update H \<iota> bv \<rbrakk>
              \<Longrightarrow> HT \<turnstile> (In, Out, H, Extract \<iota>) \<rightarrow> (In', Out, H', Skip)" |
  C_Remit:    "\<lbrakk> map_of HT \<iota> = Some \<eta>; serialize_header H \<iota> = Some bv \<rbrakk>
              \<Longrightarrow> HT \<turnstile> (In, Out, H, Remit \<iota>) \<rightarrow> (In, Out @ bv, H, Skip)" |
  C_Add:      "\<lbrakk> map_of HT \<iota> = Some \<eta>; H \<iota> = None; init_header \<eta> = bv; H' = header_update H \<iota> bv \<rbrakk>
              \<Longrightarrow> HT \<turnstile> (In, Out, H, Add \<iota>) \<rightarrow> (In, Out, H', Skip)" |
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

end