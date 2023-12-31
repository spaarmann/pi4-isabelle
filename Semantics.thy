theory Semantics imports Syntax Utils begin

no_notation inverse_divide (infixl "'/" 70) \<comment> \<open>avoid clash with division notation\<close>

section\<open>Semantics of Expressions and Formulas\<close>

text\<open>We have two types of semantics for both expressions and formulas:

- Small-step operational semantics. These are ultimately used to define the operational semantics of
  commands and thus programs. They are not presented in the paper, just referenced, so we assume
  generally standard semantics here. The only variable that can occur is the special "heap" variable
  which is bound to the input heap (In, Out, H).
- Denotational-style semantics. These are used when evaluating formulas and expressions as part of
  refinement types. Here, other variables than "heap" are allowed, and evaluation is done using a
  full `env` environment.
\<close>

text\<open>The substitution functions for expressions and formulas just need to support replacing one
variable with another.\<close>
fun subst_var_exp :: "exp \<Rightarrow> var \<Rightarrow> var \<Rightarrow> exp" ("_[_ '/ _]\<^sub>e" [1000, 49, 49] 1000)
where
  "(Num n)[s/y]\<^sub>e = Num n" |
  "(Bv bv)[s/y]\<^sub>e = Bv bv" |
  "(Plus e\<^sub>1 e\<^sub>2)[s/y]\<^sub>e = Plus e\<^sub>1[s/y]\<^sub>e e\<^sub>2[s/y]\<^sub>e" |
  "(Concat e\<^sub>1 e\<^sub>2)[s/y]\<^sub>e = Concat e\<^sub>1[s/y]\<^sub>e e\<^sub>2[s/y]\<^sub>e" |
  "(Packet x p)[s/y]\<^sub>e = (if x = y then Packet s p else Packet x p)" |
  "(Len x p)[s/y]\<^sub>e = (if x = y then Len s p else Len x p)" |
  "(Slice (SlPacket x p) rng)[s/y]\<^sub>e = Slice (SlPacket (if x = y then s else x) p) rng" |
  "(Slice (SlInstance x \<iota>) rng)[s/y]\<^sub>e = Slice (SlInstance (if x = y then s else x) \<iota>) rng"
lemma subst_var_exp_eqvt[eqvt]: "p \<bullet> e[s/y]\<^sub>e = (p \<bullet> e)[(p \<bullet> s)/(p \<bullet> y)]\<^sub>e"
  apply (induction e)
  apply (auto simp add: permute_pure)
  subgoal for sl apply (cases sl) apply (auto) done
done

fun subst_var_formula :: "formula \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula"
  ("_[_ '/ _]\<^sub>f" [1000, 49, 49] 1000)
where
  "FTrue[s/y]\<^sub>f = FTrue" |
  "FFalse[s/y]\<^sub>f = FFalse" |
  "(Eq e\<^sub>1 e\<^sub>2)[s/y]\<^sub>f = Eq e\<^sub>1[s/y]\<^sub>e e\<^sub>2[s/y]\<^sub>e" |
  "(Gt e\<^sub>1 e\<^sub>2)[s/y]\<^sub>f = Gt e\<^sub>1[s/y]\<^sub>e e\<^sub>2[s/y]\<^sub>e" |
  "(And \<phi>\<^sub>1 \<phi>\<^sub>2)[s/y]\<^sub>f = And \<phi>\<^sub>1[s/y]\<^sub>f \<phi>\<^sub>2[s/y]\<^sub>f" |
  "(Not \<phi>)[s/y]\<^sub>f = Not \<phi>[s/y]\<^sub>f" |
  "(IsValid x \<iota>)[s/y]\<^sub>f = IsValid (if x = y then s else x) \<iota>"
lemma subst_var_formula_eqvt[eqvt]: "p \<bullet> \<phi>[s/y]\<^sub>f = (p \<bullet> \<phi>)[(p \<bullet> s)/(p \<bullet> y)]\<^sub>f"
  by (induction \<phi>) (auto)


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
  E_SlicePktIn: "\<lbrakk> right rng \<le> length In; slice In rng = bs \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlPacket var_heap PktIn) rng) \<rightarrow>\<^sub>e Bv bs" |
  E_SlicePktOut:"\<lbrakk> right rng < length Out; slice Out rng = bs \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlPacket var_heap PktOut) rng) \<rightarrow>\<^sub>e Bv bs" |
  E_SliceInst:  "\<lbrakk> H \<iota> = Some bv; right rng \<le> length bv;
                   slice bv rng = bs \<rbrakk>
                \<Longrightarrow> (In, Out, H, Slice (SlInstance var_heap \<iota>) rng) \<rightarrow>\<^sub>e Bv bs"

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

fun exp_sem :: "exp \<Rightarrow> env \<Rightarrow> val option" ("\<lbrakk>_ in _\<rbrakk>\<^sub>e" [50,60] 50)
where
  "\<lbrakk>Num n in \<E>\<rbrakk>\<^sub>e = Some (VNum n)" |
  "\<lbrakk>Bv bv in \<E>\<rbrakk>\<^sub>e = bv_to_val bv" |
  "\<lbrakk>Plus e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = (case (\<lbrakk>e\<^sub>1 in \<E>\<rbrakk>\<^sub>e, \<lbrakk>e\<^sub>2 in \<E>\<rbrakk>\<^sub>e) of
    (Some (VNum n\<^sub>1), Some (VNum n\<^sub>2)) \<Rightarrow> Some (VNum (n\<^sub>1 + n\<^sub>2)) | _ \<Rightarrow> None)" |
  "\<lbrakk>Concat e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = (case (\<lbrakk>e\<^sub>1 in \<E>\<rbrakk>\<^sub>e, \<lbrakk>e\<^sub>2 in \<E>\<rbrakk>\<^sub>e) of
    (Some (VBv bv\<^sub>1), Some (VBv bv\<^sub>2)) \<Rightarrow> Some (VBv (bv\<^sub>1 @ bv\<^sub>2)) | _ \<Rightarrow> None)" |
  "\<lbrakk>Packet x p in \<E>\<rbrakk>\<^sub>e = map_option VBv (env_lookup_packet \<E> x p)" |
  "\<lbrakk>Len x p in \<E>\<rbrakk>\<^sub>e = map_option (\<lambda>bv. VNum (length bv)) (env_lookup_packet \<E> x p)" |
  "\<lbrakk>Slice sl rng in \<E>\<rbrakk>\<^sub>e = Option.bind (env_lookup_sliceable \<E> sl)
    (\<lambda>bv. if right rng \<le> length bv
          then Some (VBv (slice bv rng)) else None)"
lemma exp_sem_eqvt[eqvt]: "p \<bullet> (\<lbrakk>e in \<E>\<rbrakk>\<^sub>e) = (\<lbrakk>p \<bullet> e in p \<bullet> \<E>\<rbrakk>\<^sub>e)"
  apply (induction e)
  subgoal by (auto)
  subgoal by (auto)
  subgoal by (auto simp add: permute_pure)
  subgoal by (auto simp add: permute_pure)
  apply (auto)
done

lemma exp_sem_Plus_Some1: "\<lbrakk>Plus e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = Some v \<Longrightarrow> (\<exists>v\<^sub>1. \<lbrakk>e\<^sub>1 in \<E>\<rbrakk>\<^sub>e = Some v\<^sub>1)"
proof (rule ccontr)
  assume plus_some: "\<lbrakk>Plus e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = Some v"
  assume "\<nexists>v\<^sub>1. (\<lbrakk>e\<^sub>1 in \<E>\<rbrakk>\<^sub>e) = Some v\<^sub>1"
  then have "\<lbrakk>Plus e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = None" by (auto)
  then show "False" using plus_some by (auto)
qed
lemma exp_sem_Plus_Some2: "\<lbrakk>Plus e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = Some v \<Longrightarrow> (\<exists>v\<^sub>2. \<lbrakk>e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = Some v\<^sub>2)"
proof (rule ccontr)
  assume plus_some: "\<lbrakk>Plus e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = Some v"
  assume "\<nexists>v\<^sub>2. (\<lbrakk>e\<^sub>2 in \<E>\<rbrakk>\<^sub>e) = Some v\<^sub>2"
  then have "\<lbrakk>Plus e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = None" by (auto split: val.split split: option.split)
  then show "False" using plus_some by (auto)
qed

lemma exp_sem_Concat_Some1: "\<lbrakk>Concat e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = Some v \<Longrightarrow> (\<exists>v\<^sub>1. \<lbrakk>e\<^sub>1 in \<E>\<rbrakk>\<^sub>e = Some v\<^sub>1)"
proof (rule ccontr)
  assume plus_some: "\<lbrakk>Concat e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = Some v"
  assume "\<nexists>v\<^sub>1. (\<lbrakk>e\<^sub>1 in \<E>\<rbrakk>\<^sub>e) = Some v\<^sub>1"
  then have "\<lbrakk>Concat e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = None" by (auto)
  then show "False" using plus_some by (auto)
qed
lemma exp_sem_Concat_Some2: "\<lbrakk>Concat e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = Some v \<Longrightarrow> (\<exists>v\<^sub>2. \<lbrakk>e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = Some v\<^sub>2)"
proof (rule ccontr)
  assume plus_some: "\<lbrakk>Concat e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = Some v"
  assume "\<nexists>v\<^sub>2. (\<lbrakk>e\<^sub>2 in \<E>\<rbrakk>\<^sub>e) = Some v\<^sub>2"
  then have "\<lbrakk>Concat e\<^sub>1 e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = None" by (auto split: val.split split: option.split)
  then show "False" using plus_some by (auto)
qed

lemma exp_sem_no_BitVar: "\<lbrakk>Bv bv in \<E>\<rbrakk>\<^sub>e = Some v \<Longrightarrow> BitVar \<notin> set bv"
  by (auto simp add: bv_to_val_def)


text\<open>Unlike for the small-step semantics, semantic expression equality and comparison is explicitly
defined to be False when the semantics of either operand are undefined. (See section 3.3, p. 9)\<close>
fun formula_sem :: "formula \<Rightarrow> env \<Rightarrow> bool option" ("\<lbrakk>_ in _\<rbrakk>\<^sub>f" [50,60] 50)
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

lemma formula_sem_eqvt[eqvt]: "p \<bullet> (\<lbrakk>\<phi> in \<E>\<rbrakk>\<^sub>f) = (\<lbrakk>p \<bullet> \<phi> in p \<bullet> \<E>\<rbrakk>\<^sub>f)"
  apply (induction \<phi>)
  apply (auto)
  apply (simp_all add: permute_pure split: option.split bool.split)
done


section\<open>Commands\<close>

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
                 header_field_to_range \<eta> f = rng; splice orig_bv rng bv = bv';
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