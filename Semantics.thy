theory Semantics imports Syntax "HOL-Library.AList" begin

datatype heap = Heap "packet \<Rightarrow> bv" "instanc \<Rightarrow> bv option"

text\<open>This is necessary to use heaps in nominal_functions. It basically states that
no variables actually appear in the type.\<close>
instantiation heap :: pure begin
  definition permute_heap :: "perm \<Rightarrow> heap \<Rightarrow> heap"  where
    "permute_heap _ x = x"
  instance by standard (auto simp add: permute_heap_def)
end

fun heap_lookup_packet :: "heap \<Rightarrow> packet \<Rightarrow> bv" where
  "heap_lookup_packet (Heap pkts _) p = pkts p"
fun heap_lookup_instance :: "heap \<Rightarrow> instanc \<Rightarrow> bv option" where
  "heap_lookup_instance (Heap _ insts) i = insts i"

type_synonym env = "(var \<times> heap) list"

fun lookup_packet :: "env \<Rightarrow> var \<Rightarrow> packet \<Rightarrow> bv option" where
  "lookup_packet \<epsilon> x p = map_option (\<lambda>h. heap_lookup_packet h p) (map_of \<epsilon> x)"
fun lookup_instance :: "env \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> bv option" where
  "lookup_instance \<epsilon> x i = Option.bind (map_of \<epsilon> x) (\<lambda>h. heap_lookup_instance h i)"
(* This also doesn't work because sliceable is a nominal_datatype atm... *)
nominal_function lookup_sliceable :: "sliceable \<Rightarrow> env \<Rightarrow> bv option" where
  "lookup_sliceable (SlPacket x p) \<epsilon> = lookup_packet \<epsilon> x p" |
  "lookup_sliceable (SlInstance x i) \<epsilon> = lookup_instance \<epsilon> x i"
  using [[simproc del: alpha_lst]]
  subgoal unfolding eqvt_def by (auto simp add: lookup_sliceable_graph_aux_def permute_heap_def
                                            permute_list_def permute_option_def permute_bool_def permute_char_def)
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
  done
nominal_termination (eqvt)
  by lexicographic_order

term lookup_sliceable_graph_aux

datatype val = BV bv | Num nat

fun slice :: "'a list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a list" where
  "slice xs n m = take (nat (m - n)) (drop (nat n) xs)"

text\<open>It seems I can't define the semantics here as a function (which would be closer to how the
paper presents it. Is this a limitation of Nominal2? Am I using it wrong?\<close>
(*
nominal_function exp_sem :: "exp \<Rightarrow> val option" where
  "exp_sem (Len x p) = map_option (\<lambda>h. Num (length (heap_lookup_packet h p))) (\<epsilon> x)"
*)


text\<open>These are the expression semantics as an inductive predicate instead for now:\<close>
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



type_synonym header_instance = "string \<Rightarrow> bv"
type_synonym headers = "instanc \<Rightarrow> header_instance"

(*datatype cmd =
  Extract instanc | Remit instanc | Add instanc |
  If formula cmd cmd | Seq cmd cmd | Assign instanc string exp |
  Skip | Reset | Ascribe cmd pi_ty
*)

(* TODO: Is it possible to use O as variable name? Leads to a parse error if I try. *)
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