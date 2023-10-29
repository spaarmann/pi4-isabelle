theory Chomp imports Syntax Utils begin

section\<open>Syntactic chomp definition\<close>

fun "chomp\<^sub>1\<^sub>e" :: "exp \<Rightarrow> var \<Rightarrow> exp" where
  "chomp\<^sub>1\<^sub>e (Len x PktIn) y = (if x = y then Plus (Num 1) (Len x PktIn) else (Len x PktIn))" |
  "chomp\<^sub>1\<^sub>e (Packet x PktIn) y = (if x = y then Concat (Bv [BitVar]) (Packet x PktIn)
                                           else (Packet x PktIn))" |
  "chomp\<^sub>1\<^sub>e (Slice (SlPacket x PktIn) l r) y = (if x \<noteq> y then (Slice (SlPacket x PktIn) l r)
    else (if r \<le> 1 then (Bv [BitVar])
    else (if l = 0 then (Concat (Bv [BitVar]) (Slice (SlPacket x PktIn) 0 (r - 1)))
    else (Slice (SlPacket x PktIn) (l - 1) (r - 1)))))" |
  "chomp\<^sub>1\<^sub>e (Plus e\<^sub>1 e\<^sub>2) y = Plus (chomp\<^sub>1\<^sub>e e\<^sub>1 y) (chomp\<^sub>1\<^sub>e e\<^sub>2 y)" |
  "chomp\<^sub>1\<^sub>e (Concat e\<^sub>1 e\<^sub>2) y = Concat (chomp\<^sub>1\<^sub>e e\<^sub>1 y) (chomp\<^sub>1\<^sub>e e\<^sub>2 y)" |
  "chomp\<^sub>1\<^sub>e (Num n) _ = Num n" |
  "chomp\<^sub>1\<^sub>e (Bv bv) _ = Bv bv" |
  "chomp\<^sub>1\<^sub>e (Len x PktOut) _ = Len x PktOut" |
  "chomp\<^sub>1\<^sub>e (Packet x PktOut) _ = Packet x PktOut" |
  "chomp\<^sub>1\<^sub>e (Slice (SlPacket x PktOut) l r) _ = Slice (SlPacket x PktOut) l r" |
  "chomp\<^sub>1\<^sub>e (Slice (SlInstance x \<iota>) l r) _ = Slice (SlInstance x \<iota>) l r"
lemma chomp\<^sub>1\<^sub>e_eqvt[eqvt]: "p \<bullet> chomp\<^sub>1\<^sub>e e y = chomp\<^sub>1\<^sub>e (p \<bullet> e) (p \<bullet> y)"
  apply (induction e)
  apply (auto)
  subgoal for x pkt by (cases pkt) (auto)
  subgoal for x pkt by (cases pkt) (auto)
  subgoal for sl n m apply (cases sl) apply (auto) subgoal for x pkt by (cases pkt) (auto) done
done

fun chomp\<^sub>1\<^sub>\<phi> :: "formula \<Rightarrow> var \<Rightarrow> formula" where
  "chomp\<^sub>1\<^sub>\<phi> (Eq e\<^sub>1 e\<^sub>2) x = Eq (chomp\<^sub>1\<^sub>e e\<^sub>1 x) (chomp\<^sub>1\<^sub>e e\<^sub>2 x)" |
  "chomp\<^sub>1\<^sub>\<phi> (Gt e\<^sub>1 e\<^sub>2) x = Gt (chomp\<^sub>1\<^sub>e e\<^sub>1 x) (chomp\<^sub>1\<^sub>e e\<^sub>2 x)" |
  "chomp\<^sub>1\<^sub>\<phi> (And \<phi>\<^sub>1 \<phi>\<^sub>2) x = And (chomp\<^sub>1\<^sub>\<phi> \<phi>\<^sub>1 x) (chomp\<^sub>1\<^sub>\<phi> \<phi>\<^sub>2 x)" |
  "chomp\<^sub>1\<^sub>\<phi> (Not \<phi>) x = Not (chomp\<^sub>1\<^sub>\<phi> \<phi> x)" |
  "chomp\<^sub>1\<^sub>\<phi> FTrue _ = FTrue" |
  "chomp\<^sub>1\<^sub>\<phi> FFalse _ = FFalse" |
  "chomp\<^sub>1\<^sub>\<phi> (IsValid x \<iota>) _ = IsValid x \<iota>"
lemma chomp\<^sub>1\<^sub>\<phi>_eqvt[eqvt]: "p \<bullet> chomp\<^sub>1\<^sub>\<phi> \<phi> x = chomp\<^sub>1\<^sub>\<phi> (p \<bullet> \<phi>) (p \<bullet> x)"
  by (induction \<phi>) (auto)

nominal_function chompRef\<^sub>1 :: "heap_ty \<Rightarrow> var \<Rightarrow> heap_ty" where
  "atom y \<sharp> (x, \<tau>\<^sub>1) \<Longrightarrow> chompRef\<^sub>1 (Sigma y \<tau>\<^sub>1 \<tau>\<^sub>2) x = Sigma y (chompRef\<^sub>1 \<tau>\<^sub>1 x) (chompRef\<^sub>1 \<tau>\<^sub>2 x)" |
  "chompRef\<^sub>1 (Choice \<tau>\<^sub>1 \<tau>\<^sub>2) x = Choice (chompRef\<^sub>1 \<tau>\<^sub>1 x) (chompRef\<^sub>1 \<tau>\<^sub>2 x)" |
  "atom y \<sharp> (x, \<tau>) \<Longrightarrow> chompRef\<^sub>1 (Refinement y \<tau> \<phi>) x = Refinement y (chompRef\<^sub>1 \<tau> x) (chomp\<^sub>1\<^sub>\<phi> \<phi> x)" |
  "atom y \<sharp> (x, \<tau>\<^sub>2) \<Longrightarrow> chompRef\<^sub>1 (Substitution \<tau>\<^sub>1 y \<tau>\<^sub>2) x = Substitution (chompRef\<^sub>1 \<tau>\<^sub>1 x) y (chompRef\<^sub>1 \<tau>\<^sub>2 x)" |
  "chompRef\<^sub>1 Top _ = Top" |
  "chompRef\<^sub>1 Nothing _ = Nothing"
  using [[simproc del: alpha_lst]]
  subgoal by (simp add: eqvt_def chompRef\<^sub>1_graph_aux_def)
  subgoal by (simp)
  apply (clarify)
  subgoal for P \<tau> x
    by (rule heap_ty.strong_exhaust[of \<tau> P "(\<tau>, x)"]) (auto simp add: fresh_star_def fresh_Pair)
  apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal for y x \<tau>\<^sub>1 \<tau>\<^sub>2 ya \<tau>\<^sub>2'
    apply (erule Abs_lst1_fcb2'[where c = "x"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_star_insert Abs_fresh_iff)
  done
  subgoal for y x \<tau> \<phi> y' \<phi>'
    apply (erule Abs_lst1_fcb2'[where c = "x"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_star_insert Abs_fresh_iff)
  done
  subgoal for y x \<tau>\<^sub>2 \<tau>\<^sub>1 y' \<tau>\<^sub>1'
    apply (erule Abs_lst1_fcb2'[where c = "x"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_star_insert Abs_fresh_iff)
  done
done
nominal_termination (eqvt)
  by lexicographic_order

nominal_function chomp\<^sub>1 :: "heap_ty \<Rightarrow> heap_ty" where
  "\<lbrakk> atom y \<sharp> (x, \<tau>\<^sub>1, \<tau>\<^sub>2); atom x \<sharp> \<tau>\<^sub>1 \<rbrakk>
   \<Longrightarrow> chomp\<^sub>1 (Sigma x \<tau>\<^sub>1 \<tau>\<^sub>2) = Choice (Sigma x (chomp\<^sub>1 \<tau>\<^sub>1) (chompRef\<^sub>1 \<tau>\<^sub>2 x))
                              (Sigma x (Refinement y \<tau>\<^sub>1 (Eq (Len y PktIn) (Num 0))) (chomp\<^sub>1 \<tau>\<^sub>2))" |
  "chomp\<^sub>1 (Choice \<tau>\<^sub>1 \<tau>\<^sub>2) = Choice (chomp\<^sub>1 \<tau>\<^sub>1) (chomp\<^sub>1 \<tau>\<^sub>2)" |
  "atom x \<sharp> \<tau> \<Longrightarrow> chomp\<^sub>1 (Refinement x \<tau> \<phi>) = Refinement x (chomp\<^sub>1 \<tau>) (chomp\<^sub>1\<^sub>\<phi> \<phi> x)" |
  "atom x \<sharp> \<tau>\<^sub>2 \<Longrightarrow> chomp\<^sub>1 (Substitution \<tau>\<^sub>1 x \<tau>\<^sub>2) = Substitution (chomp\<^sub>1 \<tau>\<^sub>1) x \<tau>\<^sub>2" |
  "chomp\<^sub>1 Top = Top" |
  "chomp\<^sub>1 Nothing = Nothing"
  using [[simproc del: alpha_lst]]
  subgoal by (auto simp add: eqvt_def chomp\<^sub>1_graph_aux_def)
  subgoal by (simp)
  subgoal for P \<tau>
    apply (rule heap_ty.strong_exhaust[of \<tau> P \<tau>]) apply (auto)
    subgoal by (auto simp add: fresh_star_def) (metis obtain_fresh)
    subgoal by (auto simp add: fresh_star_def)
    subgoal by (auto simp add: fresh_star_def)
  done
  apply (auto simp add: fresh_star_def fresh_at_base)
  subgoal for y x \<tau>\<^sub>1 \<tau>\<^sub>2 y' x' \<tau>\<^sub>2'
    apply (erule Abs_lst1_fcb2'[where c = "\<tau>\<^sub>1"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_star_insert Abs_fresh_iff)
  done
  subgoal for y x \<tau>\<^sub>1 \<tau>\<^sub>2 y' x' \<tau>\<^sub>2'
    apply (erule Abs_lst1_fcb2'[where c = "\<tau>\<^sub>1"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_star_insert Abs_fresh_iff)
  done
  subgoal for y x \<tau>\<^sub>1 \<tau>\<^sub>2 y' x' \<tau>\<^sub>2' using [[simproc add: alpha_lst]] by (auto)
  subgoal for x \<tau> \<phi> x' \<phi>'
    apply (erule Abs_lst1_fcb2'[where c = "\<tau>"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_star_insert Abs_fresh_iff)
  done
  subgoal for x \<tau>\<^sub>2 \<tau>\<^sub>1 x' \<tau>\<^sub>1'
    apply (erule Abs_lst1_fcb2'[where c = "\<tau>\<^sub>2"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_star_insert Abs_fresh_iff)
  done
done
nominal_termination (eqvt)
  by lexicographic_order

text\<open>We outline the recursive bitvector case for heapRef1e because lexicographic_order is not able
to prove termination otherwise, since we would have to construct a new Bv exp in the recursive call.\<close>
fun heapRefBv :: "bv \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> exp" where
  (* The slice upper bound is originally "sz - n + 1" but swapping the order avoids the annoying
     nat edge case. *)
  "heapRefBv (b#bv) x \<iota> sz n = Concat (if b = BitVar
    then Slice (SlInstance x \<iota>) (sz - n) (sz + 1 - n)
    else Bv [b]) (heapRefBv bv x \<iota> sz n)" |
  "heapRefBv [] _ _ _ _ = Bv []"
lemma heapRefBv_eqvt[eqvt]:
  "p \<bullet> heapRefBv bv x \<iota> sz n = heapRefBv (p \<bullet> bv) (p \<bullet> x) (p \<bullet> \<iota>) (p \<bullet> sz) (p \<bullet> n)"
  by (induction bv) (auto simp add: permute_pure)

text\<open>It is useful to have heapRef not change bit vectors that contain no BitVars at all (and the
paper claims so despite mirroring the heapRefBv definition above), so we flatten Concats of single
bits produced by heapRefBv.\<close>
fun flattenBvConcats :: "exp \<Rightarrow> exp" where
  "flattenBvConcats (Concat e\<^sub>1 e\<^sub>2) = (case (flattenBvConcats e\<^sub>1, flattenBvConcats e\<^sub>2) of
    (Bv bv\<^sub>1, Bv bv\<^sub>2) \<Rightarrow> Bv (bv\<^sub>1 @ bv\<^sub>2) | (e\<^sub>1', e\<^sub>2') \<Rightarrow> Concat e\<^sub>1' e\<^sub>2')" |
  "flattenBvConcats e = e"
lemma flattenBvConcats_eqvt[eqvt]: "p \<bullet> flattenBvConcats e = flattenBvConcats (p \<bullet> e)"
  apply (induction e rule: flattenBvConcats.induct)
  apply (auto)
  apply (auto split: exp.split)
done

lemma heapRefBvNop:
  assumes "BitVar \<notin> set bv"
  shows "flattenBvConcats (heapRefBv bv x \<iota> sz n) = Bv bv"
proof -
  have "BitVar \<notin> set bv \<Longrightarrow> ?thesis" proof (induction bv)
    case Nil show ?case by (auto)
  next
    case (Cons a bv) then show ?case by (auto)
  qed
  then show ?thesis using assms by (auto)
qed

fun heapRef\<^sub>1\<^sub>e :: "exp \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> exp" where
  "heapRef\<^sub>1\<^sub>e (Bv bv) x \<iota> sz n = flattenBvConcats (heapRefBv bv x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>e (Plus e\<^sub>1 e\<^sub>2) x \<iota> sz n = Plus (heapRef\<^sub>1\<^sub>e e\<^sub>1 x \<iota> sz n) (heapRef\<^sub>1\<^sub>e e\<^sub>2 x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>e (Concat e\<^sub>1 e\<^sub>2) x \<iota> sz n = Concat (heapRef\<^sub>1\<^sub>e e\<^sub>1 x \<iota> sz n) (heapRef\<^sub>1\<^sub>e e\<^sub>2 x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>e (Num n) _ _ _ _ = Num n" |
  "heapRef\<^sub>1\<^sub>e (Packet y p) _ _ _ _ = Packet y p" |
  "heapRef\<^sub>1\<^sub>e (Len y p) _ _ _ _ = Len y p" |
  "heapRef\<^sub>1\<^sub>e (Slice sl n m) _ _ _ _ = Slice sl n m"
lemma heapRef\<^sub>1\<^sub>e_eqvt[eqvt]:
  "p \<bullet> heapRef\<^sub>1\<^sub>e e x \<iota> sz n = heapRef\<^sub>1\<^sub>e (p \<bullet> e) (p \<bullet> x) (p \<bullet> \<iota>) (p \<bullet> sz) (p \<bullet> n)"
  by (induction e) (auto simp add: permute_pure)

fun heapRef\<^sub>1\<^sub>\<phi> :: "formula \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
  "heapRef\<^sub>1\<^sub>\<phi> (Eq e\<^sub>1 e\<^sub>2) x \<iota> sz n = Eq (heapRef\<^sub>1\<^sub>e e\<^sub>1 x \<iota> sz n) (heapRef\<^sub>1\<^sub>e e\<^sub>2 x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>\<phi> (Gt e\<^sub>1 e\<^sub>2) x \<iota> sz n = Gt (heapRef\<^sub>1\<^sub>e e\<^sub>1 x \<iota> sz n) (heapRef\<^sub>1\<^sub>e e\<^sub>2 x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>\<phi> (And \<phi>\<^sub>1 \<phi>\<^sub>2) x \<iota> sz n = And (heapRef\<^sub>1\<^sub>\<phi> \<phi>\<^sub>1 x \<iota> sz n) (heapRef\<^sub>1\<^sub>\<phi> \<phi>\<^sub>2 x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>\<phi> (Not \<phi>) x \<iota> sz n = Not (heapRef\<^sub>1\<^sub>\<phi> \<phi> x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>\<phi> FTrue _ _ _ _ = FTrue" |
  "heapRef\<^sub>1\<^sub>\<phi> FFalse _ _ _ _ = FFalse" |
  "heapRef\<^sub>1\<^sub>\<phi> (IsValid x \<iota>) _ _ _ _ = IsValid x \<iota>"
lemma heapRef\<^sub>1\<^sub>\<phi>_eqvt[eqvt]:
  "p \<bullet> heapRef\<^sub>1\<^sub>\<phi> \<phi> x \<iota> sz n = heapRef\<^sub>1\<^sub>\<phi> (p \<bullet> \<phi>) (p \<bullet> x) (p \<bullet> \<iota>) (p \<bullet> sz) (p \<bullet> n)"
  by (induction \<phi>) (auto simp add: permute_pure)

nominal_function heapRef\<^sub>1 :: "heap_ty \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> heap_ty" where
  "atom x \<sharp> (y, \<tau>\<^sub>1)
   \<Longrightarrow> heapRef\<^sub>1 (Sigma x \<tau>\<^sub>1 \<tau>\<^sub>2) y \<iota> sz n = Sigma x (heapRef\<^sub>1 \<tau>\<^sub>1 y \<iota> sz n) (heapRef\<^sub>1 \<tau>\<^sub>2 y \<iota> sz n)" |
  "heapRef\<^sub>1 (Choice \<tau>\<^sub>1 \<tau>\<^sub>2) y \<iota> sz n = Choice (heapRef\<^sub>1 \<tau>\<^sub>1 y \<iota> sz n) (heapRef\<^sub>1 \<tau>\<^sub>2 y \<iota> sz n)" |
  "atom x \<sharp> (y, \<tau>)
   \<Longrightarrow> heapRef\<^sub>1 (Refinement x \<tau> \<phi>) y \<iota> sz n = Refinement x (heapRef\<^sub>1 \<tau> y \<iota> sz n) (heapRef\<^sub>1\<^sub>\<phi> \<phi> y \<iota> sz n)" |
  "atom x \<sharp> (y, \<tau>\<^sub>2)
   \<Longrightarrow> heapRef\<^sub>1 (Substitution \<tau>\<^sub>1 x \<tau>\<^sub>2) y \<iota> sz n = Substitution (heapRef\<^sub>1 \<tau>\<^sub>1 y \<iota> sz n) x (heapRef\<^sub>1 \<tau>\<^sub>2 y \<iota> sz n)" |
  "heapRef\<^sub>1 Top _ _ _ _ = Top" |
  "heapRef\<^sub>1 Nothing _ _ _ _ = Nothing"
  using [[simproc del: alpha_lst]]
  subgoal by (simp add: eqvt_def heapRef\<^sub>1_graph_aux_def)
  subgoal by (simp)
  apply (clarify)
  subgoal for P \<tau> y \<iota> sz n
    by (rule heap_ty.strong_exhaust[of \<tau> P "(y, \<tau>)"]) (auto simp add: fresh_star_def fresh_Pair)
  apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal for x y \<tau>\<^sub>1 \<tau>\<^sub>2 \<iota> sz n x' \<tau>\<^sub>2'
    apply (erule Abs_lst1_fcb2'[where c = "y"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_star_insert Abs_fresh_iff permute_pure)
  done
  subgoal for x y \<tau> \<phi> \<iota> sz n x' \<phi>'
    apply (erule Abs_lst1_fcb2'[where c = "y"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_star_insert Abs_fresh_iff permute_pure)
  done
  subgoal for x y \<tau>\<^sub>2 \<tau>\<^sub>1 \<iota> sz n x' \<tau>\<^sub>1'
    apply (erule Abs_lst1_fcb2'[where c = "y"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_star_insert Abs_fresh_iff permute_pure)
  done
done
nominal_termination (eqvt)
  by lexicographic_order

nominal_function chompRec :: "heap_ty \<Rightarrow> nat \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> nat \<Rightarrow> heap_ty" where
  "chompRec \<tau> n x \<iota> sz = (if n = 0 then \<tau> else
    (let \<tau>' = heapRef\<^sub>1 (chomp\<^sub>1 \<tau>) x \<iota> sz n in chompRec \<tau>' (n - 1) x \<iota> sz))"
  subgoal by (simp add: eqvt_def chompRec_graph_aux_def)
  apply (auto)
done

definition chomp :: "heap_ty \<Rightarrow> header_type \<Rightarrow> instanc \<Rightarrow> var \<Rightarrow> heap_ty" where
  "chomp \<tau> \<eta> \<iota> x = chompRec \<tau> (header_length \<eta>) x \<iota> (header_length \<eta>)"


section\<open>Semantic chomp definition\<close>

definition chomp\<^sub>S :: "heap \<Rightarrow> nat \<Rightarrow> heap" where
  "chomp\<^sub>S h n = h\<lparr> heap_pkt_in := drop n (heap_pkt_in h) \<rparr>"

end