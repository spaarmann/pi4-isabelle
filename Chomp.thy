theory Chomp imports Syntax begin

nominal_function "chomp\<^sub>1\<^sub>e" :: "exp \<Rightarrow> var \<Rightarrow> exp" where
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
  subgoal by (simp add: eqvt_def chomp\<^sub>1\<^sub>e_graph_aux_def)
  subgoal by (simp)
  apply clarify
  subgoal for P e y
    apply (rule exp.strong_exhaust[of e P])
    apply (auto)
    subgoal by (rule packet.exhaust) (auto)
    subgoal by (rule packet.exhaust) (auto)
    apply (rule sliceable.exhaust)
    apply (auto)
    apply (rule packet.exhaust)
    apply (auto)
  done
  apply (simp_all)
done
nominal_termination (eqvt)
  by lexicographic_order

nominal_function chomp\<^sub>1\<^sub>\<phi> :: "formula \<Rightarrow> var \<Rightarrow> formula" where
  "chomp\<^sub>1\<^sub>\<phi> (Eq e\<^sub>1 e\<^sub>2) x = Eq (chomp\<^sub>1\<^sub>e e\<^sub>1 x) (chomp\<^sub>1\<^sub>e e\<^sub>2 x)" |
  "chomp\<^sub>1\<^sub>\<phi> (Gt e\<^sub>1 e\<^sub>2) x = Gt (chomp\<^sub>1\<^sub>e e\<^sub>1 x) (chomp\<^sub>1\<^sub>e e\<^sub>2 x)" |
  "chomp\<^sub>1\<^sub>\<phi> (And \<phi>\<^sub>1 \<phi>\<^sub>2) x = And (chomp\<^sub>1\<^sub>\<phi> \<phi>\<^sub>1 x) (chomp\<^sub>1\<^sub>\<phi> \<phi>\<^sub>2 x)" |
  "chomp\<^sub>1\<^sub>\<phi> (Not \<phi>) x = Not (chomp\<^sub>1\<^sub>\<phi> \<phi> x)" |
  "chomp\<^sub>1\<^sub>\<phi> FTrue _ = FTrue" |
  "chomp\<^sub>1\<^sub>\<phi> FFalse _ = FFalse" |
  "chomp\<^sub>1\<^sub>\<phi> (IsValid x \<iota>) _ = IsValid x \<iota>"
  subgoal by (auto simp add: eqvt_def chomp\<^sub>1\<^sub>\<phi>_graph_aux_def)
  subgoal by (simp)
  apply (clarify)
  subgoal for P \<phi> x by (rule formula.strong_exhaust[of \<phi> P]) (auto)
  apply (simp_all)
done
nominal_termination (eqvt)
  by lexicographic_order

(* TODO: Is `x` as both the chomp arg and the Sigma var correct here? Same for Refinement.
   I think the impl *doesn't* keep them the same?*)
nominal_function chompRef\<^sub>1 :: "heap_ty \<Rightarrow> var \<Rightarrow> heap_ty" where
  "atom y \<sharp> (x, \<tau>\<^sub>1) \<Longrightarrow> chompRef\<^sub>1 (Sigma y \<tau>\<^sub>1 \<tau>\<^sub>2) x = Sigma y (chompRef\<^sub>1 \<tau>\<^sub>1 x) (chompRef\<^sub>1 \<tau>\<^sub>2 x)" |
  "chompRef\<^sub>1 (Choice \<tau>\<^sub>1 \<tau>\<^sub>2) x = Choice (chompRef\<^sub>1 \<tau>\<^sub>1 x) (chompRef\<^sub>1 \<tau>\<^sub>2 x)" |
  "atom y \<sharp> (x, \<tau>) \<Longrightarrow> chompRef\<^sub>1 (Refinement y \<tau> \<phi>) x = Refinement y (chompRef\<^sub>1 \<tau> x) (chomp\<^sub>1\<^sub>\<phi> \<phi> x)" |
  "atom y \<sharp> (x, \<tau>\<^sub>2) \<Longrightarrow> chompRef\<^sub>1 (Substitution \<tau>\<^sub>1 y \<tau>\<^sub>2) x = Substitution (chompRef\<^sub>1 \<tau>\<^sub>1 x) y (chompRef\<^sub>1 \<tau>\<^sub>2 x)" |
  "chompRef\<^sub>1 Top _ = Top" |
  "chompRef\<^sub>1 Nothing _ = Nothing"
  subgoal by (simp add: eqvt_def chompRef\<^sub>1_graph_aux_def)
  subgoal by (simp)
  apply (clarify)
  subgoal for P \<tau> x
    by (rule heap_ty.strong_exhaust[of \<tau> P "(\<tau>, x)"]) (auto simp add: fresh_star_def fresh_Pair)
  apply (simp_all add: fresh_at_base fresh_Pair)
  subgoal for y x \<tau>\<^sub>1 \<tau>\<^sub>2 ya \<tau>\<^sub>2' 
nominal_termination (eqvt)
  by lexicographic_order

thm heap_ty.strong_exhaust
thm fresh_star_def
thm fresh_Pair
thm fresh_at_base
thm Abs_lst1_fcb2'

nominal_function chomp\<^sub>1 :: "heap_ty \<Rightarrow> heap_ty" where
  "atom y \<sharp> x \<Longrightarrow> chomp\<^sub>1 (Sigma x \<tau>\<^sub>1 \<tau>\<^sub>2) = Choice (Sigma x (chomp\<^sub>1 \<tau>\<^sub>1) (chompRef\<^sub>1 \<tau>\<^sub>2 x))
                              (Sigma x (Refinement y \<tau>\<^sub>1 (Eq (Len y PktIn) (Num 0))) (chomp\<^sub>1 \<tau>\<^sub>2))" |
  "chomp\<^sub>1 (Choice \<tau>\<^sub>1 \<tau>\<^sub>2) = Choice (chomp\<^sub>1 \<tau>\<^sub>1) (chomp\<^sub>1 \<tau>\<^sub>2)" |
  "chomp\<^sub>1 (Refinement x \<tau> \<phi>) = Refinement x (chomp\<^sub>1 \<tau>) (chomp\<^sub>1\<^sub>\<phi> \<phi> x)" |
  "chomp\<^sub>1 (Substitution \<tau>\<^sub>1 x \<tau>\<^sub>2) = Substitution (chomp\<^sub>1 \<tau>\<^sub>1) x \<tau>\<^sub>2" |
  "chomp\<^sub>1 \<tau> = \<tau>"
  sorry
nominal_termination (eqvt)
  by lexicographic_order

text\<open>We outline the recursive bitvector case for heapRef1e because lexicographic_order is not able
to prove termination otherwise, since we would have to construct a new Bv exp in the recursive call.\<close>
nominal_function heapRefBv :: "bv \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> exp" where
  "heapRefBv (b#bv) x \<iota> sz n = Concat (if b = BitVar
    then Slice (SlInstance x \<iota>) (sz - n) (sz - n + 1)
    else Bv [b]) (heapRefBv bv x \<iota> sz n)" |
  "heapRefBv [] _ _ _ _ = Bv []"
  sorry
nominal_termination (eqvt)
  by lexicographic_order

nominal_function heapRef\<^sub>1\<^sub>e :: "exp \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> exp" where
  "heapRef\<^sub>1\<^sub>e (Bv bv) x \<iota> sz n = heapRefBv bv x \<iota> sz n" |
  "heapRef\<^sub>1\<^sub>e (Plus e\<^sub>1 e\<^sub>2) x \<iota> sz n = Plus (heapRef\<^sub>1\<^sub>e e\<^sub>1 x \<iota> sz n) (heapRef\<^sub>1\<^sub>e e\<^sub>2 x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>e (Concat e\<^sub>1 e\<^sub>2) x \<iota> sz n = Concat (heapRef\<^sub>1\<^sub>e e\<^sub>1 x \<iota> sz n) (heapRef\<^sub>1\<^sub>e e\<^sub>2 x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>e e _ _ _ _ = e"
  sorry
nominal_termination (eqvt)
  by lexicographic_order

nominal_function heapRef\<^sub>1\<^sub>\<phi> :: "formula \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
  "heapRef\<^sub>1\<^sub>\<phi> (Eq e\<^sub>1 e\<^sub>2) x \<iota> sz n = Eq (heapRef\<^sub>1\<^sub>e e\<^sub>1 x \<iota> sz n) (heapRef\<^sub>1\<^sub>e e\<^sub>2 x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>\<phi> (Gt e\<^sub>1 e\<^sub>2) x \<iota> sz n = Gt (heapRef\<^sub>1\<^sub>e e\<^sub>1 x \<iota> sz n) (heapRef\<^sub>1\<^sub>e e\<^sub>2 x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>\<phi> (And \<phi>\<^sub>1 \<phi>\<^sub>2) x \<iota> sz n = And (heapRef\<^sub>1\<^sub>\<phi> \<phi>\<^sub>1 x \<iota> sz n) (heapRef\<^sub>1\<^sub>\<phi> \<phi>\<^sub>2 x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>\<phi> (Not \<phi>) x \<iota> sz n = Not (heapRef\<^sub>1\<^sub>\<phi> \<phi> x \<iota> sz n)" |
  "heapRef\<^sub>1\<^sub>\<phi> \<phi> _ _ _ _ = \<phi>"
  sorry
nominal_termination (eqvt)
  by lexicographic_order

nominal_function heapRef\<^sub>1 :: "heap_ty \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> heap_ty" where
  "atom x \<sharp> y \<Longrightarrow> heapRef\<^sub>1 (Sigma x \<tau>\<^sub>1 \<tau>\<^sub>2) y \<iota> sz n = Sigma x (heapRef\<^sub>1 \<tau>\<^sub>1 y \<iota> sz n) (heapRef\<^sub>1 \<tau>\<^sub>2 y \<iota> sz n)" |
  "heapRef\<^sub>1 (Choice \<tau>\<^sub>1 \<tau>\<^sub>2) y \<iota> sz n = Choice (heapRef\<^sub>1 \<tau>\<^sub>1 y \<iota> sz n) (heapRef\<^sub>1 \<tau>\<^sub>2 y \<iota> sz n)" |
  "atom x \<sharp> y \<Longrightarrow> heapRef\<^sub>1 (Refinement x \<tau> \<phi>) y \<iota> sz n = Refinement x (heapRef\<^sub>1 \<tau> y \<iota> sz n) (heapRef\<^sub>1\<^sub>\<phi> \<phi> y \<iota> sz n)" |
  "atom x \<sharp> y \<Longrightarrow> heapRef\<^sub>1 (Substitution \<tau>\<^sub>1 x \<tau>\<^sub>2) y \<iota> sz n = Substitution (heapRef\<^sub>1 \<tau>\<^sub>1 y \<iota> sz n) x (heapRef\<^sub>1 \<tau>\<^sub>2 y \<iota> sz n)" |
  "heapRef\<^sub>1 \<tau> _ _ _ _ = \<tau>"
  sorry
nominal_termination (eqvt)
  by lexicographic_order

end