theory Chomp imports Syntax begin

nominal_function "chomp\<^sub>1\<^sub>e" :: "exp \<Rightarrow> var \<Rightarrow> nat \<Rightarrow> exp" where
  "chomp\<^sub>1\<^sub>e (Len x PktIn) y _ = (if x = y then Plus (Num 1) (Len x PktIn) else (Len x PktIn))" |
  "chomp\<^sub>1\<^sub>e (Packet x PktIn) y n = (if x = y then Concat (Bv [BitVar n]) (Packet x PktIn)
                                           else (Packet x PktIn))" |
  "chomp\<^sub>1\<^sub>e (Slice (SlPacket x PktIn) l r) y n = (if x \<noteq> y then (Slice (SlPacket x PktIn) l r)
    else (if r \<le> 1 then (Bv [BitVar n])
    else (if l = 0 then (Concat (Bv [BitVar n]) (Slice (SlPacket x PktIn) 0 (r - 1)))
    else (Slice (SlPacket x PktIn) (l - 1) (r - 1)))))" |
  "chomp\<^sub>1\<^sub>e (Plus e\<^sub>1 e\<^sub>2) y n = Plus (chomp\<^sub>1\<^sub>e e\<^sub>1 y n) (chomp\<^sub>1\<^sub>e e\<^sub>2 y n)" |
  "chomp\<^sub>1\<^sub>e (Concat e\<^sub>1 e\<^sub>2) y n = Concat (chomp\<^sub>1\<^sub>e e\<^sub>1 y n) (chomp\<^sub>1\<^sub>e e\<^sub>2 y n)" |
  "chomp\<^sub>1\<^sub>e e _ _ = e"
  sorry
nominal_termination (eqvt)
  by lexicographic_order

nominal_function chomp\<^sub>1\<^sub>\<phi> :: "formula \<Rightarrow> var \<Rightarrow> nat \<Rightarrow> formula" where
  "chomp\<^sub>1\<^sub>\<phi> (Eq e\<^sub>1 e\<^sub>2) x n = Eq (chomp\<^sub>1\<^sub>e e\<^sub>1 x n) (chomp\<^sub>1\<^sub>e e\<^sub>2 x n)" |
  "chomp\<^sub>1\<^sub>\<phi> (Gt e\<^sub>1 e\<^sub>2) x n = Gt (chomp\<^sub>1\<^sub>e e\<^sub>1 x n) (chomp\<^sub>1\<^sub>e e\<^sub>2 x n)" |
  "chomp\<^sub>1\<^sub>\<phi> (And \<phi>\<^sub>1 \<phi>\<^sub>2) x n = And (chomp\<^sub>1\<^sub>\<phi> \<phi>\<^sub>1 x n) (chomp\<^sub>1\<^sub>\<phi> \<phi>\<^sub>2 x n)" |
  "chomp\<^sub>1\<^sub>\<phi> (Not \<phi>) x n = Not (chomp\<^sub>1\<^sub>\<phi> \<phi> x n)" |
  "chomp\<^sub>1\<^sub>\<phi> \<phi> _ _ = \<phi>"
  sorry
nominal_termination (eqvt)
  by lexicographic_order

(* TODO: Is `x` as both the chomp arg and the Sigma var correct here? Same for Refinement*)
nominal_function chompRef\<^sub>1 :: "heap_ty \<Rightarrow> var \<Rightarrow> nat \<Rightarrow> heap_ty" where
  "chompRef\<^sub>1 (Sigma x \<tau>\<^sub>1 \<tau>\<^sub>2) x n = Sigma x (chompRef\<^sub>1 \<tau>\<^sub>1 x n) (chompRef\<^sub>1 \<tau>\<^sub>2 x n)" |
  "chompRef\<^sub>1 (Choice \<tau>\<^sub>1 \<tau>\<^sub>2) x n = Choice (chompRef\<^sub>1 \<tau>\<^sub>1 x n) (chompRef\<^sub>1 \<tau>\<^sub>2 x n)" |
  "chompRef\<^sub>1 (Refinement x \<tau> \<phi>) x n = Refinement x (chompRef\<^sub>1 \<tau> x n) (chomp\<^sub>1\<^sub>\<phi> \<phi> x n)" |
  "chompRef\<^sub>1 (Substitution \<tau>\<^sub>1 y \<tau>\<^sub>2) x n = Substitution (chompRef\<^sub>1 \<tau>\<^sub>1 x n) y (chompRef\<^sub>1 \<tau>\<^sub>2 x n)" |
  "chompRef\<^sub>1 \<tau> _ _ = \<tau>"
  sorry
nominal_termination (eqvt)
  by lexicographic_order

(* TODO: Does having Refinement y in the first def here have the same problem as heap_ty_empty etc.?*)
(* Maybe it should just have a freshness assumption for it? *)
nominal_function chomp\<^sub>1 :: "heap_ty \<Rightarrow> nat \<Rightarrow> heap_ty" where
  "chomp\<^sub>1 (Sigma x \<tau>\<^sub>1 \<tau>\<^sub>2) n = Choice (Sigma x (chomp\<^sub>1 \<tau>\<^sub>1 n) (chompRef\<^sub>1 \<tau>\<^sub>2 x n))
                              (Sigma x (Refinement y \<tau>\<^sub>1 (Eq (Len y PktIn) (Num 0))) (chomp\<^sub>1 \<tau>\<^sub>2 n))" |
  "chomp\<^sub>1 (Choice \<tau>\<^sub>1 \<tau>\<^sub>2) n = Choice (chomp\<^sub>1 \<tau>\<^sub>1 n) (chomp\<^sub>1 \<tau>\<^sub>2 0)" |
  "chomp\<^sub>1 (Refinement x \<tau> \<phi>) n = Refinement x (chomp\<^sub>1 \<tau> n) (chomp\<^sub>1\<^sub>\<phi> \<phi> x n)" |
  "chomp\<^sub>1 (Substitution \<tau>\<^sub>1 x \<tau>\<^sub>2) n = Substitution (chomp\<^sub>1 \<tau>\<^sub>1 n) x \<tau>\<^sub>2" |
  "chomp\<^sub>1 \<tau> _ = \<tau>"
  sorry
nominal_termination (eqvt)
  by lexicographic_order

end