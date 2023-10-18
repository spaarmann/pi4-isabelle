theory Chomp_Correctness imports Chomp Types begin

section\<open>Correctness of Chomp\<close>

subsection\<open>Helpers for the main proofs below\<close>

inductive unaffected_by_chomp\<^sub>e :: "exp \<Rightarrow> bool" where
  "unaffected_by_chomp\<^sub>e (Num _)" |
  "unaffected_by_chomp\<^sub>e (Bv _)" |
  "unaffected_by_chomp\<^sub>e (Packet _ PktOut)" |
  "unaffected_by_chomp\<^sub>e (Len _ PktOut)" |
  "unaffected_by_chomp\<^sub>e (Slice (SlInstance _ _) _ _)" |
  "unaffected_by_chomp\<^sub>e (Slice (SlPacket _ PktOut) _ _)" |
  "\<lbrakk> unaffected_by_chomp\<^sub>e e\<^sub>1; unaffected_by_chomp\<^sub>e e\<^sub>2 \<rbrakk> \<Longrightarrow> unaffected_by_chomp\<^sub>e (Plus e\<^sub>1 e\<^sub>2)" |
  "\<lbrakk> unaffected_by_chomp\<^sub>e e\<^sub>1; unaffected_by_chomp\<^sub>e e\<^sub>2 \<rbrakk> \<Longrightarrow> unaffected_by_chomp\<^sub>e (Concat e\<^sub>1 e\<^sub>2)"

declare unaffected_by_chomp\<^sub>e.intros[simp]
declare unaffected_by_chomp\<^sub>e.intros[intro]

lemma chomp_unaffected\<^sub>e: "unaffected_by_chomp\<^sub>e e \<Longrightarrow> (e = chomp\<^sub>1\<^sub>e e x)"
  sorry

text\<open>We use the first semantic assumption to assert that e doesn't already contain any BitVars.
It's a little stronger than what's needed for this lemma, but that's fine.\<close>
lemma ref_chomp_unaffected\<^sub>e:
  assumes sem: "\<lbrakk>e in \<E>\<rbrakk>\<^sub>e = Some v" and "unaffected_by_chomp\<^sub>e e"
  shows "e = heapRef\<^sub>1\<^sub>e (chomp\<^sub>1\<^sub>e e y) x \<iota> sz n"
proof -
  let ?ref_chomp = "\<lambda>e. heapRef\<^sub>1\<^sub>e (chomp\<^sub>1\<^sub>e e y) x \<iota> sz n"
  have "\<lbrakk>e in \<E>\<rbrakk>\<^sub>e = Some v \<Longrightarrow> ?thesis" proof (nominal_induct e rule: exp.strong_induct)
    case (Num n)
      show ?case by (auto)
    case (Bv bv)
      then have "BitVar \<notin> set bv" by (auto simp add: bv_to_bools_some)
      have "chomp\<^sub>1\<^sub>e (Bv bv) y = Bv bv" by (auto)
      show ?case by (auto)
  qed
  then show ?thesis using sem by auto
qed

thm ref_chomp_unaffected\<^sub>e

subsection\<open>Main Correctness Results\<close>

lemma semantic_chomp_exp:
  fixes e::exp and h::heap and h'::heap and \<E>::env and \<E>'::env and x::var and \<iota>::instanc
    and HT :: header_table
  assumes "h' = chomp\<^sub>S h 1"
      and "\<E>' = \<E>[x \<rightarrow> empty_heap\<lparr> heap_headers := empty_headers(\<iota> \<mapsto> v) \<rparr>]"
      and "x \<in> env_dom \<E> \<Longrightarrow> ((Some v = (map_option (\<lambda>bv. bv @ take 1 (heap_pkt_in h)) (env_lookup_instance \<E> x \<iota>)))
                            \<and> env_lookup_packet \<E> x PktIn = Some []
                            \<and> env_lookup_packet \<E> x PktOut = Some [])"
      and "x \<notin> env_dom \<E> \<Longrightarrow> (v = take 1 (heap_pkt_in h)) \<and> atom x \<sharp> e"
      and "map_of HT \<iota> = Some \<eta>"
(* TODO: y just appears in the lemma. It probably needs freshness assumptions? *)
  shows "\<lbrakk>e in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = (\<lbrakk>heapRef\<^sub>1\<^sub>e (chomp\<^sub>1\<^sub>e e y) x \<iota> (header_length \<eta>) 1 in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e)"
proof -
  let ?ref_chomp = "\<lambda>e. heapRef\<^sub>1\<^sub>e (chomp\<^sub>1\<^sub>e e y) x \<iota> (header_length \<eta>) 1"
  show ?thesis proof (nominal_induct e rule: exp.strong_induct)

  case (Num n)
  have "unaffected_by_chomp\<^sub>e (Num n)" by (auto)
  then show ?case by (auto simp add: chomp_unaffected\<^sub>e)
  (*then have "Num n = ?ref_chomp (Num n)" by (auto simp add: chomp_unaffected\<^sub>e)
  then show ?case by (auto)*)
next
  case (Bv bv)
  then have "Bv bv = ?ref_chomp (Bv bv)" sorry
  then show ?case by (auto)
next
  case (Plus e\<^sub>1 e\<^sub>2)

qed
qed

(* proof (nominal_induct t avoiding: v l p rule: term.strong_induct) *)

lemma semantic_chomp:
  fixes x::var and \<tau>::heap_ty and \<E>::env and h::heap and HT::header_table and \<iota>::instanc
  assumes "atom x \<sharp> \<tau>"
      and "h \<in> \<lbrakk>\<tau> in \<E>\<rbrakk>\<^sub>t"
      and "map_of HT \<iota> = Some \<eta>"
      and "length (heap_pkt_in h) \<ge> header_length \<eta>"
  shows "\<exists>h' \<in> \<lbrakk>chomp \<tau> \<eta> \<iota> x
          in \<E>[x \<rightarrow> empty_heap\<lparr> heap_headers := empty_headers(
                \<iota> := Some (take (header_length n) (heap_pkt_in h))
          ) \<rparr>]\<rbrakk>\<^sub>t. h' = chomp\<^sub>S h (header_length \<eta>)"
sorry

end