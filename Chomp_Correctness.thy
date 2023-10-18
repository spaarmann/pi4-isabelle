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

text\<open>We use the first semantic assumption to assert that e doesn't already contain any BitVars.
It's a little stronger than what's needed for this lemma, but that's fine.\<close>
lemma ref_chomp_unaffected\<^sub>e:
  assumes "\<lbrakk>e in \<E>\<rbrakk>\<^sub>e = Some v" and "unaffected_by_chomp\<^sub>e e"
  shows "e = heapRef\<^sub>1\<^sub>e (chomp\<^sub>1\<^sub>e e y) x \<iota> sz n"
proof -
  let ?ref_chomp = "\<lambda>e. heapRef\<^sub>1\<^sub>e (chomp\<^sub>1\<^sub>e e y) x \<iota> sz n"
  have "(\<exists>v. \<lbrakk>e in \<E>\<rbrakk>\<^sub>e = Some v) \<Longrightarrow> unaffected_by_chomp\<^sub>e e \<Longrightarrow> ?thesis" proof (induction e)
    case (Num n)
    show ?case by (auto)
  next
    case (Bv bv)
    then have "BitVar \<notin> set bv" by (auto simp add: bv_to_bools_some)
    then have "?ref_chomp (Bv bv) = Bv bv" by (auto simp add: heapRefBvNop)
    then show ?case by (auto)
  next
    case (Plus e\<^sub>1 e\<^sub>2)
    moreover have "(\<exists>v. \<lbrakk>e\<^sub>1 in \<E>\<rbrakk>\<^sub>e = Some v)" using Plus by (auto simp add: exp_sem_Plus_Some1)
    moreover have "(\<exists>v. \<lbrakk>e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = Some v)" using Plus by (auto simp add: exp_sem_Plus_Some2)
    moreover from Plus.prems(2) have "unaffected_by_chomp\<^sub>e e\<^sub>1" by (cases) (auto)
    moreover from Plus.prems(2) have "unaffected_by_chomp\<^sub>e e\<^sub>2" by (cases) (auto)
    ultimately show ?case by (auto)
  next
    case (Concat e\<^sub>1 e\<^sub>2)
    moreover have "(\<exists>v. \<lbrakk>e\<^sub>1 in \<E>\<rbrakk>\<^sub>e = Some v)" using Concat by (auto simp add: exp_sem_Concat_Some1)
    moreover have "(\<exists>v. \<lbrakk>e\<^sub>2 in \<E>\<rbrakk>\<^sub>e = Some v)" using Concat by (auto simp add: exp_sem_Concat_Some2)
    moreover from Concat.prems(2) have "unaffected_by_chomp\<^sub>e e\<^sub>1" by (cases) (auto)
    moreover from Concat.prems(2) have "unaffected_by_chomp\<^sub>e e\<^sub>2" by (cases) (auto)
    ultimately show ?case by (auto)
  next
    case (Packet z pkt)
    from Packet.prems(2) have "pkt = PktOut" by (cases) (auto)
    then show ?case by (auto)
  next
    case (Len z pkt)
    from Len.prems(2) have "pkt = PktOut" by (cases) (auto)
    then show ?case by (auto)
  next
    case (Slice sl n m)
    show ?case proof (cases sl)
      case (SlPacket z pkt)
      from Slice.prems(2) and SlPacket have "pkt = PktOut" by (cases) (auto)
      then show "Slice sl n m = ?ref_chomp (Slice sl n m)" using Slice and SlPacket by (auto)
    next
      case (SlInstance z \<iota>)
      then show "Slice sl n m = ?ref_chomp (Slice sl n m)" using Slice by (auto)
    qed
  qed
  then show ?thesis using assms by auto
qed


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
  show ?thesis
  proof (induction e)
    case (Num n)
    then show ?case by (auto)
  next
    case (Bv bv)
    (* TODO: Want to show the Some case now with all the infrastructure I built up, but the None
       case is not actually necessarily true I think. Is the paper wrong here? *)
    then have "Bv bv = ?ref_chomp (Bv bv)"
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