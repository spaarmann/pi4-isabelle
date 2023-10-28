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
    then have "BitVar \<notin> set bv" by (auto simp add: exp_sem_no_BitVar)
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

lemma unchanged_packet_in_chomped_env:
  assumes h'_def: "h' = chomp\<^sub>S h 1"
      and \<E>'_def: "\<E>' = \<E>[x \<rightarrow> empty_heap\<lparr> heap_headers := [\<iota> \<mapsto> v] \<rparr>]"
      and x_in_\<E>: "x \<in> env_dom \<E>
        \<Longrightarrow> (env_lookup_packet \<E> x PktIn = Some [] \<and> env_lookup_packet \<E> x PktOut = Some [])"
      and x_not_in_\<E>: "x \<notin> env_dom \<E> \<Longrightarrow> atom x \<sharp> (Packet z pkt)"
      and "z \<noteq> y"
  shows "\<lbrakk>Packet z pkt in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = (\<lbrakk>Packet z pkt in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e)"
proof -
  from \<open>z \<noteq> y\<close> have "\<lbrakk>Packet z pkt in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = (\<lbrakk>Packet z pkt in \<E>\<rbrakk>\<^sub>e)"
    by (auto simp add: env_lookup_packet_update_other)
  moreover from \<open>z \<noteq> y\<close> have "\<lbrakk>Packet z pkt in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e = (\<lbrakk>Packet z pkt in \<E>'\<rbrakk>\<^sub>e)"
    by (auto simp add: env_lookup_packet_update_other)
  moreover have "\<lbrakk>Packet z pkt in \<E>\<rbrakk>\<^sub>e = (\<lbrakk>Packet z pkt in \<E>'\<rbrakk>\<^sub>e)" (is ?P)
    proof (cases "z = x")
      assume "z \<noteq> x"
      then show "?P" using \<open>z \<noteq> y\<close> and \<E>'_def by (auto simp add: env_lookup_packet_update_other)
    next
      assume "z = x"
      then show "?P" proof (cases "x \<in> env_dom \<E>")
        assume "x \<in> env_dom \<E>"
        then have "\<lbrakk>Packet z pkt in \<E>\<rbrakk>\<^sub>e = Some (VBv [])" using \<open>z = x\<close> and x_in_\<E>
          by (cases pkt) (auto)
        moreover have "\<lbrakk>Packet z pkt in \<E>'\<rbrakk>\<^sub>e = Some (VBv [])" using \<open>z = x\<close> and \<E>'_def
          by (cases pkt) (auto simp add: env_lookup_packet_def)
        ultimately show "?P" by (auto)
      next
        assume "x \<notin> env_dom \<E>"
        then have "atom x \<sharp> (Packet z pkt)" using assms by (auto)
        then have "False" using \<open>z = x\<close> by (metis fresh_at_base(2) fresh_def supp_Packet)
        then show "?P" using \<open>z = x\<close> by auto
      qed
    qed
  ultimately show ?thesis by (auto)
qed


subsection\<open>Main Correctness Results\<close>

(* TODO: The paper states an equality of the semantics here. I am unconvinced at the moment that
   that actually holds if there are BitVars in the original expression.
   I add an assumption that e evaluates to Some value for now, not sure yet if this will need the
   full general equality for something later. *)
(*
 (Some v = (map_option (\<lambda>bv. bv @ take 1 (heap_pkt_in h)) (env_lookup_instance \<E> x \<iota>)))
            \<and> map_option length (env_lookup_instance \<E> x \<iota>) = Some (header_length \<eta> - n)
*)
lemma semantic_chomp_exp:
  fixes e::exp and h::heap and h'::heap and \<E>::env and \<E>'::env and x::var and \<iota>::instanc
    and HT :: header_table
  assumes "map_of HT \<iota> = Some \<eta>"
      and "header_length \<eta> \<ge> 1" (* Zero-length headers don't make sense I think *)
      and h'_def: "h' = chomp\<^sub>S h 1"
      and \<E>'_def: "\<E>' = \<E>[x \<rightarrow> empty_heap\<lparr> heap_headers := [\<iota> \<mapsto> v] \<rparr>]"
      and x_in_\<E>: "x \<in> env_dom \<E>
        \<Longrightarrow> (env_lookup_instance \<E> x \<iota> = Some x_\<iota>
            \<and> v = x_\<iota> @ take 1 (heap_pkt_in h)
            \<and> length x_\<iota> = header_length \<eta> - n
            \<and> env_lookup_packet \<E> x PktIn = Some []
            \<and> env_lookup_packet \<E> x PktOut = Some [])"
      and x_not_in_\<E>: "x \<notin> env_dom \<E> \<Longrightarrow> (v = take 1 (heap_pkt_in h))
                    \<and> atom x \<sharp> e
                    \<and> header_length \<eta> = n"
      and has_pkt_in: "length (heap_pkt_in h) \<ge> 1" (* Is required I think, implied in the paper by h(pktIn)[0:1] being well-defined *)
      and "n \<ge> 1"
      and "n \<le> header_length \<eta>"
      and "x \<noteq> y" (* Not sure about this, paper doesn't state it, but I do think needs it? *)
      and "\<lbrakk>e in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some res"
(* TODO: y just appears in the lemma. It probably needs freshness assumptions? *)
  shows "(\<lbrakk>heapRef\<^sub>1\<^sub>e (chomp\<^sub>1\<^sub>e e y) x \<iota> (header_length \<eta>) n in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e) = (\<lbrakk>e in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e)"
proof -
  let ?ref_chomp = "\<lambda>e. heapRef\<^sub>1\<^sub>e (chomp\<^sub>1\<^sub>e e y) x \<iota> (header_length \<eta>) n"
  let ?sz = "header_length \<eta>"
  have "(\<exists>res. \<lbrakk>e in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some res) \<Longrightarrow> (x \<notin> env_dom \<E> \<longrightarrow> atom x \<sharp> e)  \<Longrightarrow> ?thesis"
  proof (induction e)
    case (Num n)
    then show ?case by (auto)
  next
    case (Bv bv)
    then obtain res where "\<lbrakk>Bv bv in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some res" by (auto)
    moreover have "unaffected_by_chomp\<^sub>e (Bv bv)" by (auto)
    ultimately have "?ref_chomp (Bv bv) = Bv bv" by (metis ref_chomp_unaffected\<^sub>e[where \<E> = "\<E>[y \<rightarrow> h]"])
    then show ?case by auto
  next
    case (Plus e\<^sub>1 e\<^sub>2)
    have "\<exists>v\<^sub>1. \<lbrakk>e\<^sub>1 in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some v\<^sub>1" using Plus.prems
      by (auto simp add: exp_sem_Plus_Some1)
    moreover have "\<exists>v\<^sub>2. \<lbrakk>e\<^sub>2 in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some v\<^sub>2" using Plus.prems
      by (auto simp add: exp_sem_Plus_Some2)
    ultimately have "\<lbrakk>?ref_chomp (Plus e\<^sub>1 e\<^sub>2) in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e = (\<lbrakk>Plus e\<^sub>1 e\<^sub>2 in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e)"
      using Plus by (auto simp add: fresh_def supp_Plus)
    then show ?case by (auto)
  next
    case (Concat e\<^sub>1 e\<^sub>2)
    have "\<exists>v\<^sub>1. \<lbrakk>e\<^sub>1 in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some v\<^sub>1" using Concat.prems
      by (auto simp add: exp_sem_Concat_Some1)
    moreover have "\<exists>v\<^sub>2. \<lbrakk>e\<^sub>2 in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some v\<^sub>2" using Concat.prems
      by (auto simp add: exp_sem_Concat_Some2)
    ultimately have "\<lbrakk>?ref_chomp (Concat e\<^sub>1 e\<^sub>2) in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e = (\<lbrakk>Concat e\<^sub>1 e\<^sub>2 in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e)"
      using Concat by (auto simp add: fresh_def supp_Concat)
    then show ?case by (auto)
  next
    case (Packet z pkt)
    show ?case proof (cases "z = y")
      assume "z \<noteq> y"
      then have "?ref_chomp (Packet z pkt) = Packet z pkt" by (cases pkt) (auto)
      then show ?case using Packet and assms and \<open>z \<noteq> y\<close> by (metis unchanged_packet_in_chomped_env)
    next
      assume "z = y"
      show ?case proof (cases pkt)
        assume "pkt = PktIn"
        have v_length: "?sz - n + 1 = length v"
          using x_in_\<E> x_not_in_\<E> has_pkt_in by (cases \<open>x \<in> env_dom \<E>\<close>) (auto)
        {
          have "env_lookup_instance (\<E>'[y \<rightarrow> h']) x \<iota> = Some v" using \<E>'_def and h'_def and \<open>x \<noteq> y\<close>
            by (auto simp add: env_lookup_instance_def env_update_def update_conv)

          then have "\<lbrakk>Slice (SlInstance x \<iota>) (?sz - n) (?sz + 1 - n) in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e
                      = Some (VBv [last v])" using v_length \<open>?sz \<ge> 1\<close> \<open>n \<ge> 1\<close> \<open>n \<le> ?sz\<close>
            by (auto) (metis Suc_diff_le diff_Suc_1 slice_last zero_less_Suc)

          then have "\<lbrakk>Concat (Slice (SlInstance x \<iota>) (?sz - n) (?sz + 1 - n)) (Bv []) in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e
                        = Some (VBv [last v])" using \<E>'_def \<open>?sz \<ge> 1\<close> v_length \<open>n \<ge> 1\<close> \<open>n \<le> ?sz\<close>
            by (auto simp add: bv_to_val_def)
        }
        moreover have "\<lbrakk>Packet y PktIn in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e = Some (VBv (heap_pkt_in h'))"
          by (auto simp add: env_lookup_packet_def)
        ultimately have "\<lbrakk>?ref_chomp (Packet y PktIn) in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e
          = Some (VBv ([last v] @ heap_pkt_in h'))" by (auto)
        moreover have "last v = hd (heap_pkt_in h)" using x_in_\<E> and x_not_in_\<E> proof (cases "x \<in> env_dom \<E>")
          assume "x \<in> env_dom \<E>"
          then have "\<exists>b. v = b @ take 1 (heap_pkt_in h)" using x_in_\<E> by (auto)
          then show "last v = hd (heap_pkt_in h)" using has_pkt_in
            by (metis One_nat_def hd_conv_nth last_appendR last_snoc length_greater_0_conv
                      order.strict_trans2 take_Suc_conv_app_nth take_eq_Nil2 zero_less_one zero_neq_one)
        next
          assume "x \<notin> env_dom \<E>"
          then show "last v = hd (heap_pkt_in h)" using x_not_in_\<E>
            by (auto) (metis hd_Nil_eq_last last_ConsL take0 take_Nil take_Suc)
        qed
        ultimately have "\<lbrakk>?ref_chomp (Packet y PktIn) in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e
          = Some (VBv (hd (heap_pkt_in h) # heap_pkt_in h'))" by (auto)
        moreover have "hd (heap_pkt_in h) # heap_pkt_in h' = heap_pkt_in h"
          using h'_def has_pkt_in by (auto simp add: chomp\<^sub>S_def drop_Suc)
                                     (metis Suc_n_not_le_n hd_Cons_tl list.size(3))
        moreover have "\<lbrakk>Packet z PktIn in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some (VBv (heap_pkt_in h))"
          using \<open>z = y\<close> by (auto simp add: env_lookup_packet_def)
        ultimately show ?case using \<open>z = y\<close> and \<open>pkt = PktIn\<close> by (auto)
      next
        assume "pkt = PktOut"
        then have ref_chomp_nop: "?ref_chomp (Packet z pkt) = Packet z pkt" by (auto)
        have "env_lookup_packet \<E>[y \<rightarrow> h] y PktOut = Some (heap_pkt_out h)"
          by (auto simp add: env_lookup_packet_def)
        moreover have "env_lookup_packet \<E>'[y \<rightarrow> h'] y PktOut = Some (heap_pkt_out h)"
          using h'_def by (auto simp add: env_lookup_packet_def chomp\<^sub>S_def)
        ultimately show ?case using ref_chomp_nop and \<open>z = y\<close> and \<open>pkt = PktOut\<close> by (auto)
      qed
    qed
  next
    case (Len z pkt)
    then show ?case sorry
  next
    case (Slice sl n m)
    then show ?case sorry
  qed
  then show ?thesis using assms by auto
qed

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