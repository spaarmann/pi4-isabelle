theory Chomp_Correctness imports Chomp Types begin

section\<open>Correctness of Chomp\<close>

subsection\<open>Helpers for the main proofs below\<close>

inductive unaffected_by_chomp\<^sub>e :: "exp \<Rightarrow> bool" where
  "unaffected_by_chomp\<^sub>e (Num _)" |
  "unaffected_by_chomp\<^sub>e (Bv _)" |
  "unaffected_by_chomp\<^sub>e (Packet _ PktOut)" |
  "unaffected_by_chomp\<^sub>e (Len _ PktOut)" |
  "unaffected_by_chomp\<^sub>e (Slice (SlInstance _ _) _)" |
  "unaffected_by_chomp\<^sub>e (Slice (SlPacket _ PktOut) _)" |
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
    case (Slice sl rng)
    show ?case proof (cases sl)
      case (SlPacket z pkt)
      from Slice.prems(2) and SlPacket have "pkt = PktOut" by (cases) (auto)
      then show "Slice sl rng = ?ref_chomp (Slice sl rng)" using Slice and SlPacket by (auto)
    next
      case (SlInstance z \<iota>)
      then show "Slice sl rng = ?ref_chomp (Slice sl rng)" using Slice by (auto)
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
  
  have last_v: "last v = hd (heap_pkt_in h)" using x_in_\<E> and x_not_in_\<E>
  proof (cases "x \<in> env_dom \<E>")
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

  have v_length: "?sz - n + 1 = length v"
    using x_in_\<E> x_not_in_\<E> has_pkt_in by (cases \<open>x \<in> env_dom \<E>\<close>) (auto)
  
  have "env_lookup_instance (\<E>'[y \<rightarrow> h']) x \<iota> = Some v" using \<E>'_def and h'_def and \<open>x \<noteq> y\<close>
    by (auto simp add: env_lookup_instance_def env_update_def update_conv)
  moreover {
    have "length v > 0" using v_length \<open>n \<le> ?sz\<close> by (auto)
    then have "slice v (slice_range_one (length v - 1)) = [last v]"
      by (rule slice_last)
    moreover have "?sz - n = length v - 1" using v_length by (simp)
    ultimately have "slice v (slice_range_one (?sz - n)) = [last v]" by (simp)
  }
  ultimately have "\<lbrakk>Slice (SlInstance x \<iota>) (slice_range_one (?sz - n)) in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e
              = Some (VBv [last v])" using v_length \<open>?sz \<ge> 1\<close> \<open>n \<ge> 1\<close> \<open>n \<le> ?sz\<close>
    by (auto)
  then have slice_x_\<iota>_last_v:
    "\<lbrakk>Concat (Slice (SlInstance x \<iota>) (slice_range_one (?sz - n))) (Bv []) in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e
      = Some (VBv [last v])"
    using \<E>'_def \<open>?sz \<ge> 1\<close> v_length \<open>n \<ge> 1\<close> \<open>n \<le> ?sz\<close>
    by (auto simp add: bv_to_val_def)

  have reconstruct_heap_pkt_in: "hd (heap_pkt_in h) # heap_pkt_in h' = heap_pkt_in h"
    using h'_def has_pkt_in by (auto simp add: chomp\<^sub>S_def drop_Suc)
                               (metis Suc_n_not_le_n hd_Cons_tl list.size(3))

  have "(\<exists>res. \<lbrakk>e in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some res) \<Longrightarrow> (x \<notin> env_dom \<E> \<longrightarrow> atom x \<sharp> e) \<Longrightarrow> ?thesis"
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
        have "\<lbrakk>Packet y PktIn in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e = Some (VBv (heap_pkt_in h'))"
          by (auto simp add: env_lookup_packet_def)
        then have "\<lbrakk>?ref_chomp (Packet y PktIn) in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e
          = Some (VBv ([last v] @ heap_pkt_in h'))" using slice_x_\<iota>_last_v by (auto)
        also then have "... = Some (VBv (hd (heap_pkt_in h) # heap_pkt_in h'))"
          using last_v by (auto)
        moreover have "\<lbrakk>Packet z PktIn in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some (VBv (heap_pkt_in h))"
          using \<open>z = y\<close> by (auto simp add: env_lookup_packet_def)
        ultimately show ?case using \<open>z = y\<close> \<open>pkt = PktIn\<close> reconstruct_heap_pkt_in by (auto)
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
    show ?case proof (cases \<open>z = y\<close>)
      assume "z = y"
      then show ?case proof (cases pkt)
        assume "pkt = PktIn"
        then have "?ref_chomp (Len y pkt) = Plus (Num 1) (Len y pkt)" by (auto)
        then show ?case using \<open>z = y\<close> \<open>pkt = PktIn\<close> h'_def chomp\<^sub>S_def has_pkt_in
          by (auto simp add: env_lookup_packet_def)
      next
        assume "pkt = PktOut"
        then have "?ref_chomp (Len y pkt) = Len y pkt" by (auto)
        then show ?case using \<open>z = y\<close> \<open>pkt = PktOut\<close> h'_def chomp\<^sub>S_def
          by (auto simp add: env_lookup_packet_def)
      qed
    next
      assume "z \<noteq> y"
      then have ref_chomp_nop: "?ref_chomp (Len z pkt) = Len z pkt" by (cases pkt) (auto)
      show ?case proof (cases \<open>z = x\<close>)
        assume "z = x"
        have "atom x \<sharp> Len x pkt \<Longrightarrow> False" by (metis fresh_at_base(2) fresh_def supp_Len)
        then show ?case using \<open>z = x\<close> \<open>z \<noteq> y\<close> \<E>'_def x_in_\<E> x_not_in_\<E> Len
          by (cases \<open>x \<in> env_dom \<E>\<close>; cases pkt) (auto simp add: env_lookup_packet_def)
      next
        assume "z \<noteq> x"
        from \<open>z \<noteq> x\<close> \<open>z \<noteq> y\<close> have "\<lbrakk>Len z pkt in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = (\<lbrakk>Len z pkt in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e)"
          using \<E>'_def by (auto simp add: env_lookup_packet_def)
        then show ?case using ref_chomp_nop by (auto)
      qed
    qed
  next
    case (Slice sl rng)
    show ?case proof (cases sl)
      fix z pkt
      assume SlPacket: "sl = SlPacket z pkt"
      show ?case proof (cases \<open>z = y\<close>)
        assume "z \<noteq> y"
        then have ref_chomp_nop: "?ref_chomp (Slice sl rng) = Slice sl rng" using SlPacket
          by (cases pkt) (auto)
        then show ?case proof (cases \<open>z = x\<close>)
          assume "z = x"
          have "atom x \<sharp> Slice (SlPacket x pkt) rng \<Longrightarrow> False"
            by (metis fresh_at_base(2) fresh_def supp_Slice supp_SlPacket)
          then show ?case
            using \<open>z = x\<close> \<open>z \<noteq> y\<close> ref_chomp_nop \<E>'_def x_in_\<E> x_not_in_\<E> SlPacket Slice(2)
            by (cases \<open>x \<in> env_dom \<E>\<close>; cases pkt) (auto simp add: env_lookup_packet_def)
        next
          assume "z \<noteq> x"
          then show ?case using \<open>z \<noteq> y\<close> ref_chomp_nop SlPacket \<E>'_def
            by (auto simp add: env_lookup_packet_def)
        qed
      next
        assume "z = y"
        show ?case proof (cases pkt)
          assume "pkt = PktIn"
          show ?case proof (cases \<open>right rng \<le> 1\<close>)
            assume "right rng \<le> 1"
            then have "left rng = 0" by (transfer) (auto)
            moreover have "right rng = 1" using \<open>right rng \<le> 1\<close> by (transfer) (auto)
            ultimately have rng_val: "rng = slice_range 0 1" by (transfer) (auto)

            have "\<lbrakk>?ref_chomp (Slice sl rng) in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e = Some (VBv [last v])"
              using SlPacket \<open>z = y\<close> \<open>pkt = PktIn\<close> slice_x_\<iota>_last_v rng_val
              by (auto)
            also have "... = Some (VBv [hd (heap_pkt_in h)])" using last_v by (auto)

            moreover have "\<lbrakk>Slice sl rng in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some (VBv [hd (heap_pkt_in h)])"
              using SlPacket \<open>z = y\<close> \<open>pkt = PktIn\<close> rng_val has_pkt_in
              apply (auto simp add: env_lookup_packet_def)
              using order.strict_trans2 slice_head by (auto)

            ultimately show ?case by (auto)
          next
            assume r_gt_1: "\<not>(right rng \<le> 1)"
            then show ?case proof (cases \<open>left rng = 0\<close>)
              assume "left rng = 0"
              let ?chomped = "Concat (Concat (Slice (SlInstance x \<iota>) (slice_range_one (?sz - n)))
                                             (Bv []))
                                     (Slice (SlPacket y PktIn) (slice_range 0 (right rng - 1)))"
              have rc: "?ref_chomp (Slice sl rng) = ?chomped"
                using SlPacket \<open>z = y\<close> \<open>pkt = PktIn\<close> \<open>left rng = 0\<close> r_gt_1 by (auto)
              
              obtain r::"val option" where r_def: "\<lbrakk>Slice (SlPacket y PktIn) rng in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = r"
                by (auto)
              show ?case proof (cases r)
                assume "r = None"
                then have "right rng > length (heap_pkt_in h)" using r_def
                  by (auto simp add: env_lookup_packet_def) (meson leI option.discI)
                then have "right rng - 1 > length (heap_pkt_in h')"
                  using h'_def r_gt_1 by (auto simp add: chomp\<^sub>S_def)
                then have "\<lbrakk>?chomped in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e = None"
                  (* It should be possible to prove this without the Slice.prems(1), if that becomes
                     necessary later. *)
                  using SlPacket \<open>z = y\<close> \<open>pkt = PktIn\<close> Slice.prems(1) r_def \<open>r = None\<close> by (auto)
                then show ?case using rc r_def \<open>r = None\<close> SlPacket \<open>z = y\<close> \<open>pkt = PktIn\<close> by (simp)
              next
                fix val
                assume "r = Some val"
                then have right_valid: "right rng \<le> length (heap_pkt_in h)" using r_def
                  by (auto simp add: env_lookup_packet_def) (metis option.discI)
                moreover have "length (heap_pkt_in h') = length (heap_pkt_in h) - 1"
                  using h'_def by (auto simp add: chomp\<^sub>S_def)
                ultimately have "right (slice_range 0 (right rng - 1)) \<le> length (heap_pkt_in h')"
                   using r_gt_1 by (auto)

                then have "\<lbrakk>?chomped in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e
                  = Some (VBv ([hd (heap_pkt_in h)]
                               @ slice (heap_pkt_in h') (slice_range 0 (right rng - 1))))"
                  using slice_x_\<iota>_last_v last_v by (auto simp add: env_lookup_packet_def)

                moreover have "hd (heap_pkt_in h) # slice (heap_pkt_in h') (slice_range 0 (right rng - 1))
                  = slice (heap_pkt_in h) (slice_range 0 (right rng))"
                  using h'_def reconstruct_heap_pkt_in apply (auto simp add: chomp\<^sub>S_def)
                  using has_pkt_in r_gt_1
                  by (metis One_nat_def leI length_Cons slice_prepend zero_less_Suc)

                moreover have "\<lbrakk>Slice sl rng in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e
                  = Some (VBv (slice (heap_pkt_in h) (slice_range 0 (right rng))))"
                  using SlPacket \<open>z = y\<close> \<open>pkt = PktIn\<close> \<open>left rng = 0\<close> \<open>r = Some val\<close> right_valid
                        r_gt_1
                  apply (auto simp add: env_lookup_packet_def) using right_range_left_0 by presburger

                ultimately show ?case using rc by (auto simp add: env_lookup_packet_def)
              qed
            next
              assume "left rng \<noteq> 0"
              obtain r::"val option" where r_def: "\<lbrakk>Slice (SlPacket y PktIn) rng in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = r"
                by (auto)

              have rc: "?ref_chomp (Slice sl rng) = Slice (SlPacket y PktIn) (slice_range_sub rng 1)"
                using r_gt_1 \<open>left rng \<noteq> 0\<close> \<open>z = y\<close> SlPacket \<open>pkt = PktIn\<close> by (auto)

              show ?case proof (cases r)
                assume "r = None"
                then have "right rng > length (heap_pkt_in h)" using r_def
                  by (auto simp add: env_lookup_packet_def) (meson leI option.discI)
                moreover then have "right (slice_range_sub rng 1) > length (heap_pkt_in h')"
                  using h'_def \<open>left rng \<noteq> 0\<close> by (transfer) (auto simp add: chomp\<^sub>S_def)
                ultimately show ?case using rc SlPacket \<open>z = y\<close> \<open>pkt = PktIn\<close>
                  by (auto simp add: env_lookup_packet_def)
              next
                fix val
                assume "r = Some val"
                then have right_valid: "right rng \<le> length (heap_pkt_in h)" using r_def
                  by (auto simp add: env_lookup_packet_def) (metis option.discI)
                moreover have "length (heap_pkt_in h') = length (heap_pkt_in h) - 1"
                  using h'_def by (auto simp add: chomp\<^sub>S_def)
                ultimately have "right (slice_range_sub rng 1) \<le> length (heap_pkt_in h')"
                  using \<open>left rng \<noteq> 0\<close> by (transfer) (auto)

                then have rc_res: "\<lbrakk>?ref_chomp (Slice sl rng) in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e
                  = Some (VBv (slice (heap_pkt_in h') (slice_range_sub rng 1)))"
                  using rc by (auto simp add: env_lookup_packet_def)

                moreover have "\<lbrakk>Slice sl rng in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some (VBv (slice (heap_pkt_in h) rng))"
                  using r_def SlPacket \<open>pkt = PktIn\<close> \<open>z = y\<close> \<open>r = Some val\<close> right_valid
                  by (auto simp add: env_lookup_packet_def)
                moreover have "slice (heap_pkt_in h) rng = slice (heap_pkt_in h') (slice_range_sub rng 1)"
                  using h'_def \<open>left rng \<noteq> 0\<close> by (auto simp add: chomp\<^sub>S_def slice_drop)

                ultimately show ?case by (auto)
              qed
            qed
          qed
        next
          assume "pkt = PktOut"
          then have rc_nop: "?ref_chomp (Slice sl rng) = Slice sl rng" using SlPacket by (auto)
          show ?case proof (cases \<open>z = x\<close>)
            assume "z \<noteq> x"
            then have "\<lbrakk>Slice sl rng in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = (\<lbrakk>Slice sl rng in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e)"
              using SlPacket \<open>pkt = PktOut\<close> \<E>'_def h'_def
              by (cases \<open>z = y\<close>) (auto simp add: env_lookup_packet_def chomp\<^sub>S_def)
            then show ?case using rc_nop by (auto)
          next
            assume "z = x"
            then show ?case using \<open>z = y\<close> \<open>x \<noteq> y\<close> by (auto)
          qed
        qed
      qed
    next
      fix z \<iota>'
      assume SlInstance: "sl = SlInstance z \<iota>'"
      then have ref_chomp_nop: "?ref_chomp (Slice sl rng) = Slice sl rng" by (auto)
      show ?case proof (cases \<open>z = y\<close>)
        assume "z = y"
        then show ?case using ref_chomp_nop SlInstance h'_def chomp\<^sub>S_def
          by (auto simp add: env_lookup_instance_def)
      next
        assume "z \<noteq> y"
        show ?case proof (cases \<open>z = x\<close>)
          assume "z = x"
          then show ?case sorry (* oh oh. Maybe \<E>' should just update x's heap instead of replacing it? *)
        next
          assume "z \<noteq> x"
          then show ?case using \<open>z \<noteq> y\<close> ref_chomp_nop SlInstance \<E>'_def
            by (auto simp add: env_lookup_instance_def)
        qed
      qed
    qed
  qed
  then show ?thesis using assms by auto
qed

lemma semantic_chomp_formula:
  fixes \<phi>::formula and h::heap and h'::heap and \<E>::env and \<E>'::env and x::var and \<iota>::instanc
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
                    \<and> atom x \<sharp> \<phi>
                    \<and> header_length \<eta> = n"
      and has_pkt_in: "length (heap_pkt_in h) \<ge> 1" (* Is required I think, implied in the paper by h(pktIn)[0:1] being well-defined *)
      and "n \<ge> 1"
      and "n \<le> header_length \<eta>"
      and "x \<noteq> y" (* Not sure about this, paper doesn't state it, but I do think needs it? *)
      and "\<lbrakk>\<phi> in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>f = Some res"
(* TODO: y just appears in the lemma. It probably needs freshness assumptions? *)
  shows "(\<lbrakk>heapRef\<^sub>1\<^sub>\<phi> (chomp\<^sub>1\<^sub>\<phi> \<phi> y) x \<iota> (header_length \<eta>) n in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>f) = (\<lbrakk>\<phi> in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>f)"
proof -
  let ?ref_chomp = "\<lambda>\<phi>. heapRef\<^sub>1\<^sub>\<phi> (chomp\<^sub>1\<^sub>\<phi> \<phi> y) x \<iota> (header_length \<eta>) n"
  let ?ref_chomp\<^sub>e = "\<lambda>\<phi>. heapRef\<^sub>1\<^sub>e (chomp\<^sub>1\<^sub>e \<phi> y) x \<iota> (header_length \<eta>) n"
  have "(\<exists>res. \<lbrakk>\<phi> in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>f = Some res) \<Longrightarrow> (x \<notin> env_dom \<E> \<longrightarrow> atom x \<sharp> \<phi>) \<Longrightarrow> ?thesis"
  proof (induction \<phi>)
    case FTrue show ?case by (auto) next
    case FFalse show ?case by (auto) next
    case (Eq e\<^sub>1 e\<^sub>2)
      have "\<exists> val\<^sub>1. \<lbrakk>e\<^sub>1 in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e = Some val\<^sub>1" using Eq.prems by (auto)
      then have "\<lbrakk>?ref_chomp\<^sub>e e\<^sub>1 in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e = (\<lbrakk>e\<^sub>1 in \<E>[y \<rightarrow> h]\<rbrakk>\<^sub>e)" using assms by (simp add: semantic_chomp_exp)

      have "\<lbrakk>?ref_chomp (Eq e\<^sub>1 e\<^sub>2) in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>f
        = (\<lbrakk>?ref_chomp\<^sub>e e\<^sub>1 in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e = (\<lbrakk>?ref_chomp\<^sub>e e\<^sub>2 in \<E>'[y \<rightarrow> h']\<rbrakk>\<^sub>e))"
      have "atom x \<sharp> (Eq e\<^sub>1 e\<^sub>2) \<Longrightarrow> atom x \<sharp> e\<^sub>1" by (auto simp add: fresh_def supp_Eq)
      moreover have "atom x \<sharp> (Eq e\<^sub>1 e\<^sub>2) \<Longrightarrow> atom x \<sharp> e\<^sub>2" by (auto simp add: fresh_def supp_Eq)
      ultimately show ?case by (auto simp add: semantic_chomp_exp)
  qed
  then show ?thesis using assms by (auto)
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