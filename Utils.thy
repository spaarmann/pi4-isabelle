theory Utils imports Syntax begin

section\<open>Utility functions and lemmas\<close>

subsection\<open>Slicing and Splicing\<close>

definition slice :: "'a list \<Rightarrow> slice_range \<Rightarrow> 'a list" where
  "slice xs rng = take (right rng - left rng) (drop (left rng) xs)"

lemma slice_head: "length xs > 0 \<Longrightarrow> slice xs (slice_range 0 1) = [hd xs]"
  unfolding slice_def by (simp add: take_Suc)

lemma slice_last: "length xs > 0 \<Longrightarrow> slice xs (slice_range_one (length xs - 1)) = [last xs]" 
  unfolding slice_def apply (simp)
  by (metis One_nat_def append_butlast_last_id append_eq_conv_conj length_butlast)

lemma slice_drop: "k \<le> left rng \<Longrightarrow> slice xs rng = slice (drop k xs) (slice_range_sub rng k)"
  unfolding slice_def by (transfer) (auto)

lemma slice_prepend: "length xs > 0 \<Longrightarrow> r > 1
  \<Longrightarrow> hd xs # slice (drop 1 xs) (slice_range 0 (r - 1)) = slice xs (slice_range 0 r)"
  unfolding slice_def apply (transfer) apply (auto)
  by (metis Cons_nth_drop_Suc Suc_lessD Suc_pred drop0 hd_conv_nth length_greater_0_conv take_Suc_Cons)

lemma slice_append: "right rng \<le> length xs \<Longrightarrow> slice xs rng = slice (xs @ ys) rng"
  unfolding slice_def by (auto)

text\<open>Replaces [n:m) in the first input list with the second list.\<close>
definition splice :: "'a list \<Rightarrow> slice_range \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "splice xs rng ins = (if left rng = 0
    then ins @ (slice xs (slice_range (right rng) (length xs)))
    else (slice xs (slice_range 0 (left rng))) @ ins @ (slice xs (slice_range (right rng) (length xs))))"


subsection\<open>Nominal2 Lemmas\<close>

text\<open>To prove equivariance of some of our definitions, we first show it for some built-in functions
that do not come with equivariance lemmas in Nominal2.\<close>

lemma bind_eqvt[eqvt]: "p \<bullet> Option.bind x f = Option.bind (p \<bullet> x) (p \<bullet> f)"
  by (cases x) auto

lemma map_of_eqvt[eqvt]: "p \<bullet> map_of xs x = map_of (p \<bullet> xs) (p \<bullet> x)"
  by (induct xs) auto

lemma concat_eqvt[eqvt]: "p \<bullet> (concat xss) = concat (p \<bullet> xss)"
  by (induction xss) (auto simp add: append_eqvt)

lemma alist_update_eqvt[eqvt]: "p \<bullet> AList.update k v xs = AList.update (p \<bullet> k) (p \<bullet> v) (p \<bullet> xs)"
  by (induction xs) (auto)

lemma fresh_star_empty[simp]: "{} \<sharp>* x" by (simp add: fresh_star_def)


subsection\<open>Headers\<close>

fun header_field_to_range_helper :: "nat \<Rightarrow> field list \<Rightarrow> field_name \<Rightarrow> slice_range" where
  "header_field_to_range_helper acc (f#fs) tgt = (if field_name f = tgt then slice_range acc (acc + field_length f)
    else header_field_to_range_helper (acc + field_length f) fs tgt)" |
  "header_field_to_range_helper acc [] tgt = undefined"

definition header_field_to_range :: "header_type \<Rightarrow> field_name \<Rightarrow> slice_range" where
  "header_field_to_range \<eta> tgt = header_field_to_range_helper 0 (header_fields \<eta>) tgt"
lemma header_field_to_range_eqvt[eqvt]:
  "p \<bullet> header_field_to_range \<eta> f = header_field_to_range (p \<bullet> \<eta>) (p \<bullet> f)"
  by (simp add: permute_pure)

fun field_list_to_range :: "field list \<Rightarrow> field_name \<Rightarrow> slice_range" where
  "field_list_to_range fs tgt = header_field_to_range_helper 0 fs tgt"
lemma field_list_to_range_eqvt[eqvt]:
  "p \<bullet> field_list_to_range fs tgt = field_list_to_range (p \<bullet> fs) (p \<bullet> tgt)"
  by (simp add: permute_pure)

definition header_length :: "header_type \<Rightarrow> nat" where
  "header_length ht = (\<Sum>f \<leftarrow> header_fields ht. field_length f)"
lemma header_length_eqvt[eqvt]: "p \<bullet> header_length ht = header_length (p \<bullet> ht)"
  by (auto simp add: permute_pure)

definition init_header :: "header_type \<Rightarrow> bv" where
  "init_header \<eta> = replicate (header_length \<eta>) Zero"

definition serialize_header :: "headers \<Rightarrow> instanc \<Rightarrow> bv option" where
  "serialize_header H i = H i"

definition deserialize_header :: "header_type \<Rightarrow> bv \<Rightarrow> (bv \<times> bv)" where
  "deserialize_header \<eta> In = (let len = header_length \<eta> in (take len In, drop len In))"

definition join_headers :: "headers \<Rightarrow> headers \<Rightarrow> headers" where
  "join_headers H\<^sub>1 H\<^sub>2 = (Map.map_add H\<^sub>1 H\<^sub>2)"


subsection\<open>Heaps\<close>

definition heap_dom :: "heap \<Rightarrow> instanc set" where
  "heap_dom h = dom (heap_headers h)"
declare heap_dom_def[simp]

fun heap_lookup_packet :: "heap \<Rightarrow> packet \<Rightarrow> bv" where
  "heap_lookup_packet h PktIn = heap_pkt_in h" |
  "heap_lookup_packet h PktOut = heap_pkt_out h"
lemma heap_lookup_packet_eqvt[eqvt]:
  "p \<bullet> heap_lookup_packet h pkt = heap_lookup_packet (p \<bullet> h) (p \<bullet> pkt)"
  by (simp add: permute_pure)

fun heap_lookup_instance :: "heap \<Rightarrow> instanc \<Rightarrow> bv option" where
  "heap_lookup_instance h \<iota> = (heap_headers h) \<iota>"
lemma heap_lookup_instance_eqvt[eqvt]:
  "p \<bullet> heap_lookup_instance h \<iota> = heap_lookup_instance (p \<bullet> h) (p \<bullet> \<iota>)"
  by (simp add: permute_pure)

no_notation map_add (infixl "++" 100) \<comment> \<open>avoid clash with built-in map_add notation\<close>
definition concat_heaps :: "heap \<Rightarrow> heap \<Rightarrow> heap" (infixl "++" 100) where
  "concat_heaps h\<^sub>1 h\<^sub>2
    = \<lparr>heap_pkt_in = heap_pkt_in h\<^sub>1 @ heap_pkt_in h\<^sub>2,
       heap_pkt_out = heap_pkt_out h\<^sub>1 @ heap_pkt_out h\<^sub>2,
       heap_headers = join_headers (heap_headers h\<^sub>1) (heap_headers h\<^sub>2)\<rparr>"
lemma concat_heaps_eqvt[eqvt]: "p \<bullet> concat_heaps h\<^sub>1 h\<^sub>2 = concat_heaps (p \<bullet> h\<^sub>1) (p \<bullet> h\<^sub>2)"
  by (simp add: permute_pure)


subsection\<open>Environments\<close>

definition env_dom :: "env \<Rightarrow> var set" where
  "env_dom \<E> = fst ` set (heaps \<E>)"

lemma env_heaps_eqvt[eqvt]: "p \<bullet> heaps \<E> = heaps (p \<bullet> \<E>)"
  by (simp add: permute_env_ext_def)

definition env_lookup_packet :: "env \<Rightarrow> var \<Rightarrow> packet \<Rightarrow> bv option" where
  "env_lookup_packet \<E> x p = map_option (\<lambda>h. heap_lookup_packet h p) (map_of (heaps \<E>) x)"
lemma env_lookup_packet_eqvt[eqvt]:
  "p \<bullet> env_lookup_packet \<E> x pkt = env_lookup_packet (p \<bullet> \<E>) (p \<bullet> x) (p \<bullet> pkt)"
  by (simp add: env_lookup_packet_def permute_packet_def)

lemma env_lookup_packet_update_same[simp]:
  "env_lookup_packet \<E>[x \<rightarrow> h] x pkt = Some (heap_lookup_packet h pkt)"
  by (auto simp add: env_lookup_packet_def)
lemma env_lookup_packet_update_other[simp]:
  "x \<noteq> y \<Longrightarrow> env_lookup_packet \<E>[y \<rightarrow> h] x pkt = env_lookup_packet \<E> x pkt"
proof -
  have "x \<noteq> y \<Longrightarrow> map_of (heaps \<E>) x = map_of (heaps \<E>[y \<rightarrow> h]) x" by (simp)
  moreover assume "x \<noteq> y"
  ultimately show ?thesis by (auto simp add: env_lookup_packet_def)
qed

definition env_lookup_instance :: "env \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> bv option" where
  "env_lookup_instance \<E> x \<iota> = Option.bind (map_of (heaps \<E>) x) (\<lambda>h. heap_lookup_instance h \<iota>)"
lemma env_lookup_instance_eqvt[eqvt]:
  "p \<bullet> env_lookup_instance \<E> x \<iota> = env_lookup_instance (p \<bullet> \<E>) (p \<bullet> x) (p \<bullet> \<iota>)"
  by (simp add: env_lookup_instance_def) (simp add: permute_pure)

lemma env_lookup_instance_update_same[simp]:
  "env_lookup_instance \<E>[x \<rightarrow> h] x \<iota> = heap_lookup_instance h \<iota>"
  by (auto simp add: env_lookup_instance_def)
lemma env_lookup_instance_update_other[simp]:
  "x \<noteq> y \<Longrightarrow> env_lookup_instance \<E>[y \<rightarrow> h] x \<iota> = env_lookup_instance \<E> x \<iota>"
  by (auto simp add: env_lookup_instance_def env_update_def update_conv)

fun env_lookup_sliceable :: "env \<Rightarrow> sliceable \<Rightarrow> bv option" where
  "env_lookup_sliceable \<E> (SlPacket x p) = env_lookup_packet \<E> x p" |
  "env_lookup_sliceable \<E> (SlInstance x \<iota>) = env_lookup_instance \<E> x \<iota>"
lemma env_lookup_sliceable_eqvt[eqvt]:
  "p \<bullet> env_lookup_sliceable \<E> sl = env_lookup_sliceable (p \<bullet> \<E>) (p \<bullet> sl)"
  by (cases sl) (auto)

lemma env_update_eqvt[eqvt]: "p \<bullet> \<E>[x \<rightarrow> h] = (p \<bullet> \<E>)[p \<bullet> x \<rightarrow> p \<bullet> h]"  
  by (cases \<E>) (auto simp add: permute_pure env_update_def permute_env_ext_def)


subsection\<open>Helpers for creating expressions\<close>

definition mk_inst_read :: "header_type \<Rightarrow> instanc \<Rightarrow> var \<Rightarrow> exp" where
  "mk_inst_read \<eta> \<iota> x = (let hl = header_length \<eta> in Slice (SlInstance x \<iota>) (slice_range 0 hl))"
lemma mk_inst_read_eqvt[eqvt]:
  "p \<bullet> mk_inst_read \<eta> \<iota> x = mk_inst_read (p \<bullet> \<eta>) (p \<bullet> \<iota>) (p \<bullet> x)"
  by (simp add: mk_inst_read_def permute_pure)

definition mk_field_read :: "header_type \<Rightarrow> instanc \<Rightarrow> field_name \<Rightarrow> var \<Rightarrow> exp" where
  "mk_field_read \<eta> \<iota> f x = (let rng = header_field_to_range \<eta> f in Slice (SlInstance x \<iota>) rng)"
lemma mk_field_read_eqvt[eqvt]:
  "p \<bullet> mk_field_read \<eta> \<iota> f x = mk_field_read (p \<bullet> \<eta>) (p \<bullet> \<iota>) (p \<bullet> f) (p \<bullet> x)"
  by (auto simp add: mk_field_read_def permute_pure)


subsection\<open>Helper for creating formulas\<close>

text\<open>Creates a formula that is the AND of all given subformulas.\<close>
fun mk_and :: "formula list \<Rightarrow> formula" where
  "mk_and [\<phi>] = \<phi>" |
  "mk_and (\<phi>#\<phi>s) = And \<phi> (mk_and \<phi>s)" |
  "mk_and [] = FTrue"
lemma mk_and_eqvt[eqvt]: "p \<bullet> mk_and \<phi>s = mk_and (p \<bullet> \<phi>s)"
  by (induction \<phi>s rule: mk_and.induct) (auto)

text\<open>Predicate for whether an entire instance is equal in the given two heaps.\<close>
definition mk_instance_eq :: "header_type \<Rightarrow> instanc \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula" where
  "mk_instance_eq \<eta> \<iota> x y = Eq (mk_inst_read \<eta> \<iota> x) (mk_inst_read \<eta> \<iota> y)"
lemma mk_instance_eq_eqvt[eqvt]:
  "p \<bullet> mk_instance_eq \<eta> \<iota> x y = mk_instance_eq (p \<bullet> \<eta>) (p \<bullet> \<iota>) (p \<bullet> x) (p \<bullet> y)"
  by (simp add: mk_instance_eq_def permute_pure Let_def)

text\<open>Instance equality:
Predicate for whether two heaps are equivalent in terms of all possible instances.
Corresponds to \<equiv>_i in the paper.\<close>
definition mk_heap_eq_instances :: "header_table \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula" where
  "mk_heap_eq_instances HT x y = mk_and [mk_instance_eq \<eta> \<iota> x y. (\<iota>, \<eta>) \<leftarrow> HT]"
lemma mk_heap_eq_instances_eqvt[eqvt]:
  "p \<bullet> mk_heap_eq_instances HT x y = mk_heap_eq_instances (p \<bullet> HT) (p \<bullet> x) (p \<bullet> y)"
  by (auto simp add: mk_heap_eq_instances_def permute_pure)

text\<open>Strict equality:
Predicate for whether two heaps are equal in all instances and the in/out buffers.
Corresponds to \<equiv> in the paper.\<close>
definition mk_heap_eq :: "header_table \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula" where
  "mk_heap_eq HT x y = And (Eq (Packet x PktIn) (Packet y PktIn))
                    (And (Eq (Packet x PktOut) (Packet y PktOut))
                    (mk_heap_eq_instances HT x y))"
lemma mk_heap_eq_eqvt[eqvt]: "p \<bullet> mk_heap_eq HT x y = mk_heap_eq (p \<bullet> HT) (p \<bullet> x) (p \<bullet> y)"
  by (simp add: mk_heap_eq_def permute_pure)

text\<open>Like mk_heap_eq_instances but ignoring the given instance.\<close>
definition mk_heap_eq_instances_except :: "header_table \<Rightarrow> instanc \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula"
where
  "mk_heap_eq_instances_except HT \<iota> x y = mk_heap_eq_instances [(\<kappa>,\<eta>)\<leftarrow>HT. \<kappa> \<noteq> \<iota>] x y"
lemma mk_heap_eq_instances_except_eqvt[eqvt]:
  "p \<bullet> mk_heap_eq_instances_except HT i x y = mk_heap_eq_instances_except (p \<bullet> HT) (p \<bullet> i) (p \<bullet> x) (p \<bullet> y)"
  by (simp add: mk_heap_eq_instances_except_def permute_pure)

definition mk_single_field_eq :: "header_type \<Rightarrow> instanc \<Rightarrow> field_name \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula"
where
  "mk_single_field_eq \<eta> \<iota> f x y = Eq (mk_field_read \<eta> \<iota> f x) (mk_field_read \<eta> \<iota> f y)"
lemma mk_single_field_eq_eqvt[eqvt]:
  "p \<bullet> mk_single_field_eq \<eta> f \<iota> x y = mk_single_field_eq (p \<bullet> \<eta>) (p \<bullet> f) (p \<bullet> \<iota>) (p \<bullet> x) (p \<bullet> y)"
  by (simp add: mk_single_field_eq_def permute_pure)

definition mk_fields_eq_except :: "header_type \<Rightarrow> instanc \<Rightarrow> field_name \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula"
where
  "mk_fields_eq_except \<eta> \<iota> g x y =
    mk_and [mk_single_field_eq \<eta> \<iota> (field_name f) x y. f \<leftarrow> header_fields \<eta>, field_name f \<noteq> g]"
lemma mk_fields_eq_except_eqvt[eqvt]:
  "p \<bullet> mk_fields_eq_except ht i g x y = mk_fields_eq_except (p \<bullet> ht) (p \<bullet> i) (p \<bullet> g) (p \<bullet> x) (p \<bullet> y)"
  by (simp add: mk_fields_eq_except_def permute_pure)

end