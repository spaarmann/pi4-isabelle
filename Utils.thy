theory Utils imports Syntax begin

definition slice :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "slice xs n m = take (m - n) (drop n xs)"

lemma slice_last: "length xs > 0 \<Longrightarrow> slice xs (length xs - 1) (length xs) = [last xs]" 
  by (auto simp add: slice_def)
     (metis One_nat_def append_butlast_last_id append_eq_conv_conj length_butlast)

text\<open>Replaces [n:m) in the first input list with the second list.\<close>
definition splice :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "splice xs n m ins = (slice xs 0 n) @ ins @ (slice xs m (length xs))"


section\<open>Nominal2 Lemmas\<close>

lemma bind_eqvt[eqvt]: "p \<bullet> Option.bind x f = Option.bind (p \<bullet> x) (p \<bullet> f)"
  by (cases x) auto

lemma map_of_eqvt[eqvt]: "p \<bullet> map_of xs x = map_of (p \<bullet> xs) (p \<bullet> x)"
  by (induct xs) auto

lemma concat_eqvt[eqvt]: "p \<bullet> (concat xss) = concat (p \<bullet> xss)"
  by (induction xss) (auto simp add: append_eqvt)

lemma alist_update_eqvt[eqvt]: "p \<bullet> AList.update k v xs = AList.update (p \<bullet> k) (p \<bullet> v) (p \<bullet> xs)"
  by (induction xs) (auto)

lemma fresh_star_empty[simp]: "{} \<sharp>* x" by (simp add: fresh_star_def)


section\<open>Bitvectors\<close>

lemma bv_to_bools_some:
  assumes "bv_to_bools bv = Some bits"
  shows "BitVar \<notin> set bv"
  sorry

section\<open>Headers\<close>

definition empty_headers :: headers where "empty_headers = Map.empty"
declare empty_headers_def[simp]

fun header_field_to_range_helper :: "nat \<Rightarrow> field list \<Rightarrow> field_name \<Rightarrow> (nat \<times> nat)" where
  "header_field_to_range_helper acc (f#fs) tgt = (if field_name f = tgt then (acc, acc + field_length f)
    else header_field_to_range_helper (acc + field_length f) fs tgt)" |
  "header_field_to_range_helper acc [] tgt = undefined"

definition header_field_to_range :: "header_type \<Rightarrow> field_name \<Rightarrow> (nat \<times> nat)" where
  "header_field_to_range \<eta> tgt = header_field_to_range_helper 0 (header_fields \<eta>) tgt"
lemma header_field_to_range_eqvt[eqvt]:
  "p \<bullet> header_field_to_range \<eta> f = header_field_to_range (p \<bullet> \<eta>) (p \<bullet> f)"
  by (simp add: permute_pure)

fun field_list_to_range :: "field list \<Rightarrow> field_name \<Rightarrow> (nat \<times> nat)" where
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


section\<open>Heaps\<close>

definition empty_heap :: "heap" where
  "empty_heap = \<lparr> heap_pkt_in = [], heap_pkt_out = [], headers = empty_headers \<rparr>"
declare empty_heap_def[simp]

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


section\<open>Environments\<close>

definition env_dom :: "env \<Rightarrow> var set" where
  "env_dom \<E> = fst ` set (heaps \<E>)"

lemma env_heaps_eqvt[eqvt]: "p \<bullet> heaps \<E> = heaps (p \<bullet> \<E>)"
  by (simp add: permute_env_ext_def)

definition env_lookup_packet :: "env \<Rightarrow> var \<Rightarrow> packet \<Rightarrow> bv option" where
  "env_lookup_packet \<E> x p = map_option (\<lambda>h. heap_lookup_packet h p) (map_of (heaps \<E>) x)"
lemma env_lookup_packet_eqvt[eqvt]:
  "p \<bullet> env_lookup_packet \<E> x pkt = env_lookup_packet (p \<bullet> \<E>) (p \<bullet> x) (p \<bullet> pkt)"
  by (simp add: env_lookup_packet_def permute_packet_def)

lemma env_lookup_packet_update_other:
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

fun env_lookup_sliceable :: "env \<Rightarrow> sliceable \<Rightarrow> bv option" where
  "env_lookup_sliceable \<E> (SlPacket x p) = env_lookup_packet \<E> x p" |
  "env_lookup_sliceable \<E> (SlInstance x \<iota>) = env_lookup_instance \<E> x \<iota>"
lemma env_lookup_sliceable_eqvt[eqvt]:
  "p \<bullet> env_lookup_sliceable \<E> sl = env_lookup_sliceable (p \<bullet> \<E>) (p \<bullet> sl)"
  by (cases sl) (auto)

lemma env_update_eqvt[eqvt]: "p \<bullet> \<E>[x \<rightarrow> h] = (p \<bullet> \<E>)[p \<bullet> x \<rightarrow> p \<bullet> h]"  
  by (cases \<E>) (auto simp add: permute_pure env_update_def permute_env_ext_def)


section\<open>Helpers for creating expressions\<close>

definition mk_inst_read :: "header_type \<Rightarrow> instanc \<Rightarrow> var \<Rightarrow> exp" where
  "mk_inst_read \<eta> \<iota> x = (let hl = header_length \<eta> in Slice (SlInstance x \<iota>) 0 hl)"
lemma mk_inst_read_eqvt[eqvt]:
  "p \<bullet> mk_inst_read \<eta> \<iota> x = mk_inst_read (p \<bullet> \<eta>) (p \<bullet> \<iota>) (p \<bullet> x)"
  by (simp add: mk_inst_read_def permute_pure)

definition mk_field_read :: "header_type \<Rightarrow> instanc \<Rightarrow> field_name \<Rightarrow> var \<Rightarrow> exp" where
  "mk_field_read \<eta> \<iota> f x = (let (n, m) = header_field_to_range \<eta> f in Slice (SlInstance x \<iota>) n m)"
lemma mk_field_read_eqvt[eqvt]:
  "p \<bullet> mk_field_read \<eta> \<iota> f x = mk_field_read (p \<bullet> \<eta>) (p \<bullet> \<iota>) (p \<bullet> f) (p \<bullet> x)"
  by (auto simp add: mk_field_read_def permute_pure)


section\<open>Helper for creating formulas\<close>

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