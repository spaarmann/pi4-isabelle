theory Utils imports Syntax begin

definition slice :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "slice xs n m = take (m - n) (drop n xs)"

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


section\<open>Headers\<close>

definition empty_headers :: headers where "empty_headers = Map.empty"

fun header_field_to_range_helper :: "nat \<Rightarrow> field list \<Rightarrow> field_name \<Rightarrow> (nat \<times> nat)" where
  "header_field_to_range_helper acc (f#fs) tgt = (if field_name f = tgt then (acc, acc + field_length f)
    else header_field_to_range_helper (acc + field_length f) fs tgt)" |
  "header_field_to_range_helper acc [] tgt = undefined"

fun header_field_to_range :: "header_type \<Rightarrow> field_name \<Rightarrow> (nat \<times> nat)" where
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

definition heap_dom :: "heap \<Rightarrow> instanc set" where
  "heap_dom h = dom (heap_headers h)"

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

lemma env_heaps_eqvt[eqvt]: "p \<bullet> heaps \<E> = heaps (p \<bullet> \<E>)"
  by (simp add: permute_env_ext_def)

definition env_lookup_packet :: "env \<Rightarrow> var \<Rightarrow> packet \<Rightarrow> bv option" where
  "env_lookup_packet \<E> x p = map_option (\<lambda>h. heap_lookup_packet h p) (map_of (heaps \<E>) x)"
lemma env_lookup_packet_eqvt[eqvt]:
  "p \<bullet> env_lookup_packet \<E> x pkt = env_lookup_packet (p \<bullet> \<E>) (p \<bullet> x) (p \<bullet> pkt)"
  by (simp add: env_lookup_packet_def permute_packet_def)

definition env_lookup_instance :: "env \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> bv option" where
  "env_lookup_instance \<E> x \<iota> = Option.bind (map_of (heaps \<E>) x) (\<lambda>h. heap_lookup_instance h \<iota>)"
lemma env_lookup_instance_eqvt[eqvt]:
  "p \<bullet> env_lookup_instance \<E> x \<iota> = env_lookup_instance (p \<bullet> \<E>) (p \<bullet> x) (p \<bullet> \<iota>)"
  by (simp add: env_lookup_instance_def) (simp add: permute_pure)

nominal_function env_lookup_sliceable :: "env \<Rightarrow> sliceable \<Rightarrow> bv option" where
  "env_lookup_sliceable \<E> (SlPacket x p) = env_lookup_packet \<E> x p" |
  "env_lookup_sliceable \<E> (SlInstance x \<iota>) = env_lookup_instance \<E> x \<iota>"
  subgoal by (simp add: eqvt_def env_lookup_sliceable_graph_aux_def
                        env_lookup_packet_def env_lookup_instance_def)
  subgoal by (erule env_lookup_sliceable_graph.induct) (auto)
  apply clarify
  subgoal for P \<E> s
    by (rule sliceable.strong_exhaust[of s P]) (auto)
  apply (simp_all)
done
nominal_termination (eqvt)
  by lexicographic_order

definition env_resolve_bit :: "env \<Rightarrow> bit \<Rightarrow> bool option" where
  "env_resolve_bit \<E> b = (case b of
    Zero \<Rightarrow> Some False |
    One \<Rightarrow> Some True |
    BitVar n \<Rightarrow> (map_of (bits \<E>) n))"
lemma env_resolve_bit_eqvt[eqvt]: "p \<bullet> env_resolve_bit \<E> b = env_resolve_bit (p \<bullet> \<E>) (p \<bullet> b)"
  by (cases b) (auto simp add: env_resolve_bit_def permute_pure env_permute_bits)
lemma env_resolve_bit_permute: "env_resolve_bit (p \<bullet> \<E>) b = env_resolve_bit \<E> b"
  by (cases b) (auto simp add: env_resolve_bit_def env_permute_bits)

definition env_resolve_bits :: "env \<Rightarrow> bv \<Rightarrow> bool list option" where
  "env_resolve_bits \<E> bv = List.those (map (\<lambda>b. env_resolve_bit \<E> b) bv)"
lemma env_resolve_bits_eqvt[eqvt]: "p \<bullet> env_resolve_bits \<E> bv = env_resolve_bits (p \<bullet> \<E>) (p \<bullet> bv)"
  by (auto simp add: env_resolve_bits_def permute_pure env_resolve_bit_permute)

definition env_resolve_bits_option :: "env \<Rightarrow> bv option \<Rightarrow> bool list option" where
  "env_resolve_bits_option \<E> bv = Option.bind bv (\<lambda>bits. env_resolve_bits \<E> bits)"
lemma env_resolve_bits_option_eqvt[eqvt]:
  "p \<bullet> env_resolve_bits_option \<E> bv = env_resolve_bits_option (p \<bullet> \<E>) (p \<bullet> bv)"
  by (auto simp add: env_resolve_bits_option_def permute_pure env_resolve_bits_def env_resolve_bit_permute)

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
  by (simp add: mk_field_read_def permute_pure)

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