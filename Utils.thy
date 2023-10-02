theory Utils imports Syntax begin

fun slice :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "slice xs n m = take (m - n) (drop n xs)"

text\<open>Replaces [n:m) in the first input list with the second list.\<close>
fun splice :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "splice xs n m ins = (slice xs 0 n) @ ins @ (slice xs m (length xs))"

section\<open>Nominal2 Lemmas\<close>

lemma bind_eqvt[eqvt]: "p \<bullet> Option.bind x f = Option.bind (p \<bullet> x) (p \<bullet> f)"
  by (cases x) auto

lemma map_of_eqvt[eqvt]: "p \<bullet> map_of xs x = map_of (p \<bullet> xs) (p \<bullet> x)"
  by (induct xs) auto

lemma concat_eqvt[eqvt]: "p \<bullet> (concat xss) = concat (p \<bullet> xss)"
  by (induction xss) (auto simp add: append_eqvt)

lemma fresh_star_empty[simp]: "{} \<sharp>* x" by (simp add: fresh_star_def)

section\<open>Headers\<close>

text\<open>This is necessary to use headers (and heaps later)  in nominal_functions. It basically states
that no variables actually appear in the type.\<close>
instantiation headers :: pure begin
  definition permute_headers :: "perm \<Rightarrow> headers \<Rightarrow> headers" where
    "permute_headers _ x = x"
  instance by standard (auto simp add: permute_headers_def)
end

definition "empty_headers = Headers Map.empty"

fun header_lookup :: "headers \<Rightarrow> instanc \<Rightarrow> bv option" where
  "header_lookup (Headers h) i = h i" 

fun header_update :: "headers \<Rightarrow> instanc \<Rightarrow> bv \<Rightarrow> headers" where
  "header_update (Headers h) i bs = Headers (h(i := Some bs))"

fun header_field_to_range_helper :: "nat \<Rightarrow> field list \<Rightarrow> field_name \<Rightarrow> (nat \<times> nat)" where
  "header_field_to_range_helper acc ((Field fn fl)#fs) tgt = (if fn = tgt then (acc, acc + fl)
    else header_field_to_range_helper (acc + fl) fs tgt)" |
  "header_field_to_range_helper acc [] tgt = undefined"

fun header_field_to_range :: "header_type \<Rightarrow> field_name \<Rightarrow> (nat \<times> nat)" where
  "header_field_to_range (HeaderType _ fs) tgt = header_field_to_range_helper 0 fs tgt"
lemma header_field_to_range_eqvt[eqvt]:
  "p \<bullet> header_field_to_range ht f = header_field_to_range (p \<bullet> ht) (p \<bullet> f)"
  by (simp add: permute_pure)

fun field_list_to_range :: "field list \<Rightarrow> field_name \<Rightarrow> (nat \<times> nat)" where
  "field_list_to_range fs tgt = header_field_to_range_helper 0 fs tgt"
lemma field_list_to_range_eqvt[eqvt]:
  "p \<bullet> field_list_to_range fs tgt = field_list_to_range (p \<bullet> fs) (p \<bullet> tgt)"
  by (simp add: permute_pure)

fun header_length :: "header_type \<Rightarrow> nat" where
  "header_length (HeaderType _ fs) = (\<Sum>f\<leftarrow>fs. case f of field.Field x fl \<Rightarrow> fl)"

lemma header_length_eqvt[eqvt]: "p \<bullet> header_length ht = header_length (p \<bullet> ht)"
  by (auto simp add: permute_pure)

fun init_header :: "header_type \<Rightarrow> bv" where
  "init_header \<eta> = replicate (header_length \<eta>) False"

fun serialize_header :: "headers \<Rightarrow> instanc \<Rightarrow> bv option" where
  "serialize_header (Headers h) i = h i"

fun deserialize_header :: "header_type \<Rightarrow> bv \<Rightarrow> (bv \<times> bv)" where
  "deserialize_header \<eta> In = (let len = header_length \<eta> in (take len In, drop len In))"

fun join_headers :: "headers \<Rightarrow> headers \<Rightarrow> headers" where
  "join_headers (Headers h\<^sub>1) (Headers h\<^sub>2) = Headers (Map.map_add h\<^sub>1 h\<^sub>2)"

section\<open>Heaps\<close>

instantiation heap :: pure begin
  definition permute_heap :: "perm \<Rightarrow> heap \<Rightarrow> heap"  where
    "permute_heap _ x = x"
  instance by standard (auto simp add: permute_heap_def)
end

fun triple_to_heap :: "bv \<Rightarrow> bv \<Rightarrow> headers \<Rightarrow> heap" where
  "triple_to_heap In Out H = Heap In Out H"

fun heap_dom :: "heap \<Rightarrow> instanc set" where
  "heap_dom (Heap _ _ (Headers H)) = dom H"

fun heap_lookup_packet :: "heap \<Rightarrow> packet \<Rightarrow> bv" where
  "heap_lookup_packet (Heap In Out _) PktIn = In" |
  "heap_lookup_packet (Heap In Out _) PktOut = Out"

lemma heap_lookup_packet_eqvt[eqvt]:
  "p \<bullet> heap_lookup_packet h pkt = heap_lookup_packet (p \<bullet> h) (p \<bullet> pkt)"
  by (simp add: permute_pure)

fun heap_lookup_instance :: "heap \<Rightarrow> instanc \<Rightarrow> bv option" where
  "heap_lookup_instance (Heap _ _ (Headers insts)) i = insts i"

lemma heap_lookup_instance_eqvt[eqvt]:
  "p \<bullet> heap_lookup_instance h i = heap_lookup_instance (p \<bullet> h) (p \<bullet> i)"
  by (simp add: permute_pure)

no_notation map_add (infixl "++" 100) \<comment> \<open>avoid clash with built-in map_add notation\<close>
fun concat_heaps :: "heap \<Rightarrow> heap \<Rightarrow> heap" (infixl "++" 100) where
  "concat_heaps (Heap In\<^sub>1 Out\<^sub>1 H\<^sub>1) (Heap In\<^sub>2 Out\<^sub>2 H\<^sub>2)
    = Heap (In\<^sub>1 @ In\<^sub>2) (Out\<^sub>1 @ Out\<^sub>2) (join_headers H\<^sub>1 H\<^sub>2)"

lemma concat_heaps_eqvt[eqvt]: "p \<bullet> concat_heaps h\<^sub>1 h\<^sub>2 = concat_heaps (p \<bullet> h\<^sub>1) (p \<bullet> h\<^sub>2)"
  by (simp add: permute_pure)

section\<open>Environments\<close>

fun env_lookup_packet :: "env \<Rightarrow> var \<Rightarrow> packet \<Rightarrow> bv option" where
  "env_lookup_packet \<epsilon> x p = map_option (\<lambda>h. heap_lookup_packet h p) (map_of \<epsilon> x)"

fun env_lookup_instance :: "env \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> bv option" where
  "env_lookup_instance \<epsilon> x i = Option.bind (map_of \<epsilon> x) (\<lambda>h. heap_lookup_instance h i)"

nominal_function env_lookup_sliceable :: "env \<Rightarrow> sliceable \<Rightarrow> bv option" where
  "env_lookup_sliceable \<epsilon> (SlPacket x p) = env_lookup_packet \<epsilon> x p" |
  "env_lookup_sliceable \<epsilon> (SlInstance x i) = env_lookup_instance \<epsilon> x i"
  subgoal by (simp add: eqvt_def env_lookup_sliceable_graph_aux_def)
  subgoal by (erule env_lookup_sliceable_graph.induct) (auto)
  apply clarify
  subgoal for P e s
    by (rule sliceable.strong_exhaust[of s P]) (auto)
  apply (simp_all)
done
nominal_termination (eqvt)
  by lexicographic_order

lemma env_update_eqvt[eqvt]: "p \<bullet> \<epsilon>[x \<rightarrow> h] = (p \<bullet> \<epsilon>)[p \<bullet> x \<rightarrow> p \<bullet> h]"
  by (induct \<epsilon>) (auto simp add: permute_pure env_update_def)


section\<open>Helper for creating formulas\<close>

text\<open>Creates a formula that is the AND of all given subformulas.\<close>
fun mk_and :: "formula list \<Rightarrow> formula" where
  "mk_and [\<phi>] = \<phi>" |
  "mk_and (\<phi>#\<phi>s) = And \<phi> (mk_and \<phi>s)" |
  "mk_and [] = FTrue"

text\<open>Predicate for whether an entire instance is equal in the given two heaps.\<close>
nominal_function mk_instance_eq :: "header_type \<Rightarrow> instanc \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula" where
  "mk_instance_eq ht i x y = (let hl = header_length ht in
    Eq (Slice (SlInstance x i) 0 hl) (Slice (SlInstance y i) 0 hl))"
  subgoal by (auto simp add: eqvt_def mk_instance_eq_graph_aux_def Let_def)
  apply (auto)
done
nominal_termination (eqvt)
  by lexicographic_order

nominal_function foo :: "header_table \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula" where
  "foo HT x y = mk_and [mk_instance_eq ht i x y. (i, ht) \<leftarrow> HT]"
  subgoal apply (auto simp add: eqvt_def foo_graph_aux_def Let_def)

text\<open>Instance equality:
Predicate for whether two heaps are equivalent in terms of all possible instances.
Corresponds to \<equiv>i in the paper.\<close>
nominal_function mk_heap_instance_eq :: "header_table \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula" where
  "mk_heap_instance_eq ((i,ht)#HT) x y = (let hl = header_length ht in
   And (Eq (Slice (SlInstance x i) 0 hl) (Slice (SlInstance y i) 0 hl))
       (mk_heap_instance_eq HT x y))" |
  "mk_heap_instance_eq [] x y = FTrue"
  subgoal by (auto simp add: eqvt_def mk_heap_instance_eq_graph_aux_def Let_def)
  subgoal by (simp)
  apply (clarify)
  subgoal for P HT x y by (rule list.exhaust) (auto)
  apply (auto)
done
nominal_termination (eqvt)
  by lexicographic_order

text\<open>Strict equality:
Predicate for whether two heaps are equal in all instances and the in/out buffers.
Corresponds to \<equiv> in the paper.\<close>
nominal_function mk_heap_eq :: "header_table \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula" where
  "mk_heap_eq HT x y = And (Eq (Packet x PktIn) (Packet y PktIn))
                    (And (Eq (Packet x PktOut) (Packet y PktOut))
                    (mk_heap_instance_eq HT x y))"
  subgoal by (auto simp add: eqvt_def mk_heap_eq_graph_aux_def Let_def)
  apply (auto)
done
nominal_termination (eqvt)
  by lexicographic_order

text\<open>Like mk_heap_instance_eq but ignoring the given instance.\<close>
nominal_function mk_instances_eq_except :: "header_table \<Rightarrow> instanc \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula" where
  "mk_instances_eq_except HT i x y = mk_heap_instance_eq [(k,ht)\<leftarrow>HT. k \<noteq> i] x y"
  subgoal by (auto simp add: eqvt_def mk_instances_eq_except_graph_aux_def Let_def)
  apply (auto)
done
nominal_termination (eqvt)
  by lexicographic_order


nominal_function mk_fields_eq_except_helper :: "field list \<Rightarrow> instanc \<Rightarrow> field_name \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula"
where
  "mk_fields_eq_except_helper ((Field f _)#fs) i g x y = (let rem = mk_fields_eq_except_helper fs i g x y in
    let this = if f = g then FTrue else let (n, m) = field_list_to_range fs f in
      Eq (Slice (SlInstance x i) n m) (Slice (SlInstance y i) n m) in
    And this rem)" |
  "mk_fields_eq_except_helper [] _ _ _ _ = FTrue"
  subgoal by (auto simp add: eqvt_def mk_fields_eq_except_helper_graph_aux_def)
  subgoal by (simp)
  apply (clarify)
  subgoal for P fs i g x y
    apply (rule list.exhaust) apply (auto)
    by (rule field.exhaust) (auto)
  apply (auto)
done
nominal_termination (eqvt)
  by lexicographic_order

text\<open>Predicate for equality of all fields of a specific instance except for one.\<close>
nominal_function mk_fields_eq_except :: "header_type \<Rightarrow> instanc \<Rightarrow> field_name \<Rightarrow> var \<Rightarrow> var \<Rightarrow> formula"
where
  "mk_fields_eq_except (HeaderType _ fs) i g x y = mk_fields_eq_except_helper fs i g x y"
  subgoal by (auto simp add: eqvt_def mk_fields_eq_except_graph_aux_def)
  subgoal by (simp)
  apply (clarify)
  subgoal for P ht i g x y by (rule header_type.exhaust) (auto)
  apply (auto)
done
nominal_termination (eqvt)
  by lexicographic_order

end