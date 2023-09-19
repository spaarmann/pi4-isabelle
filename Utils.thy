theory Utils imports Syntax begin

fun slice :: "'a list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a list" where
  "slice xs n m = take (nat (m - n)) (drop (nat n) xs)"

text\<open>Replaces [n:m) in the first input list with the second list.\<close>
fun splice :: "'a list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "splice xs n m ins = (slice xs 0 n) @ ins @ (slice xs m (int (length xs)))"

section\<open>Nominal2 Lemmas\<close>

lemma bind_eqvt[eqvt]: "p \<bullet> Option.bind x f = Option.bind (p \<bullet> x) (p \<bullet> f)"
  by (cases x) auto

lemma map_of_eqvt[eqvt]: "p \<bullet> map_of xs x = map_of (p \<bullet> xs) (p \<bullet> x)"
  by (induct xs) auto

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

fun header_field_to_range_helper :: "int \<Rightarrow> field list \<Rightarrow> field_name \<Rightarrow> (int \<times> int)" where
  "header_field_to_range_helper acc ((Field fn fl)#fs) tgt = (if fn = tgt then (acc, acc + fl)
    else header_field_to_range_helper (acc + fl) fs tgt)" |
  "header_field_to_range_helper acc [] tgt = undefined"

fun header_field_to_range :: "header_type \<Rightarrow> field_name \<Rightarrow> (int \<times> int)" where
  "header_field_to_range (HeaderType _ fs) tgt = header_field_to_range_helper 0 fs tgt"

section\<open>Heaps\<close>

instantiation heap :: pure begin
  definition permute_heap :: "perm \<Rightarrow> heap \<Rightarrow> heap"  where
    "permute_heap _ x = x"
  instance by standard (auto simp add: permute_heap_def)
end

fun triple_to_heap :: "bv \<Rightarrow> bv \<Rightarrow> headers \<Rightarrow> heap" where
  "triple_to_heap In Out H = Heap In Out H"

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

section\<open>Environments\<close>

(* Easier to work with than "var \<Rightarrow> heap" with Nominal2 because it has a finite support (I think) *)
type_synonym env = "(var \<times> heap) list"

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

end