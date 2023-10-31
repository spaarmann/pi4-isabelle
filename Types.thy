theory Types imports Semantics begin

section\<open>Types\<close>

nominal_function heap_ty_sem :: "heap_ty \<Rightarrow> env \<Rightarrow> heap set" ("\<lbrakk>_ in _\<rbrakk>\<^sub>t" [50,60] 100)
where
  "\<lbrakk>Nothing in \<E>\<rbrakk>\<^sub>t = {}" |
  "\<lbrakk>Top in \<E>\<rbrakk>\<^sub>t = UNIV" |
  "atom x \<sharp> (\<tau>\<^sub>1, \<E>)
   \<Longrightarrow>\<lbrakk>Sigma x \<tau>\<^sub>1 \<tau>\<^sub>2 in \<E>\<rbrakk>\<^sub>t = {h\<^sub>1 ++ h\<^sub>2 | h\<^sub>1 h\<^sub>2. h\<^sub>1 \<in> \<lbrakk>\<tau>\<^sub>1 in \<E>\<rbrakk>\<^sub>t \<and> h\<^sub>2 \<in> \<lbrakk>\<tau>\<^sub>2 in \<E>[x \<rightarrow> h\<^sub>1]\<rbrakk>\<^sub>t}" |
  "\<lbrakk>Choice \<tau>\<^sub>1 \<tau>\<^sub>2 in \<E>\<rbrakk>\<^sub>t = \<lbrakk>\<tau>\<^sub>1 in \<E>\<rbrakk>\<^sub>t \<union> \<lbrakk>\<tau>\<^sub>2 in \<E>\<rbrakk>\<^sub>t" |
  "atom x \<sharp> (\<tau>, \<E>)
   \<Longrightarrow> \<lbrakk>Refinement x \<tau> \<phi> in \<E>\<rbrakk>\<^sub>t = {h. h \<in> \<lbrakk>\<tau> in \<E>\<rbrakk>\<^sub>t \<and> \<lbrakk>\<phi> in \<E>[x \<rightarrow> h]\<rbrakk>\<^sub>f = Some True}" |
  "atom x \<sharp> (\<tau>\<^sub>2, \<E>)
   \<Longrightarrow> \<lbrakk>Substitution \<tau>\<^sub>1 x \<tau>\<^sub>2 in \<E>\<rbrakk>\<^sub>t = {h. \<exists> h\<^sub>2. (h\<^sub>2 \<in> \<lbrakk>\<tau>\<^sub>2 in \<E>\<rbrakk>\<^sub>t) \<and> (h \<in> \<lbrakk>\<tau>\<^sub>1 in \<E>[x \<rightarrow> h\<^sub>2]\<rbrakk>\<^sub>t)}"
  using [[simproc del: alpha_lst]]
  subgoal by (auto simp add: eqvt_def heap_ty_sem_graph_aux_def)
  subgoal by (erule heap_ty_sem_graph.induct) (auto)
  apply clarify
  subgoal for P \<tau> \<E>
    apply (rule heap_ty.strong_exhaust[of \<tau> P "(\<tau>, \<E>)"])
    apply (auto simp add: fresh_star_def fresh_Pair)
    done
  apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal for x \<tau>\<^sub>1 \<E> \<tau>\<^sub>2 x' \<tau>\<^sub>2'
    apply (erule Abs_lst1_fcb2'[where c = "(\<tau>\<^sub>1, \<E>)"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_Pair pure_fresh fresh_star_insert)
  done
  subgoal for x \<tau> \<E> \<phi> x' \<phi>'
    apply (erule Abs_lst1_fcb2'[where c = "(\<tau>, \<E>)"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_Pair pure_fresh fresh_star_insert)
  done
  subgoal for x \<tau>\<^sub>2 \<E> \<tau>\<^sub>1 x' \<tau>\<^sub>1'
    apply (erule Abs_lst1_fcb2'[where c = "(\<tau>\<^sub>2, \<E>)"])
    apply (simp_all add: eqvt_at_def fresh_star_Pair)
    apply (simp_all add: perm_supp_eq fresh_Pair pure_fresh fresh_star_insert)
  done
done
nominal_termination (eqvt)
  by lexicographic_order

inductive heap_entails_ty :: "heap \<Rightarrow> env \<Rightarrow> heap_ty \<Rightarrow> bool" ("_ \<Turnstile>_ _" [50,50,50] 500)
where
  Ent_Top:      "h \<Turnstile>\<E> Top" |
  Ent_ChoiceL:  "\<lbrakk> h \<Turnstile>\<E> \<tau>\<^sub>1 \<rbrakk>
                \<Longrightarrow> h \<Turnstile>\<E> (Choice \<tau>\<^sub>1 \<tau>\<^sub>2)" |
  Ent_ChoiceR:  "\<lbrakk> h \<Turnstile>\<E> \<tau>\<^sub>2 \<rbrakk>
                \<Longrightarrow> h \<Turnstile>\<E> (Choice \<tau>\<^sub>1 \<tau>\<^sub>2)" |
  Ent_Refine:   "\<lbrakk> atom x \<sharp> (\<tau>, \<E>, h);
                   h \<Turnstile>\<E> \<tau>; \<lbrakk>\<phi> in \<E>[x \<rightarrow> h]\<rbrakk>\<^sub>f = Some True \<rbrakk>
                \<Longrightarrow> h \<Turnstile>\<E> (Refinement x \<tau> \<phi>)" |
  Ent_Sigma:    "\<lbrakk> atom x \<sharp> (\<tau>\<^sub>1, \<E>, h\<^sub>1, h\<^sub>2);
                   h\<^sub>1 \<Turnstile>\<E> \<tau>\<^sub>1; h\<^sub>2 \<Turnstile>(\<E>[x \<rightarrow> h\<^sub>1]) \<tau>\<^sub>2\<rbrakk>
                \<Longrightarrow> (h\<^sub>1 ++ h\<^sub>2) \<Turnstile>\<E> (Sigma x \<tau>\<^sub>1 \<tau>\<^sub>2)" |
  Ent_Subst:    "\<lbrakk> atom x \<sharp> (\<tau>\<^sub>2, \<E>, h, h\<^sub>2);
                   h\<^sub>2 \<Turnstile>\<E> \<tau>\<^sub>2; h \<Turnstile>(\<E>[x \<rightarrow> h\<^sub>2]) \<tau>\<^sub>1 \<rbrakk>
                \<Longrightarrow> h \<Turnstile>\<E> (Substitution \<tau>\<^sub>1 x \<tau>\<^sub>2)"

declare heap_entails_ty.intros[simp]
declare heap_entails_ty.intros[intro]

equivariance heap_entails_ty                                                   
nominal_inductive heap_entails_ty
  avoids Ent_Sigma: x
       | Ent_Refine: x
       | Ent_Subst: x
  by (auto simp add: fresh_star_def fresh_Pair pure_fresh)

definition env_entails_ty_env :: "env \<Rightarrow> ty_env \<Rightarrow> bool" ("_ \<TTurnstile> _" [50,50] 500)
where
  "(\<E> \<TTurnstile> \<Gamma>) = (\<forall>x. x \<in> (fst ` set \<Gamma>)
    \<longrightarrow> (\<exists>h \<tau>. (map_of (heaps \<E>) x = Some h) \<and> (map_of \<Gamma> x = Some \<tau>) \<and> (h \<Turnstile>\<E> \<tau>)))"

definition subtype_of :: "ty_env \<Rightarrow> heap_ty \<Rightarrow> heap_ty \<Rightarrow> bool" ("_ \<turnstile> _ <: _" [50,50,50] 50)
where
  "\<Gamma> \<turnstile> \<tau>\<^sub>1 <: \<tau>\<^sub>2 \<equiv> \<forall>\<E>. \<E> \<TTurnstile> \<Gamma> \<longrightarrow> \<lbrakk>\<tau>\<^sub>1 in \<E>\<rbrakk>\<^sub>t \<subseteq> \<lbrakk>\<tau>\<^sub>2 in \<E>\<rbrakk>\<^sub>t"

definition ty_includes :: "ty_env \<Rightarrow> heap_ty \<Rightarrow> instanc \<Rightarrow> bool" where
  "ty_includes \<Gamma> \<tau> \<iota> = (\<forall>\<E>. \<E> \<TTurnstile> \<Gamma> \<longrightarrow> (\<forall>h \<in> \<lbrakk>\<tau> in \<E>\<rbrakk>\<^sub>t. \<iota> \<in> heap_dom h))"

definition ty_excludes :: "ty_env \<Rightarrow> heap_ty \<Rightarrow> instanc \<Rightarrow> bool" where
  "ty_excludes \<Gamma> \<tau> \<iota> = (\<forall>\<E>. \<E> \<TTurnstile> \<Gamma> \<longrightarrow> (\<forall>h \<in> \<lbrakk>\<tau> in \<E>\<rbrakk>\<^sub>t. \<iota> \<notin> heap_dom h))"

(* TODO: How do I actually write this? Just need some arbitrary variable that gets bound in the second type *)
text\<open>Type denoting the empty heap, \<epsilon> in the paper.\<close>
definition heap_ty_empty :: "header_table \<Rightarrow> var \<Rightarrow> heap_ty" where
  "heap_ty_empty HT x = Refinement (x) Top (mk_and [Not (IsValid x \<iota>). (\<iota>, _) \<leftarrow> HT])"

text\<open>Type denoting heaps containing exclusively \<iota>, written as just \<iota> in the paper.\<close>
definition heap_ty_only :: "header_table \<Rightarrow> var \<Rightarrow> instanc \<Rightarrow> heap_ty" where
  "heap_ty_only HT x \<iota> = Refinement x Top (And (IsValid x \<iota>)
                                             (mk_and [Not (IsValid x \<iota>'). (\<iota>', _) \<leftarrow> HT, \<iota> \<noteq> \<iota>']))"

text\<open>Type denoting heaps containing at least \<iota>, written as \<iota>~ in the paper.\<close>
definition heap_ty_at_least :: "var \<Rightarrow> instanc \<Rightarrow> heap_ty" where
  "heap_ty_at_least x \<iota> = Refinement x Top (IsValid x \<iota>)"

inductive exp_typing :: "ty_env \<Rightarrow> exp \<Rightarrow> base_ty \<Rightarrow> bool"
  ("_ \<turnstile>\<^sub>e _ : _" [51,60,60] 60)
where
  TE_Num:       "\<Gamma> \<turnstile>\<^sub>e (Num n) : Nat" |
  TE_Bv:        "\<Gamma> \<turnstile>\<^sub>e (Bv bv) : BV" |
  TE_Plus:      "\<lbrakk> \<Gamma> \<turnstile>\<^sub>e e\<^sub>1 : Nat; \<Gamma> \<turnstile>\<^sub>e e\<^sub>2 : Nat \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e (Plus e\<^sub>1 e\<^sub>2) : Nat" |
  TE_Concat:    "\<lbrakk> \<Gamma> \<turnstile>\<^sub>e e\<^sub>1 : BV; \<Gamma> \<turnstile>\<^sub>e e\<^sub>2 : BV \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e (Concat e\<^sub>1 e\<^sub>2) : BV" |
  TE_Packet:    "\<lbrakk> map_of \<Gamma> x = Some _ \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e (Packet x p) : BV" |
  TE_Len:       "\<lbrakk> map_of \<Gamma> x = Some _ \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e (Len x p) : Nat" |
  TE_SlicePkt:  "\<lbrakk> map_of \<Gamma> x = Some _\<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e (Slice (SlPacket x p) rng) : BV" |
  (* TODO: For instances this could/should also include right m \<le> size if we make HT an input.*)
  TE_SliceInst: "\<lbrakk> map_of \<Gamma> x = Some \<tau>; ty_includes \<Gamma> \<tau> \<iota> \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>e (Slice (SlInstance x \<iota>) rng) : BV"

inductive formula_typing :: "ty_env \<Rightarrow> formula \<Rightarrow> base_ty \<Rightarrow> bool"
  ("_ \<turnstile>\<^sub>f _ : _" [50,50,50] 60)
where
  TF_True:      "\<Gamma> \<turnstile>\<^sub>f FTrue : Bool" |
  TF_False:     "\<Gamma> \<turnstile>\<^sub>f FFalse : Bool" |
  TF_EqNum:     "\<lbrakk> \<Gamma> \<turnstile>\<^sub>e e\<^sub>1 : Nat; \<Gamma> \<turnstile>\<^sub>e e\<^sub>2 : Nat \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f (Eq e\<^sub>1 e\<^sub>2) : Bool" |
  TF_EqBv:      "\<lbrakk> \<Gamma> \<turnstile>\<^sub>e e\<^sub>1 : BV; \<Gamma> \<turnstile>\<^sub>e e\<^sub>2 : BV \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f (Eq e\<^sub>1 e\<^sub>2) : Bool" |
  TF_Gt:        "\<lbrakk> \<Gamma> \<turnstile>\<^sub>e e\<^sub>1 : Nat; \<Gamma> \<turnstile>\<^sub>e e\<^sub>2 : Nat \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f (Gt e\<^sub>1 e\<^sub>2) : Bool" |
  TF_And:       "\<lbrakk> \<Gamma> \<turnstile>\<^sub>f \<phi>\<^sub>1 : Bool; \<Gamma> \<turnstile>\<^sub>f \<phi>\<^sub>2 : Bool \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f (And \<phi>\<^sub>1 \<phi>\<^sub>2) : Bool" |
  TF_Not:       "\<lbrakk> \<Gamma> \<turnstile>\<^sub>f \<phi> : Bool \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f (Not \<phi>) : Bool" |
  TF_IsValid:   "\<lbrakk> map_of \<Gamma> x = Some _ \<rbrakk>
                \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>f (IsValid x \<iota>) : Bool"

(* TODO: Freshness assumptions everywhere *)
inductive command_typing :: "header_table \<Rightarrow> ty_env \<Rightarrow> cmd \<Rightarrow> pi_ty \<Rightarrow> bool"
  ("_, _ \<turnstile> _ : _" [50,50,50,50] 60)
where
  TC_Skip:      "\<lbrakk> \<tau>\<^sub>2 = Refinement y \<tau>\<^sub>1 (mk_heap_eq HT y x)  \<rbrakk>
                \<Longrightarrow> HT, \<Gamma> \<turnstile> Skip : ((x : \<tau>\<^sub>1) \<rightarrow> \<tau>\<^sub>2)" |
  TC_Seq:       "\<lbrakk> HT, \<Gamma> \<turnstile> c\<^sub>1 : ((x : \<tau>\<^sub>1) \<rightarrow> \<tau>\<^sub>1\<^sub>2); HT, (\<Gamma>\<^bold>, x : \<tau>\<^sub>1) \<turnstile> c\<^sub>2 : ((y : \<tau>\<^sub>1\<^sub>2) \<rightarrow> \<tau>\<^sub>2\<^sub>2) \<rbrakk>
                \<Longrightarrow> HT, \<Gamma> \<turnstile> Seq c\<^sub>1 c\<^sub>2 : ((x : \<tau>\<^sub>1) \<rightarrow> (Substitution \<tau>\<^sub>2\<^sub>2 y \<tau>\<^sub>1\<^sub>2))" |
  TC_If:        "\<lbrakk> (\<Gamma>\<^bold>; \<tau>\<^sub>1) \<turnstile>\<^sub>f \<phi> : Bool;
                   HT, \<Gamma> \<turnstile> c\<^sub>1 : ((x : Refinement y \<tau>\<^sub>1 \<phi>[y/var_heap]\<^sub>f) \<rightarrow> \<tau>\<^sub>1\<^sub>2);
                   HT, \<Gamma> \<turnstile> c\<^sub>2 : ((x : Refinement y \<tau>\<^sub>1 (Not \<phi>[y/var_heap]\<^sub>f)) \<rightarrow> \<tau>\<^sub>2\<^sub>2) \<rbrakk>
                \<Longrightarrow> HT, \<Gamma> \<turnstile> (If \<phi> c\<^sub>1 c\<^sub>2) : ((x : \<tau>\<^sub>1) \<rightarrow>
                  Choice (Refinement y \<tau>\<^sub>1\<^sub>2 \<phi>[x/var_heap]\<^sub>f) (Refinement y \<tau>\<^sub>2\<^sub>2 (Not \<phi>[x/heap]\<^sub>f)))" |
                (* Ignoring the F(i,f) = BV premise here. The paper never mentions it, the thesis
                   seems to say it would be useful for potentially more fine-grained checking as
                   an extension, but it's not actually used yet. *)
  TC_Assign:    "\<lbrakk> ty_includes \<Gamma> \<tau>\<^sub>1 \<iota>;
                   (\<Gamma>\<^bold>; \<tau>\<^sub>1) \<turnstile>\<^sub>e e : BV;
                   \<phi>\<^sub>p\<^sub>k\<^sub>t = And (Eq (Packet y PktIn) (Packet x PktIn))
                              (Eq (Packet y PktOut) (Packet x PktOut));
                   \<phi>\<^sub>\<iota> = mk_heap_eq_instances_except HT \<iota> y x;
                   map_of HT \<iota> = Some \<eta>;
                   \<phi>\<^sub>f = mk_fields_eq_except \<eta> \<iota> f y x;
                   \<phi>\<^sub>f\<^sub>e\<^sub>q = Eq (mk_field_read \<eta> \<iota> f y) e[x/heap]\<^sub>e \<rbrakk>
                \<Longrightarrow> HT, \<Gamma> \<turnstile> (Assign \<iota> f e) : ((x : \<tau>\<^sub>1) \<rightarrow> Refinement y Top
                      (And \<phi>\<^sub>p\<^sub>k\<^sub>t (And \<phi>\<^sub>\<iota> (And \<phi>\<^sub>f \<phi>\<^sub>f\<^sub>e\<^sub>q))))" |
  (* TODO: T-Extract. Skipping Extract for now, want to do chomp last. *)
  TC_Remit:     "\<lbrakk> ty_includes \<Gamma> \<tau>\<^sub>1 \<iota>;
                   map_of HT \<iota> = Some \<eta>;
                   \<phi> = And (Eq (Packet z PktIn) (Bv []))
                           (Eq (Packet z PktOut) (mk_inst_read \<eta> \<iota> x));
                   atom zz \<sharp> (x, y, z)\<rbrakk>
                 \<Longrightarrow> HT, \<Gamma> \<turnstile> Remit \<iota> : ((x : \<tau>\<^sub>1) \<rightarrow> Sigma y (Refinement z \<tau>\<^sub>1 (mk_heap_eq HT z x))
                                                           (Refinement z (heap_ty_empty HT zz) \<phi>))" |
  TC_Add:       "\<lbrakk> ty_excludes \<Gamma> \<tau>\<^sub>1 \<iota>;
                   map_of HT \<iota> = Some \<eta>; init_header \<eta> = bv;
                   \<phi> = And (Eq (Packet z PktIn) (Packet z PktOut))
                           (And (Eq (Packet z PktOut) (Bv [])) (Eq (mk_inst_read \<eta> \<iota> z) (Bv bv))) \<rbrakk>
                \<Longrightarrow> HT, \<Gamma> \<turnstile> Add \<iota> : ((x : \<tau>\<^sub>1) \<rightarrow> Sigma y (Refinement z \<tau>\<^sub>1 (mk_heap_eq HT z x))
                                                        (Refinement z (heap_ty_only HT zz \<iota>) \<phi>))" |
  TC_Reset:     "\<lbrakk> \<phi>\<^sub>1 = And (Eq (Packet z PktOut) (Bv [])) (Eq (Packet z PktIn) (Packet x PktOut));
                   \<phi>\<^sub>2 = And (Eq (Packet z PktOut) (Bv [])) (Eq (Packet z PktIn) (Packet x PktIn)) \<rbrakk>
                \<Longrightarrow> HT, \<Gamma> \<turnstile> Reset : ((x : \<tau>\<^sub>1) \<rightarrow> Sigma y (Refinement z (heap_ty_empty HT zz) \<phi>\<^sub>1)
                                                        (Refinement z (heap_ty_empty HT zz) \<phi>\<^sub>2))" |
  TC_Ascribe:   "\<lbrakk> HT, \<Gamma> \<turnstile> c : \<sigma> \<rbrakk>
                \<Longrightarrow> HT, \<Gamma> \<turnstile> Ascribe c \<sigma> : \<sigma>" |
  TC_Sub:       "\<lbrakk> \<Gamma> \<turnstile> \<tau>\<^sub>1 <: \<tau>\<^sub>3; (\<Gamma>\<^bold>, x : \<tau>\<^sub>1) \<turnstile> \<tau>\<^sub>4 <: \<tau>\<^sub>2;
                   HT, \<Gamma> \<turnstile> c : ((x : \<tau>\<^sub>3) \<rightarrow> \<tau>\<^sub>4) \<rbrakk>
                \<Longrightarrow> HT, \<Gamma> \<turnstile> c : ((x : \<tau>\<^sub>1) \<rightarrow> \<tau>\<^sub>2)"


section\<open>Safety Results\<close>

find_theorems name: heap_entails_ty
lemma semantic_entailment: "h \<Turnstile>\<E> \<tau> \<Longrightarrow> h \<in> \<lbrakk>\<tau> in \<E>\<rbrakk>\<^sub>t"
proof (nominal_induct \<tau> arbitrary: h \<E> rule: heap_ty.strong_induct)
  case Nothing then show ?case by (cases)
next
  case Top then show ?case by (auto)
next
  case (Sigma x \<tau>\<^sub>1 \<tau>\<^sub>2)
  thm Abs_lst1_fcb2'
  from Sigma.prems obtain h\<^sub>1 h\<^sub>2 where "h\<^sub>2 \<Turnstile>(\<E>[x \<rightarrow> h\<^sub>1]) \<tau>\<^sub>2" apply (cases) apply (auto) sorry
  from Sigma.prems obtain h\<^sub>1 h\<^sub>2 where "h = h\<^sub>1 ++ h\<^sub>2" "h\<^sub>1 \<Turnstile>\<E> \<tau>\<^sub>1" apply (cases) apply (auto) done
  from Sigma.prems have "h\<^sub>2 \<Turnstile>(\<E>[x \<rightarrow> h\<^sub>1]) \<tau>\<^sub>2" apply (cases)
(*  h = h\<^sub>1 ++ h\<^sub>2;
                   h\<^sub>1 \<Turnstile>\<E> \<tau>\<^sub>1; h\<^sub>2 \<Turnstile>(\<E>[x \<rightarrow> h\<^sub>1]) \<tau>\<^sub>2 *)
end