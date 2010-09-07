open HolKernel bossLib boolLib SatisfySimps Parse ptypes_definitionsTheory pred_setTheory finite_mapTheory optionTheory state_optionTheory pairTheory combinTheory relationTheory lcsymtacs

val _ = new_theory "ptypes"

local
  fun Cases_on_if p (g as (asl,tm)) = let
    val tm = find_term p tm handle HOL_ERR _ =>
             Lib.tryfind (find_term p) asl
  in Cases_on [QUOTE (term_to_string tm)] end g
  fun is_var' v = let
    val (_,ty) = dest_var v
    val (tyname,_) = dest_type ty
  in
    not (Lib.mem tyname ["num","list"])
  end handle HOL_ERR _ => false | Bind => false
  val tac = srw_tac [][EQ_IMP_THM,is_embed_def] >> rpt (Cases_on_if is_var' >> fsrw_tac [][])
in
  val is_embed_Variable = Q.store_thm("is_embed_Variable", `is_embed embed_Variable`, tac);
  val is_embed_SetOfVariables = Q.store_thm("is_embed_SetOfVariables", `is_embed embed_SetOfVariables`, tac);
  val is_embed_Term = Q.store_thm("is_embed_Term", `is_embed embed_Term`, tac);
  val is_embed_Multiequation = Q.store_thm("is_embed_Multiequation", `is_embed embed_Multiequation`, tac);
  val is_embed_TempMultiequation = Q.store_thm("is_embed_TempMultiequation", `is_embed embed_TempMultiequation`, tac);
  val is_embed_System = Q.store_thm("is_embed_System", `is_embed embed_System`, tac);
  val is_embed_AuxList = Q.store_thm("is_embed_AuxList", `is_embed (embed_AuxList emb)`, tac);
  val is_embed_List = Q.store_thm("is_embed_List", `is_embed (embed_List emb)`, tac);
end

val NOTIN_INFINITE_FDOM_exists = Q.store_thm(
"NOTIN_INFINITE_FDOM_exists",
`INFINITE (UNIV : 'a set) ⇒ ∃x. x ∉ (FDOM f : 'a set)`,
PROVE_TAC [IN_INFINITE_NOT_FINITE,FDOM_FINITE]);
val _ = export_rewrites["NOTIN_INFINITE_FDOM_exists"];

val free_addr_elim_thm = Q.store_thm(
"free_addr_elim_thm",
`∀P s. (∀n. n ≠ 0 ∧ n ∉ FDOM s.store ⇒ P (SOME (addr (:'a) n,s))) ⇒ P (free_addr s)`,
srw_tac [][free_addr_def] >>
SELECT_ELIM_TAC >>
`∃x. x ∉ FDOM (s.store|+(0,ARB))` by srw_tac [][] >>
fsrw_tac [SATISFY_ss][]);

fun is_free_addr tm = let
  val (f,_) = dest_comb tm
  val ("free_addr",ty) = dest_const f
in
  can (match_type ``:state -> ('a ptr # state) option``) ty
end handle HOL_ERR _ => false | Bind => false

fun free_addr_elim_tac (g as (_, w)) = let
  val t = find_term is_free_addr w
in
  CONV_TAC (UNBETA_CONV t) THEN
  MATCH_MP_TAC free_addr_elim_thm THEN BETA_TAC
end g

val _ = augment_srw_ss [rewrites [STATE_OPTION_IGNORE_BIND_def,STATE_OPTION_BIND_def,STATE_OPTION_FAIL_def,STATE_OPTION_UNIT_def]]
val _ = augment_srw_ss [rewrites [OPTION_BIND_def]]

val CreateList_empty = Q.store_thm(
"CreateList_empty",
`(CreateList emb s0 = SOME (l, s)) ⇒ list_of_List emb s l []`,
simp_tac (srw_ss()) [CreateList_def,raw_new_def] >>
free_addr_elim_tac >> srw_tac [][EXISTS_PROD] >>
qpat_assum `free_addr X = Y` mp_tac >>
free_addr_elim_tac >> srw_tac [][] >>
fsrw_tac [][] >> srw_tac [][] >>
srw_tac [][list_of_List_def,Once list_of_AuxList_cases,EmptyList_def,FLOOKUP_UPDATE,APPLY_UPDATE_THM]);

val lookup_state = Q.store_thm(
"lookup_state",
`(raw_lookup emb ptr s = SOME p) ⇒ (SND p = s)`,
Cases_on `emb` >> Cases_on `ptr` >>
srw_tac [][FLOOKUP_DEF] >> srw_tac [][]);

val HeadOfList_state = Q.store_thm(
"HeadOfList_state",
`(HeadOfList emb l s = SOME p) ⇒ (SND p = s)`,
srw_tac [][HeadOfList_def,UNCURRY] >>
imp_res_tac lookup_state >> srw_tac [][]);

val TailOfList_store = Q.store_thm(
"TailOfList_store",
`(lookup emb l s = SOME p1) ∧ (TailOfList emb l s = SOME p2) ⇒
 ((SND p2).store \\ (ptr_to_num l) \\ (ptr_to_num (FST p1).first) =
  s.store \\ (ptr_to_num l) \\ (ptr_to_num (FST p1).first))`,
srw_tac [][TailOfList_def,UNCURRY] >>
imp_res_tac lookup_state >>
fsrw_tac [][] >> srw_tac [][] >>
qmatch_assum_rename_tac `dispose (FST p1).first (SND v) = SOME w` [] >>
Cases_on `l` >> Cases_on `(FST p1).first` >>
Cases_on `p1` >> Cases_on `v` >> Cases_on `w` >>
fsrw_tac [][state_component_equality] >>
metis_tac [DOMSUB_COMMUTES,DOMSUB_IDEM,DOMSUB_FUPDATE]);

val EmptyList_state = Q.store_thm(
"EmptyList_state",
`(EmptyList emb l s = SOME p) ⇒ (SND p = s)`,
srw_tac [][EmptyList_def,EXISTS_PROD] >>
imp_res_tac lookup_state >> fsrw_tac [][]);

val dispose_store = Q.store_thm(
"dispose_store",
`(dispose p s = SOME x) ⇒ ((SND x).store \\ ptr_to_num p = s.store \\ ptr_to_num p)`,
Cases_on `p` >> srw_tac [][] >> srw_tac [][]);

val dispose_cell_type = Q.store_thm(
"dispose_cell_type",
`(dispose p s = SOME x) ⇒ ((SND x).cell_type = s.cell_type)`,
Cases_on `p` >> srw_tac [][] >> srw_tac [][]);

val lookup_dispose = Q.store_thm(
"lookup_dispose",
`(dispose p1 s = SOME x) ⇒
 (raw_lookup emb p2 (SND x) =
  if ptr_to_num p1 = ptr_to_num p2 then NONE
  else OPTION_MAP (I ## K (SND x)) (raw_lookup emb p2 s))`,
Cases_on `p1` >> Cases_on `p2` >> ntac 2 (srw_tac [][]) >>
srw_tac [][DOMSUB_FLOOKUP_THM] >>
srw_tac [][FLOOKUP_DEF] >>
srw_tac [][] >>
qmatch_abbrev_tac `OPTION_BIND x y = z` >>
Cases_on `x` >> srw_tac [][] >>
unabbrev_all_tac >> srw_tac [][]);

val lookup_fails = Q.store_thm(
"lookup_fails",
`(raw_lookup emb p s = NONE) ⇔ (∀v. (FLOOKUP s.store (ptr_to_num p) = SOME v) ⇒ (s.cell_type (ptr_to_num p) = emb.type) ⇒ (emb.project v = NONE))`,
Cases_on `p` >> srw_tac [][FLOOKUP_DEF] >> srw_tac [][EQ_IMP_THM] >> srw_tac [][GSYM IMP_DISJ_THM]);

val lookup_succeeds = Q.store_thm(
"lookup_succeeds",
`(raw_lookup emb p s = SOME a) ⇔ ∃v. (FLOOKUP s.store (ptr_to_num p) = SOME v) ∧ (s.cell_type (ptr_to_num p) = emb.type) ∧ (emb.project v = SOME (FST a)) ∧ (SND a = s)`,
Cases_on `raw_lookup emb p s` >- (
  PROVE_TAC [lookup_fails,NOT_SOME_NONE] ) >>
Cases_on `FLOOKUP s.store (ptr_to_num p)` >>
Cases_on `p` >> Cases_on `a` >> fsrw_tac [][] >>
Cases_on `s.cell_type n = emb.type` >> fsrw_tac [][] >>
srw_tac [][EQ_IMP_THM]);

val lookup_assign = Q.store_thm(
"lookup_assign",
`is_embed emb ∧ (raw_assign emb p a s = SOME p1) ∧ (raw_lookup emb p (SND p1) = SOME p2) ⇒ (FST p2 = a)`,
Cases_on `p` >> srw_tac [][] >>
fsrw_tac [][APPLY_UPDATE_THM,FLOOKUP_UPDATE,is_embed_def] >>
srw_tac [][] >> PROVE_TAC [SOME_11]);

val assign_store = Q.store_thm(
"assign_store",
`(raw_assign emb p v s = SOME x) ⇒ ((SND x).store \\ ptr_to_num p = s.store \\ ptr_to_num p)`,
Cases_on `p` >> srw_tac [][] >> srw_tac [][]);

val assign_cell_type = Q.store_thm(
"assign_cell_type",
`(raw_assign emb p v s = SOME x) ⇒ ((SND x).cell_type = ((ptr_to_num p) =+ emb.type) s.cell_type)`,
Cases_on `p` >> srw_tac [][] >> srw_tac [][]);

val lookup_unbound = Q.store_thm(
"lookup_unbound",
`ptr_to_num p ∉ FDOM s.store ⇒ (lookup p s = NONE)`,
Cases_on `p` >> srw_tac [][FLOOKUP_DEF]);

val HeadOfList_unbound = Q.store_thm(
"HeadOfList_unbound",
`ptr_to_num p ∉ FDOM s.store ⇒ (HeadOfList emb p s = NONE)`,
Cases_on `p` >> srw_tac [][FLOOKUP_DEF,HeadOfList_def]);

val TailOfList_unbound = Q.store_thm(
"TailOfList_unbound",
`ptr_to_num p ∉ FDOM s.store ⇒ (TailOfList emb p s = NONE)`,
Cases_on `p` >> srw_tac [][FLOOKUP_DEF,TailOfList_def]);

val type_inductive = Q.store_thm(
"type_inductive",
`∀t. t ≠ List_type t ∧ t ≠ AuxList_type t`,
Induct >> srw_tac [][]);

val typed_cell_bound = Q.store_thm(
"typed_cell_bound",
`typed_cell s ms n ⇒ (n = 0) ∨ n ∈ ms ∨ n ∈ FDOM s.store`,
srw_tac [][Once has_type_cases,FLOOKUP_DEF] >> srw_tac [][]);

val assign_comm = Q.store_thm(
"assign_comm",
`ptr_to_num p1 ≠ ptr_to_num p2 ∧
 (raw_assign emb1 p1 v1 s = SOME x1) ∧
 (raw_assign emb2 p2 v2 s = SOME x2) ⇒
 (raw_assign emb1 p1 v1 (SND x2) = raw_assign emb2 p2 v2 (SND x1))`,
Cases_on `p1` >> Cases_on `p2` >> srw_tac [][] >>
srw_tac [][state_component_equality,FUN_EQ_THM,APPLY_UPDATE_THM] >>
srw_tac [][GSYM fmap_EQ,INSERT_COMM] >>
srw_tac [][FUN_EQ_THM,FAPPLY_FUPDATE_THM] >>
srw_tac [][]);

val free_addr_state = Q.store_thm(
"free_addr_state",
`(free_addr s = SOME p) ⇒ (SND p = s)`,
ntac 2 (srw_tac [][free_addr_def]));

val lookup_assign_neq = Q.store_thm(
"lookup_assign_neq",
`ptr_to_num p1 ≠ ptr_to_num p2 ∧
 (raw_assign emb2 p2 v s = SOME x) ⇒
 (OPTION_MAP FST (raw_lookup emb1 p1 (SND x)) = OPTION_MAP FST (raw_lookup emb1 p1 s))`,
Cases_on `raw_lookup emb1 p1 s` >>
Cases_on `p2` >> srw_tac [][] >>
fsrw_tac [][FLOOKUP_UPDATE,APPLY_UPDATE_THM,lookup_succeeds,lookup_fails] >>
srw_tac [][EXISTS_PROD]);

val ptr_equality = Q.store_thm(
"ptr_equality",
`(ptr_to_num p1 = ptr_to_num p2) ⇔ (p1 = p2)`,
Cases_on `p1` >> Cases_on `p2` >> srw_tac [][] >>
PROVE_TAC [ITSELF_UNIQUE]);

val typed_cell_def = Q.store_thm(
"typed_cell_def",
`typed_cell s c n =
   n ∈ FDOM s.store ∧ n ∈ c ∨
   case FLOOKUP s.store n of SOME v -> has_type s (n INSERT c) v (s.cell_type n) || NONE -> (n = 0)`,
srw_tac [][Once has_type_cases] >>
Cases_on `FLOOKUP s.store n` >> srw_tac [][] >>
fsrw_tac [][FLOOKUP_DEF] >>
PROVE_TAC []);

val has_type_INSERT_cached = Q.store_thm(
"has_type_INSERT_cached",
`(∀c v t. has_type s c v t ⇒ has_type s (m INSERT c) v t) ∧
 (∀c n. typed_cell s c n ⇒ typed_cell s (m INSERT c) n)`,
ho_match_mp_tac has_type_ind >>
reverse (srw_tac [][])
>- srw_tac [][typed_cell_def,INSERT_COMM]
>- srw_tac [][typed_cell_def,FLOOKUP_DEF]
>- srw_tac [][typed_cell_def] >>
srw_tac [][Once has_type_cases]);

val has_type_assign_unbound = Q.store_thm(
"has_type_assign_unbound",
`(∀c v t. has_type s c v t ⇒ m ≠ 0 ∧ m ∉ FDOM s.store ∧ m ∉ c ⇒
          has_type (s with <|store updated_by (m =+ w); cell_type updated_by (m =+ a)|>) c v t) ∧
 (∀c n. typed_cell s c n ⇒ m ≠ 0 ∧ m ∉ FDOM s.store ∧ m ∉ c ⇒
        typed_cell (s with <|store updated_by (m =+ w); cell_type updated_by (m =+ a)|>) c n)`,
ho_match_mp_tac has_type_strongind >>
reverse (srw_tac [][]) >- (
  fsrw_tac [][] >>
  srw_tac [][Once has_type_cases,FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
  fsrw_tac [][FLOOKUP_DEF] )
>- srw_tac [][Once has_type_cases,FLOOKUP_UPDATE]
>- srw_tac [][Once has_type_cases] >>
srw_tac [][Once has_type_cases,APPLY_UPDATE_THM] >>
fsrw_tac [][typed_cell_def,type_inductive,FLOOKUP_UPDATE] >>
fsrw_tac [][FLOOKUP_DEF]);

val has_type_assign_cached = Q.store_thm(
"has_type_assign_cached",
`(∀c v t. has_type s c v t ⇒ m ∈ c ⇒
          has_type (s with <|store updated_by (m =+ w)|>) c v t) ∧
 (∀c n. typed_cell s c n ⇒ m ∈ c ⇒
        typed_cell (s with <|store updated_by (m =+ w)|>) c n)`,
ho_match_mp_tac has_type_ind >>
reverse (srw_tac [][]) >- (
  srw_tac [][typed_cell_def,FLOOKUP_UPDATE] >>
  fsrw_tac [][APPLY_UPDATE_THM] )
>- srw_tac [][typed_cell_def,FLOOKUP_UPDATE,FLOOKUP_DEF]
>- srw_tac [][typed_cell_def] >>
srw_tac [][Once has_type_cases]);

val has_type_assign_cached_unbound = Q.store_thm(
"has_type_assign_cached_unbound",
`(∀c v t. has_type s c v t ⇒ m ∈ c ∧ m ∉ FDOM s.store ⇒
          has_type (s with <|store updated_by (m =+ w); cell_type updated_by (m =+ a)|>) c v t) ∧
 (∀c n. typed_cell s c n ⇒ m ∈ c ∧ m ∉ FDOM s.store ⇒
        typed_cell (s with <|store updated_by (m =+ w); cell_type updated_by (m =+ a)|>) c n)`,
ho_match_mp_tac has_type_strongind >>
reverse (srw_tac [][]) >- (
  fsrw_tac [][] >>
  srw_tac [][typed_cell_def,FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
  srw_tac [][] )
>- srw_tac [][typed_cell_def,FLOOKUP_UPDATE,FLOOKUP_DEF]
>- srw_tac [][typed_cell_def] >>
fsrw_tac [][] >>
srw_tac [][Once has_type_cases,APPLY_UPDATE_THM] >>
fsrw_tac [][type_inductive,typed_cell_def,FLOOKUP_DEF]);

val has_type_assign_bound = Q.store_thm(
"has_type_assign_bound",
`(∀c v t. has_type s c v t ⇒ m ≠ 0 ∧ m ∈ FDOM s.store ∧ has_type s c w (s.cell_type m) ⇒
          has_type (s with <|store updated_by (m =+ w) |>) c v t) ∧
 (∀c n. typed_cell s c n ⇒ m ≠ 0 ∧ m ∈ FDOM s.store ∧ has_type s c w (s.cell_type m) ⇒
        typed_cell (s with <|store updated_by (m =+ w) |>) c n)`,
ho_match_mp_tac has_type_ind >>
reverse (srw_tac [][]) >- (
  fsrw_tac [][has_type_INSERT_cached] >>
  srw_tac [][typed_cell_def] >>
  Cases_on `n ∈ c` >> srw_tac [][] >>
  srw_tac [][FLOOKUP_UPDATE] >> srw_tac [][] >>
  (has_type_assign_cached |> CONJUNCT1 |> MP_CANON |> MATCH_MP_TAC) >>
  srw_tac [][has_type_INSERT_cached] )
>- srw_tac [][Once has_type_cases,FLOOKUP_UPDATE]
>- srw_tac [][typed_cell_def] >>
srw_tac [][Once has_type_cases]);

val assign_FDOM = Q.store_thm(
"assign_FDOM",
`(raw_assign emb p v s = SOME x) ⇒
 (FDOM (SND x).store = (ptr_to_num p) INSERT (FDOM s.store))`,
Cases_on `p` >> srw_tac [][] >> srw_tac [][]);

val free_addr_neq_0 = Q.store_thm(
"free_addr_neq_0",
`(free_addr s = SOME p) ⇒ ptr_to_num (FST p) ≠ 0`,
free_addr_elim_tac >> srw_tac [][] >> srw_tac [][]);

val CreateList_wfstate = Q.store_thm(
"CreateList_wfstate",
`wfstate s ∧ (CreateList emb s = SOME p) ⇒ wfstate (SND p)`,
reverse (srw_tac [][CreateList_def,UNCURRY,wfstate_def]) >>
fsrw_tac [][] >- (
  imp_res_tac assign_FDOM >>
  imp_res_tac free_addr_state >>
  imp_res_tac free_addr_neq_0 >>
  srw_tac [][] ) >>
ntac 2 (qpat_assum `free_addr X = Y` mp_tac) >>
free_addr_elim_tac >> qx_gen_tac `f1` >>
free_addr_elim_tac >> qx_gen_tac `f2` >>
srw_tac [][typed_state_def] >> fsrw_tac [][] >>
srw_tac [][] >> fsrw_tac [][] >- (
  ntac 5 (srw_tac [][Once has_type_cases,FLOOKUP_UPDATE,APPLY_UPDATE_THM]))
>- (
  ntac 3 (srw_tac [][Once has_type_cases,FLOOKUP_UPDATE,APPLY_UPDATE_THM])) >>
`f1 ≠ n ∧ f2 ≠ n` by PROVE_TAC [] >>
qmatch_abbrev_tac `typed_cell (s with <|store updated_by x1 o x2; cell_type updated_by x3 o x4|>) {} n` >>
qsuff_tac `typed_cell ((s with <|store updated_by x2; cell_type updated_by x4|>) with <|store updated_by x1; cell_type updated_by x3|>) {} n` >- srw_tac [][] >>
unabbrev_all_tac >>
(has_type_assign_unbound |> CONJUNCT2 |> MP_CANON |> match_mp_tac) >>
srw_tac [][] >>
(has_type_assign_unbound |> CONJUNCT2 |> MP_CANON |> match_mp_tac) >>
srw_tac [][] >>
fsrw_tac [][typed_state_def]);

val AddToFrontOfList_wfstate = Q.store_thm(
"AddToFrontOfList_wfstate",
`wfstate s ∧ ((a = pnil) ∨ ptr_to_num a ∈ FDOM s.store ∧ (s.cell_type (ptr_to_num a) = emb.type)) ∧
 (AddToFrontOfList emb a l s = SOME p) ⇒
  wfstate (SND p)`,
qmatch_abbrev_tac `A ∧ B ∧ C ⇒ D` >>
map_every qunabbrev_tac [`A`,`C`,`D`] >>
fsrw_tac [][AddToFrontOfList_def,UNCURRY] >>
Cases_on `lookup emb l s` >> fsrw_tac [][] >>
Cases_on `l` >> fsrw_tac [][APPLY_UPDATE_THM] >>
Cases_on `s.cell_type n = List_type emb.type` >> fsrw_tac [][] >>
qmatch_assum_rename_tac `FLOOKUP s.store n = SOME lv` [] >>
Cases_on `lv` >> fsrw_tac [][] >>
qmatch_assum_rename_tac `FLOOKUP s.store n = SOME (List_value a1 a2)` [] >>
free_addr_elim_tac >> qx_gen_tac `m` >>
srw_tac [][] >>
`n ∈ FDOM s.store` by fsrw_tac [][FLOOKUP_DEF] >>
`m ≠ n` by PROVE_TAC [] >>
fsrw_tac [][wfstate_def,typed_state_def] >>
`n ≠ 0` by PROVE_TAC [] >>
fsrw_tac [][] >>
qx_gen_tac `p` >>
qmatch_abbrev_tac `G` >>
`typed_cell s {} n` by PROVE_TAC [] >>
pop_assum mp_tac >>
simp_tac (srw_ss()) [Once has_type_cases] >>
asm_simp_tac (srw_ss()) [] >>
asm_simp_tac (srw_ss()) [Once has_type_cases] >>
strip_tac >>
Cases_on `a1=n` >- fsrw_tac [][] >>
Cases_on `a2=n` >- fsrw_tac [][] >>
`a1 ≠ 0 ⇒ a1 ∈ FDOM s.store` by PROVE_TAC [IN_INSERT,NOT_IN_EMPTY,typed_cell_bound] >>
`a2 ≠ 0 ⇒ a2 ∈ FDOM s.store` by PROVE_TAC [IN_INSERT,NOT_IN_EMPTY,typed_cell_bound] >>
`a1 ≠ m` by PROVE_TAC [] >>
`a2 ≠ m` by metis_tac [] >>
`n ≠ ptr_to_num a` by (
  Cases_on `a` >> fsrw_tac [][] >>
  metis_tac [type_inductive] ) >>
`m ≠ ptr_to_num a` by metis_tac [ptr_equality,ptr_to_num_def] >>
`typed_cell s {} (ptr_to_num a)` by (
  Cases_on `a` >> fsrw_tac [][] >>
  qmatch_rename_tac `typed_cell s {} a` [] >>
  Cases_on `a=0` >- srw_tac [][Once has_type_cases] >>
  metis_tac [] ) >>
Q.UNABBREV_TAC `G` >>
qho_match_abbrev_tac `(p = n) ∨ (p = m) ∨ p ∈ FDOM s.store ⇒ typed_cell ss {} p` >>
Cases_on `p = n` >- (
  srw_tac [][Abbr`ss`,typed_cell_def,FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
  qmatch_abbrev_tac `has_type (s with <|store updated_by x1 o x2; cell_type updated_by x3 o x4|>) c v t` >>
  qsuff_tac `has_type ((s with <|store updated_by x2; cell_type updated_by x4|>) with <|store updated_by x1|>) c v t` >- (
    qsuff_tac `s with <|store updated_by x1; store updated_by x2; cell_type updated_by x4|> =
               s with <|store updated_by x1; cell_type updated_by x3; store updated_by x2; cell_type updated_by x4|>`
    >- srw_tac [][] >>
    srw_tac [][state_component_equality,Abbr`x3`,Abbr`x4`,FUN_EQ_THM,APPLY_UPDATE_THM] >>
    srw_tac [][] ) >>
  map_every Q.UNABBREV_TAC [`x1`,`x2`,`x3`,`x4`,`c`,`v`,`t`] >>
  (has_type_assign_bound |> CONJUNCT1 |> MP_CANON |> match_mp_tac) >>
  fsrw_tac [][APPLY_UPDATE_THM] >>
  srw_tac [][Once has_type_cases,APPLY_UPDATE_THM] >- (
    srw_tac [][typed_cell_def,FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
    (has_type_assign_cached_unbound |> CONJUNCT1 |> MP_CANON |> match_mp_tac) >>
    srw_tac [][Once has_type_cases,APPLY_UPDATE_THM] >-
      srw_tac [][has_type_INSERT_cached]
    >- ( Cases_on `a` >> fsrw_tac [][] >> metis_tac [] ) >>
    PROVE_TAC [has_type_INSERT_cached] ) >>
  (has_type_assign_unbound |> CONJUNCT2 |> MP_CANON |> match_mp_tac) >>
  srw_tac [][] ) >>
Cases_on `p = m` >- (
  srw_tac [][Abbr`ss`,typed_cell_def,FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
  qmatch_abbrev_tac `has_type (s with <|store updated_by x1 o x2; cell_type updated_by x3 o x4|>) c v t` >>
  qsuff_tac `has_type ((s with <|store updated_by x2; cell_type updated_by x4|>) with <|store updated_by x1|>) c v t` >- (
    qsuff_tac `s with <|store updated_by x1; store updated_by x2; cell_type updated_by x4|> =
               s with <|store updated_by x1; cell_type updated_by x3; store updated_by x2; cell_type updated_by x4|>`
    >- srw_tac [][] >>
    srw_tac [][state_component_equality,Abbr`x3`,Abbr`x4`,FUN_EQ_THM,APPLY_UPDATE_THM] >>
    srw_tac [][] >> srw_tac [][] ) >>
  map_every Q.UNABBREV_TAC [`x1`,`x2`,`x3`,`x4`,`c`,`v`,`t`] >>
  (has_type_assign_bound |> CONJUNCT1 |> MP_CANON |> match_mp_tac) >>
  fsrw_tac [][APPLY_UPDATE_THM] >>
  conj_tac >- (
    (has_type_assign_cached_unbound |> CONJUNCT1 |> MP_CANON |> match_mp_tac) >>
    srw_tac [][Once has_type_cases] >-
      srw_tac [][has_type_INSERT_cached]
    >- ( Cases_on `a` >> fsrw_tac [][] >> metis_tac [] ) >>
    Cases_on `a1=0` >- srw_tac [][Once has_type_cases] >>
    fsrw_tac [][] >>
    srw_tac [][has_type_INSERT_cached] ) >>
  srw_tac [][Once has_type_cases,APPLY_UPDATE_THM] >-
    srw_tac [][typed_cell_def] >>
  (has_type_assign_cached_unbound |> CONJUNCT2 |> MP_CANON |> match_mp_tac) >>
  srw_tac [][] >>
  Cases_on `a2=0` >- srw_tac [][Once has_type_cases] >>
  fsrw_tac [][] >>
  srw_tac [][has_type_INSERT_cached] ) >>
srw_tac [][Abbr`ss`] >>
qmatch_abbrev_tac `typed_cell (s with <|store updated_by x1 o x2; cell_type updated_by x3 o x4|>) {} p` >>
qsuff_tac `typed_cell ((s with <|store updated_by x2; cell_type updated_by x4|>) with <|store updated_by x1|>) {} p` >- (
  qsuff_tac `s with <|store updated_by x1; store updated_by x2; cell_type updated_by x4|> =
             s with <|store updated_by x1; cell_type updated_by x3; store updated_by x2; cell_type updated_by x4|>`
  >- srw_tac [][] >>
  srw_tac [][state_component_equality,Abbr`x3`,Abbr`x4`,FUN_EQ_THM,APPLY_UPDATE_THM] >>
  srw_tac [][] >> srw_tac [][] ) >>
map_every Q.UNABBREV_TAC [`x1`,`x2`,`x3`,`x4`] >>
(has_type_assign_bound |> CONJUNCT2 |> MP_CANON |> match_mp_tac) >>
fsrw_tac [][APPLY_UPDATE_THM] >>
conj_tac >- (
  (has_type_assign_unbound |> CONJUNCT2 |> MP_CANON |> match_mp_tac) >>
  srw_tac [][] ) >>
srw_tac [][Once has_type_cases,APPLY_UPDATE_THM] >- (
  srw_tac [][typed_cell_def,FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
  (has_type_assign_cached_unbound |> CONJUNCT1 |> MP_CANON |> match_mp_tac) >>
  srw_tac [][Once has_type_cases] >-
    srw_tac [][has_type_INSERT_cached]
  >- ( Cases_on `a` >> fsrw_tac [][] >> metis_tac [] ) >>
  Cases_on `a1=0` >- srw_tac [][Once has_type_cases] >>
  fsrw_tac [][] >>
  srw_tac [][has_type_INSERT_cached] ) >>
(has_type_assign_unbound |> CONJUNCT2 |> MP_CANON |> match_mp_tac) >>
srw_tac [][typed_cell_def] >>
srw_tac [][FLOOKUP_DEF] >- (
  `typed_cell s {} a2` by res_tac >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [typed_cell_def,FLOOKUP_DEF] >>
  srw_tac [][] ) >>
PROVE_TAC []);

val _ = export_theory ()
