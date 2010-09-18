open HolKernel bossLib boolLib boolSimps SatisfySimps Parse ptypes_definitionsTheory pred_setTheory finite_mapTheory optionTheory state_optionTheory pairTheory combinTheory relationTheory reachTheory lcsymtacs option_guardTheory

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
val _ = augment_srw_ss [rewrites [OPTION_BIND_def,OPTION_IGNORE_BIND_def,OPTION_GUARD_def]]

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
qpat_assum `X = SOME s` mp_tac >>
fsrw_tac [][FLOOKUP_DEF] >>
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
Cases_on `p1` >> Cases_on `p2` >>
ntac 2 (srw_tac [][]) >> fsrw_tac [][] >>
srw_tac [][DOMSUB_FLOOKUP_THM] >>
srw_tac [][FLOOKUP_DEF] >>
qmatch_assum_rename_tac `s.cell_type m = emb.type` [] >>
Cases_on `emb.project (s.store ' m)` >> srw_tac [][]);

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
`is_embed emb ∧ (raw_assign emb p a s = SOME x) ⇒ (raw_lookup emb p (SND x) = SOME (a,SND x))`,
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
Cases_on `p` >> srw_tac [][FUN_EQ_THM,APPLY_UPDATE_THM] >> ntac 2 (srw_tac [][]));

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

val assign_FDOM = Q.store_thm(
"assign_FDOM",
`(raw_assign emb p v s = SOME x) ⇒
 (FDOM (SND x).store = (ptr_to_num p) INSERT (FDOM s.store))`,
Cases_on `p` >> srw_tac [][] >> srw_tac [][]);

val assign_comm = Q.store_thm(
"assign_comm",
`ptr_to_num p1 ≠ ptr_to_num p2 ∧
 (raw_assign emb1 p1 v1 s = SOME x1) ∧
 (raw_assign emb2 p2 v2 s = SOME x2) ⇒
 (raw_assign emb1 p1 v1 (SND x2) = raw_assign emb2 p2 v2 (SND x1))`,
srw_tac [][] >>
imp_res_tac assign_store >>
imp_res_tac assign_cell_type >>
imp_res_tac assign_FDOM >>
Cases_on `p1` >> Cases_on `p2` >> srw_tac [][] >>
fsrw_tac [][APPLY_UPDATE_THM] >>
fsrw_tac [][state_component_equality] >>
srw_tac [][] >> fsrw_tac [][] >>
srw_tac [][FUPDATE_COMMUTES] >>
srw_tac [][UPDATE_COMMUTES] >>
TRY (qpat_assum `X ≠ emb2.type` mp_tac >> srw_tac [][]) >>
srw_tac [][FUN_EQ_THM,APPLY_UPDATE_THM] >>
srw_tac [][] >>
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
fsrw_tac [DNF_ss][EXISTS_PROD] >>
free_addr_elim_tac >> qx_gen_tac `m` >>
strip_tac >>
`n ∈ FDOM s.store` by fsrw_tac [][FLOOKUP_DEF] >>
`m ≠ n` by PROVE_TAC [] >>
fsrw_tac [][APPLY_UPDATE_THM] >>
srw_tac [][] >>
fsrw_tac [][wfstate_def,typed_state_def] >>
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
  qmatch_abbrev_tac `has_type (s with <|store updated_by x1 o x2; cell_type updated_by x4|>) c v t` >>
  qsuff_tac `has_type ((s with <|store updated_by x2; cell_type updated_by x4|>) with <|store updated_by x1|>) c v t`
    >- srw_tac [][] >>
  map_every Q.UNABBREV_TAC [`x1`,`x2`,`x4`,`c`,`v`,`t`] >>
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
  qmatch_abbrev_tac `has_type (s with <|store updated_by x1 o x2; cell_type updated_by x4|>) c v t` >>
  qsuff_tac `has_type ((s with <|store updated_by x2; cell_type updated_by x4|>) with <|store updated_by x1|>) c v t`
    >- srw_tac [][] >>
  map_every Q.UNABBREV_TAC [`x1`,`x2`,`x4`,`c`,`v`,`t`] >>
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
qmatch_abbrev_tac `typed_cell (s with <|store updated_by x1 o x2; cell_type updated_by x4|>) {} p` >>
qsuff_tac `typed_cell ((s with <|store updated_by x2; cell_type updated_by x4|>) with <|store updated_by x1|>) {} p`
  >- srw_tac [][] >>
map_every Q.UNABBREV_TAC [`x1`,`x2`,`x4`] >>
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

val list_of_AuxList_assign_unbound = Q.store_thm(
"list_of_AuxList_assign_unbound",
`∀p ls. list_of_AuxList emb s l p ls ⇒
        m ∉ FDOM s.store ⇒
        list_of_AuxList emb (s with <|store updated_by (m =+ w); cell_type updated_by (m =+ a)|>) l p ls`,
ho_match_mp_tac list_of_AuxList_ind >>
conj_tac >- srw_tac [][Once list_of_AuxList_cases] >>
rpt strip_tac >>
srw_tac [][Once list_of_AuxList_cases,UNCURRY] >>
fsrw_tac [][UNCURRY] >>
`ptr_to_num p ≠ m` by (
  fsrw_tac [][FLOOKUP_DEF,lookup_succeeds] >>
  PROVE_TAC [] ) >>
srw_tac [][lookup_succeeds,FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
srw_tac [DNF_ss][] >>
fsrw_tac [][lookup_succeeds] >> srw_tac [][] >>
srw_tac [][EXISTS_PROD] >>
srw_tac [][APPLY_UPDATE_THM,FLOOKUP_UPDATE] >>
fsrw_tac [][FLOOKUP_DEF]);

val tailR1_def = Define`
  tailR1 s l n1 n2 = n2 ≠ ptr_to_num l ∧ ∃h. FLOOKUP s n2 = SOME (AuxList_value h n1)`;
val _ = overload_on("tailR", ``λs last. RTC (tailR1 s last)``);

val list_of_AuxList_tailR_type = Q.store_thm(
"list_of_AuxList_tailR_type",
`∀p ls. list_of_AuxList emb s l p ls ⇒
        wfstate s ∧ (s.cell_type (ptr_to_num p) = AuxList_type emb.type) ∧
        tailR s.store l m (ptr_to_num p) ∧ m ≠ 0 ⇒
        (s.cell_type m = AuxList_type emb.type)`,
ho_match_mp_tac list_of_AuxList_ind >>
conj_tac >- srw_tac [][Once RTC_CASES2,tailR1_def] >>
srw_tac [][UNCURRY] >>
fsrw_tac [][] >> srw_tac [][] >>
qpat_assum `tailR ss l m pp` mp_tac >>
srw_tac [][Once RTC_CASES2,tailR1_def] >- srw_tac [][] >>
fsrw_tac [][lookup_succeeds] >>
qpat_assum `X = FST x` (assume_tac o SYM) >>
fsrw_tac [][] >>
`typed_cell s {} (ptr_to_num p)` by
  fsrw_tac [][FLOOKUP_DEF,wfstate_def,typed_state_def] >>
pop_assum mp_tac >> asm_simp_tac (srw_ss()) [typed_cell_def] >>
qmatch_assum_rename_tac `FLOOKUP (SND x).store h = SOME v` [] >>
Cases_on `x` >> fsrw_tac [][] >>
srw_tac [][Once has_type_cases] >>
qpat_assum `tailR ss l m u` mp_tac >>
srw_tac [][Once RTC_CASES2,tailR1_def] >-
  (first_x_assum match_mp_tac >> first_assum ACCEPT_TAC) >>
fsrw_tac [][wfstate_def,FLOOKUP_DEF] >>
first_x_assum match_mp_tac >>
first_x_assum match_mp_tac >>
PROVE_TAC []);

val headR_def = Define`
  headR s l n1 n2 = ∃a t. tailR s l a n2 ∧ (FLOOKUP s a = SOME (AuxList_value n1 t))`;

val list_of_AuxList_headR_type = Q.store_thm(
"list_of_AuxList_headR_type",
`∀p ls. list_of_AuxList emb s l p ls ⇒
        wfstate s ∧ (s.cell_type (ptr_to_num p) = AuxList_type emb.type) ∧
        headR s.store l m (ptr_to_num p) ∧ m ≠ 0 ⇒
        (s.cell_type m = emb.type)`,
ho_match_mp_tac list_of_AuxList_ind >>
conj_tac >- (
  srw_tac [][Once RTC_CASES2,headR_def,tailR1_def] >>
  fsrw_tac [][FLOOKUP_DEF,wfstate_def,typed_state_def,typed_cell_def] >>
  res_tac >> pop_assum mp_tac >>
  simp_tac (srw_ss()) [Once has_type_cases] >>
  srw_tac [][] ) >>
srw_tac [][UNCURRY] >>
fsrw_tac [][] >> srw_tac [][] >>
qpat_assum `headR ss l m pp` mp_tac >>
srw_tac [][headR_def,Once RTC_CASES2,tailR1_def] >- (
  fsrw_tac [][lookup_succeeds,FLOOKUP_DEF,wfstate_def,typed_state_def,typed_cell_def] >>
  res_tac >> pop_assum mp_tac >>
  simp_tac (srw_ss()) [Once has_type_cases] >>
  srw_tac [][] ) >>
fsrw_tac [][lookup_succeeds] >>
qpat_assum `X = FST x` (assume_tac o SYM) >>
fsrw_tac [][] >>
`typed_cell s {} (ptr_to_num p)` by
  fsrw_tac [][FLOOKUP_DEF,wfstate_def,typed_state_def] >>
pop_assum mp_tac >> asm_simp_tac (srw_ss()) [typed_cell_def] >>
qmatch_assum_rename_tac `FLOOKUP (SND x).store h = SOME v` [] >>
Cases_on `x` >> fsrw_tac [][] >>
srw_tac [][Once has_type_cases] >>
qpat_assum `tailR ss l a u` mp_tac >>
srw_tac [][Once RTC_CASES2,tailR1_def] >- (
  first_x_assum match_mp_tac >>
  fsrw_tac [][FLOOKUP_DEF,wfstate_def] >>
  `a ≠ 0` by PROVE_TAC [] >>
  fsrw_tac [][] >>
  srw_tac [][headR_def,FLOOKUP_DEF] >>
  srw_tac [][Once RTC_CASES2,tailR1_def,FLOOKUP_DEF] >>
  PROVE_TAC [] ) >>
fsrw_tac [][wfstate_def,FLOOKUP_DEF] >>
first_x_assum match_mp_tac >>
conj_tac >- (
  first_x_assum match_mp_tac >>
  PROVE_TAC [] ) >>
srw_tac [][headR_def,FLOOKUP_DEF] >>
srw_tac [][Once RTC_CASES2,tailR1_def,FLOOKUP_DEF] >>
PROVE_TAC [] );

val list_of_AuxList_assign_unreachable = Q.store_thm(
"list_of_AuxList_assign_unreachable",
`∀p ls. list_of_AuxList emb s l p ls ⇒
        ¬ headR s.store l m (ptr_to_num p) ∧ ¬ tailR s.store l m (ptr_to_num p) ⇒
        list_of_AuxList emb (s with <|store updated_by (m =+ w); cell_type updated_by (m =+ a)|>) l p ls`,
ho_match_mp_tac list_of_AuxList_ind >>
conj_tac >- srw_tac [][Once list_of_AuxList_cases] >>
rpt strip_tac >>
srw_tac [][Once list_of_AuxList_cases] >>
fsrw_tac [][UNCURRY] >> srw_tac [][] >>
fsrw_tac [][] >> srw_tac [][] >>
`ptr_to_num p ≠ m` by PROVE_TAC [RTC_RULES] >>
srw_tac [DNF_ss][EXISTS_PROD,lookup_succeeds,FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
fsrw_tac [][lookup_succeeds] >>
qmatch_assum_rename_tac `FLOOKUP s.store (ptr_to_num p) = SOME v` [] >>
qmatch_assum_rename_tac `project_AuxList v = SOME (FST x)` [] >>
Cases_on `v` >> fsrw_tac [][] >>
qmatch_assum_rename_tac `FLOOKUP s.store (ptr_to_num p) = SOME (AuxList_value nh nt)` [] >>
`headR s.store l nh (ptr_to_num p)` by (
  srw_tac [][Once RTC_CASES2,headR_def,tailR1_def,ptr_equality,cell_reach1_def,reach1_cases] >>
  PROVE_TAC [] ) >>
`m ≠ nh` by PROVE_TAC [] >>
qpat_assum `X = FST x` (assume_tac o SYM) >>
qpat_assum `SND x = s` assume_tac >>
fsrw_tac [][] >>
first_x_assum match_mp_tac >>
`tailR1 s.store l nt (ptr_to_num p)` by (
  srw_tac [][tailR1_def,reach1_cases,ptr_equality] ) >>
PROVE_TAC [headR_def,RTC_RULES_RIGHT1]);

val list_of_AuxList_remove_unreachable = Q.store_thm(
"list_of_AuxList_remove_unreachable",
`∀p ls. list_of_AuxList emb s l p ls ⇒
        ¬ headR s.store l m (ptr_to_num p) ∧ ¬ tailR s.store l m (ptr_to_num p) ⇒
        list_of_AuxList emb (s with <|store updated_by (combin$C $\\ m); cell_type updated_by (m =+ a)|>) l p ls`,
ho_match_mp_tac list_of_AuxList_ind >>
conj_tac >- srw_tac [][Once list_of_AuxList_cases] >>
rpt strip_tac >>
srw_tac [][Once list_of_AuxList_cases] >>
fsrw_tac [][UNCURRY] >> srw_tac [][] >>
fsrw_tac [][] >> srw_tac [][] >>
`ptr_to_num p ≠ m` by PROVE_TAC [RTC_RULES] >>
srw_tac [DNF_ss][EXISTS_PROD,lookup_succeeds,DOMSUB_FLOOKUP_THM,APPLY_UPDATE_THM] >>
fsrw_tac [][lookup_succeeds] >>
qmatch_assum_rename_tac `FLOOKUP s.store (ptr_to_num p) = SOME v` [] >>
qmatch_assum_rename_tac `project_AuxList v = SOME (FST x)` [] >>
Cases_on `v` >> fsrw_tac [][] >>
qmatch_assum_rename_tac `FLOOKUP s.store (ptr_to_num p) = SOME (AuxList_value nh nt)` [] >>
`headR s.store l nh (ptr_to_num p)` by (
  srw_tac [][Once RTC_CASES2,headR_def,tailR1_def,ptr_equality,cell_reach1_def,reach1_cases] >>
  PROVE_TAC [] ) >>
`m ≠ nh` by PROVE_TAC [] >>
qpat_assum `X = FST x` (assume_tac o SYM) >>
qpat_assum `SND x = s` assume_tac >>
fsrw_tac [][] >>
first_x_assum match_mp_tac >>
`tailR1 s.store l nt (ptr_to_num p)` by (
  srw_tac [][tailR1_def,reach1_cases,ptr_equality] ) >>
PROVE_TAC [headR_def,RTC_RULES_RIGHT1]);

val tailR_assign_unreachable = Q.store_thm(
"tailR_assign_unreachable",
`¬tailR s l r n ⇒ (tailR (s |+ (r,v)) l m n ⇔ tailR s l m n)`,
strip_tac >> EQ_TAC >>
strip_tac >> qpat_assum `~tailR s l r n` mp_tac >>
pop_assum mp_tac >>
map_every qid_spec_tac [`n`,`m`] >>
ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
srw_tac [][] >- (
  qmatch_assum_rename_tac `tailR1 ss l n p` ["ss"] >>
  `p ≠ r` by PROVE_TAC [RTC_REFL] >>
  `tailR1 s l n p` by (
    fsrw_tac [][tailR1_def,FLOOKUP_UPDATE]) >>
  PROVE_TAC [RTC_RULES_RIGHT1] ) >>
qmatch_assum_rename_tac `tailR1 s l n p` [] >>
`p ≠ r` by PROVE_TAC [RTC_REFL] >>
`tailR1 (s |+ (r,v)) l n p` by (
  fsrw_tac [][tailR1_def,FLOOKUP_UPDATE] ) >>
PROVE_TAC [RTC_RULES_RIGHT1] );

val tailR_assign_last = Q.store_thm(
"tailR_assign_last",
`tailR (s |+ (ptr_to_num l,v)) l m n ⇔ tailR s l m n`,
EQ_TAC >> map_every qid_spec_tac [`n`,`m`] >>
ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
srw_tac [][] >|[
  `tailR1 s l n n'` by (
    fsrw_tac [][tailR1_def,FLOOKUP_UPDATE] >>
    pop_assum mp_tac >> srw_tac [][] ),
  `tailR1 (s |+ (ptr_to_num l,v)) l n n'` by (
    fsrw_tac [][tailR1_def,FLOOKUP_UPDATE] )] >>
PROVE_TAC [RTC_RULES_RIGHT1]);

val headR_assign_unreachable = Q.store_thm(
"headR_assign_unreachable",
`¬tailR s l r n ⇒ (headR (s |+ (r,v)) l m n ⇔ headR s l m n)`,
srw_tac [][headR_def] >>
srw_tac [][tailR_assign_unreachable] >>
srw_tac [][EQ_IMP_THM,FLOOKUP_UPDATE] >>
Cases_on `a=r` >> fsrw_tac [SATISFY_ss][] >>
qexists_tac `a` >>
srw_tac [][]);

val headR_assign_irrelevant_last = Q.store_thm(
"headR_assign_irrelevant_last",
`(∀t. FLOOKUP s (ptr_to_num l) ≠ SOME (AuxList_value m t) ∧ v ≠ AuxList_value m t) ⇒
 (headR (s |+ (ptr_to_num l,v)) l m n ⇔ headR s l m n)`,
srw_tac [][headR_def,tailR_assign_last,FLOOKUP_UPDATE] >>
srw_tac [][EQ_IMP_THM] >>
Cases_on `a = ptr_to_num l` >> fsrw_tac [SATISFY_ss][] >>
TRY (qexists_tac `a`) >>
srw_tac [][] >> fsrw_tac [DNF_ss][]);

val list_of_AuxList_assign_last = Q.store_thm(
"list_of_AuxList_assign_last",
`∀p ls. list_of_AuxList emb s l p ls ⇒
        ¬ headR s.store l (ptr_to_num l) (ptr_to_num p) ⇒
        list_of_AuxList emb (s with <|store updated_by (ptr_to_num l =+ v);
                                      cell_type updated_by (ptr_to_num l =+ t)|>) l p ls`,
ho_match_mp_tac list_of_AuxList_ind >>
conj_tac >- srw_tac [][Once list_of_AuxList_cases] >>
rpt strip_tac >>
srw_tac [][Once list_of_AuxList_cases] >>
fsrw_tac [][UNCURRY] >> srw_tac [][] >>
fsrw_tac [][] >> srw_tac [][] >>
srw_tac [DNF_ss][EXISTS_PROD] >>
srw_tac [][lookup_succeeds,FLOOKUP_UPDATE,ptr_equality] >>
fsrw_tac [][lookup_succeeds] >>
srw_tac [DNF_ss][] >>
qmatch_assum_rename_tac `project_AuxList av = SOME (FST a)` [] >>
Cases_on `av` >> Cases_on `a` >> fsrw_tac [][] >>
srw_tac [][] >> fsrw_tac [][] >>
qmatch_assum_rename_tac `FLOOKUP (SND pr).store (ptr_to_num p) = SOME (AuxList_value nh nt)` [] >>
Cases_on `pr` >> fsrw_tac [][] >>
qmatch_assum_rename_tac `FLOOKUP s.store nh = SOME hv` [] >>
`nh ≠ ptr_to_num l` by (
  spose_not_then strip_assume_tac >>
  srw_tac [][] >>
  fsrw_tac [][headR_def] >>
  pop_assum (qspec_then `ptr_to_num p` mp_tac) >>
  srw_tac [][] ) >>
srw_tac [][APPLY_UPDATE_THM,ptr_equality,FLOOKUP_UPDATE] >>
first_x_assum match_mp_tac >>
spose_not_then strip_assume_tac >>
fsrw_tac [][headR_def] >>
pop_assum mp_tac >> srw_tac [][] >>
fsrw_tac [][GSYM IMP_DISJ_THM] >>
first_x_assum match_mp_tac >>
srw_tac [][Once RTC_CASES2] >>
srw_tac [][tailR1_def,ptr_equality]);

val AddToFrontOfList_CONS = Q.store_thm(
"AddToFrontOfList_CONS",
`is_embed emb ∧ wfstate s0 ∧
 list_of_List emb s0 l0 ls ∧
 (OPTION_MAP FST (raw_lookup emb e s0) = SOME e') ⇒
 ∃l s. (AddToFrontOfList emb e l0 s0 = SOME (l,s)) ∧
       list_of_List emb s l (CONS e' ls)`,
simp_tac (srw_ss()) [AddToFrontOfList_def,UNCURRY,list_of_List_def] >>
Cases_on `lookup emb l0 s0` >> simp_tac (srw_ss()) [] >>
Cases_on `raw_lookup emb e s0` >> simp_tac (srw_ss()) [] >>
imp_res_tac lookup_state >>
srw_tac [DNF_ss][] >>
qmatch_assum_rename_tac `lookup emb l0 (SND p) = SOME p` [] >>
Cases_on `p` >> fsrw_tac [][] >> srw_tac [][] >>
qmatch_assum_rename_tac `raw_lookup emb e (SND p) = SOME p` [] >>
Cases_on `p` >> fsrw_tac [][] >>
free_addr_elim_tac >>
qx_gen_tac `n` >> strip_tac >>
qmatch_assum_rename_tac `n ∉ FDOM s.store` [] >>
srw_tac [][] >>
qho_match_abbrev_tac `?x z. (assign emb l0 lv ss = SOME x) ∧ (lookup emb l0 (SND x) = SOME z) ∧ X x z` >>
`?x. assign emb l0 lv ss = SOME x` by (
  Cases_on `l0` >> fsrw_tac [DNF_ss][] >>
  qmatch_assum_rename_tac `s.cell_type n0 = List_type emb.type` [] >>
  `n0 ∈ FDOM s.store` by fsrw_tac [][FLOOKUP_DEF] >>
  `n0 ≠ 0` by PROVE_TAC [wfstate_def] >>
  srw_tac [][Abbr`ss`,APPLY_UPDATE_THM] >>
  fsrw_tac [][]) >>
srw_tac [][] >>
`lookup emb l0 (SND x) = SOME (lv,SND x)` by (
  match_mp_tac (GEN_ALL lookup_assign) >>
  qexists_tac `ss` >> srw_tac [][is_embed_List] ) >>
srw_tac [][Abbr`X`] >>
srw_tac [DNF_ss][Once list_of_AuxList_cases,UNCURRY] >>
`lv.first ≠ lv.last` by (
  srw_tac [][Abbr`lv`] >>
  srw_tac [][GSYM ptr_equality] >>
  qmatch_rename_tac `n ≠ ptr_to_num l.last` [] >>
  Cases_on `ptr_to_num l.last ∈ FDOM s.store` >- PROVE_TAC [] >>
  qsuff_tac `ptr_to_num l.last = 0` >- srw_tac [][] >>
  match_mp_tac (GEN_ALL cell_reach_typed_state_unbound_eq_0) >>
  map_every qexists_tac [`s`,`ptr_to_num l0`] >>
  fsrw_tac [][wfstate_def] >>
  srw_tac [][Once RTC_CASES2,cell_reach1_def] >- (
    fsrw_tac [][lookup_succeeds] >>
    Cases_on `v` >> fsrw_tac [][] >>
    srw_tac [][reach1_cases] >>
    PROVE_TAC [RTC_RULES] ) >>
  fsrw_tac [][lookup_succeeds,FLOOKUP_DEF] >>
  PROVE_TAC [] ) >>
`ptr_to_num l0 ≠ ptr_to_num lv.first` by (
  spose_not_then strip_assume_tac >>
  fsrw_tac [][lookup_succeeds,FLOOKUP_DEF,Abbr`lv`] ) >>
imp_res_tac assign_cell_type >>
srw_tac [DNF_ss][lookup_succeeds,APPLY_UPDATE_THM] >>
imp_res_tac assign_store >>
`FLOOKUP (SND x).store (ptr_to_num lv.first) =
 FLOOKUP ((SND x).store \\ ptr_to_num l0) (ptr_to_num lv.first)` by
   srw_tac [][DOMSUB_FLOOKUP_THM] >>
srw_tac [][Abbr`ss`] >>
pop_assum (K ALL_TAC) >>
srw_tac [][DOMSUB_FLOOKUP_THM] >>
srw_tac [][Abbr`lv`,FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
srw_tac [][EXISTS_PROD] >>
`ptr_to_num l0 ≠ ptr_to_num e` by (
  spose_not_then strip_assume_tac >>
  fsrw_tac [][lookup_succeeds] >>
  fsrw_tac [][type_inductive] ) >>
`FLOOKUP (SND x).store (ptr_to_num e) =
 FLOOKUP ((SND x).store \\ ptr_to_num l0) (ptr_to_num e)` by
   srw_tac [][DOMSUB_FLOOKUP_THM] >>
srw_tac [][] >>
srw_tac [][DOMSUB_FLOOKUP_THM] >>
`ptr_to_num e ≠ n` by (fsrw_tac [][lookup_succeeds,FLOOKUP_DEF] >> PROVE_TAC []) >>
srw_tac [][FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
fsrw_tac [][lookup_succeeds] >>
qmatch_assum_rename_tac `FLOOKUP s.store (ptr_to_num l0) = SOME v` [] >>
Cases_on `v` >> fsrw_tac [][] >>
qmatch_assum_rename_tac `FLOOKUP s.store (ptr_to_num l0) = SOME (List_value a1 a2)` [] >>
Cases_on `l0` >> fsrw_tac [][] >>
srw_tac [][] >> fsrw_tac [][] >>
qmatch_assum_rename_tac `FLOOKUP s.store l0 = SOME (List_value a1 a2)` [] >>
`l0 ∈ FDOM s.store` by fsrw_tac [][FLOOKUP_DEF] >>
fsrw_tac [][] >>
srw_tac [][] >>
qmatch_abbrev_tac `list_of_AuxList emb (s with <|store updated_by x1 o x2; cell_type updated_by x4|>) pa2 pa1 ls` >>
qsuff_tac `list_of_AuxList emb ((s with <|store updated_by x1; cell_type updated_by (l0 =+ (s.cell_type l0))|>) with <|store updated_by x2; cell_type updated_by x4|>) pa2 pa1 ls` >- (
  srw_tac [][] >>
  qsuff_tac `s with <|store updated_by x1 o x2; cell_type updated_by x4|> = s with <|store updated_by x2 o x1; cell_type updated_by x4 o (l0 =+ List_type emb.type)|>` >- metis_tac [] >>
  srw_tac [][state_component_equality,Abbr`x1`,Abbr`x2`,FUPDATE_COMMUTES,Abbr`x4`] >>
  srw_tac [][FUN_EQ_THM,APPLY_UPDATE_THM] >>
  srw_tac [][] >>
  fsrw_tac [][lookup_succeeds]) >>
unabbrev_all_tac >>
match_mp_tac (MP_CANON list_of_AuxList_assign_unbound) >>
srw_tac [][] >>
match_mp_tac (MP_CANON list_of_AuxList_assign_unreachable) >>
srw_tac [][] >- (
  spose_not_then strip_assume_tac >>
  qsuff_tac `s.cell_type l0 = emb.type` >- srw_tac [][type_inductive] >>
  match_mp_tac (MP_CANON (GEN_ALL list_of_AuxList_headR_type)) >>
  qmatch_assum_abbrev_tac `list_of_AuxList emb s pa2 pa1 ls` >>
  map_every qexists_tac [`pa2`,`pa1`,`ls`] >>
  `l0 ∈ FDOM s.store` by fsrw_tac [][FLOOKUP_DEF] >>
  fsrw_tac [][wfstate_def] >>
  `l0 ≠ 0` by PROVE_TAC [] >>
  srw_tac [][Abbr`pa1`] >>
  imp_res_tac typed_state_def >>
  pop_assum mp_tac >>
  asm_simp_tac (srw_ss()) [typed_cell_def] >>
  srw_tac [][Once has_type_cases] >>
  first_x_assum match_mp_tac >>
  fsrw_tac [][headR_def] >>
  fsrw_tac [][Once RTC_CASES2,FLOOKUP_DEF,tailR1_def] >>
  PROVE_TAC [] ) >>
spose_not_then strip_assume_tac >>
qsuff_tac `s.cell_type l0 = AuxList_type emb.type` >- srw_tac [][] >>
match_mp_tac (MP_CANON (GEN_ALL list_of_AuxList_tailR_type)) >>
qmatch_assum_abbrev_tac `list_of_AuxList emb s pa2 pa1 ls` >>
map_every qexists_tac [`pa2`,`pa1`,`ls`] >>
fsrw_tac [][wfstate_def] >>
srw_tac [][Abbr`pa1`] >>
imp_res_tac typed_state_def >>
pop_assum mp_tac >>
asm_simp_tac (srw_ss()) [typed_cell_def] >>
srw_tac [][Once has_type_cases] >>
first_x_assum match_mp_tac >>
fsrw_tac [][Once RTC_CASES2,FLOOKUP_DEF,tailR1_def] >>
PROVE_TAC []);

val list_of_AuxList_SNOC = Q.store_thm(
"list_of_AuxList_SNOC",
`∀p ls. list_of_AuxList emb s l1 p ls ⇒
        (OPTION_MAP FST (lookup emb l1 s) = SOME (AuxList h l2)) ∧
        ¬ tailR s.store l1 (ptr_to_num l2) (ptr_to_num p) ∧
        (OPTION_MAP FST (raw_lookup emb h s) = SOME e) ⇒
        list_of_AuxList emb s l2 p (SNOC e ls)`,
ho_match_mp_tac list_of_AuxList_ind >>
conj_tac >- (
  srw_tac [DNF_ss][Once list_of_AuxList_cases,UNCURRY] >>
  fsrw_tac [][lookup_succeeds] >>
  srw_tac [DNF_ss][EXISTS_PROD] >>
  qpat_assum `AuxList h l2 = X` (assume_tac o SYM) >>
  fsrw_tac [][] >>
  srw_tac [][Once list_of_AuxList_cases] >>
  srw_tac [][GSYM ptr_equality] >>
  PROVE_TAC [RTC_RULES]) >>
rpt strip_tac >>
fsrw_tac [][UNCURRY] >> srw_tac [][] >>
fsrw_tac [][] >> srw_tac [][] >>
srw_tac [DNF_ss][Once list_of_AuxList_cases,UNCURRY] >- (
  srw_tac [][GSYM ptr_equality] >>
  PROVE_TAC [RTC_RULES] ) >>
fsrw_tac [][listTheory.SNOC_APPEND] >>
first_x_assum match_mp_tac >>
qmatch_assum_rename_tac `lookup emb p s = SOME l` [] >>
`tailR1 s.store l1 (ptr_to_num (FST l).tail) (ptr_to_num p)` by (
  srw_tac [][tailR1_def,ptr_equality] >>
  fsrw_tac [][lookup_succeeds] >>
  Cases_on `v` >> fsrw_tac [][] >>
  Cases_on `l` >> fsrw_tac [][] >>
  srw_tac [][] ) >>
PROVE_TAC [RTC_RULES_RIGHT1]);

val tailR_imp_cell_reach = Q.store_thm(
"tailR_imp_cell_reach",
`∀m n. tailR s l m n ⇒ cell_reach s m n`,
ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
srw_tac [][tailR1_def] >>
srw_tac [][Once RTC_CASES2,cell_reach1_def,reach1_cases] >>
PROVE_TAC []);

val AddToEndOfList_SNOC = Q.store_thm(
"AddToEndOfList_SNOC",
`wfstate s0 ∧ is_embed emb ∧
 list_of_List emb s0 l0 ls ∧
 (OPTION_MAP FST (raw_lookup emb e s0) = SOME e') ⇒
 ∃l s.
 (AddToEndOfList emb e l0 s0 = SOME (l,s)) ∧
 list_of_List emb s l (SNOC e' ls)`,
simp_tac (srw_ss()) [AddToEndOfList_def,UNCURRY,list_of_List_def] >>
Cases_on `lookup emb l0 s0` >> simp_tac (srw_ss()) [] >>
Cases_on `raw_lookup emb e s0` >> simp_tac (srw_ss()) [] >>
imp_res_tac lookup_state >>
srw_tac [DNF_ss][] >>
qmatch_assum_rename_tac `lookup emb l0 (SND p) = SOME p` [] >>
Cases_on `p` >> fsrw_tac [][] >> srw_tac [][] >>
qmatch_assum_rename_tac `raw_lookup emb e (SND p) = SOME p` [] >>
Cases_on `p` >> fsrw_tac [][] >>
free_addr_elim_tac >>
qx_gen_tac `n` >> strip_tac >>
qmatch_assum_rename_tac `n ∉ FDOM s.store` [] >>
srw_tac [][] >>
`ptr_to_num l0 ∈ FDOM s.store` by fsrw_tac [][lookup_succeeds,FLOOKUP_DEF] >>
fsrw_tac [][wfstate_def] >>
imp_res_tac typed_state_def >>
`ptr_to_num l0 ≠ n` by PROVE_TAC [] >>
srw_tac [][lookup_succeeds,FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
`?v. FLOOKUP s.store (ptr_to_num l0) = SOME v` by fsrw_tac [][lookup_succeeds] >>
srw_tac [][] >>
`∃lv. project_List v = SOME lv` by fsrw_tac [][lookup_succeeds] >>
srw_tac [][EXISTS_PROD] >>
Cases_on `lv` >> fsrw_tac [][] >>
qmatch_assum_rename_tac `project_List v = SOME (List a1 a2)` [] >>
Cases_on `v` >> fsrw_tac [][] >>
`cell_reach s.store (ptr_to_num a1) (ptr_to_num l0)` by (
  srw_tac [][Once RTC_CASES2,cell_reach1_def,reach1_cases] >>
  PROVE_TAC [RTC_REFL] ) >>
`cell_reach s.store (ptr_to_num a2) (ptr_to_num l0)` by (
  srw_tac [][Once RTC_CASES2,cell_reach1_def,reach1_cases] >>
  PROVE_TAC [RTC_REFL] ) >>
`ptr_to_num l0 ≠ 0` by PROVE_TAC [] >>
`s.cell_type (ptr_to_num l0) = List_type emb.type` by (
  fsrw_tac [][typed_cell_def] >>
  fsrw_tac [][Once has_type_cases] >>
  fsrw_tac [][lookup_succeeds] ) >>
`ptr_to_num a1 ≠ ptr_to_num l0` by (
  spose_not_then strip_assume_tac >>
  srw_tac [][] >>
  fsrw_tac [][typed_cell_def,Once has_type_cases] ) >>
`ptr_to_num a2 ≠ ptr_to_num l0` by (
  spose_not_then strip_assume_tac >>
  srw_tac [][] >>
  fsrw_tac [][typed_cell_def, Once has_type_cases] ) >>
qmatch_assum_rename_tac `lookup emb l0 s = SOME (lv,s)` [] >>
`lv = List a1 a2` by fsrw_tac [][lookup_succeeds] >>
fsrw_tac [][] >>
`ptr_to_num a1 ∉ FDOM s.store ⇒ (ptr_to_num a1 = 0)` by (
  strip_tac >>
  match_mp_tac (GEN_ALL cell_reach_typed_state_unbound_eq_0) >>
  map_every qexists_tac [`s`,`ptr_to_num l0`] >>
  srw_tac [][] ) >>
`ptr_to_num a2 ∉ FDOM s.store ⇒ (ptr_to_num a2 = 0)` by (
  strip_tac >>
  match_mp_tac (GEN_ALL cell_reach_typed_state_unbound_eq_0) >>
  map_every qexists_tac [`s`,`ptr_to_num l0`] >>
  srw_tac [][] ) >>
`ptr_to_num a2 ∈ FDOM s.store` by (
  spose_not_then strip_assume_tac >>
  fsrw_tac [][GSYM ptr_equality] ) >>
fsrw_tac [][] >>
`ptr_to_num a1 ≠ n` by PROVE_TAC [] >>
`ptr_to_num a2 ≠ n` by PROVE_TAC [] >>
qpat_assum `X = a1` (assume_tac o SYM) >>
qpat_assum `X = a2` (assume_tac o SYM) >>
fsrw_tac [][APPLY_UPDATE_THM] >>
srw_tac [][] >>
qmatch_assum_rename_tac `FLOOKUP s.store (ptr_to_num l0) = SOME (List_value a1 a2)` [] >>
fsrw_tac [][typed_cell_def] >>
fsrw_tac [][Once has_type_cases] >>
qho_match_abbrev_tac `?p1 p2 p3 p4. (assign emb l0 (List pa1 pn) ss = SOME (p1,p2)) ∧ X p2 p3 p4` >>
`∃s'. assign emb l0 (List pa1 pn) ss = SOME ((),s')` by (
  Cases_on `l0` >> fsrw_tac [][Abbr`ss`,APPLY_UPDATE_THM] ) >>
srw_tac [DNF_ss][Abbr`X`] >>
imp_res_tac assign_cell_type >>
fsrw_tac [][APPLY_UPDATE_THM] >>
`is_embed (embed_List emb)` by srw_tac [][is_embed_List] >>
`lookup emb l0 s' = SOME (List pa1 pn, s')` by (
  imp_res_tac lookup_assign >>
  fsrw_tac [][] ) >>
`FLOOKUP s'.store (ptr_to_num l0) = SOME (List_value a1 n)` by (
  fsrw_tac [][lookup_succeeds] >>
  qmatch_rename_tac `w = List_value a1 n` [] >>
  Cases_on `w` >> fsrw_tac [][GSYM ptr_equality] ) >>
srw_tac [][GSYM ptr_equality,Abbr`pn`] >>
match_mp_tac (MP_CANON (GEN_ALL list_of_AuxList_SNOC)) >>
qabbrev_tac `pa2 = addr (:'a AuxList) a2` >>
qexists_tac `pa2` >> srw_tac [DNF_ss][EXISTS_PROD] >>
qexists_tac `e` >>
`ptr_to_num e ≠ ptr_to_num l0` by (
  fsrw_tac [][lookup_succeeds] >>
  PROVE_TAC [type_inductive] ) >>
srw_tac [DNF_ss][lookup_succeeds,APPLY_UPDATE_THM] >-
  fsrw_tac [][Abbr`pa2`] >>
imp_res_tac assign_store >>
`FLOOKUP s'.store (ptr_to_num pa2) = SOME (AuxList_value (ptr_to_num e) n)` by (
  `FLOOKUP s'.store (ptr_to_num pa2) = FLOOKUP (s'.store \\ ptr_to_num l0) (ptr_to_num pa2)` by
    srw_tac [][DOMSUB_FLOOKUP_THM] >>
  fsrw_tac [][] >>
  srw_tac [][Abbr`ss`,DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE,Abbr`pa2`] ) >>
srw_tac [][] >>
`ss.cell_type (ptr_to_num pa2) = AuxList_type emb.type` by (
  srw_tac [][Abbr`ss`,APPLY_UPDATE_THM,Abbr`pa2`] ) >>
srw_tac [][] >>
srw_tac [][GSYM ptr_equality] >>
`a2 ≠ ptr_to_num e` by (
  fsrw_tac [][lookup_succeeds] >>
  spose_not_then strip_assume_tac >>
  Cases_on `a2 = 0` >>
  fsrw_tac [][FLOOKUP_DEF,type_inductive] ) >>
`n ≠ ptr_to_num e` by (
  spose_not_then strip_assume_tac >>
  fsrw_tac [][lookup_succeeds,FLOOKUP_DEF] ) >>
qmatch_assum_rename_tac `raw_lookup emb e s = SOME (ev,s)` [] >>
`FLOOKUP s'.store (ptr_to_num e) = SOME (emb.inject ev)` by (
  `FLOOKUP s'.store (ptr_to_num e) = FLOOKUP (s'.store \\ ptr_to_num l0) (ptr_to_num e)` by
    srw_tac [][DOMSUB_FLOOKUP_THM] >>
  fsrw_tac [][] >>
  srw_tac [][Abbr`ss`,DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE] >>
  fsrw_tac [][lookup_succeeds] >>
  PROVE_TAC [is_embed_def] ) >>
`ss.cell_type (ptr_to_num e) = emb.type` by fsrw_tac [][lookup_succeeds,Abbr`ss`,APPLY_UPDATE_THM] >>
`emb.project (emb.inject ev) = SOME ev` by PROVE_TAC [is_embed_def] >>
fsrw_tac [][] >>
`list_of_AuxList emb ss pa2 pa1 ls` by (
  srw_tac [][Abbr`ss`] >>
  qmatch_abbrev_tac `list_of_AuxList emb (s with <|store updated_by (x1 o x2); cell_type updated_by x4|>) pa2 pa1 ls` >>
  qsuff_tac `list_of_AuxList emb ((s with <|store updated_by x1|>) with
                                          <|store updated_by x2; cell_type updated_by x4|>) pa2 pa1 ls` >- (
    srw_tac [][] >>
    qsuff_tac `s with <|store updated_by x1 o x2; cell_type updated_by x4|> =
               s with <|store updated_by x2 o x1; cell_type updated_by x4|>` >- metis_tac [] >>
    srw_tac [][state_component_equality,Abbr`x2`,Abbr`x1`,FUPDATE_COMMUTES] ) >>
  map_every qunabbrev_tac [`x1`,`x2`,`x4`] >>
  (list_of_AuxList_assign_unbound |> MP_CANON |> MATCH_MP_TAC) >>
  reverse conj_tac >- srw_tac [][] >>
  qmatch_abbrev_tac `list_of_AuxList emb ss pa2 pa1 ls` >>
  qabbrev_tac `sss = s with <|store updated_by (ptr_to_num pa2 =+ AuxList_value (ptr_to_num e) n);
                              cell_type updated_by (ptr_to_num pa2 =+ AuxList_type emb.type)|>` >>
  `ss = sss` by (
    srw_tac [][Abbr`ss`,Abbr`sss`,state_component_equality,Abbr`pa2`,Abbr`pa1`,FUN_EQ_THM,APPLY_UPDATE_THM] >>
    srw_tac [][] >>
    fsrw_tac [][] ) >>
  qsuff_tac `list_of_AuxList emb sss pa2 pa1 ls` >- srw_tac [][] >>
  qunabbrev_tac `sss` >>
  (list_of_AuxList_assign_last |> MP_CANON |> MATCH_MP_TAC) >>
  srw_tac [][] >>
  spose_not_then strip_assume_tac >>
  Cases_on `a1=0` >- (
    srw_tac [][] >>
    fsrw_tac [][Abbr`pa1`] >>
    fsrw_tac [][headR_def] >>
    fsrw_tac [][Once RTC_CASES2] >-
      (fsrw_tac [][FLOOKUP_DEF] >> PROVE_TAC []) >>
    fsrw_tac [][tailR1_def,FLOOKUP_DEF] >>
    PROVE_TAC [] ) >>
  `s.cell_type (ptr_to_num pa2) = emb.type` by (
    match_mp_tac (MP_CANON (GEN_ALL list_of_AuxList_headR_type)) >>
    map_every qexists_tac [`pa2`,`pa1`,`ls`] >>
    srw_tac [][wfstate_def] >>
    fsrw_tac [][Abbr`pa2`,Abbr`pa1`] ) >>
  fsrw_tac [][Abbr`pa2`,APPLY_UPDATE_THM] >>
  PROVE_TAC [type_inductive] ) >>
`¬tailR ss.store pa2 (ptr_to_num l0) (ptr_to_num pa1)` by (
  srw_tac [][Abbr`ss`,Abbr`pa2`] >>
  srw_tac [][tailR_assign_last
             |> Q.GEN `l` |> Q.ISPEC `addr (:'a AuxList) a2`
             |> SIMP_RULE (srw_ss()) []] >>
  qsuff_tac `~tailR s.store (addr (:'a AuxList) a2) n (ptr_to_num pa1)` >- (
    srw_tac [][tailR_assign_unreachable] >>
    spose_not_then strip_assume_tac >>
    `s.cell_type (ptr_to_num l0) = AuxList_type emb.type` by (
      match_mp_tac (MP_CANON (GEN_ALL list_of_AuxList_tailR_type)) >>
      map_every qexists_tac [`addr (:'a AuxList) a2`,`pa1`,`ls`] >>
      srw_tac [][wfstate_def,Abbr`pa1`] >>
      fsrw_tac [][Once RTC_CASES2,tailR1_def] >-
        srw_tac [][] >>
      fsrw_tac [][FLOOKUP_DEF] >>
      `a1 ≠ 0` by PROVE_TAC [] >>
      fsrw_tac [][] ) >>
    fsrw_tac [][] ) >>
  fsrw_tac [][Abbr`pa1`] >>
  PROVE_TAC [tailR_imp_cell_reach,cell_reach_typed_state_unbound_eq_0] ) >>
qmatch_assum_abbrev_tac `assign emb l0 v ss = SOME ((),sss)` >>
qunabbrev_tac `sss` >>
qmatch_assum_rename_tac `assign emb l0 v ss = SOME ((),sss)` [] >>
`sss = ss with store updated_by (ptr_to_num l0 =+ (embed_List emb).inject v)` by (
  qpat_assum `assign emb l0 v ss = X` mp_tac >>
  Cases_on `l0` >> fsrw_tac [][Abbr`ss`,APPLY_UPDATE_THM] ) >>
fsrw_tac [][tailR_assign_unreachable] >>
`¬tailR s.store pa2 n a1` by (
  qsuff_tac `~cell_reach s.store n a1` >-
  PROVE_TAC [tailR_imp_cell_reach] >>
  PROVE_TAC [cell_reach_typed_state_unbound_eq_0] ) >>
conj_tac >- (
  qsuff_tac `list_of_AuxList emb (ss with <|store updated_by (ptr_to_num l0 =+ (embed_List emb).inject v) ;
                                            cell_type updated_by (ptr_to_num l0 =+ List_type emb.type)|>)
                                 pa2 pa1 ls` >- (
    qmatch_abbrev_tac `list_of_AuxList emb ss1 pa2 pa1 ls ⇒ list_of_AuxList emb ss2 pa2 pa1 ls` >>
    qsuff_tac `ss1 = ss2` >- srw_tac [][] >>
    srw_tac [][Abbr`ss1`,Abbr`ss2`,state_component_equality] ) >>
  match_mp_tac (MP_CANON list_of_AuxList_assign_unreachable) >>
  srw_tac [][] >>
  srw_tac [][Abbr`ss`] >>
  qmatch_abbrev_tac `~headR (ss |+ (a2,av)) pa2 (ptr_to_num l0) (ptr_to_num pa1)` >>
  `a2 = ptr_to_num pa2` by srw_tac [][Abbr`pa2`] >>
  srw_tac [][] >>
  `∀t. FLOOKUP ss (ptr_to_num pa2) ≠ SOME (AuxList_value (ptr_to_num l0) t) ∧
       av ≠ AuxList_value (ptr_to_num l0) t` by (
    fsrw_tac [][markerTheory.Abbrev_def] >>
    srw_tac [][FLOOKUP_UPDATE] >>
    spose_not_then strip_assume_tac >>
    `typed_cell s {} (ptr_to_num pa2)` by PROVE_TAC [typed_state_def] >>
    pop_assum mp_tac >> srw_tac [][typed_cell_def] >>
    srw_tac [][Once has_type_cases,type_inductive] ) >>
  srw_tac [][headR_assign_irrelevant_last] >>
  qunabbrev_tac `ss` >>
  `¬tailR s.store pa2 n (ptr_to_num pa1)` by PROVE_TAC [ptr_to_num_def] >>
  srw_tac [][headR_assign_unreachable] >>
  spose_not_then strip_assume_tac >>
  `s.cell_type (ptr_to_num l0) = emb.type` by (
    match_mp_tac (MP_CANON (GEN_ALL list_of_AuxList_headR_type)) >>
    map_every qexists_tac [`pa2`,`pa1`,`ls`] >>
    fsrw_tac [][wfstate_def] >>
    srw_tac [][Abbr`pa1`] >>
    first_x_assum match_mp_tac >>
    fsrw_tac [][headR_def] >>
    `a ∈ FDOM s.store` by fsrw_tac [][FLOOKUP_DEF] >>
    Cases_on `a1=a` >- PROVE_TAC [] >>
    fsrw_tac [][Once RTC_CASES2,tailR1_def] >>
    `a1 ∈ FDOM s.store` by fsrw_tac [][FLOOKUP_DEF] >>
    PROVE_TAC [] ) >>
  PROVE_TAC [type_inductive] ) >>
`a2 = ptr_to_num pa2` by srw_tac [][Abbr`pa2`] >>
srw_tac [][Abbr`ss`,Abbr`pa1`] >>
srw_tac [][tailR_assign_last] >>
srw_tac [][tailR_assign_unreachable]);

val HeadOfList_HD = Q.store_thm(
"HeadOfList_HD",
`list_of_List emb s l (h::ls) ⇒
 ∃p.
 (HeadOfList emb l s = SOME (p,s)) ∧
 (raw_lookup emb p s = SOME (h,s))`,
srw_tac [][list_of_List_def,EXISTS_PROD] >>
fsrw_tac [][Once list_of_AuxList_cases,UNCURRY] >>
srw_tac [][] >> fsrw_tac [][] >> srw_tac [][] >>
srw_tac [][HeadOfList_def,UNCURRY,EXISTS_PROD] >>
fsrw_tac [][lookup_succeeds] >>
srw_tac [][]);

val EmptyList_NULL = Q.store_thm(
"EmptyList_NULL",
`list_of_List emb s l ls ⇒
 (EmptyList emb l s = SOME (ls = [],s))`,
srw_tac [][list_of_List_def,EmptyList_def,UNCURRY,EXISTS_PROD] >>
fsrw_tac [][lookup_succeeds] >> srw_tac [][] >>
EQ_TAC >> srw_tac [][] >>
fsrw_tac [][Once list_of_AuxList_cases]);

val list_of_AuxList_imp_tailR = Q.store_thm(
"list_of_AuxList_imp_tailR",
`∀p ls. list_of_AuxList emb s l p ls ⇒ tailR s.store l (ptr_to_num l) (ptr_to_num p)`,
ho_match_mp_tac list_of_AuxList_ind >>
srw_tac [][UNCURRY] >>
fsrw_tac [][] >> srw_tac [][] >>
srw_tac [][Once RTC_CASES2,tailR1_def] >>
fsrw_tac [][lookup_succeeds] >>
Cases_on `v` >> fsrw_tac [][] >>
qpat_assum `X = FST x` (assume_tac o SYM) >>
fsrw_tac [][] >> PROVE_TAC [] );

val list_of_AuxList_imp_tailR_antisymmetric = Q.store_thm(
"list_of_AuxList_imp_tailR_antisymmetric",
`∀p ls. list_of_AuxList emb s l p ls ⇒
        ∀m. tailR s.store l m (ptr_to_num p) ∧
            tailR s.store l (ptr_to_num p) m ⇒
            (m = ptr_to_num p)`,
ho_match_mp_tac list_of_AuxList_ind >>
srw_tac [][UNCURRY] >- (
  fsrw_tac [][Once RTC_CASES2,tailR1_def] ) >>
full_simp_tac std_ss [] >>
srw_tac [][] >>
qmatch_assum_rename_tac `lookup emb p s = SOME x` [] >>
`tailR s.store l (ptr_to_num (FST x).tail) (ptr_to_num p)` by (
  match_mp_tac RTC_SUBSET >>
  srw_tac [][tailR1_def,ptr_equality] >>
  fsrw_tac [][lookup_succeeds] >>
  Cases_on `v` >> fsrw_tac [][] >>
  qpat_assum `X = FST x` (assume_tac o SYM) >>
  fsrw_tac [][] ) >>
`tailR s.store l (ptr_to_num (FST x).tail) m` by PROVE_TAC [RTC_TRANSITIVE,transitive_def] >>
qpat_assum `tailR s.store l m (ptr_to_num p)` mp_tac >>
simp_tac (srw_ss()) [Once RTC_CASES2] >>
srw_tac [][tailR1_def] >>
fsrw_tac [][lookup_succeeds] >>
qpat_assum `X = FST x` (assume_tac o SYM) >>
fsrw_tac [][] >>
PROVE_TAC [RTC_TRANSITIVE,transitive_def]);

val TailOfList_TL = Q.store_thm(
"TailOfList_TL",
`wfstate s ∧ is_embed emb ∧
 list_of_List emb s l (h::ls) ⇒
 ∃s'. (TailOfList emb l s = SOME (l,s')) ∧
      (list_of_List emb s' l ls)`,
simp_tac (srw_ss()) [SimpL implication,list_of_List_def,Once list_of_AuxList_cases] >>
srw_tac [DNF_ss][list_of_List_def,TailOfList_def,UNCURRY,EXISTS_PROD] >>
imp_res_tac lookup_state >>
srw_tac [][] >> fsrw_tac [][] >> srw_tac [][] >>
qmatch_assum_rename_tac `lookup emb lv.first s = SOME (av,s)` [] >>
`∃s'. assign emb l (List av.tail lv.last) s = SOME ((),s')` by (
  Cases_on `l` >> srw_tac [][] >>
  fsrw_tac [][wfstate_def,FLOOKUP_DEF] >>
  PROVE_TAC [] ) >>
srw_tac [][] >>
`∃s''. dispose lv.first s' = SOME ((),s'')` by (
  Cases_on `lv.first` >> srw_tac [][] ) >>
srw_tac [][] >>
`lookup emb l s' = SOME (List av.tail lv.last,s')` by (
  `is_embed (embed_List emb)` by srw_tac [][is_embed_List] >>
  imp_res_tac lookup_assign >>
  fsrw_tac [][] ) >>
`lookup emb l s'' = SOME (List av.tail lv.last,s'')` by (
  imp_res_tac (lookup_dispose |> Q.GEN `p1` |> Q.ISPEC `lv.first`
                              |> Q.GEN `p2` |> Q.ISPEC `l:'a List ptr`) >>
  pop_assum (qspecl_then [`l`,`embed_List emb`] mp_tac) >>
  `ptr_to_num lv.first ≠ ptr_to_num l` by (
    fsrw_tac [][lookup_succeeds] >>
    spose_not_then strip_assume_tac >>
    fsrw_tac [][type_inductive] ) >>
  srw_tac [][] ) >>
srw_tac [][] >>
`s' = s with store updated_by (ptr_to_num l =+ (inject_List (List av.tail lv.last)))` by (
  Cases_on `l` >> fsrw_tac [][FLOOKUP_DEF] >>
  qpat_assum `n ∈ FDOM s.store` assume_tac >> fsrw_tac [][] ) >>
`s'' = s' with store updated_by (λs. s \\ ptr_to_num lv.first)` by (
  Cases_on `lv.first` >> fsrw_tac [][] ) >>

list_of_AuxList_dispose_unreachable

list_of_AuxList_assign_unreachable

val _ = export_theory ()
