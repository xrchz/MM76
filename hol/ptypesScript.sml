open HolKernel bossLib boolLib SatisfySimps Parse ptypes_definitionsTheory pred_setTheory finite_mapTheory optionTheory option_transformerTheory state_transformerTheory pairTheory combinTheory relationTheory lcsymtacs

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
`∀P s. (∀n. n ≠ 0 ∧ n ∉ FDOM s.store ⇒ P (addr (:'a) n,s)) ⇒ P (free_addr s)`,
srw_tac [][free_addr_def] >>
SELECT_ELIM_TAC >>
`∃x. x ∉ FDOM (s.store|+(0,ARB))` by srw_tac [][] >>
fsrw_tac [SATISFY_ss][]);

fun is_free_addr tm = let
  val (f,_) = dest_comb tm
  val ("free_addr",ty) = dest_const f
in
  can (match_type ``:state -> 'a ptr # state``) ty
end handle HOL_ERR _ => false | Bind => false

fun free_addr_elim_tac (g as (_, w)) = let
  val t = find_term is_free_addr w
in
  CONV_TAC (UNBETA_CONV t) THEN
  MATCH_MP_TAC free_addr_elim_thm THEN BETA_TAC
end g

val _ = augment_srw_ss [rewrites [BIND_DEF,IGNORE_BIND_DEF,UNIT_DEF,OPTIONT_BIND_def,OPTIONT_FAIL_def,OPTIONT_UNIT_def]]

val CreateList_empty = Q.store_thm(
"CreateList_empty",
`(CreateList emb s0 = (l, s)) ⇒ list_of_List emb s l []`,
simp_tac (srw_ss()) [CreateList_def,raw_new_def] >>
free_addr_elim_tac >> srw_tac [][UNCURRY] >>
free_addr_elim_tac >>
srw_tac [][list_of_List_def,Once list_of_AuxList_cases,EmptyList_def,FLOOKUP_UPDATE,APPLY_UPDATE_THM]);

val lookup_state = Q.store_thm(
"lookup_state",
`SND (raw_lookup emb ptr s) = s`,
Cases_on `emb` >> Cases_on `ptr` >>
srw_tac [][FLOOKUP_DEF] >> srw_tac [][]);
val _ = export_rewrites["lookup_state"];

val HeadOfList_state = Q.store_thm(
"HeadOfList_state",
`SND (HeadOfList emb l s) = s`,
`SND (lookup emb l s) = s` by MATCH_ACCEPT_TAC lookup_state >>
srw_tac [][HeadOfList_def,lookup_state,UNCURRY] >>
Cases_on `FST (lookup emb l s)` >> srw_tac [][] >>
`SND (lookup emb x.first s) = s` by MATCH_ACCEPT_TAC lookup_state >>
srw_tac [][UNCURRY] >>
Cases_on `FST (lookup emb x.first s)` >> srw_tac [][]);
val _ = export_rewrites["HeadOfList_state"];

val TailOfList_store = Q.store_thm(
"TailOfList_store",
`(lookup emb l s = (SOME l', s')) ⇒ ((SND (TailOfList emb l s)).store \\ (ptr_to_num l) \\ (ptr_to_num l'.first) = s.store \\ (ptr_to_num l) \\ (ptr_to_num l'.first))`,
srw_tac [][TailOfList_def,UNCURRY] >>
`s' = s` by PROVE_TAC [lookup_state,SND] >>
`SND (lookup emb l'.first s) = s` by PROVE_TAC [lookup_state,SND] >>
Cases_on `FST (lookup emb l'.first s)` >> srw_tac [][] >>
Cases_on `l` >> Cases_on `l'.first` >>
srw_tac [][DOMSUB_COMMUTES]);

val EmptyList_state = Q.store_thm(
"EmptyList_state",
`SND (EmptyList emb l s) = s`,
srw_tac [][EmptyList_def,lookup_state,UNCURRY] >>
Cases_on `FST (lookup emb l s) ` >> srw_tac [][]);
val _ = export_rewrites["EmptyList_state"];

val dispose_store = Q.store_thm(
"dispose_store",
`s.store \\ ptr_to_num p = (SND (dispose p s)).store \\ ptr_to_num p`,
Cases_on `p` >> srw_tac [][]);

val dispose_cell_type = Q.store_thm(
"dispose_cell_type",
`(SND (dispose p s)).cell_type = s.cell_type`,
Cases_on `p` >> srw_tac [][]);

val lookup_dispose = Q.store_thm(
"lookup_dispose",
`raw_lookup emb p2 (SND (dispose p1 s)) = (if ptr_to_num p1 = ptr_to_num p2 then NONE else (FST (raw_lookup emb p2 s)), (SND (dispose p1 s)))`,
Cases_on `p1` >> Cases_on `p2` >> srw_tac [][] >>
fsrw_tac [][DOMSUB_FLOOKUP_THM] >>
srw_tac [][FLOOKUP_DEF] >> srw_tac [][]);

val lookup_fails = Q.store_thm(
"lookup_fails",
`(FST (raw_lookup emb p s) = NONE) ⇔ (∀v. (FLOOKUP s.store (ptr_to_num p) = SOME v) ⇒ (s.cell_type (ptr_to_num p) = emb.type) ⇒ (emb.project v = NONE))`,
Cases_on `p` >> srw_tac [][FLOOKUP_DEF] >> srw_tac [][]);

val lookup_succeeds = Q.store_thm(
"lookup_succeeds",
`(FST (raw_lookup emb p s) = SOME a) ⇔ ∃v. (FLOOKUP s.store (ptr_to_num p) = SOME v) ∧ (s.cell_type (ptr_to_num p) = emb.type) ∧ (emb.project v = SOME a)`,
Cases_on `FST (raw_lookup emb p s)` >- (
  PROVE_TAC [lookup_fails,NOT_SOME_NONE] ) >>
Cases_on `FLOOKUP s.store (ptr_to_num p)` >>
Cases_on `p` >> fsrw_tac [][] >>
Cases_on `s.cell_type n = emb.type` >> fsrw_tac [][]);

val lookup_assign = Q.store_thm(
"lookup_assign",
`is_embed emb ⇒ (FST (raw_lookup emb p (SND (raw_assign emb p a s))) = SOME a)`,
Cases_on `p` >> srw_tac [][FLOOKUP_UPDATE,APPLY_UPDATE_THM,is_embed_def] >> PROVE_TAC []);

val assign_store = Q.store_thm(
"assign_store",
`(SND (raw_assign emb p v s)).store \\ ptr_to_num p = s.store \\ ptr_to_num p`,
Cases_on `p` >> srw_tac [][]);

val assign_cell_type = Q.store_thm(
"assign_cell_type",
`(SND (raw_assign emb p v s)).cell_type = ((ptr_to_num p) =+ emb.type) s.cell_type`,
Cases_on `p` >> srw_tac [][]);
val _ = export_rewrites["assign_cell_type"];

val lookup_unbound = Q.store_thm(
"lookup_unbound",
`ptr_to_num p ∉ FDOM s.store ⇒ (lookup p s = (NONE, s))`,
Cases_on `p` >> srw_tac [][FLOOKUP_DEF]);

val HeadOfList_unbound = Q.store_thm(
"HeadOfList_unbound",
`ptr_to_num p ∉ FDOM s.store ⇒ (HeadOfList emb p s = (NONE, s))`,
Cases_on `p` >> srw_tac [][FLOOKUP_DEF,HeadOfList_def]);

val TailOfList_unbound = Q.store_thm(
"TailOfList_unbound",
`ptr_to_num p ∉ FDOM s.store ⇒ (TailOfList emb p s = (NONE, s))`,
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
`ptr_to_num p1 ≠ ptr_to_num p2 ⇒
 (SND (raw_assign emb1 p1 v1 (SND (raw_assign emb2 p2 v2 s))) =
  SND (raw_assign emb2 p2 v2 (SND (raw_assign emb1 p1 v1 s))))`,
Cases_on `p1` >> Cases_on `p2` >> srw_tac [][] >>
srw_tac [][state_component_equality,FUN_EQ_THM,APPLY_UPDATE_THM] >>
srw_tac [][GSYM fmap_EQ,INSERT_COMM] >>
srw_tac [][FUN_EQ_THM,FAPPLY_FUPDATE_THM] >>
srw_tac [][]);

val free_addr_state = Q.store_thm(
"free_addr_state",
`SND (free_addr s) = s`,
srw_tac [][free_addr_def]);
val _ = export_rewrites["free_addr_state"];

val lookup_assign_neq = Q.store_thm(
"lookup_assign_neq",
`ptr_to_num p1 ≠ ptr_to_num p2 ⇒
 (FST (raw_lookup emb1 p1 (SND (raw_assign emb2 p2 v s))) = FST (raw_lookup emb1 p1 s))`,
Cases_on `FST (raw_lookup emb1 p1 s)` >>
Cases_on `p2` >> fsrw_tac [][FLOOKUP_UPDATE,APPLY_UPDATE_THM,lookup_succeeds,lookup_fails]);

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
`FDOM (SND (raw_assign emb p v s)).store = (ptr_to_num p) INSERT (FDOM s.store)`,
Cases_on `p` >> srw_tac [][]);
val _ = export_rewrites["assign_FDOM"];

val free_addr_neq_0 = Q.store_thm(
"free_addr_neq_0",
`ptr_to_num (FST (free_addr s)) ≠ 0`,
free_addr_elim_tac >> srw_tac [][]);
val _ = export_rewrites["free_addr_neq_0"];

val CreateList_wfstate = Q.store_thm(
"CreateList_wfstate",
`wfstate s ⇒ wfstate (SND (CreateList emb s))`,
srw_tac [][CreateList_def,UNCURRY,wfstate_def] >>
free_addr_elim_tac >> qx_gen_tac `f1` >> fsrw_tac [][] >>
free_addr_elim_tac >> qx_gen_tac `f2` >> fsrw_tac [][] >>
strip_tac >> strip_tac >>
srw_tac [][typed_state_def,APPLY_UPDATE_THM] >- (
  ntac 5 (srw_tac [][Once has_type_cases,FLOOKUP_UPDATE,APPLY_UPDATE_THM]) )
>- (
  ntac 3 (srw_tac [][Once has_type_cases,FLOOKUP_UPDATE,APPLY_UPDATE_THM]) ) >>
`f1 ≠ n ∧ f2 ≠ n` by PROVE_TAC [] >>
srw_tac [][] >>
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
`wfstate s ∧ ((a = pnil) ∨ ptr_to_num a ∈ FDOM s.store ∧ (s.cell_type (ptr_to_num a) = emb.type)) ⇒
 wfstate (SND (AddToFrontOfList emb a l s))`,
fsrw_tac [][AddToFrontOfList_def,UNCURRY] >>
Cases_on `FST (lookup emb l s)` >> fsrw_tac [][lookup_state,UNCURRY] >>
Cases_on `l` >> fsrw_tac [][APPLY_UPDATE_THM] >>
Cases_on `FLOOKUP s.store n` >> fsrw_tac [][] >>
Cases_on `s.cell_type n = List_type emb.type` >> fsrw_tac [][] >>
qmatch_assum_rename_tac `FLOOKUP s.store n = SOME lv` [] >>
Cases_on `lv` >> fsrw_tac [][] >>
qmatch_assum_rename_tac `FLOOKUP s.store n = SOME (List_value a1 a2)` [] >>
free_addr_elim_tac >> qx_gen_tac `m` >> strip_tac >>
`m ≠ n` by (fsrw_tac [][FLOOKUP_DEF] >> PROVE_TAC []) >>
fsrw_tac [][wfstate_def,typed_state_def] >>
REWRITE_TAC [GSYM AND_IMP_INTRO] >> ntac 2 strip_tac >>
`n ≠ 0` by (fsrw_tac [][FLOOKUP_DEF] >> PROVE_TAC []) >>
fsrw_tac [][] >>
qmatch_abbrev_tac `H ⇒ C` >>
srw_tac [][] >>
`typed_cell s {} n` by fsrw_tac [][FLOOKUP_DEF] >>
pop_assum mp_tac >>
asm_simp_tac (srw_ss()) [Once has_type_cases] >>
asm_simp_tac (srw_ss()) [Once has_type_cases] >>
strip_tac >>
Cases_on `a1=n` >- fsrw_tac [][FLOOKUP_DEF] >>
Cases_on `a2=n` >- fsrw_tac [][FLOOKUP_DEF] >>
`a1 ≠ 0 ⇒ a1 ∈ FDOM s.store` by PROVE_TAC [IN_INSERT,NOT_IN_EMPTY,typed_cell_bound] >>
`a2 ≠ 0 ⇒ a2 ∈ FDOM s.store` by PROVE_TAC [IN_INSERT,NOT_IN_EMPTY,typed_cell_bound] >>
`a1 ≠ m` by PROVE_TAC [] >>
`a2 ≠ m` by metis_tac [] >>
`n ∈ FDOM s.store` by fsrw_tac [][FLOOKUP_DEF] >>
`n ≠ ptr_to_num a` by (
  Cases_on `a` >> fsrw_tac [][] >>
  metis_tac [type_inductive] ) >>
`m ≠ ptr_to_num a` by metis_tac [ptr_equality,ptr_to_num_def] >>
`typed_cell s {} (ptr_to_num a)` by (
  Cases_on `a` >> fsrw_tac [][] >>
  qmatch_rename_tac `typed_cell s {} a` [] >>
  Cases_on `a=0` >- srw_tac [][Once has_type_cases] >>
  metis_tac [] ) >>
Q.UNABBREV_TAC `C` >>
qx_gen_tac `p` >>
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
