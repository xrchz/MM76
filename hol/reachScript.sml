open HolKernel bossLib boolLib Parse SatisfySimps ptypes_definitionsTheory finite_mapTheory relationTheory lcsymtacs

val _ = new_theory "reach"

val (reach1_rules, reach1_ind, reach1_cases) = Hol_reln`
  (reach1 m (Variable_value _ m)) ∧
  (reach1 m (SetOfVariables_value _ _ m)) ∧
  (reach1 m (Term_value (INL m))) ∧
  (reach1 m (Term_value (INR (_,m)))) ∧
  (reach1 m (Multiequation_value _ m _)) ∧
  (reach1 m (Multiequation_value _ _ m)) ∧
  (reach1 m (TempMultiequation_value m _)) ∧
  (reach1 m (TempMultiequation_value _ m)) ∧
  (reach1 m (System_value m _)) ∧
  (reach1 m (System_value _ m)) ∧
  (reach1 m (List_value m _)) ∧
  (reach1 m (List_value _ m)) ∧
  (reach1 m (AuxList_value m _)) ∧
  (reach1 m (AuxList_value _ m))`;

val cell_reach1_def = Define`
  cell_reach1 (s:store) m n = ∃v. (FLOOKUP s n = SOME v) ∧ reach1 m v`;
val _ = overload_on("cell_reach",``λs. RTC (cell_reach1 s)``);

val reach_def = Define`
  reach s m v = ∃n. reach1 n v ∧ cell_reach s m n`;

val cell_reach_FUPDATE_end = Q.store_thm(
"cell_reach_FUPDATE_end",
`cell_reach (s |+ (m,w)) m n ⇔ cell_reach s m n`,
reverse EQ_TAC >- (
  map_every qid_spec_tac [`n`,`m`] >>
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
  srw_tac [][cell_reach1_def] >>
  qmatch_assum_rename_tac `FLOOKUP s p = SOME v` [] >>
  Cases_on `m = p` >- PROVE_TAC [RTC_REFL] >>
  `FLOOKUP (s |+ (m,w)) p = SOME v` by PROVE_TAC [FLOOKUP_UPDATE] >>
  PROVE_TAC [cell_reach1_def,RTC_RULES_RIGHT1] ) >>
qsuff_tac `!s0 s m n. cell_reach s m n ⇒ (s = s0 |+ (m,w)) ⇒ cell_reach s0 m n`
>- srw_tac [][] >>
ntac 2 gen_tac >>
ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
srw_tac [][cell_reach1_def] >>
qmatch_assum_rename_tac `FLOOKUP (s0 |+ (m,w)) p = SOME v` [] >>
Cases_on `m=p` >- PROVE_TAC [RTC_REFL] >>
`FLOOKUP s0 p = SOME v` by PROVE_TAC [FLOOKUP_UPDATE] >>
PROVE_TAC [cell_reach1_def,RTC_RULES_RIGHT1]);

val reach_FUPDATE_end = Q.store_thm(
"reach_FUPDATE_end",
`reach (s |+ (m,w)) m v ⇔ reach s m v`,
srw_tac [][reach_def,cell_reach_FUPDATE_end]);

val cell_reach_bound = Q.store_thm(
"cell_reach_bound",
`cell_reach s m n ∧ n ≠ m ⇒ n ∈ FDOM s`,
srw_tac [][Once RTC_CASES2,cell_reach1_def,FLOOKUP_DEF]);

val FLOOKUP_reach_imp_cell_reach = Q.store_thm(
"FLOOKUP_reach_imp_cell_reach",
`(FLOOKUP s n = SOME v) ∧ reach s m v ⇒ cell_reach s m n`,
srw_tac [][reach_def] >>
srw_tac [SATISFY_ss][Once RTC_CASES2,cell_reach1_def]);

val has_type_assign_unreachable = Q.store_thm(
"has_type_assign_unreachable",
`(∀c v t. has_type s c v t ⇒ ¬ reach s.store m v ⇒ has_type (s with store updated_by (m =+ w)) c v t) ∧
 (∀c n. typed_cell s c n ⇒ ¬ cell_reach s.store m n ⇒ typed_cell (s with store updated_by (m =+ w)) c n)`,
ho_match_mp_tac has_type_ind >>
reverse (srw_tac [][]) >- (
  srw_tac [][Once has_type_cases,FLOOKUP_UPDATE] >>
  PROVE_TAC [RTC_REFL,FLOOKUP_reach_imp_cell_reach] )
>- (
  srw_tac [][Once has_type_cases] >>
  PROVE_TAC [RTC_REFL] )
>- srw_tac [][Once has_type_cases] >>
fsrw_tac [][reach_def,reach1_cases] >>
srw_tac [][Once has_type_cases] >>
first_x_assum match_mp_tac >>
PROVE_TAC []);

val has_type_remove_unreachable = Q.store_thm(
"has_type_remove_unreachable",
`(∀c v t. has_type s c v t ⇒ ¬ reach s.store m v ⇒ has_type (s with store updated_by combin$C $\\ m) c v t) ∧
 (∀c n. typed_cell s c n ⇒ ¬ cell_reach s.store m n ⇒ typed_cell (s with store updated_by combin$C $\\ m) c n)`,
ho_match_mp_tac has_type_ind >>
reverse (srw_tac [][]) >- (
  srw_tac [][Once has_type_cases,DOMSUB_FLOOKUP_THM] >>
  PROVE_TAC [RTC_REFL,FLOOKUP_reach_imp_cell_reach] ) >>
srw_tac [][Once has_type_cases] >>
fsrw_tac [][reach_def,reach1_cases] >>
PROVE_TAC [RTC_RULES]);

val cell_reach_typed_state_unbound_eq_0 = Q.store_thm(
"cell_reach_typed_state_unbound_eq_0",
`typed_state s ∧ cell_reach s.store m n ∧ m ≠ n ∧ m ∉ FDOM s.store ⇒ (m = 0)`,
REWRITE_TAC [GSYM AND_IMP_INTRO] >>
strip_tac >>
map_every qid_spec_tac [`n`,`m`] >>
ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
srw_tac [][] >>
fsrw_tac [][cell_reach1_def] >>
qmatch_assum_rename_tac `FLOOKUP s.store p = SOME v` [] >>
`p ∈ FDOM s.store` by fsrw_tac [][FLOOKUP_DEF] >>
Cases_on `m = n` >> srw_tac [][] >>
imp_res_tac typed_state_def >>
fsrw_tac [][Once has_type_cases] >>
fsrw_tac [][] >> srw_tac [][] >>
fsrw_tac [][reach1_cases] >> srw_tac [][] >>
fsrw_tac [][Once has_type_cases] >>
fsrw_tac [][Once has_type_cases] >>
fsrw_tac [][FLOOKUP_DEF] );

val _ = export_theory ()
