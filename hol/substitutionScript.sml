open HolKernel boolLib bossLib Parse termTheory finite_mapTheory listTheory relationTheory pred_setTheory lcsymtacs

val _ = new_theory "substitution";

val _ = type_abbrev("substitution", ``:'a |-> ('a,'b) term``);

(*val SAPPLY_def = Define*)
val SAPPLY_def = TotalDefn.tDefine "SAPPLY"`
  (SAPPLY s (Var v) = case FLOOKUP s v of SOME t -> t || NONE -> (Var v)) ∧
  (SAPPLY s (App f xs) = App f (MAP (SAPPLY s) xs))`
( WF_REL_TAC `measure (term_size ARB ARB o SND)` >>
  metis_tac [subterms_smaller,prim_recTheory.measure_thm,term_size_def] );
val _ = export_rewrites ["SAPPLY_def"];

val psubterm1_mono_SAPPLY = Q.store_thm(
"psubterm1_mono_SAPPLY",
`∀t u. psubterm1 t u ⇒ psubterm1 (SAPPLY s t) (SAPPLY s u)`,
gen_tac >> ho_match_mp_tac psubterm1_ind >>
srw_tac [][psubterm1_cases,MEM_MAP] >>
metis_tac []);

val psubterm_mono_SAPPLY = save_thm(
"psubterm_mono_SAPPLY",
TC_lifts_monotonicities |>
Q.GEN `f` |> Q.ISPEC `SAPPLY s` |>
Q.GEN `R` |> Q.ISPEC `psubterm1` |>
C MATCH_MP psubterm1_mono_SAPPLY);

val rangevars_def = Define`
  rangevars s = BIGUNION (IMAGE vars (FRANGE s))`;

val FINITE_rangevars = Q.store_thm(
"FINITE_rangevars",
`FINITE (rangevars s)`,
SRW_TAC [][rangevars_def] THEN SRW_TAC [][]);
val _ = export_rewrites ["FINITE_rangevars"];

val IN_FRANGE_rangevars = Q.store_thm(
"IN_FRANGE_rangevars",
`t ∈ FRANGE s ⇒ vars t SUBSET rangevars s`,
SRW_TAC [][rangevars_def,SUBSET_DEF] THEN METIS_TAC []);

val FDOM_DISJOINT_vars = Q.store_thm(
"FDOM_DISJOINT_vars",
`DISJOINT (FDOM s) (vars t) ⇒ (SAPPLY s t = t)`,
Q.ID_SPEC_TAC `t` >>
ho_match_mp_tac term_ind >>
srw_tac [][IN_DISJOINT,FLOOKUP_DEF] >>
full_simp_tac (srw_ss()) [MEM_MAP,EVERY_MEM,MEM_EL,LIST_EQ_REWRITE] >>
srw_tac [][rich_listTheory.EL_MAP] >>
metis_tac []);

val NOTIN_rangevars_IN_vars = Q.store_thm(
"NOTIN_rangevars_IN_vars",
`!t v s. v IN vars (SAPPLY s t) /\ v NOTIN rangevars s ==> v IN vars t`,
ho_match_mp_tac term_ind >>
srw_tac [][rangevars_def] >- (
  Cases_on `FLOOKUP s v` >>
  full_simp_tac (srw_ss()) [FLOOKUP_DEF,FRANGE_DEF] >>
  metis_tac [] ) >>
full_simp_tac (srw_ss()) [MEM_MAP,EVERY_MEM,FRANGE_DEF] >>
metis_tac []);

val NOTIN_FDOM_IN_vars = Q.store_thm(
"NOTIN_FDOM_IN_vars",
`!t v s. v IN vars t /\ v NOTIN FDOM s ==> v IN vars (SAPPLY s t)`,
ho_match_mp_tac term_ind >>
srw_tac [][] >- (
  Cases_on `FLOOKUP s v` >>
  full_simp_tac (srw_ss()) [FLOOKUP_DEF] ) >>
full_simp_tac (srw_ss()) [MEM_MAP,EVERY_MEM] >>
metis_tac []);

val IN_FDOM_NOTIN_rangevars = Q.store_thm(
"IN_FDOM_NOTIN_rangevars",
`!t v s. v IN FDOM s /\ v NOTIN rangevars s ==> v NOTIN vars (SAPPLY s t)`,
ho_match_mp_tac term_ind >>
srw_tac [][rangevars_def] >- (
  Cases_on `FLOOKUP s v` >>
  full_simp_tac (srw_ss()) [FLOOKUP_DEF,FRANGE_DEF] >>
  metis_tac [] ) >>
full_simp_tac (srw_ss()) [MEM_MAP,EVERY_MEM,FRANGE_DEF] >>
metis_tac []);

val unify_corresponding_subterms = Q.store_thm(
"unify_corresponding_subterms",
`(SAPPLY s t1 = SAPPLY s t2) ∧ subterm_at u1 ns t1 ∧ subterm_at u2 ns t2 ⇒ (SAPPLY s u1 = SAPPLY s u2)`,
qsuff_tac `∀ns t1. subterm_at u1 ns t1 ⇒ ∀u2 t2. subterm_at u2 ns t2 ∧ (SAPPLY s t1 = SAPPLY s t2) ⇒ (SAPPLY s u1 = SAPPLY s u2)`
>- metis_tac [] >>
ho_match_mp_tac subterm_at_ind >>
srw_tac [][] >>
Cases_on `t2` >> fsrw_tac [][] >>
first_x_assum match_mp_tac >>
qmatch_assum_abbrev_tac `subterm_at u2 ns t2` >>
qexists_tac `t2` >> srw_tac [][Abbr`t2`] >>
fsrw_tac [][LIST_EQ_REWRITE,rich_listTheory.EL_MAP]);

val _ = export_theory ();
