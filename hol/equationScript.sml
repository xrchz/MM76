open HolKernel boolLib bossLib Parse SatisfySimps termTheory substitutionTheory pred_setTheory pairTheory finite_mapTheory lcsymtacs

val _ = new_theory "equation"

val _ = type_abbrev("equation", ``:('a,'b) term # ('a,'b) term``);

val SAPPLYeq_def = Define`
  SAPPLYeq s (t1,t2) = (SAPPLY s t1, SAPPLY s t2)`;
val _ = export_rewrites ["SAPPLYeq_def"];

val set_unifier_def = Define`
  set_unifier eqs = {s | ∀t1 t2. (t1,t2) ∈ eqs ⇒ (SAPPLY s t1 = SAPPLY s t2)}`;

val varseq_def = Define`
  varseq (t1, t2) = vars t1 ∪ vars t2`;
val _ = export_rewrites ["varseq_def"];

val FINITE_varseq = Q.store_thm(
"FINITE_varseq",
`FINITE (varseq eq)`,
Cases_on `eq` >> srw_tac [][]);
val _ = export_rewrites ["FINITE_varseq"];

val solved_form_def = Define`
  solved_form eqs =
    FINITE eqs ∧
    ∀eq. eq ∈ eqs ⇒
         ∃v t. (eq = (Var v, t)) ∧ (v ∉ vars t) ∧
               ∀eq'. eq' ∈ eqs ∧ eq' ≠ eq ⇒ v ∉ varseq eq'`;

val eqsvdom_def = Define`eqsvdom eqs = {v | ∃t. (Var v, t) ∈ eqs}`

val FINITE_eqsvdom = store_thm(
  "FINITE_eqsvdom",
  ``FINITE eqs ⇒ FINITE (eqsvdom eqs)``,
  strip_tac >>
  `eqsvdom eqs ⊆ (IMAGE (term_case I ARB o FST) eqs)` by (
    srw_tac [][SUBSET_DEF,eqsvdom_def] >- (
    qexists_tac `(Var x, t)` >> srw_tac [][] ) >>
  full_simp_tac (srw_ss()) [solved_form_def] >>
  res_tac >> srw_tac [][] >>
  qexists_tac `t` >> asm_simp_tac pure_ss [] ) >>
  metis_tac [SUBSET_FINITE, IMAGE_FINITE]);

val solved_form_functional = store_thm(
  "solved_form_functional",
  ``solved_form eqs ∧ (v,t1) ∈ eqs ∧ (v,t2) ∈ eqs ⇒ (t1 = t2)``,
  srw_tac [][solved_form_def] >>
  first_x_assum (Q.SPEC_THEN `(v,t1)` MP_TAC) >>
  asm_simp_tac (srw_ss()) [] >>
  DISCH_THEN (Q.X_CHOOSE_THEN `w` STRIP_ASSUME_TAC) >>
  first_x_assum (Q.SPEC_THEN `(v,t2)` MP_TAC) >>
  asm_simp_tac (srw_ss()) []);

val solved_form_unifier = Q.store_thm(
"solved_form_unifier",
`solved_form eqs ⇒
   (FUN_FMAP (λv. @t. (Var v,t) ∈ eqs) (eqsvdom eqs)) ∈ set_unifier eqs`,
strip_tac >>
Q.MATCH_ABBREV_TAC `FUN_FMAP f P ∈ set_unifier eqs` >>
`FINITE eqs` by full_simp_tac pure_ss [solved_form_def] >>
`FINITE P` by metis_tac [FINITE_eqsvdom] >>
srw_tac [][set_unifier_def] >>
`∃v. t1 = Var v` by metis_tac [solved_form_def, PAIR_EQ] >>
`v ∈ P` by srw_tac [SATISFY_ss][Abbr`P`,eqsvdom_def] >>
srw_tac [][FLOOKUP_FUN_FMAP] >>
`f v = t2` by (srw_tac [][Abbr`f`] >> SELECT_ELIM_TAC >>
               metis_tac [solved_form_functional]) >>
qsuff_tac `DISJOINT (FDOM (FUN_FMAP f P)) (vars t2)`
  >- metis_tac [FDOM_DISJOINT_vars] >>
asm_simp_tac (srw_ss())[FUN_FMAP_DEF, DISJOINT_DEF, EXTENSION] >>
qx_gen_tac `w` >> Cases_on `w ∈ P` >> asm_simp_tac (srw_ss()) [] >>
`∃t. (Var w,t) ∈ eqs`
  by full_simp_tac (srw_ss() ++ SATISFY_ss)
                   [Abbr`P`, eqsvdom_def] >>
`v ∉ vars t2` by metis_tac [solved_form_def, PAIR_EQ, term_11] >>
full_simp_tac (srw_ss()) [solved_form_def] >>
first_x_assum (Q.SPEC_THEN `(Var w,t)` MP_TAC) >>
srw_tac [][] >>
first_x_assum (Q.SPEC_THEN `(Var v,f v)` MP_TAC) >>
srw_tac [][] >> metis_tac []);

(* prove the solved form unifier most general? *)

val fsym_counteq_def = Define`
  fsym_counteq (t1, t2) = fsym_count t1 + fsym_count t2`;
val _ = export_rewrites ["fsym_counteq_def"];

val _ = export_theory ()
