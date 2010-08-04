open HolKernel boolLib bossLib Parse termTheory bagTheory substitutionTheory equationTheory pred_setTheory relationTheory lcsymtacs

val _ = new_theory "multiequation"

val _ = type_abbrev("multiequation", ``:'a set # ('a,'b) term bag``);

val wfm_def = Define`
  wfm ((s,m):('a,'b) multiequation) = FINITE s ∧ s ≠ {} ∧ FINITE_BAG m ∧ BAG_EVERY (λt. ∀x. t ≠ Var x) m`;

val terms_of_def = Define`
  terms_of (s,m) = IMAGE Var s ∪ SET_OF_BAG m`;

val meq_unifier_def = Define`
  meq_unifier meq = {s | ∀t1 t2. t1 ∈ terms_of meq ∧ t2 ∈ terms_of meq ⇒ (SAPPLY s t1 = SAPPLY s t2)}`;

val eqs_correspond_to_meq_def = Define`
  eqs_correspond_to_meq eqs meq =
    (∀t1 t2. (t1,t2) ∈ eqs ⇒ t1 ∈ terms_of meq ∧ t2 ∈ terms_of meq) ∧
    (∀t1 t2. t1 ∈ terms_of meq ∧ t2 ∈ terms_of meq ⇒
             (λt1 t2. (t1,t2) ∈ eqs ∨ (t2,t1) ∈ eqs)^* t1 t2)`;

val meq_unifier_corresponds_set_unifier = Q.store_thm(
"meq_unifier_corresponds_set_unifier",
`eqs_correspond_to_meq eqs meq ⇒ (set_unifier eqs = meq_unifier meq)`,
srw_tac [][set_unifier_def,meq_unifier_def,EXTENSION,EQ_IMP_THM,eqs_correspond_to_meq_def] >- (
  Q.PAT_ASSUM `!t1 t2. P t1 t2 ⇒ R^* t1 t2` (Q.SPECL_THEN [`t1`,`t2`] mp_tac) >> srw_tac [][] >>
  Q.PAT_ASSUM `R^* t1 t2` mp_tac >>
  map_every Q.ID_SPEC_TAC [`t2`,`t1`] >>
  ho_match_mp_tac RTC_INDUCT >>
  metis_tac [] ) >>
metis_tac []);

(* same as above for sets of multiequations? *)

val (common_part_frontier_rules, common_part_frontier_ind, common_part_frontier_cases) = Hol_reln`
  (Var v <: m ⇒ common_part_frontier m (Var v, {({x | Var x <: m}, BAG_FILTER (λt. ∀x. t ≠ Var x) m)})) ∧
  (BAG_EVERY (λt. ∃ts. (t = App f ts) ∧ (LENGTH ts = n)) m ∧
   (∀i. i < n ⇒ common_part_frontier (BAG_IMAGE (term_case ARB (λf ts. EL i ts)) m) (common_part i, frontier i)) ⇒
   common_part_frontier m (App f (GENLIST common_part n), BIGUNION {frontier i | i < n}))`;

val _ = export_theory ()
