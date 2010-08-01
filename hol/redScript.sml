open HolKernel boolLib bossLib Parse termTheory substTheory pred_setTheory listTheory relationTheory finite_mapTheory lcsymtacs

val _ = new_theory "red";

val _ = type_abbrev("equation", ``:('a,'b) term # ('a,'b) term``);

val (term_red_rules,term_red_ind,term_red_cases) = Hol_reln`
  (LENGTH xs = LENGTH ys) ∧ (App f xs, App f ys) ∈ eqs
  ⇒ term_red eqs (eqs DELETE (App f xs, App f ys) ∪ (set (ZIP (xs,ys))))`;

val (var_elim_rules,var_elim_ind,var_elim_cases) = Hol_reln`
  (Var x, t) ∈ eqs
  ⇒ var_elim eqs
   ((Var x, t) INSERT (IMAGE (λ(t1,t2). (SAPPLY (FEMPTY|+(x,t)) t1, SAPPLY (FEMPTY|+(x,t)) t2))
                             (eqs DELETE (Var x, t))))`;

val set_unifier_def = Define`
  set_unifier eqs = {s | ∀t1 t2. (t1,t2) ∈ eqs ⇒ (SAPPLY s t1 = SAPPLY s t2)}`;

val distinct_heads = Q.store_thm( (* half of Theorem 2.1 *)
"distinct_heads",
`(App f1 ts1, App f2 ts2) ∈ eqs ∧ (f1 ≠ f2) ⇒ (set_unifier eqs = {})`,
srw_tac [][set_unifier_def,EXTENSION] >>
Q.MATCH_ASSUM_ABBREV_TAC `(t1,t2) ∈ eqs` >>
map_every qexists_tac [`t1`,`t2`] >>
srw_tac [][Abbr`t1`,Abbr`t2`]);

val term_red_sound = Q.store_thm( (* half of Theorem 2.1 *)
"term_red_sound",
`term_red eqs1 eqs2 ⇒ (set_unifier eqs1 = set_unifier eqs2)`,
srw_tac [][term_red_cases] >>
srw_tac [][set_unifier_def,EXTENSION,EQ_IMP_THM] >>
full_simp_tac (srw_ss()) [] >>
Q.PAT_ASSUM `LENGTH xs = LENGTH ys` ASSUME_TAC >- (
  res_tac >>
  full_simp_tac (srw_ss()) [MEM_ZIP,LIST_EQ_REWRITE] >>
  FIRST_X_ASSUM (Q.SPEC_THEN `n` MP_TAC) >> srw_tac [][rich_listTheory.EL_MAP] ) >>
REVERSE (Cases_on `(t1,t2) = (App f xs, App f ys)`) >>
full_simp_tac (srw_ss()) [MEM_ZIP] >>
srw_tac [][LIST_EQ_REWRITE,rich_listTheory.EL_MAP] >>
metis_tac []);

val TC_psubterm_neq = Q.store_thm(
"TC_psubterm_neq",
`∀t. ¬ psubterm^+ t t`,
metis_tac [WF_TC,WF_psubterm,WF_NOT_REFL]);

val occurs_not_unify = Q.store_thm(
"occurs_not_unify",
`x ∈ vars t ∧ t ≠ Var x ⇒ SAPPLY s (Var x) ≠ SAPPLY s t`,
srw_tac [][vars_RTC_psubterm,RTC_CASES_TC] >>
imp_res_tac TC_psubterm_mono_SAPPLY >>
full_simp_tac (srw_ss()) [] >>
metis_tac [TC_psubterm_neq]);

val no_cycles = Q.store_thm( (* half of Theorem 2.2 *)
"no_cycles",
`(Var x, t) ∈ eqs ∧ x ∈ vars t ∧ t ≠ Var x ⇒ (set_unifier eqs = {})`,
srw_tac [][set_unifier_def,EXTENSION] >>
Q.MATCH_ASSUM_ABBREV_TAC `(t1,t2) ∈ eqs` >>
map_every qexists_tac [`t1`,`t2`] >>
srw_tac [][Abbr`t1`,Abbr`t2`] >>
imp_res_tac occurs_not_unify >>
full_simp_tac (srw_ss()) []);

val var_elim_sound = Q.store_thm( (* half of Theorem 2.2 *)
"var_elim_sound",
`var_elim eqs1 eqs2 ⇒ (set_unifier eqs1 = set_unifier eqs2)`,
srw_tac [][var_elim_cases] >>
srw_tac [][set_unifier_def,EXTENSION,EQ_IMP_THM] >>
full_simp_tac (srw_ss()) [] >- (
  Q.MATCH_ASSUM_RENAME_TAC `eq ∈ eqs1` [] >>
  Cases_on `eq` >> full_simp_tac (srw_ss()) [] >> srw_tac [][] >>
  Q.MATCH_ASSUM_RENAME_TAC `(t1,t2) ∈ eqs1` [] >- (

    Cases_on `t1` >> srw_tac [][FLOOKUP_UPDATE] >- (
      res_tac >> full_simp_tac (srw_ss()) [] >>
      Cases_on `t2` >> full_simp_tac (srw_ss()) [FLOOKUP_UPDATE] >>
      srw_tac [][] >> srw_tac [][] >>


val _ = export_theory ();
