open HolKernel boolLib bossLib Parse termTheory substTheory pred_setTheory listTheory relationTheory finite_mapTheory pairTheory lcsymtacs;

val _ = new_theory "red";

val FLOOKUP_FUN_FMAP = Q.store_thm(
"FLOOKUP_FUN_FMAP",
`FINITE P ⇒ (FLOOKUP (FUN_FMAP f P) k = if k ∈ P then SOME (f k) else NONE)`,
srw_tac [][FUN_FMAP_DEF,FLOOKUP_DEF]);

val _ = type_abbrev("equation", ``:('a,'b) term # ('a,'b) term``);

val (term_red_rules,term_red_ind,term_red_cases) = Hol_reln`
  (LENGTH xs = LENGTH ys) ∧ (App f xs, App f ys) ∈ eqs
  ⇒ term_red eqs (App f xs, App f ys) (eqs DELETE (App f xs, App f ys) ∪ (set (ZIP (xs,ys))))`;

val (var_elim_rules,var_elim_ind,var_elim_cases) = Hol_reln`
  (Var x, t) ∈ eqs
  ⇒ var_elim eqs ((Var x, t):('a,'b) equation)
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
`term_red eqs1 eq eqs2 ⇒ (set_unifier eqs1 = set_unifier eqs2)`,
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

val move_var_early = Q.store_thm(
"move_var_early",
`(SAPPLY s (Var x) = SAPPLY s t) ==> (SAPPLY s o (SAPPLY (FEMPTY|+(x,t))) = SAPPLY s)`,
strip_tac >>
full_simp_tac (srw_ss()) [FUN_EQ_THM] >>
ho_match_mp_tac term_ind >>
srw_tac [][FLOOKUP_UPDATE] >>
full_simp_tac (srw_ss()) [rich_listTheory.MAP_EQ_f,rich_listTheory.MAP_MAP_o,EVERY_MEM]);

val var_elim_sound = Q.store_thm( (* half of Theorem 2.2 *)
"var_elim_sound",
`var_elim eqs1 eq eqs2 ⇒ (set_unifier eqs1 = set_unifier eqs2)`,
srw_tac [][var_elim_cases] >>
srw_tac [][set_unifier_def,EXTENSION,EQ_IMP_THM] >>
full_simp_tac (srw_ss()) [EXISTS_PROD] >- (
  Q.MATCH_RENAME_TAC `SAPPLY s t1 = SAPPLY s t2` [] >>
  `SAPPLY s (Var x) = SAPPLY s t` by res_tac >>
  imp_res_tac move_var_early >>
  full_simp_tac (srw_ss()) [FUN_EQ_THM] >>
  Q.MATCH_ASSUM_RENAME_TAC `eq ∈ eqs1` [] >>
  Cases_on `eq` >> full_simp_tac (srw_ss()) []) >>
Q.MATCH_RENAME_TAC `SAPPLY s t1 = SAPPLY s t2` [] >>
`SAPPLY s (Var x) = SAPPLY s t` by metis_tac [] >>
imp_res_tac move_var_early >>
full_simp_tac (srw_ss()) [FUN_EQ_THM] >>
Cases_on `(t1,t2) = (Var x,t)` >>
full_simp_tac (srw_ss()) [] >>
srw_tac [][] >>
FIRST_X_ASSUM (Q.SPECL_THEN [`SAPPLY (FEMPTY |+ (x,t)) t1`, `SAPPLY (FEMPTY |+ (x,t)) t2`] MP_TAC) >>
srw_tac [][] >>
metis_tac []);

val solved_form_def = Define`
  solved_form eqs = FINITE eqs ∧
  ∀eq. eq ∈ eqs ⇒
    ∃v t. (eq = (Var v, t)) ∧ (v ∉ vars t) ∧
          ∀t1 t2. (t1,t2) ∈ eqs ∧ (t1,t2) ≠ eq ⇒ v ∉ vars t1 ∧ v ∉ vars t2`;

val FDOM_DISJOINT_vars = Q.store_thm(
"FDOM_DISJOINT_vars",
`DISJOINT (FDOM s) (vars t) ⇒ (SAPPLY s t = t)`,
Q.ID_SPEC_TAC `t` >>
ho_match_mp_tac term_ind >>
srw_tac [][IN_DISJOINT,FLOOKUP_DEF] >>
full_simp_tac (srw_ss()) [MEM_MAP,EVERY_MEM,MEM_EL,LIST_EQ_REWRITE] >>
srw_tac [][rich_listTheory.EL_MAP] >>
metis_tac []);

val solved_form_unifier = Q.store_thm(
"solved_form_unifier",
`solved_form eqs ⇒ (FUN_FMAP (λv. @t. (Var v,t) ∈ eqs) {v | ∃t. (Var v, t) ∈ eqs}) ∈ set_unifier eqs`,
strip_tac >>
Q.MATCH_ABBREV_TAC `FUN_FMAP f P ∈ set_unifier eqs` >>
`P = (IMAGE (term_case I ARB o FST) eqs)` by (
  srw_tac [][EXTENSION,Abbr`P`,EQ_IMP_THM] >- (
    qexists_tac `(Var x, t)` >> srw_tac [][] ) >>
  full_simp_tac (srw_ss()) [solved_form_def] >>
  res_tac >> srw_tac [][] >>
  qexists_tac `t` >> asm_simp_tac pure_ss [] ) >>
`FINITE eqs` by full_simp_tac pure_ss [solved_form_def] >>
`FINITE P` by full_simp_tac pure_ss [IMAGE_FINITE] >>
srw_tac [][set_unifier_def] >>
full_simp_tac (srw_ss()) [solved_form_def] >>
UNABBREV_ALL_TAC >>
res_tac >> srw_tac [][] >>
srw_tac [][FLOOKUP_FUN_FMAP] >- (
  SELECT_ELIM_TAC >>
  srw_tac [][] >- (qexists_tac `t` >> asm_simp_tac pure_ss []) >>
  res_tac >> srw_tac [][] >>
  full_simp_tac (srw_ss()) [] >>
  match_mp_tac (GSYM FDOM_DISJOINT_vars) >>
  srw_tac [][IN_DISJOINT,FUN_FMAP_DEF] >>
  Cases_on `x ∈ vars t` >> srw_tac [][] >>
  SPOSE_NOT_THEN STRIP_ASSUME_TAC >>
  res_tac >> srw_tac [][] >>
  metis_tac [] ) >>
full_simp_tac (srw_ss()) []);

(* prove the solved form unifier most general? *)

(* Algorithm A *)
val (alga1_rules,alga1_ind,alga1_cases) = Hol_reln`
  ((t, Var x) ∈ eqs ⇒ alga1 eqs ((Var x, t) INSERT (eqs DELETE (t, Var x)))) ∧
  ((Var x, Var x) ∈ eqs ⇒ alga1 eqs (eqs DELETE (Var x, Var x))) ∧
  (term_red eqs1 eq eqs2 ⇒ alga1 eqs1 eqs2) ∧
  (var_elim eqs1 (Var x, t) eqs2 ∧ x ∉ vars t ∧
   (∃t1 t2. (t1,t2) ∈ eqs1 ∧ (t1,t2) ≠ (Var x, t) ∧
            (x ∈ vars t1 ∨ x ∈ vars t2))
   ⇒ alga1 eqs1 eqs2)`;

val _ = export_theory ();
