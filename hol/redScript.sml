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

val varseq_def = Define`
  varseq (t1, t2) = vars t1 ∪ vars t2`;
val _ = export_rewrites ["varseq_def"];

val FINITE_varseq = Q.store_thm(
"FINITE_varseq",
`FINITE (varseq eq)`,
Cases_on `eq` >> srw_tac [][]);
val _ = export_rewrites ["FINITE_varseq"];

val solved_form_def = Define`
  solved_form eqs = FINITE eqs ∧
  ∀eq. eq ∈ eqs ⇒
    ∃v t. (eq = (Var v, t)) ∧ (v ∉ vars t) ∧
          ∀eq'. eq' ∈ eqs ∧ eq' ≠ eq ⇒ v ∉ varseq eq'`;

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
  Cases_on `x = v` >> full_simp_tac (srw_ss()) [] >>
  Q.MATCH_ABBREV_TAC `eq ∉ eqs` >>
  NTAC 2 (FIRST_X_ASSUM (Q.SPEC_THEN `eq` MP_TAC)) >>
  srw_tac [][Abbr`eq`] >>
  SPOSE_NOT_THEN STRIP_ASSUME_TAC >>
  full_simp_tac (srw_ss()) [] >>
  FIRST_X_ASSUM (Q.SPEC_THEN `(Var v,t)` MP_TAC) >>
  srw_tac [][] ) >>
full_simp_tac (srw_ss()) []);

(* prove the solved form unifier most general? *)

(* Algorithm A *)
val (alga1_rules,alga1_ind,alga1_cases) = Hol_reln`
  (FINITE eqs ∧ (t, Var x) ∈ eqs ∧ (∀y. t ≠ Var y) ⇒ alga1 eqs ((Var x, t) INSERT (eqs DELETE (t, Var x)))) ∧
  (FINITE eqs ∧ (Var x, Var x) ∈ eqs ⇒ alga1 eqs (eqs DELETE (Var x, Var x))) ∧
  (FINITE eqs ∧ term_red eqs1 eq eqs2 ⇒ alga1 eqs1 eqs2) ∧
  (FINITE eqs ∧ var_elim eqs1 (Var x, t) eqs2 ∧
   x ∉ vars t ∧ (∃eq. eq ∈ eqs1 ∧ eq ≠ (Var x, t) ∧ (x ∈ varseq eq))
   ⇒ alga1 eqs1 eqs2)`;

val fsym_counteq_def = Define`
  fsym_counteq (t1, t2) = fsym_count t1 + fsym_count t2`;
val _ = export_rewrites ["fsym_counteq_def"];

val swap_under_IMAGE = Q.store_thm(
"swap_under_IMAGE",
`(f x = f y) ∧ x ∈ s ⇒ (IMAGE f (y INSERT s DELETE x) = IMAGE f s)`,
srw_tac [][EXTENSION,EQ_IMP_THM] >> metis_tac []);

val CARD_PSUBSET_match = (SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM,AND_IMP_INTRO] CARD_PSUBSET);
val CARD_SUBSET_match = (SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM,AND_IMP_INTRO] CARD_SUBSET);
val SUBSET_FINITE_match = (SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM,AND_IMP_INTRO] SUBSET_FINITE);

val WF_alga1 = Q.store_thm( (* Theorem 2.3 a *)
"WF_alga1",
`WF (inv alga1)`,
match_mp_tac WF_SUBSET >>
qexists_tac
`inv_image ($< LEX $< LEX $<)
  (λeqs. (CARD ((BIGUNION (IMAGE varseq eqs)) DIFF
                {v | ∃t. (Var v, t) ∈ eqs ∧ ∀eq'. eq' ∈ eqs ∧ v ∈ varseq eq' ⇒ (eq' = (Var v, t))}),
          SIGMA fsym_counteq eqs,
          CARD {eq | eq ∈ eqs ∧ ∃x.((eq = (Var x, Var x)) ∨ ∃t.((eq = (t, Var x)) ∧ ∀y. (t ≠ Var y)))}))` >>
srw_tac [][] >- (
  match_mp_tac WF_inv_image >>
  NTAC 2 (match_mp_tac WF_LEX >> simp_tac bool_ss [prim_recTheory.WF_LESS])) >>
full_simp_tac (srw_ss()) [inv_DEF] >>
Q.MATCH_ASSUM_RENAME_TAC `alga1 eqs1 eqs2` [] >>
Q.HO_MATCH_ABBREV_TAC `inv_image f (λeqs. (CARD (s1 eqs), SIGMA fsym_counteq eqs, CARD (s2 eqs))) eqs2 eqs1` >>
full_simp_tac pure_ss [alga1_cases] >- (
  srw_tac [][inv_image_def,LEX_DEF,Abbr`f`] >>
  Q.MATCH_ABBREV_TAC `n1b < n1a ∨ ((n1b = n1a) ∧ (n2b < n2a ∨ ((n2b = n2a) ∧ n3b < n3a)))` >>
  Cases_on `n1b = n1a` >> srw_tac [][] >- (
    Cases_on `n2b = n2a` >> srw_tac [][] >- (
      UNABBREV_ALL_TAC >>
      Q.MATCH_ABBREV_TAC `CARD s1 < CARD s2` >>
      match_mp_tac CARD_PSUBSET_match >>
      srw_tac [][PSUBSET_DEF] >- (
        match_mp_tac SUBSET_FINITE_match >>
        qexists_tac `eqs1` >> srw_tac [][Abbr`s2`,SUBSET_DEF] )
      >- (
        srw_tac [][Abbr`s2`,Abbr`s1`,SUBSET_DEF] >>
        srw_tac [][] ) >>
      srw_tac [][Abbr`s2`,Abbr`s1`,NOT_EQUAL_SETS] >>
      qexists_tac `(t,Var x)` >> srw_tac [][EQ_IMP_THM] ) >>
    UNABBREV_ALL_TAC >>
    POP_ASSUM mp_tac >>
    `FINITE (eqs1 DELETE (t,Var x))` by srw_tac [][FINITE_DELETE] >>
    `fsym_counteq (t,Var x:('a,'b) term) ≤ SIGMA fsym_counteq eqs1`
      by (match_mp_tac SUM_IMAGE_IN_LE >> srw_tac [][] ) >>
    srw_tac [ARITH_ss][SUM_IMAGE_THM,SUM_IMAGE_DELETE] >>
    full_simp_tac (srw_ss()) [] >> DECIDE_TAC ) >>
  UNABBREV_ALL_TAC >>
  Q.MATCH_ABBREV_TAC `CARD s1 < CARD s2` >>
  match_mp_tac CARD_PSUBSET_match >>
  conj_tac >- (
    match_mp_tac SUBSET_FINITE_match >>
    qexists_tac `BIGUNION (IMAGE varseq eqs1)` >> srw_tac [][SUBSET_DEF,Abbr`s2`] >> srw_tac [][] ) >>
  `s1 ≠ s2` by (SPOSE_NOT_THEN STRIP_ASSUME_TAC >> full_simp_tac bool_ss []) >>
  srw_tac [][PSUBSET_DEF] >>
  simp_tac bool_ss [Abbr`s1`,Abbr`s2`] >>
  Q.MATCH_ABBREV_TAC `s1 DIFF s2 ⊆ s3 DIFF s4` >>
  `s1 = s3` by (
    UNABBREV_ALL_TAC >>
    AP_TERM_TAC >>
    match_mp_tac swap_under_IMAGE >>
    srw_tac [][UNION_COMM] ) >>
  asm_simp_tac (srw_ss()) [SUBSET_DIFF,DISJOINT_DEF,EXTENSION] >>
  strip_tac >>
  Q.MATCH_RENAME_TAC `(v ∉ s3 ∨ v ∈ s2) ∨ v ∉ s4` [] >>
  Cases_on `v ∈ s3` >> asm_simp_tac (srw_ss()) [] >>
  Cases_on `v ∈ s4` >> asm_simp_tac (srw_ss()) [] >>
  Q.UNABBREV_TAC `s3` >> UNABBREV_ALL_TAC >>
  full_simp_tac (srw_ss()) [] >> srw_tac [][] >>
  qexists_tac `t'` >> srw_tac [][] >- (
    first_x_assum (Q.SPEC_THEN `(t,Var x)` mp_tac) >>
    srw_tac [][] >> full_simp_tac (srw_ss()) [] ) >>
  first_x_assum match_mp_tac >>
  srw_tac [][] )
>- (
  srw_tac [][inv_image_def,LEX_DEF,Abbr`f`] >>
  Q.MATCH_ABBREV_TAC `n1b < n1a ∨ ((n1b = n1a) ∧ (n2b < n2a ∨ ((n2b = n2a) ∧ n3b < n3a)))` >>
  Cases_on `n1b = n1a` >> srw_tac [][] >- (
    DISJ2_TAC >>
    conj_tac >- (
      UNABBREV_ALL_TAC >>
      srw_tac [][SUM_IMAGE_DELETE] ) >>
    UNABBREV_ALL_TAC >>
    match_mp_tac CARD_PSUBSET_match >>
    conj_tac >- (
      match_mp_tac SUBSET_FINITE_match >>
      qexists_tac `eqs1` >> srw_tac [][SUBSET_DEF] ) >>
    srw_tac [][PSUBSET_EQN,SUBSET_DEF] ) >>
  UNABBREV_ALL_TAC >>
  Q.MATCH_ABBREV_TAC `CARD s1 < CARD s2` >>
  `s1 ⊆ s2` by (
    srw_tac [][Abbr`s1`,Abbr`s2`,SUBSET_DEF] >>
    metis_tac [] ) >>
  qsuff_tac `CARD s1 ≤ CARD s2` >- DECIDE_TAC >>
  match_mp_tac CARD_SUBSET_match >>
  srw_tac [][] >>
  match_mp_tac SUBSET_FINITE_match >>
  qexists_tac `BIGUNION (IMAGE varseq eqs1)` >>
  srw_tac [][Abbr`s2`,SUBSET_DEF] >>
  srw_tac [][] )
>- (

val _ = export_theory ();
