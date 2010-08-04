open HolKernel boolLib bossLib SatisfySimps Parse termTheory substitutionTheory equationTheory pred_setTheory listTheory relationTheory finite_mapTheory pairTheory arithmeticTheory lcsymtacs

val _ = new_theory "algorithm_a";

val SUM_IMAGE_LIST_TO_SET = Q.store_thm(
"SUM_IMAGE_LIST_TO_SET",
`SIGMA f (set ls) <= SUM (MAP f ls)`,
Q.ID_SPEC_TAC `ls` >> Induct >>
srw_tac [][SUM_IMAGE_THM,SUM_IMAGE_DELETE] >>
DECIDE_TAC);

val SUM_MAP_ZIP = Q.store_thm(
"SUM_MAP_ZIP",
`(LENGTH ls1 = LENGTH ls2) /\ (!x y. f (x,y) = g x + h y) ==>(SUM (MAP f (ZIP (ls1,ls2))) = SUM (MAP g ls1) + SUM (MAP h ls2))`,
MAP_EVERY Q.ID_SPEC_TAC [`ls2`,`ls1`] >>
Induct >> Cases_on `ls2` >> srw_tac [ARITH_ss][]);

val (term_red_rules,term_red_ind,term_red_cases) = Hol_reln`
  (LENGTH xs = LENGTH ys) ∧ (App f xs, App f ys) ∈ eqs
  ⇒ term_red eqs (App f xs, App f ys) (eqs DELETE (App f xs, App f ys) ∪ (set (ZIP (xs,ys))))`;

val (var_elim_rules,var_elim_ind,var_elim_cases) = Hol_reln`
  (Var x, t) ∈ eqs
  ⇒ var_elim eqs ((Var x, t):('a,'b) equation)
   ((Var x, t) INSERT (IMAGE (SAPPLYeq (FEMPTY |+ (x,t))) (eqs DELETE (Var x, t))))`;

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

val term_red_FINITE = Q.store_thm(
"term_red_FINITE",
`∀eq. term_red eqs1 eq eqs2 ∧ FINITE eqs1 ⇒ FINITE eqs2`,
srw_tac [][term_red_cases] >> srw_tac [][]);

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

val var_elim_FINITE = Q.store_thm(
"var_elim_FINITE",
`∀eq. var_elim eqs1 eq eqs2 ∧ FINITE eqs1 ⇒ FINITE eqs2`,
srw_tac [][var_elim_cases] >> srw_tac [][]);

(* Algorithm A *)
val (alga1_rules,alga1_ind,alga1_cases) = Hol_reln`
  (FINITE eqs ∧ (t, Var x) ∈ eqs ∧ (∀y. t ≠ Var y) ⇒ alga1 eqs ((Var x, t) INSERT (eqs DELETE (t, Var x)))) ∧
  (FINITE eqs ∧ (Var x, Var x) ∈ eqs ⇒ alga1 eqs (eqs DELETE (Var x, Var x))) ∧
  (FINITE eqs1 ∧ term_red eqs1 eq eqs2 ⇒ alga1 eqs1 eqs2) ∧
  (FINITE eqs1 ∧ var_elim eqs1 (Var x, t) eqs2 ∧
   x ∉ vars t ∧ (∃eq. eq ∈ eqs1 ∧ eq ≠ (Var x, t) ∧ (x ∈ varseq eq))
   ⇒ alga1 eqs1 eqs2)`;

val swap_under_IMAGE = Q.store_thm(
"swap_under_IMAGE",
`(f x = f y) ∧ x ∈ s ⇒ (IMAGE f (y INSERT s DELETE x) = IMAGE f s)`,
srw_tac [][EXTENSION,EQ_IMP_THM] >> metis_tac []);

val CARD_PSUBSET_match = (MP_CANON CARD_PSUBSET);
val CARD_SUBSET_match = (MP_CANON CARD_SUBSET);
val SUBSET_FINITE_match = (MP_CANON SUBSET_FINITE);

val var_elim_elim = Q.store_thm(
"var_elim_elim",
`x NOTIN vars t ==> !u. x NOTIN vars (SAPPLY (FEMPTY |+ (x,t)) u)`,
strip_tac >>
ho_match_mp_tac term_ind >>
srw_tac [][FLOOKUP_UPDATE] >>
srw_tac [][MEM_MAP] >>
full_simp_tac (srw_ss()) [EVERY_MEM] >>
metis_tac []);

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
full_simp_tac pure_ss [alga1_cases] >>
srw_tac [][inv_image_def,LEX_DEF,Abbr`f`] >>
Q.MATCH_ABBREV_TAC `n1b < n1a ∨ ((n1b = n1a) ∧ (n2b < n2a ∨ ((n2b = n2a) ∧ n3b < n3a)))` >- (
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
  full_simp_tac (srw_ss()) [term_red_cases] >>
  srw_tac [][] >>
  Cases_on `n1b = n1a` >> srw_tac [][] >- (
    DISJ1_TAC >>
    UNABBREV_ALL_TAC >>
    Q.MATCH_ABBREV_TAC `SIGMA fu (s UNION t) < SIGMA fu eqs1` >>
    `FINITE t` by metis_tac [FINITE_LIST_TO_SET] >>
    `FINITE s` by srw_tac [][Abbr`s`,FINITE_DELETE] >>
    `SIGMA fu s = SIGMA fu eqs1 - fu (App f xs, App f ys)` by srw_tac [][Abbr`s`, SUM_IMAGE_DELETE] >>
    `fu (App f xs, App f ys) <= SIGMA fu eqs1` by metis_tac [SUM_IMAGE_IN_LE] >>
    `SIGMA fu t < fu (App f xs, App f ys)` by (
      UNABBREV_ALL_TAC >>
      full_simp_tac (srw_ss()++ARITH_ss) [] >>
      match_mp_tac LESS_EQ_LESS_TRANS >>
      qexists_tac `SUM (MAP fsym_counteq (ZIP (xs,ys)))` >>
      srw_tac [ARITH_ss][SUM_IMAGE_LIST_TO_SET] >>
      Q.MATCH_ABBREV_TAC `A < B + (C + 2)` >>
      `A = B + C` by (
        UNABBREV_ALL_TAC >>
        match_mp_tac SUM_MAP_ZIP >>
        srw_tac [][] ) >>
      DECIDE_TAC ) >>
    srw_tac [ARITH_ss][SUM_IMAGE_UNION] ) >>
  UNABBREV_ALL_TAC >>
  match_mp_tac CARD_PSUBSET_match >>
  conj_tac >- (
    match_mp_tac SUBSET_FINITE_match >>
    qexists_tac `BIGUNION (IMAGE varseq eqs1)` >>
    srw_tac [][] >> srw_tac [][] ) >>
  Q.MATCH_ABBREV_TAC `s1 PSUBSET s2` >>
  `s1 <> s2` by metis_tac [] >>
  `!x eq. x IN varseq eq /\ MEM eq (ZIP (xs,ys)) ==> x IN varseq (App f xs, App f ys)` by (
    srw_tac [][MEM_ZIP] >>
    full_simp_tac (srw_ss()) [MEM_MAP,MEM_EL] >>
    metis_tac [] ) >>
  UNABBREV_ALL_TAC >>
  srw_tac [][PSUBSET_DEF,SUBSET_DEF] >>
  metis_tac [PAIR_EQ,term_distinct] ) >>
DISJ1_TAC >>
UNABBREV_ALL_TAC >>
match_mp_tac CARD_PSUBSET_match >>
conj_tac >- (
  match_mp_tac SUBSET_FINITE_match >>
  qexists_tac `BIGUNION (IMAGE varseq eqs1)` >>
  srw_tac [][] >> srw_tac [][] ) >>
simp_tac bool_ss [] >>
Q.MATCH_ABBREV_TAC `s1 DIFF s2 PSUBSET s3 DIFF s4` >>
`s1 = s3` by (
  UNABBREV_ALL_TAC >>
  full_simp_tac (srw_ss()) [var_elim_cases] >>
  simp_tac pure_ss [EXTENSION] >>
  strip_tac >>
  EQ_TAC >- (
    strip_tac >>
    full_simp_tac (srw_ss()) [] >- (
      qexists_tac `varseq (Var x, t)` >> srw_tac [][] >>
      qexists_tac `(Var x, t)` >> srw_tac [][] )
    >- (
      qexists_tac `varseq (Var x, t)` >> srw_tac [][] >>
      qexists_tac `(Var x, t)` >> srw_tac [][] )
    >- (
      Q.MATCH_ASSUM_RENAME_TAC `eq' IN eqs1` [] >>
      Cases_on `x' IN vars t` >- (
        qexists_tac `varseq (Var x, t)` >> srw_tac [][] >>
        qexists_tac `(Var x, t)` >> srw_tac [][] ) >>
      qexists_tac `varseq eq'` >>
      REVERSE (srw_tac [][]) >- metis_tac [] >>
      Q.PAT_ASSUM `eq' <> (X,Y)` (K ALL_TAC) >>
      Cases_on `eq'` >> full_simp_tac (srw_ss()) [] >| [
        DISJ1_TAC, DISJ2_TAC ] >>
      match_mp_tac NOTIN_rangevars_IN_vars >>
      qexists_tac `FEMPTY |+ (x,t)` >>
      srw_tac [][rangevars_def,FRANGE_DEF] )) >>
    srw_tac [][] >>
    Cases_on `x=x'` >> srw_tac [][] >>
    Cases_on `x' IN vars t` >> srw_tac [][] >>
    Q.MATCH_ASSUM_RENAME_TAC `eq' IN eqs1` [] >>
    Cases_on `eq' = (Var x, t)` >> srw_tac [][] >>
    full_simp_tac (srw_ss()) [] >>
    qexists_tac `varseq (SAPPLYeq (FEMPTY |+ (x,t)) eq')` >>
    REVERSE conj_tac >- (
      qexists_tac `SAPPLYeq (FEMPTY |+ (x,t)) eq'` >> srw_tac [][] >>
      qexists_tac `eq'` >> srw_tac [][] ) >>
    Q.PAT_ASSUM `eq' <> (X,Y)` (K ALL_TAC) >>
    Cases_on `eq'` >> full_simp_tac (srw_ss()) [] >| [
      DISJ1_TAC, DISJ2_TAC ] >>
    match_mp_tac NOTIN_FDOM_IN_vars >> srw_tac [][] ) >>
full_simp_tac (srw_ss()) [] >> srw_tac [][] >>
`s2 SUBSET s1` by (
  UNABBREV_ALL_TAC >>
  srw_tac [][SUBSET_DEF] >>
  qexists_tac `varseq (Var x',t')` >> srw_tac [][] >>
  qexists_tac `(Var x',t')` >> srw_tac [][] ) >>
qsuff_tac `s4 PSUBSET s2` >- (
  srw_tac [][PSUBSET_DEF,SUBSET_DEF,NOT_EQUAL_SETS] >>
  full_simp_tac (srw_ss()) [SUBSET_DEF] >>
  metis_tac [] ) >>
REVERSE (srw_tac [][PSUBSET_DEF]) >- (
  srw_tac [][NOT_EQUAL_SETS] >>
  qexists_tac `x` >>
  `x NOTIN s4` by (
    UNABBREV_ALL_TAC >> srw_tac [][] >>
    Cases_on `eq = (Var x, t')` >> srw_tac [][] >- (
      qexists_tac `(Var x, t)` >> srw_tac [][] >>
      full_simp_tac (srw_ss()) [var_elim_cases] ) >>
    DISJ2_TAC >>
    qexists_tac `eq` >> srw_tac [][] ) >>
  srw_tac [][] >>
  UNABBREV_ALL_TAC >>
  srw_tac [][] >>
  qexists_tac `t` >>
  full_simp_tac (srw_ss()) [var_elim_cases] >>
  srw_tac [][] >>
  Q.MATCH_ASSUM_RENAME_TAC `eq' IN eqs1` [] >>
  Cases_on `eq'` >>
  Q.MATCH_ASSUM_RENAME_TAC `(t1,t2) IN eqs1` [] >>
  (IN_FDOM_NOTIN_rangevars |> Q.SPECL_THEN [`t1`,`x`,`FEMPTY|+(x,t)`] MP_TAC) >>
  (IN_FDOM_NOTIN_rangevars |> Q.SPECL_THEN [`t2`,`x`,`FEMPTY|+(x,t)`] MP_TAC) >>
  srw_tac [][rangevars_def] >>
  full_simp_tac (srw_ss()) [] ) >>
UNABBREV_ALL_TAC >>
srw_tac [][SUBSET_DEF] >>
full_simp_tac (srw_ss()) [var_elim_cases] >>
srw_tac [][] >>
Cases_on `x=x'` >> srw_tac [][] >- (
  qexists_tac `t` >> srw_tac [][] >> full_simp_tac (srw_ss()) [] >>
  Q.MATCH_ASSUM_RENAME_TAC `eq' IN eqs1` [] >>
  Cases_on `eq'` >>
  Q.MATCH_ASSUM_RENAME_TAC `(t1,t2) IN eqs1` [] >>
  (IN_FDOM_NOTIN_rangevars |> Q.SPECL_THEN [`t1`,`x`,`FEMPTY|+(x,t)`] MP_TAC) >>
  (IN_FDOM_NOTIN_rangevars |> Q.SPECL_THEN [`t2`,`x`,`FEMPTY|+(x,t)`] MP_TAC) >>
  srw_tac [][rangevars_def] >> full_simp_tac (srw_ss()) [] ) >>
qexists_tac `SAPPLY (FEMPTY|+(x,t)) t'` >> srw_tac [][] >- (
  qexists_tac `(Var x',t')` >> srw_tac [][FLOOKUP_UPDATE] )
>- (
  FIRST_X_ASSUM (Q.SPEC_THEN `(Var x,t)` MP_TAC) >>
  srw_tac [][] ) >>
Cases_on `x' IN vars t` >- (
  FIRST_X_ASSUM (Q.SPEC_THEN `(Var x,t)` MP_TAC) >>
  srw_tac [][] ) >>
Q.MATCH_ASSUM_RENAME_TAC `eq' IN eqs1` [] >>
Cases_on `eq'` >>
Q.MATCH_ASSUM_RENAME_TAC `(t1,t2) IN eqs1` [] >>
(NOTIN_rangevars_IN_vars |> Q.SPECL_THEN [`t1`,`x'`,`FEMPTY|+(x,t)`] MP_TAC) >>
(NOTIN_rangevars_IN_vars |> Q.SPECL_THEN [`t2`,`x'`,`FEMPTY|+(x,t)`] MP_TAC) >>
FIRST_X_ASSUM (Q.SPEC_THEN `(t1,t2)` mp_tac) >>
srw_tac [][rangevars_def] >> full_simp_tac (srw_ss()) [FLOOKUP_UPDATE]);

val alga1_sound = Q.store_thm(
"alga1_sound",
`alga1 eqs1 eqs2 ⇒ (set_unifier eqs1 = set_unifier eqs2)`,
srw_tac [][alga1_cases]
>- ( srw_tac [][set_unifier_def,EXTENSION] >> metis_tac [] )
>- ( srw_tac [][set_unifier_def,EXTENSION] >> metis_tac [] )
>- ( match_mp_tac term_red_sound >> asm_simp_tac pure_ss [] )
>- ( match_mp_tac (GEN_ALL var_elim_sound) >> asm_simp_tac (pure_ss ++ SATISFY_ss) [] ));

val alga1_FINITE = Q.store_thm(
"alga1_FINITE",
`alga1 eqs1 eqs2 ⇒ FINITE eqs1 ∧ FINITE eqs2`,
srw_tac [][alga1_cases] >> srw_tac [][] >| [
  match_mp_tac term_red_FINITE,
  match_mp_tac var_elim_FINITE
] >> srw_tac [SATISFY_ss][] );

(* We diverge slightly from the text below by
   requiring Algorithm A to check that the same function symbol
   is always applied to the same number of arguments. *)
val alga_fail_def = Define`
  alga_fail eqs = (∃f xs g ys. (App f xs, App g ys) ∈ eqs ∧
                               (f ≠ g ∨ LENGTH xs ≠ LENGTH ys)) ∨
                  (∃x t. (Var x, t) ∈ eqs ∧ x ∈ vars t ∧ t ≠ Var x)`;

val alga_stop_def = Define`
  alga_stop eqs1 eqs2 = FINITE eqs1 ∧ alga1^* eqs1 eqs2 ∧ ∀eqs3. ¬alga1 eqs2 eqs3`;

val alga_preserves_unifiers = Q.store_thm(
"alga_preserves_unifiers",
`alga_stop eqs1 eqs2 ⇒ (set_unifier eqs1 = set_unifier eqs2)`,
srw_tac [][alga_stop_def] >>
metis_tac [RTC_lifts_equalities, alga1_sound]);

val alga_sound = Q.store_thm( (* Half of Theorem 2.3 b (given alga_preserves_unifiers) *)
"alga_sound",
`alga_stop eqs1 eqs2 ∧ ¬alga_fail eqs2 ⇒ solved_form eqs2`,
srw_tac [][alga_stop_def] >>
`FINITE eqs2` by
  metis_tac [RTC_CASES2, alga1_FINITE] >>
srw_tac [][solved_form_def] >>
`∀eq. eq ∈ eqs2 ⇒ ∃v t. (eq = (Var v, t))` by (
  Q.PAT_ASSUM `eq ∈ eqs2` (K ALL_TAC) >>
  srw_tac [][] >>
  full_simp_tac bool_ss [alga1_cases,term_red_cases,var_elim_cases] >>
  Cases_on `eq` >> srw_tac [][] >>
  Q.MATCH_ASSUM_RENAME_TAC `(t1,t2) ∈ eqs2` [] >>
  Cases_on `t1` >> full_simp_tac (srw_ss()) [] >>
  Q.MATCH_ASSUM_RENAME_TAC `(App f ts,t2) ∈ eqs2` [] >>
  Cases_on `t2` >> full_simp_tac (srw_ss()) [] >- (
    Q.MATCH_ASSUM_RENAME_TAC `(App f ts,Var v) ∈ eqs2` [] >>
    FIRST_X_ASSUM (Q.SPEC_THEN `(Var v, App f ts) INSERT eqs2 DELETE (App f ts, Var v)` MP_TAC) >>
    srw_tac [][] >>
    DISJ1_TAC >>
    map_every qexists_tac [`App f ts`,`v`] >>
    srw_tac [][] ) >>
  Q.MATCH_ASSUM_RENAME_TAC `(App f xs,App g ys) ∈ eqs2` [] >>
  Cases_on `(f = g) ∧ (LENGTH xs = LENGTH ys)` >- (
    srw_tac [][] >>
    FIRST_X_ASSUM (Q.SPEC_THEN `eqs2 DELETE (App f xs,App f ys) ∪ set (ZIP (xs,ys))` MP_TAC) >>
    srw_tac [][] >>
    DISJ2_TAC >> DISJ2_TAC >> DISJ1_TAC >>
    map_every qexists_tac [`f`,`xs`,`ys`] >>
    srw_tac [][] ) >>
  metis_tac [alga_fail_def] ) >>
res_tac >>
srw_tac [][] >- (
  REVERSE (Cases_on `t = Var v`) >-
    metis_tac [alga_fail_def] >>
  full_simp_tac (srw_ss()) [alga1_cases] >>
  first_x_assum (Q.SPEC_THEN `eqs2 DELETE (Var v, Var v)` mp_tac) >>
  srw_tac [][] >>
  DISJ2_TAC >> DISJ1_TAC >>
  qexists_tac `v` >> srw_tac [][]) >>
Q.MATCH_RENAME_TAC `v ∉ varseq eq` [] >>
`∃w u. eq = (Var w, u)` by ( res_tac >> srw_tac [SATISFY_ss][] ) >>
full_simp_tac bool_ss [alga1_cases,var_elim_cases] >>
asm_simp_tac (srw_ss()) [] >>
`v ∉ vars t` by metis_tac [alga_fail_def] >>
FIRST_X_ASSUM (Q.SPEC_THEN `(Var v, t) INSERT IMAGE (SAPPLYeq (FEMPTY |+(v,t)))
                               (eqs2 DELETE (Var v,t))` MP_TAC) >>
asm_simp_tac (srw_ss()) [] >>
strip_tac >>
first_x_assum (Q.SPECL_THEN [`t`,`v`] MP_TAC) >>
asm_simp_tac (srw_ss()) [] >>
disch_then (Q.SPEC_THEN `(Var w, u)` MP_TAC) >>
srw_tac [][]);

val alga_complete = Q.store_thm( (* Half of Theorem 2.3 b *)
"alga_complete",
`alga_stop eqs1 eqs2 ∧ alga_fail eqs2 ⇒ (set_unifier eqs1 = {})`,
srw_tac [][] >>
imp_res_tac alga_preserves_unifiers >>
full_simp_tac (srw_ss()) [alga_fail_def,set_unifier_def,EXTENSION] >>
qx_gen_tac `s` >>
Q.MATCH_ASSUM_ABBREV_TAC `(t1,t2) ∈ eqs2` >>
map_every qexists_tac [`t1`,`t2`] >>
UNABBREV_ALL_TAC >>
srw_tac [][] >- metis_tac [LENGTH_MAP] >>
imp_res_tac occurs_not_unify >>
full_simp_tac (srw_ss()) []);

(* Determinize to get Algorithm R? *)

val _ = export_theory ();
