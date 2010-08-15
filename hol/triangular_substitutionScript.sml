open HolKernel boolLib bossLib boolSimps SatisfySimps Parse termTheory substitutionTheory arithmeticTheory relationTheory pred_setTheory prim_recTheory finite_mapTheory listTheory lcsymtacs

val _ = new_theory "triangular_substitution"

val FUNPOW_extends_mono = Q.store_thm(
"FUNPOW_extends_mono",
`∀P f. (∀x. P x ⇒ P (f x)) ∧ P x ⇒ P (FUNPOW f n x)`,
STRIP_TAC THEN Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);

val vR_def = Define`
  vR s y x = case FLOOKUP s x of SOME t -> y ∈ vars t || _ -> F`;

val wfs_def = Define `wfs s = WF (vR s)`;

val rangevars_FUPDATE = Q.store_thm(
"rangevars_FUPDATE",
`v ∉ FDOM s ⇒ (rangevars (s |+ (v,t)) = rangevars s UNION vars t)`,
SRW_TAC [][rangevars_def,DOMSUB_NOT_IN_DOM,UNION_COMM]);

val substvars_def = Define`
  substvars s = FDOM s UNION rangevars s`;

val FINITE_substvars = Q.store_thm(
"FINITE_substvars",
`FINITE (substvars s)`,
SRW_TAC [][substvars_def]);
val _ = export_rewrites ["FINITE_substvars"];

val wfs_FEMPTY = Q.store_thm(
"wfs_FEMPTY",
`wfs FEMPTY`,
SRW_TAC [][wfs_def] THEN
Q_TAC SUFF_TAC `(vR FEMPTY) = EMPTY_REL` THEN1 METIS_TAC [WF_EMPTY_REL] THEN
SRW_TAC [][FUN_EQ_THM,vR_def]);
val _ = export_rewrites ["wfs_FEMPTY"];

val wfs_SUBMAP = Q.store_thm(
"wfs_SUBMAP",
`wfs sx /\ s SUBMAP sx ==> wfs s`,
SRW_TAC [][wfs_def,SUBMAP_DEF] THEN
Q_TAC SUFF_TAC `!y x.vR s y x ==> vR sx y x`
  THEN1 METIS_TAC [WF_SUBSET] THEN
SRW_TAC [][vR_def,FLOOKUP_DEF] THEN
METIS_TAC []);

val wfs_no_cycles = Q.store_thm(
  "wfs_no_cycles",
  `wfs s <=> !v. ~(vR s)^+ v v`,
  EQ_TAC THEN1 METIS_TAC [WF_TC,wfs_def,WF_NOT_REFL] THEN
  SRW_TAC [] [wfs_def,WF_IFF_WELLFOUNDED,wellfounded_def] THEN
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  `!n. (f n) IN FDOM s /\ f (SUC n) IN vars (s ' (f n))` by
    (STRIP_TAC THEN Q.PAT_ASSUM `!n.vR s (f (SUC n)) (f n)` (Q.SPEC_THEN `n` MP_TAC)
     THEN FULL_SIMP_TAC (srw_ss()) [vR_def] THEN Cases_on `FLOOKUP s (f n)` THEN
     Q.PAT_ASSUM `FLOOKUP s (f n) = Z` MP_TAC THEN SRW_TAC [] [FLOOKUP_DEF])
  THEN
  `!n m. (vR s)^+ (f (SUC (n + m))) (f n)` by
    (REPEAT STRIP_TAC THEN Induct_on `m` THEN1
       (SRW_TAC [] [] THEN METIS_TAC [TC_SUBSET]) THEN
     Q.PAT_ASSUM `!n. f n IN FDOM s /\ Z` (Q.SPEC_THEN `SUC (n + m)` MP_TAC)
     THEN SRW_TAC [] [] THEN
     `(vR s) (f (SUC (SUC (n + m)))) (f (SUC (n + m)))` by METIS_TAC
     [vR_def,FLOOKUP_DEF] THEN METIS_TAC [TC_RULES,ADD_SUC])
  THEN
  `?n m. f (SUC (n + m)) = f n` by
    (`~INJ f (count (SUC (CARD (FDOM s)))) (FDOM s)`
         by (SRW_TAC [] [PHP,CARD_COUNT,COUNT_SUC,CARD_DEF]) THEN
     FULL_SIMP_TAC (srw_ss()) [INJ_DEF] THEN1 METIS_TAC [] THEN
     ASSUME_TAC (Q.SPECL [`x`,`y`] LESS_LESS_CASES) THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN1 METIS_TAC [] THENL [
       Q.EXISTS_TAC `x` THEN Q.EXISTS_TAC `y - x - 1`,
       Q.EXISTS_TAC `y` THEN Q.EXISTS_TAC `x - y - 1`
     ] THEN SRW_TAC [ARITH_ss] [ADD1])
  THEN METIS_TAC []);

val SAPPLY_FAPPLY = Q.store_thm(
"SAPPLY_FAPPLY",
`v IN FDOM s ==> (s ' v = SAPPLY s (Var v))`,
SRW_TAC [][SAPPLY_def,FLOOKUP_DEF]);

val noids_def = Define`
  noids s = ∀v. FLOOKUP s v ≠ SOME (Var v)`;

val SAPPLY_id = Q.store_thm(
"SAPPLY_id",
`(SAPPLY s t = t) <=> !v.v IN (vars t) ∧ v IN FDOM s ⇒ (s ' v = Var v)`,
EQ_TAC THEN
qid_spec_tac `t` >>
ho_match_mp_tac term_ind >>
srw_tac [DNF_ss][FLOOKUP_DEF,MEM_MAP,EVERY_MEM,LIST_EQ_REWRITE,rich_listTheory.EL_MAP,MEM_EL] >>
fsrw_tac [SATISFY_ss][]);

val idempotent_def = Define`
  idempotent s = !t.SAPPLY s (SAPPLY s t) = SAPPLY s t`;

val wfs_noids = Q.store_thm(
"wfs_noids",
`wfs s ⇒ noids s`,
SRW_TAC [][wfs_no_cycles,noids_def] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
FIRST_X_ASSUM (Q.SPEC_THEN `v` MP_TAC) THEN
SRW_TAC [][] THEN MATCH_MP_TAC TC_SUBSET THEN
SRW_TAC [][vR_def]);

val idempotent_rangevars = Q.store_thm(
"idempotent_rangevars",
`idempotent s ∧ noids s <=> DISJOINT (FDOM s) (rangevars s)`,
EQ_TAC THEN1 (
  SRW_TAC [][DISJOINT_BIGUNION,idempotent_def,noids_def,FLOOKUP_DEF,rangevars_def] THEN
  `∃v. v IN FDOM s ∧ (s ' v = x)`
  by (POP_ASSUM MP_TAC THEN SRW_TAC [][FRANGE_DEF]) THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `Var v` MP_TAC) THEN
  SRW_TAC [][FLOOKUP_DEF] THEN
  IMP_RES_TAC SAPPLY_id THEN
  SRW_TAC [][IN_DISJOINT] THEN
  PROVE_TAC []) THEN
SRW_TAC [][noids_def,IN_DISJOINT,FLOOKUP_DEF,idempotent_def,SAPPLY_id,rangevars_def] THEN1 (
  qpat_assum `v ∈ FDOM s` mp_tac >>
  qpat_assum `v ∈ vars (SAPPLY s t)` mp_tac >>
  map_every qid_spec_tac [`v`,`t`] >>
  ho_match_mp_tac term_ind >>
  srw_tac [DNF_ss][FLOOKUP_DEF,EVERY_MEM,MEM_MAP] >> fsrw_tac [][] >>
  `s ' v ∈ FRANGE s` by (SRW_TAC [][FRANGE_DEF] >> PROVE_TAC []) >>
  PROVE_TAC [] ) >>
Cases_on `v IN FDOM s` THEN SRW_TAC [][] THEN
`s ' v IN FRANGE s` by (SRW_TAC [][FRANGE_DEF] THEN PROVE_TAC []) THEN
`v NOTIN (vars (s ' v))` by PROVE_TAC [] THEN
Cases_on `s ' v` THEN FULL_SIMP_TAC (srw_ss()) []);

val wfs_FAPPLY_var = Q.store_thm(
"wfs_FAPPLY_var",
`wfs s ==> !v.v IN FDOM s ==> s ' v <> (Var v)`,
SRW_TAC [][wfs_no_cycles] THEN
`~vR s v v` by METIS_TAC [TC_SUBSET] THEN
POP_ASSUM MP_TAC THEN
Cases_on `s ' v` THEN
SRW_TAC [][vR_def,FLOOKUP_DEF]);

val TC_vR_vars_FRANGE = Q.store_thm(
"TC_vR_vars_FRANGE",
`∀u v. (vR s)^+ u v ⇒ v IN FDOM s ⇒ u IN BIGUNION (IMAGE vars (FRANGE s))`,
HO_MATCH_MP_TAC TC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [][vR_def] THEN1 (
  Cases_on `FLOOKUP s v` THEN FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF] THEN
  Q.EXISTS_TAC `vars x` THEN SRW_TAC [][] THEN SRW_TAC [][FRANGE_DEF] THEN
  Q.EXISTS_TAC `s ' v` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `v` THEN SRW_TAC [][] ) THEN
FIRST_X_ASSUM MATCH_MP_TAC THEN
IMP_RES_TAC TC_CASES2 THEN
FULL_SIMP_TAC (srw_ss()) [vR_def] THEN
FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF] THEN
spose_not_then strip_assume_tac >> fsrw_tac [][]);

val wfs_idempotent = Q.store_thm(
"wfs_idempotent",
`idempotent s ∧ noids s ⇒ wfs s`,
STRIP_TAC THEN IMP_RES_TAC idempotent_rangevars THEN
FULL_SIMP_TAC (srw_ss()) [rangevars_def] THEN
SRW_TAC [][wfs_no_cycles] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
IMP_RES_TAC TC_vR_vars_FRANGE THEN
IMP_RES_TAC TC_CASES2 THEN
FULL_SIMP_TAC (srw_ss()) [vR_def,FLOOKUP_DEF] THEN
Cases_on `v IN FDOM s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN SRW_TAC [][] THEN
PROVE_TAC [IN_DISJOINT]);

val selfapp_def = Define`
  (selfapp s = (SAPPLY s) o_f s)`;

val selfapp_eq_iter_APPLY = Q.store_thm(
"selfapp_eq_iter_APPLY",
`∀t. SAPPLY (selfapp s) t = SAPPLY s (SAPPLY s t)`,
ho_match_mp_tac term_ind >>
SRW_TAC [DNF_ss][selfapp_def,FLOOKUP_DEF,EVERY_MEM,LIST_EQ_REWRITE,rich_listTheory.EL_MAP,MEM_EL]);

val FDOM_selfapp = Q.store_thm(
"FDOM_selfapp",
`FDOM (selfapp s) = FDOM s`,
SRW_TAC [][selfapp_def]);
val _ = export_rewrites["FDOM_selfapp"];

val IN_vars_APPLY = Q.store_thm(
"IN_vars_APPLY",
`∀t v. v IN vars (SAPPLY s t) ⇔ v NOTIN FDOM s ∧ v IN vars t ∨ ∃x. vR s v x ∧ x IN vars t`,
ho_match_mp_tac term_ind >>
SRW_TAC [][vR_def,EQ_IMP_THM] THEN
fsrw_tac [DNF_ss][MEM_MAP,FLOOKUP_DEF,EVERY_MEM] >> srw_tac [][] >> fsrw_tac [][] >>
metis_tac []);

val vR1_def = Define`
  vR1 s y x = vR s y x ∧ y NOTIN FDOM s`;

val vR_selfapp = Q.store_thm(
"vR_selfapp",
`vR (selfapp s) = vR1 s RUNION NRC (vR s) 2`,
SRW_TAC [][RUNION,FUN_EQ_THM,vR1_def,selfapp_def,vR_def,
           FLOOKUP_DEF,EQ_IMP_THM] THEN
FULL_SIMP_TAC bool_ss [TWO,ONE,NRC] THEN
Cases_on `x' IN FDOM s` THEN
FULL_SIMP_TAC (srw_ss()) [IN_vars_APPLY,vR_def,FLOOKUP_DEF] THEN
METIS_TAC []);

val vR1_selfapp = Q.store_thm(
"vR1_selfapp",
`vR1 (selfapp s) = vR1 s RUNION (vR s O vR1 s)`,
SRW_TAC [][FUN_EQ_THM,EQ_IMP_THM,vR1_def] THEN
FULL_SIMP_TAC (srw_ss()) [vR_selfapp,RUNION,O_DEF] THEN
FULL_SIMP_TAC bool_ss [TWO,ONE,NRC,vR1_def]
THEN METIS_TAC []);

val FDOM_FUNPOW_selfapp = Q.store_thm(
"FDOM_FUNPOW_selfapp",
`FDOM (FUNPOW selfapp n s) = FDOM s`,
(FUNPOW_extends_mono |> Q.ISPEC `λs'. FDOM s' = FDOM s` |>
      SIMP_RULE (srw_ss()) [] |> MATCH_MP_TAC ) THEN
SRW_TAC [][]);
val _ = export_rewrites["FDOM_FUNPOW_selfapp"];

val NRC_2_IMP_TC_vR_selfapp = Q.store_thm(
"NRC_2_IMP_TC_vR_selfapp",
`∀n u v. NRC (vR s) (2* SUC n) u v ⇒ (vR (selfapp s))^+ u v`,
Induct THEN SRW_TAC [][] THEN1 (
  MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][vR_selfapp,RUNION] ) THEN
Cases_on `2 * SUC (SUC n)` THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [NRC_SUC_RECURSE_LEFT,MULT_SUC,ADD1] THEN
Cases_on `n'` THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [NRC_SUC_RECURSE_LEFT,ADD1] THEN
`2*n + 2 = n''` by DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
`vR (selfapp s) z' v` by (
  SRW_TAC [][vR_selfapp,RUNION] THEN
  SIMP_TAC bool_ss [TWO,ONE,NRC] THEN
  METIS_TAC [] ) THEN
METIS_TAC [TC_RULES]);

val NRC_2_1_IMP_TC_vR_selfapp = Q.store_thm(
"NRC_2_1_IMP_TC_vR_selfapp",
`∀n v u. NRC (vR s) (2 * n) v u ∧ vR1 s w v ⇒ (vR (selfapp s))^+ w u`,
Induct THEN SRW_TAC [][] THEN1 (
  MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][vR_selfapp,RUNION] ) THEN
Cases_on `2 * SUC n` THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [NRC_SUC_RECURSE_LEFT,ADD1] THEN
Cases_on `n'` THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [NRC_SUC_RECURSE_LEFT,ADD1] THEN
`2*n = n''` by DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
`vR (selfapp s) z' u` by (
  SRW_TAC [][vR_selfapp,RUNION] THEN
  SIMP_TAC bool_ss [TWO,ONE,NRC] THEN
  METIS_TAC [] ) THEN
IMP_RES_TAC TC_RULES);

val TC_vR_selfapp = Q.store_thm(
"TC_vR_selfapp",
`(vR (selfapp s))^+ v u ⇔ (∃n. NRC (vR s) (2 * (SUC n)) v u) ∨ (∃n u'. NRC (vR s) (2 * n) u' u ∧ vR1 s v u')`,
EQ_TAC THEN1 (
  MAP_EVERY Q.ID_SPEC_TAC [`u`,`v`] THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN
  SRW_TAC [][vR_selfapp,RUNION] THENL [
    DISJ2_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`0`,`u`] THEN
    SRW_TAC [][],
    DISJ1_TAC THEN Q.EXISTS_TAC `0` THEN
    SRW_TAC [][],
    IMP_RES_TAC NRC_ADD_I THEN
    FULL_SIMP_TAC (srw_ss()++ARITH_ss) [GSYM LEFT_ADD_DISTRIB,GSYM ADD_SUC] THEN
    PROVE_TAC [],
    Cases_on `2 * SUC n` THEN
    FULL_SIMP_TAC (srw_ss()) [NRC_SUC_RECURSE_LEFT,vR1_def,vR_def,FLOOKUP_DEF],
    IMP_RES_TAC NRC_ADD_I THEN
    FULL_SIMP_TAC (srw_ss()++ARITH_ss) [GSYM LEFT_ADD_DISTRIB,GSYM ADD_SUC] THEN
    METIS_TAC [],
    Cases_on `2 * n` THEN
    FULL_SIMP_TAC (srw_ss()) [NRC_SUC_RECURSE_LEFT,vR1_def,vR_def,FLOOKUP_DEF] THEN
    SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []
  ] ) THEN
SRW_TAC [][] THEN1
IMP_RES_TAC NRC_2_IMP_TC_vR_selfapp THEN
IMP_RES_TAC NRC_2_1_IMP_TC_vR_selfapp);

val wfs_selfapp = Q.store_thm(
"wfs_selfapp",
`wfs s ⇔ wfs (selfapp s)`,
SRW_TAC [][wfs_no_cycles,EQ_IMP_THM,TC_vR_selfapp] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THENL [
  Cases_on `2 * SUC n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  IMP_RES_TAC TC_eq_NRC THEN METIS_TAC [],
  Cases_on `2 * n` THEN FULL_SIMP_TAC (srw_ss()) [NRC_SUC_RECURSE_LEFT] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [vR1_def,vR_def,FLOOKUP_DEF] THEN
  FULL_SIMP_TAC (srw_ss()) [],
  IMP_RES_TAC TC_eq_NRC THEN
  IMP_RES_TAC NRC_ADD_I THEN
  FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
  METIS_TAC []
]);

val vR_LRC_ALL_DISTINCT = Q.store_thm(
"vR_LRC_ALL_DISTINCT",
`wfs s ⇒ ∀ls v u. LRC (vR s) ls v u ⇒ ALL_DISTINCT ls`,
STRIP_TAC THEN Induct THEN SRW_TAC [][LRC_def] THEN1 (
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  IMP_RES_TAC LRC_MEM_right THEN
  Cases_on `ls` THEN FULL_SIMP_TAC (srw_ss()) [LRC_def,wfs_no_cycles] THEN
  SRW_TAC [][] THEN1 (
    IMP_RES_TAC TC_SUBSET THEN RES_TAC) THEN
  RES_TAC THEN
  IMP_RES_TAC NRC_LRC THEN
  `NRC (vR s) (LENGTH p) h z` by METIS_TAC [] THEN
  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [LRC_def] THEN
  SRW_TAC [][] THEN1 (
    NTAC 2 (IMP_RES_TAC TC_RULES) THEN
    RES_TAC ) THEN
  IMP_RES_TAC TC_eq_NRC THEN
  SRW_TAC [][] THEN
  NTAC 2 (IMP_RES_TAC TC_RULES) THEN
  RES_TAC) THEN RES_TAC);

val vR_LRC_FDOM = Q.store_thm(
"vR_LRC_FDOM",
`LRC (vR s) (h::t) v u ∧ MEM e t ⇒ e IN FDOM s`,
SRW_TAC [][] THEN IMP_RES_TAC LRC_MEM_right THEN
Cases_on `e IN FDOM s` THEN
FULL_SIMP_TAC (srw_ss()) [LRC_def,vR_def,FLOOKUP_DEF]);

val vR_LRC_bound = Q.store_thm(
"vR_LRC_bound",
`wfs s ∧ LRC (vR s) ls u v ⇒ LENGTH ls ≤ CARD (FDOM s) + 1`,
Cases_on `ls` THEN SRW_TAC [ARITH_ss][ADD1] THEN
IMP_RES_TAC vR_LRC_ALL_DISTINCT THEN
IMP_RES_TAC vR_LRC_FDOM THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC ALL_DISTINCT_CARD_LIST_TO_SET THEN
`set t SUBSET FDOM s` by SRW_TAC [][SUBSET_DEF] THEN
METIS_TAC [CARD_SUBSET,FDOM_FINITE]);

val idempotent_selfapp = Q.store_thm(
"idempotent_selfapp",
`idempotent s ⇔ (selfapp s = s)`,
SRW_TAC [][idempotent_def,EQ_IMP_THM,GSYM fmap_EQ,FUN_EQ_THM] THEN1 (
  Cases_on `x IN FDOM s` THEN1 (
    FIRST_X_ASSUM (Q.SPEC_THEN `Var x` MP_TAC) THEN
    SRW_TAC [][FLOOKUP_DEF,selfapp_def] ) THEN
  ASSUME_TAC FDOM_selfapp THEN
  SRW_TAC [][NOT_FDOM_FAPPLY_FEMPTY] ) THEN
qid_spec_tac `t` >> ho_match_mp_tac term_ind >>
srw_tac [DNF_ss][LIST_EQ_REWRITE,rich_listTheory.EL_MAP,EVERY_MEM,MEM_EL,FLOOKUP_DEF] >>
FIRST_X_ASSUM (Q.SPEC_THEN `v` MP_TAC) THEN
SRW_TAC [][selfapp_def,o_f_DEF]);

val fixpoint_IMP_wfs = Q.store_thm(
"fixpoint_IMP_wfs",
`idempotent (FUNPOW selfapp n s) ∧ noids (FUNPOW selfapp n s) ⇒ wfs s`,
SRW_TAC [][] THEN IMP_RES_TAC wfs_idempotent THEN
POP_ASSUM MP_TAC THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN
Induct_on `n` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [FUNPOW_SUC] THEN
IMP_RES_TAC wfs_selfapp THEN
RES_TAC);

val idempotent_substeq = Q.store_thm(
"idempotent_substeq",
`(SAPPLY s1 = SAPPLY s2) ⇒ (idempotent s1 ⇔ idempotent s2)`,
SRW_TAC [][idempotent_def,EQ_IMP_THM]);

val vR_FUNPOW_selfapp_bound = Q.store_thm(
"vR_FUNPOW_selfapp_bound",
`∀n v u. vR (FUNPOW selfapp n s) v u ⇒ ∃m. 1 ≤ m ∧ NRC (vR s) m v u ∧ (v IN FDOM s ⇒ n ≤ m)`,
Induct THEN SRW_TAC [][] THEN1 (
  Q.EXISTS_TAC `1` THEN SRW_TAC [][] ) THEN
FULL_SIMP_TAC (srw_ss()) [FUNPOW_SUC,vR_selfapp,RUNION,vR1_def] THEN1 (
  RES_TAC THEN Q.EXISTS_TAC `m` THEN SRW_TAC [][] ) THEN
FULL_SIMP_TAC bool_ss [TWO,ONE,NRC] THEN
RES_TAC THEN IMP_RES_TAC NRC_ADD_I THEN
Q.EXISTS_TAC `m' + m` THEN SRW_TAC [][] THEN1
  DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [vR_def,FLOOKUP_DEF] THEN
Cases_on `z IN FDOM s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
DECIDE_TAC);

val idempotent_or_vR = Q.store_thm(
"idempotent_or_vR",
`idempotent s ∨ ∃u v. vR s v u ∧ v IN FDOM s`,
Cases_on `idempotent s` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [idempotent_def] THEN
pop_assum mp_tac >>
qid_spec_tac `t` >>
ho_match_mp_tac term_ind >>
SRW_TAC [][LIST_EQ_REWRITE,rich_listTheory.EL_MAP,EVERY_MEM,MEM_EL] THEN
Cases_on `FLOOKUP s v` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Q.EXISTS_TAC `v` THEN SRW_TAC [][vR_def] THEN
(SAPPLY_id |> Q.INST [`t`|->`x`] |> EQ_IMP_RULE |> snd |>
 CONTRAPOS |> IMP_RES_TAC) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN PROVE_TAC []);

val wfs_IMP_fixpoint = Q.store_thm(
"wfs_IMP_fixpoint",
`wfs s ⇒ ∃n. idempotent (FUNPOW selfapp n s) ∧ noids (FUNPOW selfapp n s)`,
STRIP_TAC THEN
`∀n. wfs (FUNPOW selfapp n s)`
by (MATCH_MP_TAC FUNPOW_extends_mono THEN
    SRW_TAC [][Once wfs_selfapp]) THEN
`∀n. noids (FUNPOW selfapp n s)`
by METIS_TAC [wfs_noids] THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
`∀n. ∃u v. vR (FUNPOW selfapp n s) v u ∧ v IN FDOM (FUNPOW selfapp n s)`
by METIS_TAC [idempotent_or_vR] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∀n. ∃m v u. 1 ≤ m ∧ NRC (vR s) m v u ∧ n ≤ m`
by METIS_TAC [vR_FUNPOW_selfapp_bound] THEN
`∀n. ∃ls v u. LRC (vR s) ls v u ∧ n ≤ LENGTH ls`
by METIS_TAC [NRC_LRC] THEN
POP_ASSUM (Q.SPEC_THEN `CARD (FDOM s) + 2` STRIP_ASSUME_TAC) THEN
IMP_RES_TAC vR_LRC_bound THEN
DECIDE_TAC);

val wfs_iff_fixpoint = Q.store_thm(
"wfs_iff_fixpoint",
`wfs s ⇔ ∃n. idempotent (FUNPOW selfapp n s) ∧ noids (FUNPOW selfapp n s)`,
METIS_TAC [wfs_IMP_fixpoint,fixpoint_IMP_wfs]);

val _ = export_theory ();
