open HolKernel Parse boolLib bossLib boolSimps SatisfySimps relationTheory pairTheory bagTheory prim_recTheory finite_mapTheory triangular_substitutionTheory termTheory walkTheory pred_setTheory listTheory lcsymtacs

val _ = new_theory "walkstar"

val pre_walkstar_def = TotalDefn.xDefineSchema "pre_walkstar"
 `walkstar t =
    case walk s t
    of App f ts -> App f (MAP walkstar ts)
    || w -> w`;

val _ = overload_on("walk*",``walkstar``)

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "◁", BreakSpace(1,0)],
                  term_name = "walk*",
                  fixity = Infixr 700}

val walkstarR_def = Define
`walkstarR s = inv_image ((LEX) (mlt1 (vR s)^+)^+ (measure (term_size ARB ARB))) (\t. (varb t, t))`;

val inst_walkstar =  Q.INST [`R` |-> `walkstarR s`]

val [hrec,hWF] = hyp (inst_walkstar pre_walkstar_def)

val walkstar_threc = Q.store_thm("walkstar_threc",
  `wfs s ⇒ ^hrec`,
SRW_TAC [][inv_image_def,LEX_DEF,walkstarR_def] THEN
Q.PAT_ASSUM `wfs s` ASSUME_TAC THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
  DISJ1_TAC THEN MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][mlt1_def] THEN
  qmatch_assum_rename_tac `MEM t1 ts` [] >>
  qmatch_assum_rename_tac `vwalk s n = App f ts` [] >>
  MAP_EVERY Q.EXISTS_TAC [`n`,`varb t1`,`{||}`] THEN
  srw_tac [][] >>
  match_mp_tac (MP_CANON vwalk_vR) >>
  srw_tac [DNF_ss,SATISFY_ss][MEM_MAP],
  qmatch_assum_rename_tac `MEM t2 ts` [] >>
  rpt (qpat_assum `X = Y` (K ALL_TAC)) >>
  srw_tac [][LIST_TO_SET_MAP] >>
  `FINITE_BAG (BIG_BAG_UNION (IMAGE varb (set ts)))` by (
    match_mp_tac FINITE_BIG_BAG_UNION >>
    ntac 2 (srw_tac [][]) ) >>
  srw_tac [][measure_thm,subterms_smaller] >>
  Cases_on `varb t2 = {||}` THEN1 (
    Cases_on `BIG_BAG_UNION (IMAGE varb (set ts)) = {||}` >>
    SRW_TAC [][] >>
    srw_tac [][mlt_TO_EMPTY_BAG] ) >>
  Cases_on `varb t2 = BIG_BAG_UNION (IMAGE varb (set ts))` >>
  srw_tac [][] >>
  `IMAGE varb (set ts) = (varb t2) INSERT (IMAGE varb (set ts)) DELETE (varb t2)` by (
    match_mp_tac (GSYM INSERT_DELETE) >>
    srw_tac [][] >>
    PROVE_TAC [] ) >>
  qmatch_assum_abbrev_tac `IMAGE varb (set ts) = varb t2 INSERT ss`  >>
  `FINITE ss` by srw_tac [][Abbr`ss`] >>
  srw_tac [][BIG_BAG_UNION_INSERT] >>
  MATCH_MP_TAC TC_mlt1_UNION2_I THEN
  SRW_TAC [][Abbr`ss`] THEN1 (
    match_mp_tac FINITE_BIG_BAG_UNION >>
    ntac 2 (srw_tac [][]) ) >>
  srw_tac [DNF_ss][GSYM bagTheory.MEMBER_NOT_EMPTY] >>
  spose_not_then strip_assume_tac >>
  qpat_assum `varb t2 ≠ BIG_BAG_UNION sob` mp_tac >>
  srw_tac [][] >>
  qmatch_abbrev_tac `b = BIG_BAG_UNION sob` >>
  `FINITE sob ∧ b ∈ sob` by (
    unabbrev_all_tac >> srw_tac [][] >> PROVE_TAC [] ) >>
  qsuff_tac `!b'. b' ∈ sob ⇒ (b' = b) ∨ (b' = {||})` >-
    metis_tac [BIG_BAG_UNION_EQ_ELEMENT] >>
  unabbrev_all_tac >> srw_tac [][] >>
  PROVE_TAC [bagTheory.MEMBER_NOT_EMPTY,IN_varb_vars]
]);

val walkstar_thWF = Q.store_thm("walkstar_thWF",
`wfs s ⇒ ^hWF`,
SRW_TAC [][wfs_def,walkstarR_def] THEN
MATCH_MP_TAC WF_inv_image THEN
SRW_TAC [][WF_measure, WF_TC, WF_LEX, WF_mlt1]);

fun walkstar_wfs_hyp th =
  th |>
  PROVE_HYP (UNDISCH walkstar_threc) |>
  PROVE_HYP (UNDISCH walkstar_thWF);

val walkstar_def = save_thm("walkstar_def",DISCH_ALL(walkstar_wfs_hyp (inst_walkstar pre_walkstar_def)));
val walkstar_ind = save_thm("walkstar_ind",walkstar_wfs_hyp (inst_walkstar (theorem "pre_walkstar_ind")));

val walkstar_thm = save_thm(
  "walkstar_thm",
[walkstar_def |> UNDISCH |> Q.SPEC `Var v` |> SIMP_RULE (srw_ss()) [],
 walkstar_def |> UNDISCH |> Q.SPEC `App f ts` |> SIMP_RULE (srw_ss()) []]
|> LIST_CONJ |> DISCH_ALL);
val _ = export_rewrites["walkstar_thm"];

val walkstar_FEMPTY = Q.store_thm(
"walkstar_FEMPTY",
`!t.(walk* FEMPTY t = t)`,
ASSUME_TAC wfs_FEMPTY THEN
HO_MATCH_MP_TAC (Q.INST[`s`|->`FEMPTY`]walkstar_ind) THEN
Cases_on `t` THEN
SRW_TAC [DNF_ss][LIST_EQ_REWRITE,rich_listTheory.EL_MAP,MEM_EL]);
val _ = export_rewrites ["walkstar_FEMPTY"];

val NOT_FDOM_walkstar = Q.store_thm(
"NOT_FDOM_walkstar",
`wfs s ==> !t. v NOTIN FDOM s ==> v IN vars t ==> v IN vars (walk* s t)`,
DISCH_TAC THEN HO_MATCH_MP_TAC walkstar_ind THEN SRW_TAC [][] THEN Cases_on `t` THENL [
  Q.PAT_ASSUM `wfs s` ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [Once vwalk_def, vars_def, FLOOKUP_DEF],
  Q.PAT_ASSUM `wfs s` ASSUME_TAC THEN
  fsrw_tac [DNF_ss][MEM_MAP] >>
  PROVE_TAC []
]);

val vwalk_EQ_var_vR = prove(
  ``wfs s ==> !u v1 v2. (vwalk s u = Var v1) /\ (vR s)^+ v2 u /\
                        v2 NOTIN FDOM s ==> (v1 = v2)``,
  STRIP_TAC THEN HO_MATCH_MP_TAC vwalk_ind THEN SRW_TAC [][] THEN
  IMP_RES_TAC TC_CASES2 THEN
  FULL_SIMP_TAC (srw_ss()) [vR_def] THEN
  Cases_on `FLOOKUP s u` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_ASSUM `vwalk s u = UU` MP_TAC THEN
  SRW_TAC [][Once vwalk_def] THEN
  Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  POP_ASSUM MP_TAC THEN SRW_TAC [][NOT_FDOM_vwalk]);

val vwalk_EQ_app_vR = Q.prove(
  `!v u. (vR s)^+ v u ==>
         !f ts. v NOTIN FDOM s /\ wfs s /\ (vwalk s u = App f ts) ==>
                 ?t u. (MEM t ts ∧ u IN vars t) /\ (vR s)^* v u`,
  HO_MATCH_MP_TAC TC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [vR_def] THENL [
    Cases_on `FLOOKUP s u` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Q.PAT_ASSUM `vwalk s u = XXX` MP_TAC THEN
    SRW_TAC [][Once vwalk_def] THEN
    Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
      POP_ASSUM MP_TAC THEN SRW_TAC [][NOT_FDOM_vwalk],
      fsrw_tac [][MEM_MAP] >> PROVE_TAC [RTC_REFL]
    ],
    qmatch_assum_rename_tac `vwalk s u' = App f ts` [] >>
    Cases_on `FLOOKUP s u'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Q.PAT_ASSUM `vwalk s u' = XXX` MP_TAC THEN
    SRW_TAC [][Once vwalk_def] THEN
    Cases_on `x` >>
    fsrw_tac [][MEM_MAP] >>
    PROVE_TAC [TC_RTC]
  ]);

val TC_vR_vars_walkstar = Q.store_thm(
  "TC_vR_vars_walkstar",
  `wfs s /\ u IN vars t /\ (vR s)^+ v u /\ v NOTIN FDOM s ==>
   v IN vars (walk* s t)`,
  Q_TAC SUFF_TAC
     `wfs s ==>
     !t v u. (vR s)^+ v u /\ v NOTIN FDOM s /\ u IN vars t ==>
             v IN vars (walk* s t)`
     THEN1 METIS_TAC [] THEN
  STRIP_TAC THEN HO_MATCH_MP_TAC walkstar_ind THEN
  SRW_TAC [][] THEN Cases_on `t` THENL [
    qmatch_rename_tac `v IN vars (walk* s (Var s'))` [] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
    Cases_on `vwalk s s'` THEN SRW_TAC [][] THENL [
      PROVE_TAC [vwalk_EQ_var_vR],
      qmatch_assum_rename_tac `vwalk s u = App f ts` [] >>
      `?t w. w IN vars t ∧ (MEM t ts)  /\ (vR s)^* v w`
         by PROVE_TAC [vwalk_EQ_app_vR] >>
      fsrw_tac [][RTC_CASES_TC] >>
      fsrw_tac [DNF_ss][MEM_MAP] >>
      PROVE_TAC [NOT_FDOM_walkstar]
    ],
    fsrw_tac [DNF_ss][MEM_MAP] >>
    PROVE_TAC []
  ]);

val walkstar_SUBMAP = Q.store_thm(
"walkstar_SUBMAP",
`s SUBMAP sx ∧ wfs sx ⇒ (walk* sx t = walk* sx (walk* s t))`,
STRIP_TAC THEN IMP_RES_TAC wfs_SUBMAP THEN
Q.ID_SPEC_TAC `t` THEN
HO_MATCH_MP_TAC walkstar_ind THEN
SRW_TAC [][] THEN
Q.PAT_ASSUM `wfs s` ASSUME_TAC THEN
fsrw_tac [DNF_ss][MEM_EL] >>
Cases_on `t` THEN SRW_TAC [][LIST_EQ_REWRITE,rich_listTheory.EL_MAP] THEN
Q.SPECL_THEN [`a`,`s`] MP_TAC (UNDISCH vwalk_SUBMAP) THEN
Cases_on `vwalk s a` THEN SRW_TAC [][LIST_EQ_REWRITE,rich_listTheory.EL_MAP]);

val walkstar_idempotent = Q.store_thm(
"walkstar_idempotent",
`wfs s ==> !t.(walk* s t = walk* s (walk* s t))`,
METIS_TAC [walkstar_SUBMAP,SUBMAP_REFL])

val walkstar_subterm_idem = Q.store_thm(
"walkstar_subterm_idem",
`(walk* s t1 = App f ts) ∧ MEM t ts  ∧ wfs s ⇒ (walk* s t = t)`,
SRW_TAC [][] THEN
IMP_RES_TAC walkstar_idempotent THEN
POP_ASSUM (Q.SPEC_THEN `t1` MP_TAC) THEN
FULL_SIMP_TAC (srw_ss()) [MEM_EL,LIST_EQ_REWRITE,rich_listTheory.EL_MAP])

val walkstar_walk = Q.store_thm(
"walkstar_walk",
`wfs s ==> (walk* s (walk s t) = walk* s t)`,
Cases_on `t` THEN SRW_TAC [][] THEN SRW_TAC [][] THEN
qmatch_rename_tac `walk* s (vwalk s n) = IX` ["IX"] >>
Cases_on `vwalk s n` THEN SRW_TAC [][] THEN
qmatch_assum_rename_tac `vwalk s n = Var n'` [] >>
`vwalk s n' = Var n'` by METIS_TAC [vwalk_to_var,NOT_FDOM_vwalk] THEN
SRW_TAC [][])

val walkstar_to_var = Q.store_thm(
"walkstar_to_var",
`(walk* s t = (Var v)) ∧ wfs s ⇒ v NOTIN (FDOM s) ∧ ∃u.t = Var u`,
REVERSE (SRW_TAC [][]) THEN1
(Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
IMP_RES_TAC walkstar_idempotent THEN
POP_ASSUM (Q.SPEC_THEN `t` MP_TAC) THEN
ASM_SIMP_TAC (srw_ss()) [] THEN
Cases_on `vwalk s v` THEN SRW_TAC [][] THEN
METIS_TAC [vwalk_to_var])

(* direct version of walkstar that does the walk itself *)

val apply_ts_thm = Q.store_thm(
"apply_ts_thm",
`wfs s ⇒
  (walk* s (Var v) =
     case FLOOKUP s v of NONE -> (Var v)
                      || SOME t -> walk* s t) ∧
  (walk* s (App f ts) = App f (MAP (walk* s) ts))`,
SIMP_TAC (srw_ss()) [] THEN STRIP_TAC THEN
Q.ID_SPEC_TAC `v` THEN
HO_MATCH_MP_TAC vwalk_ind THEN
SRW_TAC [][] THEN
Cases_on `FLOOKUP s v` THEN SRW_TAC [][Once vwalk_def] THEN1
(Cases_on `x` THEN SRW_TAC [][]) >>
metis_tac []);

val apply_ts_ind = save_thm(
"apply_ts_ind",
UNDISCH (Q.prove(
`wfs s ⇒
 ∀P. (∀v. (∀t. (FLOOKUP s v = SOME t) ⇒ P t) ⇒ P (Var v)) ∧
     (∀f ts. (∀t. MEM t ts ⇒ P t) ⇒ P (App f ts)) ⇒
     ∀t. P t`,
SRW_TAC [][] THEN
Q.ID_SPEC_TAC `t` THEN
HO_MATCH_MP_TAC walkstar_ind THEN
STRIP_TAC THEN Cases_on `t` THEN
SRW_TAC [][] THEN
qmatch_rename_tac `P (Var n)` [] >>
NTAC 3 (POP_ASSUM MP_TAC) THEN
Q.ID_SPEC_TAC `n` THEN
HO_MATCH_MP_TAC vwalk_ind THEN
SRW_TAC [][] THEN
Cases_on `FLOOKUP s n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Q.PAT_ASSUM `wfs s` ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [Once vwalk_def] THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Q_TAC SUFF_TAC `∀t. (FLOOKUP s n = SOME t) ⇒ P t` THEN1 METIS_TAC [] THEN
SRW_TAC [][] THEN
Q.PAT_ASSUM `∀f ts a'. X ⇒ P t2` MP_TAC THEN
SRW_TAC [][Once vwalk_def])));

val vars_walkstar = Q.store_thm(
"vars_walkstar",
`wfs s ⇒ ∀t. vars (walkstar s t) SUBSET vars t UNION BIGUNION (FRANGE (vars o_f s))`,
STRIP_TAC THEN HO_MATCH_MP_TAC apply_ts_ind THEN
SRW_TAC [][apply_ts_thm] THENL [
  Cases_on `FLOOKUP s v` THEN SRW_TAC [][] THEN
  `vars x SUBSET BIGUNION (FRANGE (vars o_f s))`
  by (MATCH_MP_TAC SUBSET_BIGUNION_I THEN
      MATCH_MP_TAC o_f_FRANGE THEN
      METIS_TAC [FRANGE_FLOOKUP]) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  Q.EXISTS_TAC `vars x UNION BIGUNION (FRANGE (vars o_f s))` THEN SRW_TAC [][] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  Q.EXISTS_TAC `BIGUNION (FRANGE (vars o_f s))` THEN SRW_TAC [][],
  SRW_TAC [DNF_ss][LIST_TO_SET_MAP,SUBSET_DEF,MEM_MAP] >>
  fsrw_tac [DNF_ss][SUBSET_DEF] >>
  PROVE_TAC []
]);

val _ = export_theory ()
