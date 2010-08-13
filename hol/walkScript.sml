open HolKernel boolLib boolSimps bossLib SatisfySimps Parse finite_mapTheory relationTheory termTheory triangular_substitutionTheory arithmeticTheory pred_setTheory rich_listTheory listTheory lcsymtacs

val _ = new_theory "walk"

fun vwalk_wfs_hyp th =
let val th =
  Q.INST [`R` |-> `(vR s)`] th
in
  foldl (fn (h,th) => PROVE_HYP h th) th
    (map
      (UNDISCH o (fn t => prove (``wfs s ==> ^t``, SRW_TAC [] [wfs_def,vR_def])))
      (hyp th))
end

val vwalk_def = save_thm("vwalk_def",vwalk_wfs_hyp
(TotalDefn.xDefineSchema "pre_vwalk"
 `vwalk v =
    case FLOOKUP s v of
          SOME (Var u) -> vwalk u
       || SOME t -> t
       || NONE -> Var v`) |> DISCH_ALL)
val vwalk_ind = save_thm("vwalk_ind",vwalk_wfs_hyp (theorem "pre_vwalk_ind"))

val NOT_FDOM_vwalk = Q.store_thm(
  "NOT_FDOM_vwalk",
  `wfs s /\ v NOTIN FDOM s ==> (vwalk s v = Var v)`,
  SRW_TAC [] [Once vwalk_def, FLOOKUP_DEF]);

val vwalk_to_var = Q.store_thm(
  "vwalk_to_var",
  `wfs s ==> !v u. (vwalk s v = Var u) ==> u NOTIN FDOM s`,
  DISCH_TAC THEN HO_MATCH_MP_TAC vwalk_ind THEN
  SRW_TAC [][] THEN
  Cases_on `FLOOKUP s v` THEN1
    (REPEAT (POP_ASSUM MP_TAC) THEN
     REPEAT (SRW_TAC [][Once vwalk_def, FLOOKUP_DEF])) THEN
  `?w.x = Var w`
     by (Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [Once (UNDISCH vwalk_def)]) THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `w` MP_TAC) THEN SRW_TAC [][] THEN
  `vwalk s w = Var u` by (REPEAT (POP_ASSUM MP_TAC) THEN
                          SRW_TAC [] [Once vwalk_def] THEN
                          FULL_SIMP_TAC (srw_ss()) []) THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `u` MP_TAC) THEN SRW_TAC [][]);

val walk_def = Define`
  walk s t = case t of Var v -> vwalk s v || t -> t`;

val walk_thm = Q.store_thm(
"walk_thm",
`(walk s (Var v) = vwalk s v) /\
 (walk s (App f ts) = App f ts)`,
SRW_TAC [][walk_def]);
val _ = export_rewrites ["walk_thm"];

val walk_FEMPTY = Q.store_thm(
"walk_FEMPTY",
`(walk FEMPTY t = t) /\
 (vwalk FEMPTY v = Var v)`,
Cases_on `t` THEN NTAC 2 (SRW_TAC [][Once(DISCH_ALL vwalk_def)]));
val _ = export_rewrites ["walk_FEMPTY"];

val walk_var_vwalk = Q.store_thm(
"walk_var_vwalk",
`wfs s ==> (walk s t = Var v)
  ==> ?u.(t = Var u) /\ (vwalk s u = Var v)`,
SRW_TAC [][walk_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []);

val walk_to_var = Q.store_thm(
"walk_to_var",
`wfs s /\ (walk s t = Var v) ==>
   v NOTIN FDOM s /\ ?u.(t = Var u)`,
Cases_on `t` THEN SRW_TAC [][] THEN
PROVE_TAC [vwalk_to_var]);

val vwalk_vR = Q.store_thm(
"vwalk_vR",
`wfs s ==> !v u. u IN vars (vwalk s v) /\ vwalk s v <> Var v ==>
           (vR s)^+ u v`,
DISCH_TAC THEN HO_MATCH_MP_TAC vwalk_ind THEN SRW_TAC [][] THEN
`(FLOOKUP s v = NONE) \/ ?t. FLOOKUP s v = SOME t`
   by (Cases_on `FLOOKUP s v` THEN SRW_TAC [][]) THEN1
(`vwalk s v = Var v` by (ONCE_REWRITE_TAC [UNDISCH vwalk_def] THEN
 SRW_TAC [][])) THEN
Cases_on `t` THENL [
  qmatch_assum_rename_tac `FLOOKUP s v = SOME (Var n)` [] >>
  `vwalk s v = vwalk s n` by (SRW_TAC [][Once vwalk_def]) THEN
  `vR s n v` by SRW_TAC [][vR_def] THEN
  Cases_on `vwalk s n = Var n` THENL [
    `u = n` by FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][TC_SUBSET],
    `(vR s)^+ u n` by METIS_TAC [] THEN
    MATCH_MP_TAC
        (GEN_ALL (CONJUNCT2 (SPEC_ALL TC_RULES))) THEN
    METIS_TAC [TC_SUBSET]
  ],
  qmatch_assum_rename_tac `FLOOKUP s v = SOME (App f ts)` [] >>
  `vwalk s v = App f ts` by (SRW_TAC [][Once vwalk_def]) THEN
  MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][vR_def] THEN
  fsrw_tac [SATISFY_ss,DNF_ss][MEM_MAP]
]);

val vwalk_IN_FRANGE = Q.store_thm(
"vwalk_IN_FRANGE",
`wfs s ∧ v ∈ FDOM s ⇒ vwalk s v ∈ FRANGE s`,
SIMP_TAC (srw_ss()) [GSYM AND_IMP_INTRO] THEN
STRIP_TAC THEN Q.ID_SPEC_TAC `v` THEN
HO_MATCH_MP_TAC vwalk_ind THEN SRW_TAC [][] THEN
SRW_TAC [][Once vwalk_def] THEN
FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF] THEN
Cases_on `s ' v` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
  qmatch_assum_rename_tac `s ' v = Var n` [] >>
  Cases_on `n ∈ FDOM s` THEN SRW_TAC [][NOT_FDOM_vwalk],
  ALL_TAC] THEN
SRW_TAC [][FRANGE_DEF] THEN METIS_TAC []);

val walk_IN_FRANGE = Q.store_thm(
"walk_IN_FRANGE",
`wfs s ∧ walk s t ≠ t ⇒ walk s t ∈ FRANGE s`,
Cases_on `t` THEN SRW_TAC [][] THEN
qmatch_assum_rename_tac `vwalk s n ≠ Var n` [] >>
`n ∈ FDOM s` by METIS_TAC [NOT_FDOM_vwalk] THEN
SRW_TAC [][vwalk_IN_FRANGE]);

val vwalk_SUBMAP = Q.store_thm(
"vwalk_SUBMAP",
`wfs sx ==> !v s.s SUBMAP sx ==>
   (case vwalk s v of Var u -> (vwalk sx v = vwalk sx u)
                   || t -> (vwalk sx v = t))`,
STRIP_TAC THEN HO_MATCH_MP_TAC (Q.INST[`s`|->`sx`]vwalk_ind) THEN
SRW_TAC [][] THEN
`wfs s` by METIS_TAC [wfs_SUBMAP] THEN
POP_ASSUM MP_TAC THEN
SIMP_TAC (srw_ss())[Once vwalk_def] THEN
Cases_on `FLOOKUP s v` THEN SRW_TAC [][] THEN
Cases_on `x` THEN SRW_TAC [][] THENL [
  qmatch_assum_rename_tac `FLOOKUP s v = SOME (Var n)` [] >>
  `FLOOKUP sx v = SOME (Var n)`
     by METIS_TAC [FLOOKUP_SUBMAP] THEN
  `vwalk sx v = vwalk sx n`
     by SRW_TAC [][Once (DISCH_ALL vwalk_def), SimpLHS] THEN
  METIS_TAC [],
  qmatch_assum_rename_tac `FLOOKUP s v = SOME (App f ts)` [] >>
  `FLOOKUP sx v = SOME (App f ts)` by METIS_TAC [FLOOKUP_SUBMAP] THEN
  SRW_TAC [][Once (DISCH_ALL vwalk_def)]
]);

val _ = export_theory ()
