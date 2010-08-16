open HolKernel boolLib bossLib boolSimps SatisfySimps Parse multiequationTheory pred_setTheory listTheory termTheory substitutionTheory triangular_substitutionTheory bagTheory finite_mapTheory pairTheory relationTheory lcsymtacs

val _ = new_theory "multiequation_system"

val _ = type_abbrev("system", ``:('a,'b) multiequation list # ('a,'b) multiequation set``)

val meqs_of_def = Define`
  meqs_of (sys:('a,'b) system) = set (FST sys) ∪ (SND sys)`;

val meqs_of_pair_rewrite = Q.store_thm(
"meqs_of_pair_rewrite",
`meqs_of (t,u) = set t ∪ u`,
srw_tac [][meqs_of_def]);

(* We differ from the text by requiring the bags in the t part to
   have cardinality = 1 rather than ≤ 1.
   The only time they would have cardinality 0 is when the
   remaining equations from the u part are transferred to the t part,
   and we don't explicitly perform that step. *)
val wfsystem_def = Define`
  wfsystem (t,u) =
    FINITE u ∧
    RES_FORALL (meqs_of (t,u)) wfm ∧
    right_vars (meqs_of (t,u)) ⊆ left_vars (meqs_of (t,u)) ∧
    (∀meq1 meq2.
      ((∃i j. (meq1 = EL i t) ∧ (meq2 = EL j t) ∧ i < j ∧ j < LENGTH t) ∨
       (meq1 ∈ u ∧ meq2 ∈ u ∧ meq1 ≠ meq2) ∨
       (MEM meq1 t ∧ meq2 ∈ u)) ⇒
      DISJOINT (FST meq1) (FST meq2)) ∧
    (∀meq. MEM meq t ⇒ (BAG_CARD (SND meq) = 1)) ∧
    (∀i tm. i < LENGTH t ∧
            ((∃j. tm <: (SND (EL j t)) ∧ i ≤ j ∧ j < LENGTH t) ∨
             tm ∈ BIGUNION (IMAGE (SET_OF_BAG o SND) u))
            ⇒ DISJOINT (FST (EL i t)) (vars tm))`;

val wfsystem_FINITE = Q.store_thm(
"wfsystem_FINITE",
`wfsystem sys ⇒ FINITE (SND sys)`,
Cases_on `sys` >> srw_tac [][wfsystem_def]);
val _ = export_rewrites["wfsystem_FINITE"];

val wfsystem_FINITE_pair = Q.store_thm(
"wfsystem_FINITE_pair",
`wfsystem (t,u) ⇒ FINITE u`,
srw_tac [][wfsystem_def]);
val _ = export_rewrites["wfsystem_FINITE_pair"];

val wfsystem_wfm = Q.store_thm(
"wfsystem_wfm",
`(wfsystem sys ∧ meq ∈ SND sys ⇒ wfm meq) ∧
 (wfsystem sys ∧ MEM meq (FST sys) ⇒ wfm meq)`,
Cases_on `sys` >> srw_tac [][wfsystem_def,meqs_of_def]);
val _ = export_rewrites["wfsystem_wfm"];

val wfsystem_wfm_pair = Q.store_thm(
"wfsystem_wfm_pair",
`(wfsystem (t,u) ∧ meq ∈ u ⇒ wfm meq) ∧
 (wfsystem (t,u) ∧ MEM meq t ⇒ wfm meq)`,
srw_tac [][wfsystem_def,meqs_of_def]);
val _ = export_rewrites["wfsystem_wfm_pair"];

val wfsystem_unsolved_vars_SUBSET_left_vars = Q.store_thm(
"wfsystem_unsolved_vars_SUBSET_left_vars",
`∀t u. wfsystem (t,u) ⇒ right_vars u ⊆ left_vars u`,
srw_tac [DNF_ss][wfsystem_def,SUBSET_DEF,left_vars_def,right_vars_def] >>
qmatch_assum_rename_tac `meq ∈ u` [] >>
qmatch_assum_rename_tac `v ∈ vars tm` [] >>
first_x_assum (qspecl_then [`v`,`tm`,`meq`] mp_tac) >>
srw_tac [][meqs_of_def,MEM_EL] >- (
  first_x_assum (qspecl_then [`n`,`tm`,`meq`] mp_tac) >>
  srw_tac [][IN_DISJOINT] >>
  metis_tac [] ) >>
srw_tac [SATISFY_ss][]);

val system_subst_def = Define
`system_subst sys =
 FUN_FMAP
 (λx. @tm. ∃s m.((MEM (s,m) (FST sys) ∧ x ∈ s ∧ tm <: m) ∨
                 (s,m) ∈ (SND sys) ∧ x ∈ REST s ∧ (tm = Var (CHOICE s))))
 (left_vars (set (FST sys)) ∪
  left_vars (IMAGE (λ(s,m). (REST s, m)) (SND sys)))`;

val wfsystem_wfs = Q.store_thm(
"wfsystem_wfs",
`wfsystem sys ⇒ wfs (system_subst sys)`,
srw_tac [][wfs_def] >>
`?t u. sys = (t,u)` by (Cases_on `sys` >> srw_tac [][]) >>
srw_tac [][] >>
match_mp_tac WF_SUBSET >>
WF_REL_TAC `measure (λv. @i. (∃n s m. (n < LENGTH t) ∧ (EL n t = (s,m)) ∧ v ∈ s ∧ (i = 2 + LENGTH t - n)) ∨
                             (∃s m. (s,m) ∈ u ∧ v ∈ (REST s) ∧ (i = 1)) ∨
                             ((∀n. n < LENGTH t ⇒ v ∉ (FST (EL n t))) ∧
                              (∀s m. (s,m) ∈ u ⇒ v ∉ (REST s)) ∧
                              (i = 0)))` >>
`FINITE (left_vars (set t) ∪
         left_vars (IMAGE (λ(s,m). (REST s, m)) u))` by (
  srw_tac [][left_vars_def,EXISTS_PROD] >>
  PROVE_TAC [FINITE_REST,wfsystem_FINITE_pair,IMAGE_FINITE,wfsystem_wfm_pair,FST,wfm_FINITE] ) >>
fsrw_tac [DNF_ss][vR_def,system_subst_def,FLOOKUP_FUN_FMAP,left_vars_def] >>
map_every qx_gen_tac [`v2`,`v1`] >>
qmatch_abbrev_tac `(case if X then SOME Y else NONE of NONE -> F || SOME tm -> v2 ∈ vars tm) ⇒ A` >>
reverse (Cases_on `X = T`) >- srw_tac [][] >>
asm_simp_tac (srw_ss()) [] >>
Q.UNABBREV_TAC `X` >>
Q.UNABBREV_TAC `Y` >>
SELECT_ELIM_TAC >>
conj_tac >- (
  unabbrev_all_tac >>
  reverse (fsrw_tac [][EXISTS_PROD]) >>
  fsrw_tac [][wfsystem_def] >- PROVE_TAC [] >>
  qmatch_assum_rename_tac `MEM (vs,ms) t` [] >>
  `BAG_CARD ms = 1` by PROVE_TAC [SND] >>
  fsrw_tac [][meqs_of_def,RES_FORALL_THM] >>
  `FINITE_BAG ms` by PROVE_TAC [wfm_FINITE_BAG,SND] >>
  full_simp_tac pure_ss [arithmeticTheory.ONE] >>
  fsrw_tac [][BCARD_SUC] >> srw_tac [][] >>
  fsrw_tac [][BCARD_0] >> srw_tac [][] >>
  PROVE_TAC [BAG_IN_BAG_INSERT] ) >>
pop_assum (K ALL_TAC) >>
fsrw_tac [DNF_ss][] >>
conj_tac >>
srw_tac [][] >>
unabbrev_all_tac >>
fsrw_tac [][wfsystem_def] >>
fsrw_tac [][FORALL_PROD] >>
fsrw_tac [][EXISTS_PROD] >>
fsrw_tac [][MEM_EL,IN_DISJOINT] >- (
  SELECT_ELIM_TAC >>
  conj_tac >- (
    fsrw_tac [DNF_ss][] >>
    qmatch_abbrev_tac `A ∨ B ∨ C` >>
    Cases_on `A = T` >> srw_tac [][] >>
    Cases_on `B = T` >> srw_tac [][] >>
    DISJ2_TAC >> DISJ2_TAC >>
    unabbrev_all_tac >>
    conj_tac >- (
      qx_gen_tac `nn` >>
      fsrw_tac [][] >>
      first_x_assum (qspecl_then [`nn`,`FST (EL nn t)`,`SND (EL nn t)`] mp_tac) >>
      srw_tac [][] >> srw_tac [][] ) >>
    map_every qx_gen_tac [`ss`,`mm`] >>
    fsrw_tac [][] >>
    first_x_assum (qspecl_then [`ss`,`mm`] mp_tac) >>
    srw_tac [][] >> srw_tac [][] ) >>
  SELECT_ELIM_TAC >>
  conj_tac >- PROVE_TAC [] >>
  fsrw_tac [DNF_ss,ARITH_ss][] >>
  conj_tac >- (
    srw_tac [][] >>
    qmatch_rename_tac `LENGTH t + 2 < n2 + (LENGTH t + 2) - n1` [] >>
    `n = n1` by (
      spose_not_then strip_assume_tac >>
      Cases_on `n < n1` >- PROVE_TAC [] >>
      Cases_on `n1 < n` >- PROVE_TAC [] >>
      DECIDE_TAC ) >>
    `~(n2 ≤ n)` by metis_tac [FST,SND,PAIR_EQ] >>
    DECIDE_TAC ) >>
  conj_tac >- PROVE_TAC [REST_SUBSET,SUBSET_DEF] >>
  PROVE_TAC [FST] ) >>
SELECT_ELIM_TAC >>
conj_tac >- (
  fsrw_tac [DNF_ss][] >>
  DISJ2_TAC >> DISJ2_TAC >>
  conj_tac >- (
    srw_tac [][] >>
    `CHOICE s ∈ s` by PROVE_TAC [CHOICE_DEF,pred_setTheory.MEMBER_NOT_EMPTY,REST_SUBSET,SUBSET_DEF] >>
    Cases_on `EL n t` >> srw_tac [][] >>
    PROVE_TAC [CHOICE_NOT_IN_REST,FST,CHOICE_DEF,pred_setTheory.MEMBER_NOT_EMPTY,REST_SUBSET,SUBSET_DEF] ) >>
  metis_tac [CHOICE_NOT_IN_REST,FST,CHOICE_DEF,pred_setTheory.MEMBER_NOT_EMPTY,REST_SUBSET,SUBSET_DEF] ) >>
SELECT_ELIM_TAC >>
conj_tac >- PROVE_TAC [] >>
fsrw_tac [DNF_ss,ARITH_ss][] >>
conj_tac >- PROVE_TAC [REST_SUBSET,SUBSET_DEF] >>
conj_tac >- (
  conj_tac >- (
    srw_tac [][] >>
    PROVE_TAC [REST_SUBSET,SUBSET_DEF,CHOICE_DEF,pred_setTheory.MEMBER_NOT_EMPTY] ) >>
  srw_tac [][] >>
  metis_tac [CHOICE_NOT_IN_REST,REST_SUBSET,SUBSET_DEF,CHOICE_DEF,pred_setTheory.MEMBER_NOT_EMPTY] ) >>
PROVE_TAC []);

val meqR_def = Define`
  meqR meqs meq1 meq2 = meq1 ∈ meqs ∧ meq2 ∈ meqs ∧ ∃v tm. v ∈ FST meq1 ∧ tm <: SND meq2 ∧ v ∈ vars tm`;

val WF_meqR = Q.store_thm( (* Strengthened form of Theorem 3.3 *)
"WF_meqR",
`RES_FORALL meqs wfm ∧ meqs_unifier meqs ≠ {} ⇒ WF (meqR meqs)`,
srw_tac [DNF_ss][FORALL_PROD,GSYM pred_setTheory.MEMBER_NOT_EMPTY,
                 RES_FORALL_THM,wfm_def,BAG_EVERY,
                 meqs_unifier_def,meq_unifier_def] >>
fsrw_tac [][terms_of_def] >>
match_mp_tac WF_SUBSET >>
WF_REL_TAC `inv_image (measure (term_size ARB ARB)) (λ(s,m). SAPPLY x (Var (CHOICE s)))` >>
REWRITE_TAC [meqR_def] >>
rpt strip_tac >>
qmatch_assum_rename_tac `tm <: m2` [] >>
qmatch_assum_rename_tac `(s2,m2) ∈ meqs` [] >>
qmatch_rename_tac `term_size ARB ARB (SAPPLY s (Var (CHOICE s1))) < X` ["X"] >>
`∃f ts. tm = App f ts` by PROVE_TAC [term_nchotomy] >>
`psubterm (Var v) tm` by PROVE_TAC [vars_subterm,RTC_CASES_TC] >>
`SAPPLY s (Var (CHOICE s1)) = SAPPLY s (Var v)` by PROVE_TAC [CHOICE_DEF,pred_setTheory.MEMBER_NOT_EMPTY] >>
`SAPPLY s (Var (CHOICE s2)) = SAPPLY s tm` by PROVE_TAC [CHOICE_DEF,pred_setTheory.MEMBER_NOT_EMPTY] >>
PROVE_TAC [psubterm_mono_SAPPLY,psubterm_term_size,prim_recTheory.measure_thm]);

val transitive_WF_imp_StrongOrder = Q.store_thm( (* this can take you closer to Theorem 3.3 as in the text *)
"transitive_WF_imp_StrongOrder",
`transitive R ∧ WF R ⇒ StrongOrder R`,
srw_tac [][StrongOrder] >-
  PROVE_TAC [irreflexive_def,WF_NOT_REFL] >>
srw_tac [][antisymmetric_def] >>
fsrw_tac [][prim_recTheory.WF_IFF_WELLFOUNDED,prim_recTheory.wellfounded_def] >>
first_x_assum (qspec_then `\n. if EVEN n then x else y` mp_tac) >>
srw_tac [][] >>
Cases_on `EVEN n` >> fsrw_tac [][arithmeticTheory.EVEN] );

val _ = export_theory ()
