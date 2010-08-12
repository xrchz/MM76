open HolKernel boolLib bossLib boolSimps SatisfySimps Parse multiequationTheory pred_setTheory listTheory lcsymtacs

val _ = new_theory "multiequation_system"

val _ = type_abbrev("system", ``:('a,'b) multiequation list # ('a,'b) multiequation set``)

val meqs_of_def = Define`
  meqs_of (sys:('a,'b) system) = set (FST sys) ∪ (SND sys)`;

val meqs_of_pair_rewrite = Q.store_thm(
"meqs_of_pair_rewrite",
`meqs_of (t,u) = set t ∪ u`,
srw_tac [][meqs_of_def]);

val wfsystem_def = Define`
  wfsystem (t,u) =
    FINITE u ∧
    RES_FORALL (meqs_of (t,u)) wfm ∧
    right_vars (meqs_of (t,u)) ⊆ left_vars (meqs_of (t,u)) ∧
    pairwise (RC (inv_image DISJOINT FST)) (meqs_of (t,u)) ∧
    (∀meq. MEM meq t ⇒ BAG_CARD (SND meq) ≤ 1) ∧
    (∀i tm. i < LENGTH t ∧
            ((∃j. tm <: (SND (EL j t)) ∧ i < j ∧ j < LENGTH t) ∨
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

val _ = export_theory ()
