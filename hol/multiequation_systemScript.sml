open HolKernel boolLib bossLib Parse multiequationTheory lcsymtacs

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
    BIGUNION (IMAGE vars (BIGUNION (IMAGE (SET_OF_BAG o SND) (meqs_of (t,u))))) ⊆ BIGUNION (IMAGE FST (meqs_of (t,u))) ∧
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

val _ = export_theory ()
