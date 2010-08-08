open HolKernel boolLib bossLib Parse multiequationTheory

val _ = new_theory "multiequation_system"

val _ = type_abbrev("system", ``:('a,'b) multiequation list # ('a,'b) multiequation set``)

val meqs_of_def = Define`
  meqs_of (t,u) = set t ∪ u`;

val wfsystem_def = Define`
  wfsystem (t,u) =
    FINITE u ∧
    pairwise (RC (inv_image DISJOINT FST)) (meqs_of (t,u)) ∧
    (∀meq. MEM meq t ⇒ FINITE_BAG (SND meq) ∧ BAG_CARD (SND meq) ≤ 1) ∧
    (∀i tm. i < LENGTH t ∧
            ((∃j. tm <: (SND (EL j t)) ∧ i < j ∧ j < LENGTH t) ∨
             tm ∈ BIGUNION (IMAGE (SET_OF_BAG o SND) u))
            ⇒ DISJOINT (FST (EL i t)) (vars tm))`;

val _ = export_theory ()
