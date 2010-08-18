open HolKernel boolLib bossLib boolSimps Parse pairTheory pred_setTheory multiequation_systemTheory algorithm_bTheory multiequationTheory bagTheory substitutionTheory finite_mapTheory lcsymtacs

val _ = new_theory "unify"

val (unify1_rules,unify1_ind,unify1_cases) = Hol_reln`
  wfsystem (t1,u1) ∧
  (s,m) ∈ u1 ∧
  DISJOINT s (right_vars u1) ∧
  (∀meq. meq ∈ u1 ∧ meq ≠ (s,m) ⇒ DISJOINT s (FST meq)) ∧
  (m ≠ {||} ⇒ meq_red u1 (s,m) (c,f) u2)
  ⇒
  unify1 (t1,u1) (if m = {||} then (SNOC (s,m) t1, u1 DELETE (s,m))
                 else (SNOC (s,{|c|}) t1, (compactify u2) DELETE (s,{|c|})))`;

val DISJOINT_meqs_vars_elim = Q.store_thm(
"DISJOINT_meqs_vars_elim",
`FINITE s ∧ RES_FORALL meqs (FINITE_BAG o SND) ∧
 DISJOINT s (right_vars meqs) ⇒
 (meqs_vars_elim s c meqs = meqs)`,
srw_tac [][meqs_vars_elim_def,EXTENSION,EQ_IMP_THM,RES_FORALL_THM] >>
qmatch_assum_rename_tac `meq ∈ meqs` [] >>
(qsuff_tac `BAG_IMAGE (vars_elim s c) (SND meq) = (SND meq)` >- (
   Cases_on `meq` >> fsrw_tac [][] >>
   PROVE_TAC [FST,SND] )) >>
`FINITE_BAG (SND meq)` by PROVE_TAC [] >>
match_mp_tac BAG_IMAGE_FINITE_RESTRICTED_I >>
srw_tac [][BAG_EVERY,vars_elim_def] >>
match_mp_tac FDOM_DISJOINT_vars >>
srw_tac [][FUN_FMAP_DEF] >>
fsrw_tac [DNF_ss][right_vars_def] >>
PROVE_TAC []);

val unify1_subset_algb1 = Q.store_thm(
"unify1_subset_algb1",
`unify1 sys1 sys2 ⇒ algb1 sys1 sys2`,
srw_tac [][unify1_cases,algb1_cases] >>
Cases_on `m = {||}` >> fsrw_tac [][] >>
map_every qexists_tac [`f`,`m`,`u2`] >>
reverse (srw_tac [][]) >- (
  fsrw_tac [][meq_red_cases] >>
  `FINITE_BAG m` by PROVE_TAC [wfsystem_wfm_pair,wfm_FINITE_BAG,SND] >>
  imp_res_tac frontier_left_vars_occur >>
  PROVE_TAC [bag_vars_SUBSET_right_vars,DISJOINT_SUBSET,SND] ) >>
`meqs_vars_elim s c (compactify u2) = compactify u2` by (
  match_mp_tac DISJOINT_meqs_vars_elim >>
  `RES_FORALL u1 wfm` by PROVE_TAC [wfsystem_wfm_pair,meqs_of_def,IN_UNION,RES_FORALL_THM] >>
  `RES_FORALL u2 wfm` by PROVE_TAC [wfm_meq_red] >>
  `FINITE u2` by PROVE_TAC [meq_red_FINITE,wfsystem_FINITE_pair] >>
  `RES_FORALL (compactify u2) wfm` by PROVE_TAC [wfm_compactify] >>
  `FINITE s` by PROVE_TAC [wfsystem_wfm_pair,wfm_FINITE,FST] >>
  `FINITE_BAG m` by PROVE_TAC [RES_FORALL_THM,wfm_FINITE_BAG,SND] >>
  srw_tac [][RES_FORALL_THM] >- PROVE_TAC [RES_FORALL_THM,wfm_FINITE_BAG] >>
  PROVE_TAC [meq_red_right_vars_SUBSET,DISJOINT_SUBSET] ) >>
srw_tac [][]);

val _ = export_theory ()
