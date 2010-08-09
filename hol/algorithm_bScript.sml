open HolKernel boolLib bossLib boolSimps SatisfySimps Parse pairTheory stringTheory substitutionTheory multiequationTheory multiequation_systemTheory pred_setTheory listTheory relationTheory bagTheory finite_mapTheory lcsymtacs

val _ = new_theory "algorithm_b"

val (algb1_rules,algb1_ind,algb1_cases) = Hol_reln`
  wfsystem (t1,u1) ∧
  (s,m) ∈ u1 ∧
  DISJOINT s (BIGUNION (IMAGE FST f)) ∧
  meq_red u1 (s,m) (c,f) u2
    ⇒
  algb1 (t1,u1)
        (SNOC (s,{|c|}) t1,
         (IMAGE (λmeq. (FST meq, BAG_IMAGE (SAPPLY (FUN_FMAP (K c) s)) (SND meq))) (compactify u2))
         DELETE (s,{|c|}))`;

val algb_stop_def = Define`
  algb_stop sys1 sys2 = wfsystem sys1 ∧ algb1^* sys1 sys2 ∧ ∀sys3. ¬algb1 sys2 sys3`;

val algb_fail_def = Define`
  algb_fail (t,u) = ∃s m. (s,m) ∈ u ∧ m ≠ {||} ∧
                    ∀c f. common_part_frontier m (c,f) ⇒
                          ¬ DISJOINT s (BIGUNION (IMAGE FST f))`;

val BIGUNION_IMAGE_PSUBSET_lemma = Q.store_thm(
"BIGUNION_IMAGE_PSUBSET_lemma",
`(∀y. y ∈ s ∧ y ≠ x ⇒ DISJOINT (f y) (f x)) ∧ x ∈ s ∧ (f x ≠ {}) ⇒ BIGUNION (IMAGE f (s DELETE x)) ⊂ BIGUNION (IMAGE f s)`,
srw_tac [][PSUBSET_DEF,SUBSET_DEF] >- PROVE_TAC [] >>
srw_tac [DNF_ss][Once NOT_EQUAL_SETS] >>
fsrw_tac [][GSYM pred_setTheory.MEMBER_NOT_EMPTY,IN_DISJOINT] >>
PROVE_TAC [] );

val WF_algb1 = Q.store_thm( (* Part of Theorem 3.2 *)
"WF_algb1",
`WF (inv algb1)`,
match_mp_tac WF_SUBSET >>
WF_REL_TAC `inv_image (measure CARD) (BIGUNION o IMAGE FST o SND)` >>
srw_tac [DNF_ss][inv_DEF,algb1_cases,meq_red_cases] >>
match_mp_tac (MP_CANON CARD_PSUBSET) >>
qmatch_assum_rename_tac `wfsystem (t1,u1)` [] >>
ntac 2 (srw_tac [SATISFY_ss][]) >>
qmatch_abbrev_tac `BIGUNION (IMAGE FST (IMAGE sapp s1 DELETE e)) PSUBSET s2` >>
match_mp_tac PSUBSET_SUBSET_TRANS >>
qexists_tac `BIGUNION (IMAGE FST (IMAGE sapp s1))` >>
`wfm (s,m)` by metis_tac [wfsystem_wfm_pair] >>
reverse (srw_tac [][]) >- (
  `IMAGE FST (IMAGE sapp s1) = IMAGE FST s1` by (
    srw_tac [DNF_ss][EXTENSION,Abbr`sapp`] ) >>
  srw_tac [][Abbr`s1`,Abbr`s2`,compactify_same_vars] >- (
    srw_tac [DNF_ss,SATISFY_ss][SUBSET_DEF] )
  >- (
    srw_tac [DNF_ss][Abbr`e`,SUBSET_DEF] >>
    qexists_tac `(s,m)` >> srw_tac [][] ) >>
 srw_tac [DNF_ss][SUBSET_DEF] >>
 REWRITE_TAC [Once CONJ_COMM] >>
 match_mp_tac wfsystem_unsolved_var_in_unsolved_left >>
 map_every qexists_tac [`t1`,`s`,`m`] >>
 srw_tac [][] >>
 match_mp_tac frontier_vars_occur >>
 metis_tac [FST,SND,wfm_FINITE_BAG] ) >>
`FINITE s` by PROVE_TAC [wfm_def] >>
`sapp e = e` by (
  unabbrev_all_tac >>
  srw_tac [][] >>
  match_mp_tac (MP_CANON (FDOM_DISJOINT_vars)) >>
  srw_tac [][FUN_FMAP_DEF,IN_DISJOINT] >>
  Cases_on `x ∈ vars c` >> srw_tac [][] >>
  imp_res_tac vars_common_part_SUBSET_FST_frontier >>
  fsrw_tac [DNF_ss][SUBSET_DEF] >>
  PROVE_TAC [IN_DISJOINT] ) >>
`e ∈ s1` by (
  unabbrev_all_tac >> fsrw_tac [][] >>
  srw_tac [][compactify_def] >>
  DISJ2_TAC >> DISJ1_TAC >>
  qmatch_abbrev_tac `e = meq_merge_all ((share_vars meqs)^= e)` >>
  qsuff_tac `(share_vars meqs)^= e = {e}` >- (
    srw_tac [][Abbr`meqs`,Abbr`e`,meq_merge_all_def,BIG_BAG_UNION_INSERT] ) >>
  srw_tac [][EXTENSION,IN_DEF,EQ_IMP_THM] >>
  fsrw_tac [][EQC_DEF,RC_DEF] >>
  Cases_on `e=x` >> srw_tac [][] >>
  `?z. share_vars meqs e z ∧ e ≠ z` by metis_tac [TC_implies_one_step,symmetric_SC_identity,symmetric_share_vars] >>
  reverse (fsrw_tac [][Abbr`meqs`,Abbr`e`,share_vars_def]) >-
    PROVE_TAC [] >>
  `pairwise (RC (inv_image DISJOINT FST)) (meqs_of (t1,u1))` by PROVE_TAC [wfsystem_def] >>
  fsrw_tac [][pairwise_def,RC_DEF,inv_image_def,meqs_of_def] >>
  PROVE_TAC [FST] ) >>
match_mp_tac BIGUNION_IMAGE_PSUBSET_lemma >>
`s ≠ {}` by PROVE_TAC [wfm_def] >>
`e ∈ IMAGE sapp s1` by PROVE_TAC [IN_IMAGE] >>
srw_tac [][Abbr`e`] >>
srw_tac [][Abbr`sapp`] >>
`pairwise (RC (inv_image DISJOINT FST)) s1` by (
  unabbrev_all_tac >>
  MATCH_ACCEPT_TAC compactified_vars_disjoint) >>
pop_assum mp_tac >>
simp_tac std_ss [pairwise_def,inv_image_def,RC_DEF] >>
metis_tac [FST]);

val _ = export_theory ()
