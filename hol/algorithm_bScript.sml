open HolKernel boolLib bossLib boolSimps SatisfySimps Parse pairTheory stringTheory termTheory substitutionTheory multiequationTheory multiequation_systemTheory pred_setTheory listTheory relationTheory bagTheory finite_mapTheory collapseTheory walkTheory walkstarTheory lcsymtacs

val _ = new_theory "algorithm_b"

val vars_elim_def = Define`
  vars_elim s c = SAPPLY (FUN_FMAP (K c) s)`;

val meqs_vars_elim_def = Define`
  meqs_vars_elim s c = IMAGE (λmeq. (FST meq, BAG_IMAGE (vars_elim s c) (SND meq)))`;

val vars_vars_elim = Q.store_thm(
"vars_vars_elim",
`FINITE s ⇒ (vars (vars_elim s c t) = if DISJOINT s (vars t) then vars t else vars t DIFF s ∪ vars c)`,
strip_tac >>
Cases_on `DISJOINT s (vars t)` >> srw_tac [][] >- (
  pop_assum mp_tac >>
  qid_spec_tac `t` >>
  ho_match_mp_tac term_ind >>
  srw_tac [][vars_elim_def,LIST_TO_SET_MAP,IN_DISJOINT,FLOOKUP_FUN_FMAP,MEM_MAP,EVERY_MEM] >>
  srw_tac [][SET_EQ_SUBSET] >>
  srw_tac [][SUBSET_DEF] >>
  PROVE_TAC [] ) >>
pop_assum mp_tac >>
qid_spec_tac `t` >>
ho_match_mp_tac term_ind >>
srw_tac [][vars_elim_def,FLOOKUP_FUN_FMAP,IN_DISJOINT,LIST_TO_SET_MAP,EVERY_MEM] >>
srw_tac [][SET_EQ_SUBSET] >> srw_tac [DNF_ss][SUBSET_DEF] >- (
  qmatch_assum_rename_tac `y ∈ vars X` ["X"] >>
  Cases_on `y ∈ vars c` >> srw_tac [][] >>
  `y ∈ vars a` by (
    match_mp_tac NOTIN_rangevars_IN_vars >>
    qexists_tac `FUN_FMAP (K c) s` >>
    srw_tac [DNF_ss][rangevars_def] ) >>
  Cases_on `y ∈ s` >> srw_tac [SATISFY_ss][] >>
  first_x_assum (qspec_then `a` mp_tac) >>
  srw_tac [SATISFY_ss][EXTENSION] >>
  PROVE_TAC [] )
>- (
  qmatch_assum_rename_tac `y ∉ s` [] >>
  qmatch_assum_rename_tac `y ∈ vars t` [] >>
  qexists_tac `t` >> srw_tac [][] >>
  match_mp_tac NOTIN_FDOM_IN_vars >>
  srw_tac [][FUN_FMAP_DEF] ) >>
qmatch_assum_rename_tac `x ∈ vars t` [] >>
qexists_tac `t` >> srw_tac [][] >>
res_tac >> srw_tac [][]);

val left_vars_meqs_vars_elim = Q.store_thm(
"left_vars_meqs_vars_elim",
`left_vars (meqs_vars_elim s c meqs) = left_vars meqs`,
srw_tac [DNF_ss][meqs_vars_elim_def,left_vars_def,EXTENSION]);
val _ = export_rewrites ["left_vars_meqs_vars_elim"];

val (algb1_rules,algb1_ind,algb1_cases) = Hol_reln`
  wfsystem (t1,u1) ∧
  (s,m) ∈ u1 ∧
  DISJOINT s (left_vars f) ∧
  meq_red u1 (s,m) (c,f) u2
    ⇒
  algb1 (t1,u1) (SNOC (s,{|c|}) t1, (meqs_vars_elim s c (compactify u2)) DELETE (s,{|c|}))`;

val algb_stop_def = Define`
  algb_stop sys1 sys2 = wfsystem sys1 ∧ algb1^* sys1 sys2 ∧ ∀sys3. ¬algb1 sys2 sys3`;

val algb_fail_def = Define`
  algb_fail (t,u) = ∃s m. (s,m) ∈ u ∧ m ≠ {||} ∧
                    ∀c f. common_part_frontier m (c,f) ⇒
                          ¬ DISJOINT s (left_vars f)`;

val BIGUNION_IMAGE_PSUBSET_lemma = Q.store_thm(
"BIGUNION_IMAGE_PSUBSET_lemma",
`(∀y. y ∈ s ∧ y ≠ x ⇒ DISJOINT (f y) (f x)) ∧ x ∈ s ∧ (f x ≠ {}) ⇒ BIGUNION (IMAGE f (s DELETE x)) ⊂ BIGUNION (IMAGE f s)`,
srw_tac [][PSUBSET_DEF,SUBSET_DEF] >- PROVE_TAC [] >>
srw_tac [DNF_ss][Once NOT_EQUAL_SETS] >>
fsrw_tac [][GSYM pred_setTheory.MEMBER_NOT_EMPTY,IN_DISJOINT] >>
PROVE_TAC [] );

val vars_elim_leaves_common_part = Q.store_thm(
"vars_elim_leaves_common_part",
`FINITE s ∧ common_part_frontier m (c,f) ∧ DISJOINT s (left_vars f) ⇒
 (vars_elim s c c = c)`,
srw_tac [][vars_elim_def] >>
match_mp_tac (MP_CANON (FDOM_DISJOINT_vars)) >>
srw_tac [][FUN_FMAP_DEF,IN_DISJOINT] >>
Cases_on `x ∈ vars c` >> srw_tac [][] >>
imp_res_tac vars_common_part_SUBSET_left_vars_frontier >>
fsrw_tac [DNF_ss][SUBSET_DEF] >>
PROVE_TAC [IN_DISJOINT]);

val compactify_leaves_common_part_meq = Q.store_thm(
"compactify_leaves_common_part_meq",
`meq_red u1 (s,m) (c,f) u2 ∧
 DISJOINT s (left_vars f) ∧
 pairwise (RC (inv_image DISJOINT FST)) u1
 ⇒ (s,{|c|}) ∈ compactify u2`,
srw_tac [][compactify_def,meq_red_cases] >>
DISJ2_TAC >> DISJ1_TAC >>
qmatch_abbrev_tac `e = meq_merge_all ((share_vars meqs)^= e)` >>
qsuff_tac `(share_vars meqs)^= e = {e}` >- (
  srw_tac [][Abbr`meqs`,Abbr`e`,meq_merge_all_def,BIG_BAG_UNION_INSERT] ) >>
srw_tac [][EXTENSION,IN_DEF,EQ_IMP_THM] >>
fsrw_tac [][EQC_DEF,RC_DEF] >>
Cases_on `e=x` >> srw_tac [][] >>
`?z. share_vars meqs e z ∧ e ≠ z` by metis_tac [TC_implies_one_step,symmetric_SC_identity,symmetric_share_vars] >>
reverse (fsrw_tac [][left_vars_def,Abbr`meqs`,Abbr`e`,share_vars_def]) >-
  PROVE_TAC [] >>
fsrw_tac [][pairwise_def,RC_DEF,inv_image_def,meqs_of_def] >>
PROVE_TAC [FST] );

val WF_algb1 = Q.store_thm( (* Part of Theorem 3.2 *)
"WF_algb1",
`WF (inv algb1)`,
match_mp_tac WF_SUBSET >>
WF_REL_TAC `inv_image (measure CARD) (left_vars o SND)` >>
srw_tac [DNF_ss][inv_DEF,algb1_cases] >>
match_mp_tac (MP_CANON CARD_PSUBSET) >>
qmatch_assum_rename_tac `wfsystem (t1,u1)` [] >>
conj_tac >- ntac 2 (srw_tac [SATISFY_ss][left_vars_def]) >>
qmatch_abbrev_tac `(left_vars (meqs_vars_elim s c s1 DELETE e)) PSUBSET s2` >>
match_mp_tac PSUBSET_SUBSET_TRANS >>
qexists_tac `left_vars (meqs_vars_elim s c s1)` >>
`wfm (s,m)` by metis_tac [wfsystem_wfm_pair] >>
reverse conj_tac >- (
  fsrw_tac [][meq_red_cases] >>
  srw_tac [][Abbr`s1`,Abbr`s2`,Abbr`e`] >- (
    srw_tac [DNF_ss,SATISFY_ss][left_vars_def,SUBSET_DEF] )
  >- (
    srw_tac [DNF_ss][left_vars_def,SUBSET_DEF] >>
    PROVE_TAC [FST] ) >>
  qmatch_abbrev_tac `left_vars s1 ⊆ left_vars u1` >>
  qsuff_tac `left_vars s1 ⊆ left_vars u1 ∪ right_vars u1` >-
    PROVE_TAC [wfsystem_unsolved_vars_SUBSET_left_vars,SUBSET_DEF,IN_UNION] >>
  `FINITE_BAG m` by PROVE_TAC [SND,wfm_FINITE_BAG] >>
  imp_res_tac frontier_left_vars_occur >>
  fsrw_tac [DNF_ss][left_vars_def,right_vars_def,SUBSET_DEF,Abbr`s1`] >>
  PROVE_TAC [FST,SND]) >>
`FINITE s` by PROVE_TAC [wfm_def] >>
simp_tac (std_ss) [left_vars_def] >>
match_mp_tac BIGUNION_IMAGE_PSUBSET_lemma >>
`s ≠ {}` by PROVE_TAC [wfm_def] >>
`pairwise (RC (inv_image DISJOINT FST)) s1` by (
  unabbrev_all_tac >>
  MATCH_ACCEPT_TAC compactified_vars_disjoint) >>
pop_assum mp_tac >>
simp_tac std_ss [pairwise_def,inv_image_def,RC_DEF] >>
`e ∈ s1` by (
  unabbrev_all_tac >>
  match_mp_tac compactify_leaves_common_part_meq >>
  srw_tac [][pairwise_def,RC_DEF,inv_image_def] >>
  metis_tac [wfsystem_def]) >>
`BAG_IMAGE (vars_elim s c) {|c|} = {|c|}` by (
  unabbrev_all_tac >> srw_tac [][] >>
  match_mp_tac vars_elim_leaves_common_part >>
  fsrw_tac [DNF_ss][meq_red_cases,left_vars_def] ) >>
asm_simp_tac (srw_ss())[meqs_vars_elim_def,FORALL_PROD,EXISTS_PROD,Abbr`e`] >>
PROVE_TAC [] );

val meqs_vars_elim_sound = Q.store_thm(
"meqs_vars_elim_sound",
`FINITE s ∧ RES_FORALL meqs (FINITE_BAG o SND) ∧
 (s,{|c|}) ∈ meqs ∧ (vars_elim s c c = c)
 ⇒ (meqs_unifier meqs = meqs_unifier (meqs_vars_elim s c meqs))`,
srw_tac [DNF_ss][FORALL_PROD,RES_FORALL_THM,meq_unifier_def,meqs_vars_elim_def,meqs_unifier_def,Once EXTENSION] >>
srw_tac [][EQ_IMP_THM] >>
qmatch_assum_rename_tac `(vs,m) ∈ meqs` [] >>
`!v1 v2. v1 ∈ vs ∧ v2 ∈ vs ⇒ (SAPPLY x (Var v1) = SAPPLY x (Var v2))` by
  fsrw_tac [SATISFY_ss][terms_of_pair_rewrite] >>
`!v. v ∈ s ⇒ (SAPPLY x (Var v) = SAPPLY x c)` by (
  rpt strip_tac >>
  first_x_assum (qspecl_then [`s`,`{|c|}`,`Var v`,`c`] mp_tac) >>
  srw_tac [][terms_of_def] ) >>
`!t. (SAPPLY x (vars_elim s c t) = SAPPLY x t)` by (
  ho_match_mp_tac termTheory.term_ind >>
  srw_tac [][MEM_EL,EVERY_MEM,vars_elim_def,FLOOKUP_FUN_FMAP,LIST_EQ_REWRITE,rich_listTheory.EL_MAP] >- (
    res_tac >> fsrw_tac [][] ) >>
  PROVE_TAC [] ) >>
`FINITE_BAG m` by PROVE_TAC [] >>
full_simp_tac std_ss [BAG_IN_FINITE_BAG_IMAGE,terms_of_thm] >>
metis_tac [BAG_IN_FINITE_BAG_IMAGE] );

val algb1_sound = Q.store_thm(
"algb1_sound",
`algb1 sys1 sys2 ⇒ (meqs_unifier (meqs_of sys1) = meqs_unifier (meqs_of sys2))`,
srw_tac [DNF_ss][meqs_of_def,algb1_cases] >>
srw_tac [][meqs_unifier_UNION,LIST_TO_SET_SNOC,meqs_unifier_INSERT] >>
`FINITE s` by PROVE_TAC [wfsystem_wfm_pair,wfm_FINITE,FST] >>
qmatch_abbrev_tac `A ∩ B = C ∩ A ∩ (meqs_unifier (meqs_vars_elim s c D DELETE e))` >>
`e ∈ D` by (
  unabbrev_all_tac >> srw_tac [][] >>
  match_mp_tac compactify_leaves_common_part_meq >>
  fsrw_tac [][wfsystem_def,pairwise_def,RC_DEF,inv_image_def] >>
  PROVE_TAC []) >>
`vars_elim s c c = c` by (
  match_mp_tac vars_elim_leaves_common_part >>
  fsrw_tac [][meq_red_cases] ) >>
`e ∈ meqs_vars_elim s c D` by (
  unabbrev_all_tac >> srw_tac [][meqs_vars_elim_def] >>
  qexists_tac `(s,{|c|})` >> srw_tac [][] ) >>
qsuff_tac `A ∩ B = A ∩ (C ∩ meqs_unifier (meqs_vars_elim s c D DELETE e))` >- PROVE_TAC [INTER_COMM,INTER_ASSOC] >>
srw_tac [][meqs_unifier_IN_INTER_DELETE,Abbr`C`] >>
qmatch_abbrev_tac `A ∩ B = A ∩ C` >>
qsuff_tac `B = C` >- srw_tac [][] >>
`B = meqs_unifier (compactify u2)` by
  metis_tac [meq_red_sound,wfsystem_wfm_pair,wfm_FINITE_BAG,
             compactify_sound,meq_red_FINITE,wfsystem_FINITE_pair] >>
unabbrev_all_tac >> srw_tac [][] >>
match_mp_tac meqs_vars_elim_sound >>
srw_tac [][RES_FORALL_THM] >>
PROVE_TAC [ wfm_FINITE_BAG, wfm_compactify, RES_FORALL_THM,
            wfsystem_wfm_pair, wfm_meq_red,
            meq_red_FINITE, wfsystem_FINITE_pair] );

val wfm_meqs_vars_elim = Q.store_thm(
"wfm_meqs_vars_elim",
`RES_FORALL meqs wfm ⇒ RES_FORALL (meqs_vars_elim s c meqs) wfm`,
srw_tac [][RES_FORALL_THM,meqs_vars_elim_def,FORALL_PROD] >>
Cases_on `meq` >> fsrw_tac [SATISFY_ss][wfm_def,BAG_EVERY,vars_elim_def] >>
srw_tac [DNF_ss][] >>
Cases_on `y` >> fsrw_tac [][] >> PROVE_TAC []);

val right_vars_meqs_vars_elim_SUBSET = Q.store_thm(
"right_vars_meqs_vars_elim_SUBSET",
`FINITE s ∧ RES_FORALL meqs (FINITE_BAG o SND) ⇒ (right_vars (meqs_vars_elim s c meqs) ⊆ right_vars meqs ∪ vars c)`,
strip_tac >>
srw_tac [DNF_ss][right_vars_def,meqs_vars_elim_def,SUBSET_DEF] >>
fsrw_tac [][RES_FORALL_THM] >>
res_tac >> fsrw_tac [][] >>
srw_tac [][] >>
qpat_assum `FINITE s` assume_tac >>
fsrw_tac [][vars_vars_elim] >>
qmatch_assum_rename_tac `y <: SND meq` [] >>
Cases_on `DISJOINT s (vars y)` >> fsrw_tac [SATISFY_ss][]);

val meqs_vars_elim_elim_right = Q.store_thm(
"meqs_vars_elim_elim_right",
`FINITE s ∧ RES_FORALL meqs (FINITE_BAG o SND) ∧
 DISJOINT s (vars c)
 ⇒ DISJOINT s (right_vars (meqs_vars_elim s c meqs))`,
srw_tac [DNF_ss][RES_FORALL_THM,meqs_vars_elim_def,right_vars_def] >>
qpat_assum `x <: B` mp_tac >>
srw_tac [][] >>
srw_tac [][vars_vars_elim,IN_DISJOINT] >>
PROVE_TAC [IN_DISJOINT]);

val wfsystem_algb1 = Q.store_thm(
"wfsystem_algb1",
`algb1 sys1 sys2 ⇒ wfsystem sys2`,
srw_tac [][algb1_cases,RES_FORALL_THM] >>
`FINITE_BAG m` by PROVE_TAC [wfsystem_wfm_pair,wfm_FINITE_BAG,SND] >>
`FINITE u2` by PROVE_TAC [wfsystem_FINITE,SND,meq_red_FINITE] >>
`FINITE (compactify u2)` by PROVE_TAC [FINITE_compactify] >>
qpat_assum `wfsystem (t1,u1)` mp_tac >>
srw_tac [][wfsystem_def,RES_FORALL_THM] >- (
  srw_tac [SATISFY_ss][meqs_vars_elim_def] )
>- (
  fsrw_tac [][meqs_of_def,rich_listTheory.IS_EL_SNOC] >- (
    imp_res_tac wfm_meq_red >>
    fsrw_tac [][meq_red_cases,RES_FORALL_THM] ) >>
  metis_tac [meq_red_FINITE,wfm_meq_red,wfm_compactify,wfm_meqs_vars_elim,RES_FORALL_THM] )
>- (
  fsrw_tac [DNF_ss][SUBSET_DEF,meqs_of_def] >>
  `FINITE s` by PROVE_TAC [wfm_FINITE,FST] >>
  srw_tac [][] >- (
    fsrw_tac [][right_vars_def,rich_listTheory.IS_EL_SNOC] >>
    fsrw_tac [][SET_OF_BAG_INSERT] >>
    srw_tac [][] >- (
      DISJ2_TAC >>
      match_mp_tac left_vars_DELETE >>
      srw_tac [][] >- (
        imp_res_tac meq_red_left_vars >>
        srw_tac [][] >>
        fsrw_tac [][meq_red_cases] >>
        imp_res_tac vars_common_part_SUBSET_left_vars_frontier >>
        fsrw_tac [][SUBSET_DEF] ) >>
      fsrw_tac [][meq_red_cases] >>
      imp_res_tac vars_common_part_SUBSET_left_vars_frontier >>
      fsrw_tac [][SUBSET_DEF,IN_DISJOINT] >>
      PROVE_TAC [] ) >>
    srw_tac [][LIST_TO_SET_SNOC] >>
    fsrw_tac [DNF_ss][] >>
    qmatch_assum_rename_tac `x ∈ vars tm` [] >>
    qmatch_assum_rename_tac `tm <: SND meq` [] >>
    ntac 2 (first_x_assum (qspecl_then [`x`,`tm`,`meq`] mp_tac)) >>
    ntac 2 (srw_tac [][]) >>
    Cases_on `x ∈ s` >> srw_tac [][] >>
    DISJ2_TAC >>
    match_mp_tac left_vars_DELETE >>
    srw_tac [][] >>
    imp_res_tac meq_red_left_vars >>
    srw_tac [][] ) >>
  `x ∈ right_vars (meqs_vars_elim s c (compactify u2))` by PROVE_TAC [right_vars_DELETE_SUBSET,SUBSET_DEF] >>
  srw_tac [][LIST_TO_SET_SNOC] >>
  `RES_FORALL (compactify u2) (FINITE_BAG o SND)` by (
    srw_tac [][RES_FORALL_THM] >>
    PROVE_TAC [wfm_FINITE_BAG,wfm_meq_red,wfm_compactify,RES_FORALL_THM] ) >>
  `right_vars (meqs_vars_elim s c (compactify u2)) ⊆ right_vars (compactify u2) ∪ vars c` by (
    match_mp_tac right_vars_meqs_vars_elim_SUBSET >>
    srw_tac [][RES_FORALL_THM] ) >>
  qpat_assum `FINITE u2` assume_tac >>
  fsrw_tac [][SUBSET_DEF] >>
  Cases_on `x ∈ right_vars u2` >- (
    `x ∈ left_vars (set t1) ∨ x ∈ left_vars u1` by PROVE_TAC [meq_red_right_vars_SUBSET,SUBSET_DEF] >>
    srw_tac [][] >>
    DISJ2_TAC >>
    match_mp_tac left_vars_DELETE >>
    srw_tac [][] >- (
      imp_res_tac meq_red_left_vars >>
      srw_tac [][] ) >>
    `DISJOINT s (right_vars (meqs_vars_elim s c (compactify u2)))` by (
      match_mp_tac meqs_vars_elim_elim_right >>
      srw_tac [][] >>
      fsrw_tac [][meq_red_cases] >>
      metis_tac [FST,SND,vars_common_part_SUBSET_left_vars_frontier,IN_DISJOINT,SUBSET_DEF] ) >>
  PROVE_TAC [IN_DISJOINT] ) >>
  `x ∈ vars c` by PROVE_TAC [] >>
  fsrw_tac [][meq_red_cases] >>
  imp_res_tac vars_common_part_SUBSET_left_vars_frontier >>
  fsrw_tac [][SUBSET_DEF] >>
  Cases_on `x ∈ s` >> srw_tac [][] >>
  DISJ2_TAC >>
  match_mp_tac left_vars_DELETE >>
  srw_tac [][] )
>- (
  `i < LENGTH t1` by DECIDE_TAC >>
  Cases_on `j < LENGTH t1` >- (
    fsrw_tac [SATISFY_ss][rich_listTheory.EL_SNOC] >>
    PROVE_TAC []) >>
  `j = LENGTH t1` by DECIDE_TAC >>
  fsrw_tac [][rich_listTheory.EL_LENGTH_SNOC,rich_listTheory.EL_SNOC,IN_DISJOINT] >>
  PROVE_TAC [FST,MEM_EL] )
>- (
  fsrw_tac [][meqs_vars_elim_def] >>
  `pairwise (RC (inv_image DISJOINT FST)) (compactify u2)` by MATCH_ACCEPT_TAC compactified_vars_disjoint >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [pairwise_def,RC_DEF,inv_image_def] >>
  metis_tac [] )
>- (
  `(s,{|c|}) ∈ compactify u2` by (
    match_mp_tac compactify_leaves_common_part_meq >>
    srw_tac [][pairwise_def,RC_DEF,inv_image_def] >>
    PROVE_TAC [] ) >>
  fsrw_tac [][meqs_vars_elim_def] >>
  `vars_elim s c c = c` by (
    match_mp_tac vars_elim_leaves_common_part >>
    fsrw_tac [][meq_red_cases,meqs_of_def] >>
    PROVE_TAC [wfm_FINITE,FST] ) >>
  `meq ≠ (s,{|c|})` by (
    spose_not_then strip_assume_tac >>
    fsrw_tac [][] ) >>
  Cases_on `meq1 = (s,{|c|})` >- (
    `pairwise (RC (inv_image DISJOINT FST)) (compactify u2)` by MATCH_ACCEPT_TAC compactified_vars_disjoint >>
    pop_assum mp_tac >>
    simp_tac (srw_ss()) [pairwise_def,RC_DEF,inv_image_def] >>
    metis_tac [FST] ) >>
  fsrw_tac [][rich_listTheory.IS_EL_SNOC] >>
  qsuff_tac `FST meq ⊆ left_vars u1 ∪ BIGUNION (IMAGE vars (SET_OF_BAG m))` >- (
    fsrw_tac [DNF_ss][SUBSET_DEF,IN_DISJOINT,left_vars_def,MEM_EL] >>
    qx_gen_tac `x` >>
    reverse (Cases_on `x ∈ FST meq`) >- srw_tac [][] >>
    disch_then (qspec_then `x` mp_tac) >>
    asm_simp_tac (srw_ss()) [] >>
    strip_tac >- PROVE_TAC [] >>
    qmatch_assum_rename_tac `tm <: m` [] >>
    first_x_assum (qspecl_then [`n`,`tm`,`(s,m)`,`x`] mp_tac) >>
    srw_tac [][] ) >>
  match_mp_tac SUBSET_TRANS >>
  qexists_tac `left_vars (compactify u2)` >>
  conj_tac >- (
    simp_tac std_ss [left_vars_def] >>
    match_mp_tac SUBSET_BIGUNION_I >>
    PROVE_TAC [IN_IMAGE] ) >>
  `left_vars u2 = left_vars u1 ∪ left_vars f` by PROVE_TAC [meq_red_left_vars] >>
  `left_vars f ⊆ BIGUNION (IMAGE vars (SET_OF_BAG m))` by (
    fsrw_tac [][meq_red_cases] >>
    PROVE_TAC [frontier_vars,SND,SUBSET_UNION,SUBSET_TRANS] ) >>
  asm_simp_tac (srw_ss()) [] >>
  PROVE_TAC [SUBSET_UNION,SUBSET_TRANS] )
>- (
  fsrw_tac [][rich_listTheory.IS_EL_SNOC,BAG_CARD_THM] )
>- (
  Cases_on `j < LENGTH t1` >- (
    `i < LENGTH t1` by DECIDE_TAC >>
    fsrw_tac [SATISFY_ss][EL_SNOC] ) >>
  `j = LENGTH t1` by DECIDE_TAC >>
  Cases_on `i = j` >- (
    fsrw_tac [][EL_LENGTH_SNOC,meq_red_cases] >>
    imp_res_tac vars_common_part_SUBSET_left_vars_frontier >>
    fsrw_tac [DNF_ss][SUBSET_DEF,IN_DISJOINT] >>
    PROVE_TAC [] ) >>
  `i < LENGTH t1` by DECIDE_TAC >>
  fsrw_tac [][rich_listTheory.EL_LENGTH_SNOC,rich_listTheory.EL_SNOC,IN_DISJOINT] >>
  qx_gen_tac `v` >>
  Cases_on `v ∈ vars c` >> srw_tac [][] >>
  fsrw_tac [][meq_red_cases] >>
  imp_res_tac vars_common_part_SUBSET_left_vars_frontier >>
  fsrw_tac [DNF_ss][SUBSET_DEF] >>
  `v ∈ left_vars f` by PROVE_TAC [] >>
  imp_res_tac frontier_left_vars_occur >>
  qpat_assum `FINITE_BAG m` assume_tac >>
  fsrw_tac [DNF_ss][SUBSET_DEF] >>
  PROVE_TAC [SND])
>- (
  `RES_FORALL (compactify u2) wfm` by (
    match_mp_tac wfm_compactify >>
    conj_tac >- srw_tac [][] >>
    match_mp_tac (GEN_ALL wfm_meq_red) >>
    map_every qexists_tac [`u1`,`(s,m)`,`(c,f)`] >>
    srw_tac [][RES_FORALL_THM] >>
    fsrw_tac [][meqs_of_def] ) >>
  fsrw_tac [][meqs_of_def] >>
  `FINITE s` by PROVE_TAC [wfm_FINITE,FST] >>
  Cases_on `i = LENGTH t1` >- (
    fsrw_tac [][rich_listTheory.EL_LENGTH_SNOC,meqs_vars_elim_def] >>
    srw_tac [][] >>
    fsrw_tac [][RES_FORALL_THM] >>
    srw_tac [][vars_vars_elim] >>
    srw_tac [][IN_DISJOINT] >-
      PROVE_TAC [] >>
    fsrw_tac [][meq_red_cases] >>
    imp_res_tac vars_common_part_SUBSET_left_vars_frontier >>
    fsrw_tac [][SUBSET_DEF,IN_DISJOINT] >>
    PROVE_TAC [] ) >>
  `i < LENGTH t1` by DECIDE_TAC >>
  srw_tac [][rich_listTheory.EL_SNOC] >>
  `right_vars (meqs_vars_elim s c (compactify u2)) ⊆ right_vars (compactify u2) ∪ vars c` by (
    match_mp_tac right_vars_meqs_vars_elim_SUBSET >>
    srw_tac [][RES_FORALL_THM] ) >>
  qpat_assum `FINITE u2` assume_tac >>
  fsrw_tac [][] >>
  `right_vars u2 ⊆ right_vars u1` by PROVE_TAC [meq_red_right_vars_SUBSET] >>
  `vars tm ⊆ right_vars (meqs_vars_elim s c (compactify u2))` by (
    srw_tac [SATISFY_ss,DNF_ss][right_vars_def,SUBSET_DEF] ) >>
  fsrw_tac [][meq_red_cases] >>
  `vars c ⊆ left_vars f` by PROVE_TAC [FST,SND,vars_common_part_SUBSET_left_vars_frontier] >>
  `left_vars f ⊆ BIGUNION (IMAGE vars (SET_OF_BAG m))` by PROVE_TAC [SND,frontier_left_vars_occur] >>
  fsrw_tac [DNF_ss][SUBSET_DEF,IN_DISJOINT,right_vars_def] >>
  metis_tac [SND] )
);

val wfsystem_algb = save_thm(
"wfsystem_algb",
RTC_lifts_invariants
|> Q.GEN `P` |> Q.ISPEC `wfsystem`
|> Q.GEN `R` |> Q.ISPEC `algb1`
|> UNDISCH
|> PROVE_HYP (
     wfsystem_algb1
     |> DISCH ``wfsystem sys1``
     |> SIMP_RULE bool_ss [AND_IMP_INTRO]
     |> Q.GEN `sys2` |> Q.GEN `sys1`)
|> Q.SPEC `sys1` |> Q.SPEC `sys2`);

val algb_complete = Q.store_thm( (* Part of Theorem 3.2 *)
"algb_complete",
`algb_stop sys1 sys2 ∧ algb_fail sys2 ⇒ (meqs_unifier (meqs_of sys2) = {})`,
srw_tac [][algb_stop_def] >>
qsuff_tac `wfsystem sys2` >- (
  strip_tac >>
  Cases_on `sys2` >> fsrw_tac [DNF_ss][algb_fail_def,algb_stop_def,meqs_of_def,meqs_unifier_def] >>
  srw_tac [DNF_ss][Once EXTENSION] >>
  DISJ2_TAC >>
  qexists_tac `(s,m)` >>
  `FINITE_BAG m` by PROVE_TAC [wfsystem_wfm_pair,wfm_FINITE_BAG,SND] >>
  reverse (Cases_on `?c f. common_part_frontier m (c,f)`) >- (
    metis_tac [pair_CASES,no_common_part,EXTENSION,NOT_IN_EMPTY] ) >>
  fsrw_tac [][IN_DISJOINT] >>
  metis_tac [wfsystem_wfm_pair,FST,meq_occurs_not_unify,EXTENSION,NOT_IN_EMPTY] ) >>
PROVE_TAC [wfsystem_algb]);

val algb_sound = save_thm(
"algb_sound",
RTC_lifts_equalities
|> Q.GEN `f` |> Q.ISPEC `meqs_unifier o meqs_of`
|> Q.GEN `R` |> Q.ISPEC `algb1`
|> SIMP_RULE std_ss []
|> UNDISCH
|> PROVE_HYP (algb1_sound |> Q.GEN `sys2` |> Q.GEN `sys1`)
|> Q.SPEC `sys1` |> Q.SPEC `sys2`);

val algb_success_empty_unsolved_bags = Q.store_thm(
"algb_success_empty_unsolved_bags",
`wfsystem sys ∧ (!sys'. ¬algb1 sys sys') ∧  ¬algb_fail sys ∧ meq ∈ SND sys ⇒ (SND meq = {||})`,
Cases_on `sys` >> Cases_on `meq` >>
srw_tac [][algb_fail_def,algb1_cases,meq_red_cases,algb1_cases] >>
PROVE_TAC []);

val wfsystem_singleton_solved_bags = Q.store_thm(
"wfsystem_singleton_solved_bags",
`wfsystem sys ∧ MEM meq (FST sys) ⇒ ∃tm. SND meq = {|tm|}`,
Cases_on `sys` >> Cases_on `meq` >>
srw_tac [][wfsystem_def,RES_FORALL_THM,meqs_of_def] >>
res_tac >>
imp_res_tac wfm_FINITE_BAG >>
fsrw_tac [][] >>
full_simp_tac pure_ss [arithmeticTheory.ONE] >>
fsrw_tac [][BCARD_SUC] >>
srw_tac [][] >>
fsrw_tac [][BCARD_0]);

val var_in_terms_of_wfm = Q.store_thm(
"var_in_terms_of_wfm",
`wfm meq ⇒ (Var v ∈ terms_of meq ⇔ v ∈ FST meq)`,
Cases_on `meq` >> srw_tac [][wfm_def,BAG_EVERY,terms_of_def] >>
PROVE_TAC []);

val algb_unifier = Q.store_thm(
"algb_unifier",
`algb_stop sys1 sys2 ∧ ¬algb_fail sys2 ⇒ collapse (system_subst sys2) ∈ meqs_unifier (meqs_of sys1)`,
srw_tac [][algb_stop_def] >>
`wfsystem sys2` by PROVE_TAC [wfsystem_algb] >>
`wfs (system_subst sys2)` by PROVE_TAC [wfsystem_wfs] >>
imp_res_tac algb_sound >>
srw_tac [][] >>
pop_assum (K ALL_TAC) >>
qpat_assum `wfsystem sys1` (K ALL_TAC) >>
qpat_assum `algb1^* sys1 sys2` (K ALL_TAC) >>
srw_tac [][meqs_unifier_def,meq_unifier_def] >>
srw_tac [][GSPECIFICATION,collapse_APPLY_eq_walkstar] >>
`FINITE (left_vars (set (FST sys2)) ∪ left_vars (IMAGE (\(s,m). (REST s,m)) (SND sys2)))` by (
  srw_tac [][EXISTS_PROD,left_vars_def] >>
  PROVE_TAC [wfsystem_wfm,FST,wfm_FINITE,FINITE_REST] ) >>
fsrw_tac [][meqs_of_def] >- (
  qmatch_assum_rename_tac `MEM meq (FST sys2)` [] >>
  `∃tm. SND meq = {|tm|}` by PROVE_TAC [wfsystem_singleton_solved_bags] >>
  qmatch_abbrev_tac `walk* s t1 = walk* s t2` >>
  `!v. v ∈ FST meq ⇒ (walk* s (Var v) = walk* s tm)` by (
    rpt strip_tac >>
    qsuff_tac `FLOOKUP s v = SOME tm` >- srw_tac [][Once vwalk_def,Once apply_ts_thm] >>
    srw_tac [][Abbr`s`,system_subst_def,FLOOKUP_FUN_FMAP] >- (
      srw_tac [DNF_ss,SATISFY_ss][left_vars_def] ) >>
    SELECT_ELIM_TAC >>
    conj_tac >- (Cases_on `meq` >> fsrw_tac [][] >> PROVE_TAC [BAG_IN_BAG_INSERT]) >>
    srw_tac [][] >>
    Cases_on `sys2` >>
    fsrw_tac [][wfsystem_def] >>
    fsrw_tac [][FORALL_PROD] >>
    fsrw_tac [][IN_DISJOINT] >>
    fsrw_tac [DNF_ss][] >- (
      fsrw_tac [][MEM_EL] >>
      qmatch_assum_rename_tac `(s,m) = EL n2 ls` [] >>
      qmatch_assum_rename_tac `meq = EL n1 ls` [] >>
      `¬(n1 < n2)` by PROVE_TAC [FST,pair_CASES] >>
      `¬(n2 < n1)` by PROVE_TAC [FST,pair_CASES] >>
      `n1 = n2` by DECIDE_TAC >>
      fsrw_tac [][] >>
      srw_tac [][] >>
      qpat_assum `(s,m) = EL n1 ls` (assume_tac o SYM) >>
      fsrw_tac [][] >>
      srw_tac [][] >>
      fsrw_tac [][] ) >>
    PROVE_TAC [REST_SUBSET,SUBSET_DEF,FST,pair_CASES] ) >>
  qpat_assum `wfs s` assume_tac >>
  fsrw_tac [][terms_of_def] ) >>
qmatch_assum_rename_tac `meq ∈ SND sys2` [] >>
`SND meq = {||}` by PROVE_TAC [algb_success_empty_unsolved_bags] >>
qmatch_abbrev_tac `walk* s t1 = walk* s t2` >>
`!v. v ∈ FST meq ⇒ (walk* s (Var v) = walk* s (Var (CHOICE (FST meq))))` by (
  rpt strip_tac >>
  qsuff_tac `(v = CHOICE (FST meq)) ∨ (FLOOKUP s v = SOME (Var (CHOICE (FST meq))))` >- (
    srw_tac [][] >>
    srw_tac [][Once vwalk_def] ) >>
  Cases_on `v = CHOICE (FST meq)` >>
  srw_tac [][Abbr`s`,system_subst_def,FLOOKUP_FUN_FMAP] >- (
    srw_tac [DNF_ss][left_vars_def] >>
    DISJ2_TAC >>
    qexists_tac `meq` >>
    Cases_on `meq` >> srw_tac [][] >>
    fsrw_tac [][] >>
    PROVE_TAC [CHOICE_INSERT_REST,IN_INSERT,pred_setTheory.MEMBER_NOT_EMPTY] ) >>
  SELECT_ELIM_TAC >>
  conj_tac >- metis_tac [pair_CASES,FST,CHOICE_INSERT_REST,IN_INSERT,pred_setTheory.MEMBER_NOT_EMPTY] >>
  srw_tac [][] >>
  Cases_on `sys2` >>
  fsrw_tac [][wfsystem_def] >>
  fsrw_tac [][FORALL_PROD] >>
  fsrw_tac [][IN_DISJOINT] >>
  fsrw_tac [DNF_ss][] >- (
    Cases_on `meq` >> fsrw_tac [][] >>
    PROVE_TAC [] ) >>
  Cases_on `meq` >>
  fsrw_tac [][] >>
  PROVE_TAC [REST_SUBSET,SUBSET_DEF] ) >>
fsrw_tac [][terms_of_def]);

(*
val algb1_example0 = Q.store_thm(
"algb1_example0",
`algb1 ([],
        {({"x"},
          {|App "f" [Var "x1"; App "g" [Var "x2"; Var "x3"]; Var "x2"; App "b" []];
            App "f" [App "g" [App "h" [App "a" []; Var "x5"]; Var "x2"]; Var "x1"; App "h" [App "a" []; Var "x4"]; Var "x4"]|});
         ({"x1"},{||});
         ({"x2"},{||});
         ({"x3"},{||});
         ({"x4"},{||});
         ({"x5"},{||})})

         ([({"x"},{|App "f" [Var "x1"; Var "x1"; Var "x2"; Var "x4"]|})],
          {({"x1"},{|App "g" [App "h" [App "a" []; Var "x5"]; Var "x2"]; App "g" [Var "x2"; Var "x3"]|});
           ({"x2"},{|App "h" [App "a" []; Var "x4"]|});
           ({"x3"},{||});
           ({"x4"},{|App "b" []|});
           ({"x5"},{||})})`,
srw_tac [][algb1_cases] >>
srw_tac [DNF_ss][EQUAL_SING] >>
srw_tac [][meq_red_cases] >>
srw_tac [DNF_ss][] >>
qho_match_abbrev_tac `?f c f'. P c f' ∧ (common_part_frontier m (cp,f) ∧ Q f ∧ common_part_frontier m (c,f'))` >>
simp_tac pure_ss [Once SWAP_EXISTS_THM] >>
qexists_tac `cp` >> srw_tac [][Abbr`P`] >>
srw_tac [DNF_ss][Abbr`cp`,Once common_part_frontier_cases] >>
unabbrev_all_tac >>
srw_tac [DNF_ss][] >>
simp_tac pure_ss [Once SWAP_EXISTS_THM] >>
qexists_tac `\i. EL i [Var "x1"; Var "x1"; Var "x2"; Var "x4"]` >>
srw_tac [][] >>
qho_match_abbrev_tac `?f' frontier. P f' ∧ (Q frontier ∧ R frontier f')` >>
srw_tac [DNF_ss][Abbr`R`,Once common_part_frontier_cases] >>
simp_tac pure_ss [Once SWAP_EXISTS_THM] >>
qexists_tac `\i. EL i [Var "x1"; Var "x1"; Var "x2"; Var "x4"]` >>
srw_tac [][] >>
ntac 2 (simp_tac pure_ss [Once CONJ_ASSOC]) >>
unabbrev_all_tac >>
qho_match_abbrev_tac `?frontier frontier'. P frontier frontier' ∧ ∀i. i < 4 ⇒ common_part_frontier {|EL i ls1;EL i ls2|} (EL i ls3,frontier' i)` >>
srw_tac [][Once common_part_frontier_cases] >>
qho_match_abbrev_tac `?frontier frontier'. P frontier frontier' ∧
∀i. i < 4 ⇒ (?v. ((Y i v ∧ (frontier' i = ZZ i v)) ∧ QQ frontier' i v)) ∨ XX frontier' i` >>
ntac 2 (qexists_tac `\i. EL i (MAP (\(i,ls). ZZ i (term_case I ARB (EL i ls))) [(0,ls1);(1,ls2);(2,ls1);(3,ls2)])`) >>
reverse conj_tac >- (
  unabbrev_all_tac >> srw_tac [][] >>
  Cases_on `i` >> fsrw_tac [][] >>
  Cases_on `n` >> fsrw_tac [][] >>
  Cases_on `n'` >> fsrw_tac [][] >>
  Cases_on `n` >> fsrw_tac [][] >>
  Cases_on `n'` >> fsrw_tac [ARITH_ss][] ) >>
srw_tac [][Abbr`ZZ`,Abbr`ls1`,Abbr`ls2`,Abbr`ls3`] >>
qmatch_abbrev_tac `P fr fr` >>
reverse (srw_tac [][Abbr`P`]) >- (
  Cases_on `i` >> fsrw_tac [][Abbr`fr`] >>
  Cases_on `n` >> fsrw_tac [][] >>
  Cases_on `n'` >> fsrw_tac [][] >>
  Cases_on `n` >> fsrw_tac [][] >>
  Cases_on `n'` >> fsrw_tac [ARITH_ss][] )
>- (
  srw_tac [][Once common_part_frontier_cases] >>
  Cases_on `i` >> fsrw_tac [][Abbr`fr`] >>
  Cases_on `n` >> fsrw_tac [][] >>
  Cases_on `n'` >> fsrw_tac [][] >>
  Cases_on `n` >> fsrw_tac [][] >>
  Cases_on `n'` >> fsrw_tac [ARITH_ss][] ) >>
unabbrev_all_tac >>
srw_tac [DNF_ss][BIGUNION] >>
srw_tac [][Once arithmeticTheory.EXISTS_NUM] >>
srw_tac [][Once arithmeticTheory.EXISTS_NUM] >>
srw_tac [][Once arithmeticTheory.EXISTS_NUM] >>
srw_tac [ARITH_ss][Once arithmeticTheory.EXISTS_NUM] >>
srw_tac [][DELETE_INSERT] >>
srw_tac [][GSPEC_EQ,GSPEC_OR] >>
srw_tac [][GSYM INSERT_SING_UNION] >>
srw_tac [][INSERT_UNION] >>
qmatch_abbrev_tac `s1 = IMAGE f (compactify {meq0;meq1;meq2;meq3;meq4;meq5;meq6;meq7;meq8;meq9}) DELETE meq5` >>
qmatch_abbrev_tac `s1 = IMAGE f (compactify s2) DELETE meq5` >>
srw_tac [][compactify_def] >>
`symmetric (share_vars s2)` by (
  srw_tac [][symmetric_def,share_vars_def,DISJOINT_SYM,EQ_IMP_THM] ) >>
`(share_vars s2)^= meq0 = {meq0;meq6;meq7}` by (
  srw_tac [][EXTENSION,IN_DEF] >>
  srw_tac [][EQ_IMP_THM] >- (
    Cases_on `x = meq0` >> srw_tac [][] >>
    Cases_on `x = meq6` >> srw_tac [][] >>
    Cases_on `x = meq7` >> srw_tac [][] >>
    qpat_assum `symmetric SSS` assume_tac >>
    fsrw_tac [][EQC_DEF,RC_DEF,symmetric_SC_identity] >>
*)

val pairwise_DISJOINT_implies_EQC_share_vars_sing = Q.store_thm(
"pairwise_DISJOINT_implies_EQC_share_vars_sing",
`!meqs meq. meq ∈ meqs ∧ pairwise (RC (inv_image DISJOINT FST)) meqs ⇒ ((share_vars meqs)^= meq = {meq})`,
srw_tac [][pairwise_def,RC_DEF,EXTENSION,inv_image_def] >>
simp_tac bool_ss [IN_DEF] >>
srw_tac [][EQ_IMP_THM] >>
qpat_assum `meq ∈ meqs` mp_tac >>
qpat_assum `R^= X Y` mp_tac >>
map_every qid_spec_tac [`x`,`meq`] >>
ho_match_mp_tac STRONG_EQC_INDUCTION >>
srw_tac [][share_vars_def] >>
metis_tac [EQC_share_vars_implies_IN] );

val EQC_eq = Q.store_thm(
"EQC_eq",
`$= ^= = $=`,
SRW_TAC [][EQC_DEF,FUN_EQ_THM,RC_DEF,SC_DEF,TC_DEF,EQ_IMP_THM] THEN
FIRST_X_ASSUM MATCH_MP_TAC THEN
SRW_TAC [][]);

val pairwise_UNION = Q.store_thm(
"pairwise_UNION",
`pairwise R (s1 ∪ s2) ⇔ pairwise R s1 ∧ pairwise R s2 ∧ (!x y. x ∈ s1 ∧ y ∈ s2 ⇒ R x y ∧ R y x)`,
srw_tac [DNF_ss][pairwise_def] >> metis_tac []);

val pairwise_SUBSET = Q.store_thm(
"pairwise_SUBSET",
`∀R s t. pairwise R t ∧ s ⊆ t ⇒ pairwise R s`,
srw_tac [][SUBSET_DEF,pairwise_def]);

val FINITE_BAG_IMAGE_eq_INSERT = Q.store_thm(
"FINITE_BAG_IMAGE_eq_INSERT",
`∀b. FINITE_BAG b ⇒ ∀x c. ((BAG_IMAGE f b = BAG_INSERT x c) ⇔ ∃e b0. (x = f e) ∧ (BAG_DELETE b e b0) ∧ (c = BAG_IMAGE f b0))`,
ho_match_mp_tac STRONG_FINITE_BAG_INDUCT >>
srw_tac [][BAG_DELETE] >>
srw_tac [][BAG_INSERT_EQUAL] >>
srw_tac [][EQ_IMP_THM] >- (
  map_every qexists_tac [`e`,`b`] >> srw_tac [][] )
>- (
  fsrw_tac [][] >>
  pop_assum mp_tac >> srw_tac [][] >>
  srw_tac [DNF_ss][] >>
  Cases_on `f e = f e'` >- (
    DISJ1_TAC >>
    map_every qexists_tac [`e'`,`b0`] >>
    srw_tac [][] ) >>
  srw_tac [][] >>
  map_every qexists_tac [`e'`,`b0`] >>
  srw_tac [][] ) >>
fsrw_tac [][] >>
Cases_on `f e = f e'` >> srw_tac [][] >>
map_every qexists_tac [`e'`,`k`] >>
srw_tac [][] );

val BAG_IMAGE_EQ_EMPTY = Q.store_thm(
"BAG_IMAGE_EQ_EMPTY",
`FINITE_BAG b ∧ (BAG_IMAGE f b = {||}) ⇒ (b = {||})`,
STRUCT_CASES_TAC (SPEC_ALL BAG_cases) THEN
SRW_TAC [][GSYM AND_IMP_INTRO]);

val INJ_IMAGE_DELETE = Q.store_thm(
"INJ_IMAGE_DELETE",
`INJ f s t ∧ x ∈ s ⇒ (IMAGE f (s DELETE x) = IMAGE f s DELETE (f x))`,
srw_tac [][EXTENSION,EQ_IMP_THM,INJ_DEF] >>
metis_tac []);

val meqs_unifier_INTER_DELETE = Q.store_thm(
"meqs_unifier_INTER_DELETE",
`meq_unifier meq ∩ meqs_unifier (meqs DELETE meq) = meq_unifier meq ∩ meqs_unifier meqs`,
srw_tac [][meqs_unifier_def] >>
Cases_on `meq ∈ meqs` >> srw_tac [][] >>
srw_tac [DNF_ss][BIGINTER,INTER_DEF,GSPEC_ETA] >>
srw_tac [][FUN_EQ_THM] >> PROVE_TAC []);

val _ = export_theory ()
