open HolKernel boolLib bossLib boolSimps SatisfySimps Parse pairTheory stringTheory substitutionTheory multiequationTheory multiequation_systemTheory pred_setTheory listTheory relationTheory bagTheory finite_mapTheory lcsymtacs

val _ = new_theory "algorithm_b"

val vars_elim_def = Define`
  vars_elim s c = SAPPLY (FUN_FMAP (K c) s)`;

val meqs_vars_elim_def = Define`
  meqs_vars_elim s c = IMAGE (λmeq. (FST meq, BAG_IMAGE (vars_elim s c) (SND meq)))`;

val (algb1_rules,algb1_ind,algb1_cases) = Hol_reln`
  wfsystem (t1,u1) ∧
  (s,m) ∈ u1 ∧
  DISJOINT s (BIGUNION (IMAGE FST f)) ∧
  meq_red u1 (s,m) (c,f) u2
    ⇒
  algb1 (t1,u1) (SNOC (s,{|c|}) t1, (meqs_vars_elim s c (compactify u2)) DELETE (s,{|c|}))`;

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

val vars_elim_leaves_common_part = Q.store_thm(
"vars_elim_leaves_common_part",
`FINITE s ∧ common_part_frontier m (c,f) ∧ (∀x. x ∈ f ⇒ DISJOINT s (FST x)) ⇒
 (vars_elim s c c = c)`,
srw_tac [][vars_elim_def] >>
match_mp_tac (MP_CANON (FDOM_DISJOINT_vars)) >>
srw_tac [][FUN_FMAP_DEF,IN_DISJOINT] >>
Cases_on `x ∈ vars c` >> srw_tac [][] >>
imp_res_tac vars_common_part_SUBSET_FST_frontier >>
fsrw_tac [DNF_ss][SUBSET_DEF] >>
PROVE_TAC [IN_DISJOINT]);

val compactify_leaves_common_part_meq = Q.store_thm(
"compactify_leaves_common_part_meq",
`meq_red u1 (s,m) (c,f) u2 ∧
 (∀x. x ∈ f ⇒ DISJOINT s (FST x)) ∧
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
reverse (fsrw_tac [][Abbr`meqs`,Abbr`e`,share_vars_def]) >-
  PROVE_TAC [] >>
fsrw_tac [][pairwise_def,RC_DEF,inv_image_def,meqs_of_def] >>
PROVE_TAC [FST] );

val WF_algb1 = Q.store_thm( (* Part of Theorem 3.2 *)
"WF_algb1",
`WF (inv algb1)`,
match_mp_tac WF_SUBSET >>
WF_REL_TAC `inv_image (measure CARD) (BIGUNION o IMAGE FST o SND)` >>
srw_tac [DNF_ss][inv_DEF,algb1_cases] >>
match_mp_tac (MP_CANON CARD_PSUBSET) >>
qmatch_assum_rename_tac `wfsystem (t1,u1)` [] >>
ntac 2 (srw_tac [SATISFY_ss][]) >>
qmatch_abbrev_tac `BIGUNION (IMAGE FST (meqs_vars_elim s c s1 DELETE e)) PSUBSET s2` >>
match_mp_tac PSUBSET_SUBSET_TRANS >>
qexists_tac `BIGUNION (IMAGE FST (meqs_vars_elim s c s1))` >>
`wfm (s,m)` by metis_tac [wfsystem_wfm_pair] >>
reverse (srw_tac [][]) >- (
  `IMAGE FST (meqs_vars_elim s c s1) = IMAGE FST s1` by (
    srw_tac [DNF_ss][EXTENSION,meqs_vars_elim_def] ) >>
  fsrw_tac [][meq_red_cases] >>
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
  `pairwise (RC (inv_image DISJOINT FST)) (meqs_of (t1,u1))` by PROVE_TAC [wfsystem_def] >>
  fsrw_tac [][pairwise_def,RC_DEF,inv_image_def,meqs_of_def] ) >>
`BAG_IMAGE (vars_elim s c) {|c|} = {|c|}` by (
  unabbrev_all_tac >> srw_tac [][] >>
  match_mp_tac vars_elim_leaves_common_part >>
  fsrw_tac [][meq_red_cases] ) >>
asm_simp_tac (srw_ss())[meqs_vars_elim_def,Abbr`e`,FORALL_PROD,EXISTS_PROD] >>
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
  fsrw_tac [][wfsystem_def,meqs_of_def,pairwise_def] ) >>
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

val vars_common_part_SUBSET = Q.store_thm(
"vars_common_part_SUBSET",
`!m cf. common_part_frontier m cf ⇒ FINITE_BAG m ⇒ vars (FST cf) ⊆ BIGUNION (IMAGE vars (SET_OF_BAG m))`,
ho_match_mp_tac common_part_frontier_ind >>
srw_tac [DNF_ss][] >- (
  qexists_tac `Var v` >> srw_tac [][] ) >>
srw_tac [DNF_ss][SUBSET_DEF,rich_listTheory.MAP_GENLIST,MEM_EL] >>
fsrw_tac [DNF_ss][BAG_EVERY,rich_listTheory.EL_GENLIST,SUBSET_DEF] >>
qmatch_assum_rename_tac `i < n` [] >>
first_x_assum (qspecl_then [`i`,`x`] mp_tac) >>
srw_tac [][] >>
qexists_tac `y` >>
res_tac >> fsrw_tac [][] >>
srw_tac [SATISFY_ss,DNF_ss][MEM_MAP,MEM_EL]);

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

val frontier_left_FINITE = Q.store_thm(
"frontier_left_FINITE",
`!m cf. common_part_frontier m cf ⇒ FINITE_BAG m ⇒ RES_FORALL (SND cf) (FINITE o FST)`,
ho_match_mp_tac common_part_frontier_ind >>
ntac 2 (srw_tac [SATISFY_ss][RES_FORALL_THM]) >>
`{x | Var x <: m} = IMAGE (term_case I ARB) (SET_OF_BAG (BAG_FILTER (\t. ?v. t = Var v) m))` by (
  srw_tac [DNF_ss][EXTENSION,EQ_IMP_THM] ) >>
srw_tac [][]);

val frontier_left_nonempty = Q.store_thm(
"frontier_left_nonempty",
`!m cf. common_part_frontier m cf ⇒ RES_FORALL (SND cf) ($<> {} o FST)`,
ho_match_mp_tac common_part_frontier_ind >>
ntac 2 (srw_tac [SATISFY_ss][RES_FORALL_THM,NOT_EQUAL_SETS]));

val frontier_right_FINITE_BAG = Q.store_thm(
"frontier_right_FINITE_BAG",
`!m cf. common_part_frontier m cf ⇒ FINITE_BAG m ⇒ RES_FORALL (SND cf) (FINITE_BAG o SND)`,
ho_match_mp_tac common_part_frontier_ind >>
ntac 2 (srw_tac [SATISFY_ss][RES_FORALL_THM]));

val frontier_right_not_var = Q.store_thm(
"frontier_right_not_var",
`!m cf. common_part_frontier m cf ⇒ ∀t meq. meq ∈ SND cf ∧ t <: SND meq ⇒ (∀x. t ≠ Var x)`,
ho_match_mp_tac common_part_frontier_ind >>
ntac 2 (srw_tac [SATISFY_ss][]));

val wfm_frontier = Q.store_thm( (* Don't know why mutual induction didn't work when I tried *)
"wfm_frontier",
`common_part_frontier m (c,f) ∧ wfm (s,m) ⇒ RES_FORALL f wfm`,
srw_tac [][RES_FORALL_THM,FORALL_PROD,wfm_def,BAG_EVERY] >>
imp_res_tac frontier_left_FINITE >>
imp_res_tac frontier_left_nonempty >>
imp_res_tac frontier_right_FINITE_BAG >>
fsrw_tac [][RES_FORALL_THM,FORALL_PROD] >>
metis_tac [frontier_right_not_var,SND]);

val _ = export_theory ()
