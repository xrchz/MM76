open HolKernel boolLib bossLib Parse SatisfySimps termTheory bagTheory substitutionTheory equationTheory pred_setTheory relationTheory listTheory finite_mapTheory algorithm_aTheory lcsymtacs

val _ = new_theory "multiequation"

val _ = type_abbrev("multiequation", ``:'a set # ('a,'b) term bag``);

val wfm_def = Define`
  wfm ((s,m):('a,'b) multiequation) = FINITE s ∧ s ≠ {} ∧ FINITE_BAG m ∧ BAG_EVERY (λt. ∀x. t ≠ Var x) m`;

val terms_of_def = Define`
  terms_of (s,m) = IMAGE Var s ∪ SET_OF_BAG m`;

val meq_unifier_def = Define`
  meq_unifier meq = {s | ∀t1 t2. t1 ∈ terms_of meq ∧ t2 ∈ terms_of meq ⇒ (SAPPLY s t1 = SAPPLY s t2)}`;

val eqs_correspond_to_meq_def = Define`
  eqs_correspond_to_meq meq eqs =
    (∀t1 t2. (t1,t2) ∈ eqs ⇒ t1 ∈ terms_of meq ∧ t2 ∈ terms_of meq) ∧
    (∀t1 t2. t1 ∈ terms_of meq ∧ t2 ∈ terms_of meq ⇒
             (λt1 t2. (t1,t2) ∈ eqs ∨ (t2,t1) ∈ eqs)^* t1 t2)`;

val eqs_corresponding_to_meq_exists = Q.store_thm(
"eqs_corresponding_to_meq_exists",
`∃eqs. eqs_correspond_to_meq meq eqs`,
srw_tac [][eqs_correspond_to_meq_def] >>
qexists_tac `{(t1,t2) | t1 ∈ terms_of meq ∧ t2 ∈ terms_of meq}` >>
srw_tac [][]);

val eqs_correspond_to_meq_extend = Q.store_thm(
"eqs_correspond_to_meq_extend",
`eqs_correspond_to_meq meq eqs ∧ extra ⊆ { (t1,t2) | t1 ∈ terms_of meq ∧ t2 ∈ terms_of meq } ⇒
 eqs_correspond_to_meq meq (eqs ∪ extra)`,
reverse (srw_tac [][pairTheory.FORALL_PROD,eqs_correspond_to_meq_def,SUBSET_DEF]) >- (
  qmatch_abbrev_tac `Q^* t1 t2` >>
  qmatch_assum_abbrev_tac `!t1 t2. t1 ∈ terms_of meq ∧ t2 ∈ terms_of meq ⇒ R^* t1 t2` >>
  qsuff_tac `Q^* = R^*` >- srw_tac [][] >>
  simp_tac bool_ss [FUN_EQ_THM,EQ_IMP_THM,FORALL_AND_THM] >>
  conj_tac >> ho_match_mp_tac RTC_INDUCT >>
  srw_tac [][Abbr`Q`,Abbr`R`] >>
  qmatch_abbrev_tac `R^* x y` >>
  metis_tac [RTC_RULES,transitive_RTC,transitive_def] ) >>
metis_tac []);

val meq_unifier_corresponds_set_unifier = Q.store_thm(
"meq_unifier_corresponds_set_unifier",
`eqs_correspond_to_meq meq eqs ⇒ (set_unifier eqs = meq_unifier meq)`,
srw_tac [][set_unifier_def,meq_unifier_def,EXTENSION,EQ_IMP_THM,eqs_correspond_to_meq_def] >- (
  Q.PAT_ASSUM `!t1 t2. P t1 t2 ⇒ R^* t1 t2` (Q.SPECL_THEN [`t1`,`t2`] mp_tac) >> srw_tac [][] >>
  Q.PAT_ASSUM `R^* t1 t2` mp_tac >>
  map_every Q.ID_SPEC_TAC [`t2`,`t1`] >>
  ho_match_mp_tac RTC_INDUCT >>
  metis_tac [] ) >>
metis_tac []);

(* same as above for sets of multiequations? *)

val (common_part_frontier_rules, common_part_frontier_ind, common_part_frontier_cases) = Hol_reln`
  (Var v <: m ⇒ common_part_frontier m (Var v, {({x | Var x <: m}, BAG_FILTER (λt. ∀x. t ≠ Var x) m)})) ∧
  (BAG_EVERY (λt. ∃ts. (t = App f ts) ∧ (LENGTH ts = n)) m ∧
   (∀i. i < n ⇒ common_part_frontier (BAG_IMAGE (term_case ARB (λf ts. EL i ts)) m) (common_part i, frontier i)) ⇒
   common_part_frontier m (App f (GENLIST common_part n), BIGUNION {frontier i | i < n}))`;

val unifier_implies_common_part = Q.store_thm(
"unifier_implies_common_part",
`FINITE_BAG m ∧ (∀t1 t2. t1 <: m ∧ t2 <: m ⇒ (SAPPLY s t1 = SAPPLY s t2)) ⇒ ∃cf. common_part_frontier m cf`,
qidspec_tac `m` >>
qho_match_abbrev_tac `∀m. P m ⇒ Q m` >>
qsuff_tac `∀t m. t <: m ⇒ P m ⇒ Q m` >- (
  srw_tac [][Abbr`P`,Abbr`Q`] >>
  Cases_on `?t. t <: m` >> srw_tac [][] >>
  metis_tac [common_part_frontier_rules,bagTheory.MEMBER_NOT_EMPTY,BAG_EVERY_THM,prim_recTheory.NOT_LESS_0] ) >>
ho_match_mp_tac term_ind >>
srw_tac [][Abbr`P`,Abbr`Q`] >-
  metis_tac [common_part_frontier_rules] >>
fsrw_tac [boolSimps.DNF_ss][EVERY_MEM,MEM_EL] >>
Cases_on `?v. Var v <: m` >- metis_tac [common_part_frontier_rules] >>
`?common_part frontier.
  !i. i < LENGTH ts ⇒ common_part_frontier
                          (BAG_IMAGE (term_case ARB (\f ts. EL i ts)) m)
                          (common_part i, frontier i)` by (
  srw_tac [][GSYM SKOLEM_THM,RIGHT_EXISTS_IMP_THM] >>
  fsrw_tac [][pairTheory.EXISTS_PROD,AND_IMP_INTRO] >>
  first_x_assum match_mp_tac >>
  qexists_tac `i` >> srw_tac [][] >- (
    qexists_tac `App f ts` >> srw_tac [][] ) >>
  map_every Cases_on [`y`,`y'`] >> TRY (res_tac >> fsrw_tac [][] >> NO_TAC) >>
  srw_tac [][] >>
  qmatch_rename_tac `SAPPLY s (EL i l1) = SAPPLY s (EL i l2)` [] >>
  qmatch_assum_rename_tac `App f1 l1 <: m` [] >>
  qmatch_assum_rename_tac `App f2 l2 <: m` [] >>
  first_assum (qspecl_then [`App f1 l1`,`App f2 l2`] mp_tac) >>
  first_x_assum (qspecl_then [`App f1 l1`,`App f ts`] mp_tac) >>
  srw_tac [][] >>
  fsrw_tac [][LIST_EQ_REWRITE] >>
  ntac 2 (first_x_assum (qspec_then `i` mp_tac)) >>
  srw_tac [][rich_listTheory.EL_MAP] ) >>
`BAG_EVERY (λt. ∃xs. (t = App f xs) ∧ (LENGTH xs = LENGTH ts)) m` by (
  srw_tac [][BAG_EVERY] >>
  Cases_on `t` >> res_tac >> fsrw_tac [][] >>
  metis_tac [LENGTH_MAP] ) >>
metis_tac [common_part_frontier_rules]);

val (meq_red_rules, meq_red_ind, meq_red_cases) = Hol_reln`
  (s,m) ∈ meq ∧ m ≠ {||} ∧ common_part_frontier m (c,f) ⇒
  meq_red meqs ((meqs DELETE (s,m)) ∪ ((s,{|c|}) INSERT f))`;

val no_common_part = Q.store_thm( (* Part of Theorem 3.1 *)
"no_common_part",
`FINITE_BAG m ∧ (∀cf. ¬common_part_frontier m cf) ⇒ (meq_unifier (s,m) = {})`,
srw_tac [][meq_unifier_def,EXTENSION,BAG_EVERY,terms_of_def] >>
metis_tac [unifier_implies_common_part,common_part_frontier_rules] );

val frontier_vars_occur = Q.store_thm(
"frontier_vars_occur",
`∀m cf. common_part_frontier m cf ⇒ FINITE_BAG m ⇒ ∀meq. meq ∈ SND cf ∧ x ∈ FST meq ⇒ ∃t. t <: m ∧ x ∈ vars t`,
ho_match_mp_tac common_part_frontier_ind >>
srw_tac [][] >- (
  qexists_tac `Var x` >> srw_tac [][] ) >>
fsrw_tac [boolSimps.DNF_ss][] >>
first_x_assum (qspecl_then [`i`,`meq`] mp_tac) >>
srw_tac [][] >>
qexists_tac `y` >> srw_tac [][] >>
fsrw_tac [][BAG_EVERY] >>
first_x_assum (qspec_then `y` mp_tac) >>
srw_tac [][] >> srw_tac [][MEM_MAP] >>
fsrw_tac [][MEM_EL] >> metis_tac []);

val meq_occurs_not_unify = Q.store_thm( (* Part of Theorem 3.1 *)
"meq_occurs_not_unify",
`wfm (s,m) ∧ x ∈ s ∧ common_part_frontier m (c,f) ∧ meq ∈ f ∧ x ∈ (FST meq) ⇒ (meq_unifier (s,m) = {})`,
srw_tac [][wfm_def,BAG_EVERY] >>
(frontier_vars_occur |> MP_CANON |> Q.SPECL [`m`,`(c,f)`,`meq`] |> mp_tac) >>
srw_tac [][] >>
qsuff_tac `?eqs. eqs_correspond_to_meq (s,m) eqs ∧ (set_unifier eqs = {})` >-
  metis_tac [meq_unifier_corresponds_set_unifier] >>
(eqs_corresponding_to_meq_exists |> Q.GEN `meq` |> Q.SPEC `(s,m)` |> STRIP_ASSUME_TAC) >>
qexists_tac ` eqs ∪ {(Var x,t)}` >>
reverse conj_tac >- (
  match_mp_tac (GEN_ALL no_cycles) >>
  srw_tac [][] >>
  metis_tac [] ) >>
match_mp_tac eqs_correspond_to_meq_extend >>
srw_tac [][SUBSET_DEF,terms_of_def] );

val _ = export_theory ()
