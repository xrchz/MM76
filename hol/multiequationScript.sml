open HolKernel boolLib boolSimps bossLib Parse SatisfySimps termTheory bagTheory substitutionTheory equationTheory pred_setTheory relationTheory listTheory finite_mapTheory algorithm_aTheory lcsymtacs

val _ = new_theory "multiequation"

val BIG_BAG_UNION_def = Define`
 BIG_BAG_UNION sob = λx. SIGMA (λb. b x) sob`;

val BIG_BAG_UNION_EMPTY = Q.store_thm(
"BIG_BAG_UNION_EMPTY",
`BIG_BAG_UNION {} = {||}`,
SRW_TAC [][BIG_BAG_UNION_def,SUM_IMAGE_THM,EMPTY_BAG,FUN_EQ_THM]);
val _ = export_rewrites ["BIG_BAG_UNION_EMPTY"];

val BIG_BAG_UNION_INSERT = Q.store_thm(
"BIG_BAG_UNION_INSERT",
`FINITE sob ⇒ (BIG_BAG_UNION (b INSERT sob) = b + BIG_BAG_UNION (sob
DELETE b))`,
SRW_TAC [][BIG_BAG_UNION_def,SUM_IMAGE_THM,BAG_UNION,FUN_EQ_THM]);

val FINITE_BIG_BAG_UNION = Q.store_thm(
"FINITE_BIG_BAG_UNION",
`∀sob. FINITE sob ∧ (∀b. b ∈ sob ⇒ FINITE_BAG b) ⇒ FINITE_BAG
(BIG_BAG_UNION sob)`,
SIMP_TAC bool_ss [GSYM AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
    SRW_TAC [][BIG_BAG_UNION_INSERT] THEN
      FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT]);

val BAG_IN_BIG_BAG_UNION = Q.store_thm(
"BAG_IN_BIG_BAG_UNION",
`FINITE P ⇒ (e <: BIG_BAG_UNION P ⇔ ∃b. e <: b ∧ b ∈ P)`,
srw_tac [][BIG_BAG_UNION_def,BAG_IN,BAG_INN,EQ_IMP_THM] >- (
  spose_not_then strip_assume_tac >>
  (SUM_IMAGE_upper_bound
   |> Q.GEN `f`
   |> Q.ISPEC_THEN `\b:'a bag. b e` (Q.ISPEC_THEN `P` mp_tac)) >>
  srw_tac [][] >>
  qexists_tac `0` >>
  srw_tac [ARITH_ss][] >>
  first_x_assum (qspec_then `x` mp_tac) >>
  srw_tac [ARITH_ss][] ) >>
fsrw_tac [][arithmeticTheory.GREATER_EQ] >>
`1 ≤ SIGMA (\b. b e) {b}` by srw_tac [][SUM_IMAGE_THM] >>
match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
qexists_tac `SIGMA (\b.b e) {b}` >>
srw_tac [][] >>
match_mp_tac SUM_IMAGE_SUBSET_LE >>
srw_tac [][]);
val _ = export_rewrites ["BAG_IN_BIG_BAG_UNION"];

val pairwise_def = Define`
  pairwise P s = ∀e1 e2. e1 ∈ s ∧ e2 ∈ s ⇒ P e1 e2`;

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

val meqs_unifier_def = Define`
  meqs_unifier meqs = BIGINTER (IMAGE meq_unifier meqs)`;

val (common_part_frontier_rules, common_part_frontier_ind, common_part_frontier_cases) = Hol_reln`
  (Var v <: m ⇒ common_part_frontier m (Var v, {({x | Var x <: m}, BAG_FILTER (λt. ∀x. t ≠ Var x) m)})) ∧
  (BAG_EVERY (λt. ∃ts. (t = App f ts) ∧ (LENGTH ts = n)) m ∧ m ≠ {||} ∧
   (∀i. i < n ⇒ common_part_frontier (BAG_IMAGE (term_case ARB (λf ts. EL i ts)) m) (common_part i, frontier i)) ⇒
   common_part_frontier m (App f (GENLIST common_part n), BIGUNION {frontier i | i < n}))`;

val unifier_implies_common_part = Q.store_thm(
"unifier_implies_common_part",
`FINITE_BAG m ∧ m ≠ {||} ∧ (∀t1 t2. t1 <: m ∧ t2 <: m ⇒ (SAPPLY s t1 = SAPPLY s t2)) ⇒ ∃cf. common_part_frontier m cf`,
qid_spec_tac `m` >>
qho_match_abbrev_tac `∀m. P m ⇒ Q m` >>
qsuff_tac `∀t m. t <: m ⇒ P m ⇒ Q m` >- (
  srw_tac [][Abbr`P`,Abbr`Q`] >>
  Cases_on `?t. t <: m` >> srw_tac [][] >>
  metis_tac [common_part_frontier_rules,bagTheory.MEMBER_NOT_EMPTY,BAG_EVERY_THM,prim_recTheory.NOT_LESS_0] ) >>
ho_match_mp_tac term_ind >>
srw_tac [][Abbr`P`,Abbr`Q`] >-
  metis_tac [common_part_frontier_rules] >>
fsrw_tac [DNF_ss][EVERY_MEM,MEM_EL] >>
Cases_on `?v. Var v <: m` >- metis_tac [common_part_frontier_rules] >>
`?common_part frontier.
  !i. i < LENGTH ts ⇒ common_part_frontier
                          (BAG_IMAGE (term_case ARB (\f ts. EL i ts)) m)
                          (common_part i, frontier i)` by (
  srw_tac [][GSYM SKOLEM_THM,RIGHT_EXISTS_IMP_THM] >>
  fsrw_tac [][pairTheory.EXISTS_PROD,AND_IMP_INTRO] >>
  first_x_assum match_mp_tac >>
  qexists_tac `i` >> srw_tac [][] >- (
    qexists_tac `App f ts` >> srw_tac [][] )
  >- (
    fsrw_tac [SATISFY_ss][GSYM bagTheory.MEMBER_NOT_EMPTY] ) >>
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
  (s,m) ∈ meqs ∧ common_part_frontier m (c,f) ⇒
  meq_red meqs ((meqs DELETE (s,m)) ∪ ((s,{|c|}) INSERT f))`;

val no_common_part = Q.store_thm( (* Part of Theorem 3.1 *)
"no_common_part",
`FINITE_BAG m ∧ m ≠ {||} ∧ (∀cf. ¬common_part_frontier m cf) ⇒ (meq_unifier (s,m) = {})`,
srw_tac [][meq_unifier_def,EXTENSION,BAG_EVERY,terms_of_def] >>
metis_tac [unifier_implies_common_part,common_part_frontier_rules] );

val frontier_same_address = Q.store_thm(
"frontier_same_address",
`∀m cf. common_part_frontier m cf ⇒
        FINITE_BAG m ⇒
        ∀meq. meq ∈ (SND cf) ⇒
              ∃ns. ∀u. u ∈ terms_of meq ⇒
                       ∃t. t <: m ∧ subterm_at u ns t`,
ho_match_mp_tac common_part_frontier_ind >>
srw_tac [][] >- (
  qexists_tac `[]` >>
  srw_tac [][terms_of_def] >>
  first_assum ACCEPT_TAC ) >>
fsrw_tac [DNF_ss][BAG_EVERY] >>
first_x_assum (qspecl_then [`i`,`meq`] mp_tac) >> srw_tac [][] >>
qexists_tac `i::ns` >> srw_tac [][] >>
first_x_assum (qspec_then `u` mp_tac) >> srw_tac [][] >>
res_tac >> fsrw_tac [][] >>
metis_tac [subterm_at_rules]);

val frontier_vars_occur = Q.store_thm(
"frontier_vars_occur",
`∀m cf meq. common_part_frontier m cf ∧ FINITE_BAG m ∧ meq ∈ SND cf ∧ x ∈ FST meq ⇒ ∃t. t <: m ∧ x ∈ vars t`,
srw_tac [][] >>
imp_res_tac frontier_same_address >>
Cases_on `meq` >>
fsrw_tac [][terms_of_def] >>
metis_tac [subterm_eq_subterm_at,vars_def,IN_INSERT,NOT_IN_EMPTY,vars_subterm]);

val meq_occurs_not_unify = Q.store_thm( (* Part of Theorem 3.1 *)
"meq_occurs_not_unify",
`wfm (s,m) ∧ x ∈ s ∧ common_part_frontier m (c,f) ∧ meq ∈ f ∧ x ∈ (FST meq) ⇒ (meq_unifier (s,m) = {})`,
srw_tac [][wfm_def,BAG_EVERY] >>
(frontier_vars_occur |> Q.SPECL [`m`,`(c,f)`,`meq`] |> mp_tac) >>
srw_tac [][] >>
qsuff_tac `?eqs. eqs_correspond_to_meq (s,m) eqs ∧ (set_unifier eqs = {})` >-
  metis_tac [meq_unifier_corresponds_set_unifier] >>
(eqs_corresponding_to_meq_exists |> Q.GEN `meq` |> Q.SPEC `(s,m)` |> strip_assume_tac) >>
qexists_tac ` eqs ∪ {(Var x,t)}` >>
reverse conj_tac >- (
  match_mp_tac (GEN_ALL no_cycles) >>
  srw_tac [][] >>
  metis_tac [] ) >>
match_mp_tac eqs_correspond_to_meq_extend >>
srw_tac [][SUBSET_DEF,terms_of_def] );

val meq_unifier_also_common_part = Q.store_thm(
"meq_unifier_also_common_part",
`∀m cf. common_part_frontier m cf ⇒ FINITE_BAG m ⇒ ∀s. meq_unifier (s,m) = meq_unifier (s,BAG_INSERT (FST cf) m)`,
ho_match_mp_tac common_part_frontier_ind >>
conj_tac >- (
  srw_tac [][meq_unifier_def,EQ_IMP_THM,EXTENSION] >>
  fsrw_tac [][terms_of_def] ) >>
rpt gen_tac >>
ntac 2 strip_tac >>
qx_gen_tac `vs` >>
simp_tac (srw_ss()) [meq_unifier_def,EXTENSION] >>
qx_gen_tac `s` >>
fsrw_tac [DNF_ss][BAG_EVERY] >>
reverse (srw_tac [][EQ_IMP_THM]) >>
`∀v1 v2. v1 ∈ vs ∧ v2 ∈ vs ⇒ (SAPPLY s (Var v1) = SAPPLY s (Var v2))` by (
  rpt strip_tac >> fsrw_tac [][terms_of_def] ) >>
`∀t1 t2. t1 <: m ∧ t2 <: m ⇒ (SAPPLY s t1 = SAPPLY s t2)` by (
  rpt strip_tac >> fsrw_tac [][terms_of_def] ) >>
`∀v t. v ∈ vs ∧ t <: m ⇒ (SAPPLY s (Var v) = SAPPLY s t)` by (
  rpt strip_tac >> fsrw_tac [][terms_of_def] ) >-
  fsrw_tac [][terms_of_def] >>
`∀t. t <: m ⇒ (SAPPLY s t = SAPPLY s (App f (GENLIST common_part n)))` by (
  rpt strip_tac >>
  `?ts. (t = App f ts) ∧ (LENGTH ts = n)` by (res_tac >> srw_tac [][]) >>
  srw_tac [][LIST_EQ_REWRITE,rich_listTheory.EL_MAP] >>
  qmatch_assum_rename_tac `i < LENGTH ts` [] >>
  first_x_assum (qspecl_then [`i`,`{}`] mp_tac) >>
  asm_simp_tac (srw_ss()) [meq_unifier_def,EXTENSION,terms_of_def] >>
  disch_then (qspec_then `s` (mp_tac o fst o EQ_IMP_RULE)) >>
  srw_tac [DNF_ss][] >>
  first_x_assum (qspec_then `App f ts` mp_tac) >>
  simp_tac (srw_ss()) [] >>
  disch_then (match_mp_tac o MP_CANON) >>
  asm_simp_tac (srw_ss()) [] >>
  map_every qx_gen_tac [`u1`,`u2`] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`u1`,`u2`] mp_tac) >>
  `?us1. (u1 = App f us1) ∧ (LENGTH us1 = LENGTH ts)` by (res_tac >> srw_tac [][]) >>
  `?us2. (u2 = App f us2) ∧ (LENGTH us2 = LENGTH ts)` by (res_tac >> srw_tac [][]) >>
  srw_tac [][LIST_EQ_REWRITE,rich_listTheory.EL_MAP] ) >>
fsrw_tac [][terms_of_def] >>
metis_tac [bagTheory.MEMBER_NOT_EMPTY]);

val frontier_unifier_also_common_part = Q.store_thm(
"frontier_unifier_also_common_part",
`∀m cf. common_part_frontier m cf ⇒
        FINITE_BAG m ⇒
        ∀vs. s ∈ meq_unifier (vs,{|FST cf|}) ∧
            (∀meq. meq ∈ SND cf ⇒ s ∈ meq_unifier meq) ⇒
               s ∈ meq_unifier (vs,BAG_INSERT (FST cf) m)`,
ho_match_mp_tac common_part_frontier_ind >>
conj_tac >- (
  srw_tac [][meq_unifier_def,terms_of_def] >>
  metis_tac [] ) >>
srw_tac [][] >>
fsrw_tac [DNF_ss][BAG_EVERY] >>
srw_tac [][meq_unifier_def] >>
`!v1 v2. v1 ∈ vs ∧ v2 ∈ vs ⇒ (SAPPLY s (Var v1) = SAPPLY s (Var v2))` by (
  fsrw_tac [][terms_of_def,meq_unifier_def] ) >>
`!v. v ∈ vs ⇒ (SAPPLY s (Var v) = SAPPLY s (App f (GENLIST common_part n)))` by (
  fsrw_tac [][terms_of_def,meq_unifier_def] ) >>
qsuff_tac `!t. t <: m ⇒ (SAPPLY s t = SAPPLY s (App f (GENLIST common_part n)))` >- (
  strip_tac >>
  rpt (qpat_assum `tn ∈ terms_of X` mp_tac) >>
  srw_tac [][terms_of_def] >>
  TRY (first_x_assum (fn th => match_mp_tac th >> srw_tac [][] >> NO_TAC)) >>
  TRY (first_x_assum (fn th => (match_mp_tac o GSYM) th >> srw_tac [][] >> NO_TAC)) >>
  metis_tac [] ) >>
rpt strip_tac >>
res_tac >>
srw_tac [][rich_listTheory.MAP_GENLIST,LIST_EQ_REWRITE,rich_listTheory.EL_MAP] >>
qmatch_assum_rename_tac `i < LENGTH X` ["X"] >>
first_x_assum (qspecl_then [`i`,`{}`] mp_tac) >>
asm_simp_tac (srw_ss()++SATISFY_ss) [] >>
srw_tac [DNF_ss][meq_unifier_def,terms_of_def] >>
res_tac >> first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) []));

val meq_unifier_submeq = Q.store_thm(
"meq_unifier_submeq",
`vs1 ⊆ vs2 ∧ m1 ≤ m2 ⇒ meq_unifier (vs2,m2) ⊆ meq_unifier (vs1,m1)`,
srw_tac [][SUBSET_DEF,meq_unifier_def,SUB_BAG,BAG_INN] >>
first_x_assum match_mp_tac >>
fsrw_tac [][terms_of_def,BAG_IN,BAG_INN]);

val unify_common_part_and_frontier = Q.store_thm(
"unify_common_part_and_frontier",
`common_part_frontier m cf ∧ FINITE_BAG m ∧
 s ∈ meq_unifier (vs,{|FST cf|}) ∧
 (∀meq. meq ∈ (SND cf) ⇒ s ∈ meq_unifier meq) ⇒
   s ∈ meq_unifier (vs,m)`,
qsuff_tac
`∀m cf. common_part_frontier m cf ⇒ FINITE_BAG m ⇒
        ∀vs. s ∈ meq_unifier (vs,BAG_INSERT (FST cf) m) ∧
             (∀meq. meq ∈ (SND cf) ⇒ s ∈ meq_unifier meq) ⇒
                s ∈ meq_unifier (vs,m)` >-
  metis_tac [frontier_unifier_also_common_part] >>
ho_match_mp_tac common_part_frontier_ind >>
srw_tac [][] >- (
  fsrw_tac [][meq_unifier_def,terms_of_def] >>
  metis_tac [] ) >>
fsrw_tac [DNF_ss][BAG_EVERY] >>
`∀v1 v2. v1 ∈ vs ∧ v2 ∈ vs ⇒ (SAPPLY s (Var v1) = SAPPLY s (Var v2))` by (
  rpt strip_tac >> fsrw_tac [][meq_unifier_def,terms_of_def] ) >>
`∀v. v ∈ vs ⇒ (SAPPLY s (Var v) = SAPPLY s (App f (GENLIST common_part n)))` by (
  rpt strip_tac >> fsrw_tac [][meq_unifier_def,terms_of_def] ) >>
qsuff_tac `∀t. t <: m ⇒ (SAPPLY s t = SAPPLY s (App f (GENLIST common_part n)))` >- (
  srw_tac [][meq_unifier_def,terms_of_def] >> fsrw_tac [][] ) >>
qpat_assum `s ∈ meq_unifier (vs,X)` mp_tac >>
srw_tac [][meq_unifier_def,terms_of_def]);

val meq_red_sound = Q.store_thm( (* Half of Theorem 3.1 *)
"meq_red_sound",
`meq_red meqs1 meqs2 ∧ (∀meq. meq ∈ meqs1 ⇒ FINITE_BAG (SND meq)) ⇒ (meqs_unifier meqs1 = meqs_unifier meqs2)`,
srw_tac [][meq_red_cases,meqs_unifier_def] >>
REWRITE_TAC [EXTENSION] >>
qmatch_assum_rename_tac `(vs,m) ∈ meqs1` [] >>
qx_gen_tac `s` >>
EQ_TAC >> rpt strip_tac >- (
  fsrw_tac [][] >> srw_tac [][] >-
    metis_tac []
  >- (
    first_x_assum (qspec_then `(vs,m)` mp_tac) >> srw_tac [][] >>
    first_x_assum (qspec_then `meq_unifier (vs,m)` mp_tac) >>
    qsuff_tac `meq_unifier (vs,BAG_INSERT c m) ⊆ meq_unifier (vs,{|c|})` >- (
      srw_tac [][SUBSET_DEF] >>
      first_x_assum match_mp_tac >>
      imp_res_tac (GSYM meq_unifier_also_common_part) >>
      fsrw_tac [][] >>
      first_x_assum match_mp_tac >>
      metis_tac [] ) >>
    match_mp_tac meq_unifier_submeq >>
    srw_tac [][SUB_BAG,BAG_INN,BAG_INN_BAG_INSERT] >>
    srw_tac [ARITH_ss][] ) >>
  fsrw_tac [DNF_ss][] >>
  rpt (first_x_assum (qspec_then `(vs,m)` mp_tac)) >>
  srw_tac [][meq_unifier_def] >>
  qmatch_assum_rename_tac `meq ∈ f` [] >>
  (frontier_same_address |> MP_CANON |> qspecl_then [`m`,`(c,f)`,`meq`] mp_tac) >>
  srw_tac [][] >>
  fsrw_tac [][terms_of_def] >>
  metis_tac [unify_corresponding_subterms] ) >>
fsrw_tac [DNF_ss][] >>
srw_tac [][] >>
qmatch_assum_rename_tac `meq ∈ meqs1` [] >>
Cases_on `meq = (vs,m)` >> srw_tac [][] >>
match_mp_tac (GEN_ALL unify_common_part_and_frontier) >>
qexists_tac `(c,f)` >> srw_tac [][] >>
res_tac >> fsrw_tac [][]);

val meq_merge_all_def = Define`
  meq_merge_all meqs = (BIGUNION (IMAGE FST meqs), BIG_BAG_UNION (IMAGE SND meqs))`;

val meqs_share_vars_def = Define`
  meqs_share_vars meq1 meq2 = ¬ DISJOINT (FST meq1) (FST meq2)`;

val compactify_def = Define`
  compactify meqs = { meq_merge_all (meqs_share_vars^= meq) | meq ∈ meqs }`;

val compactified_vars_disjoint = Q.store_thm(
"compactified_vars_disjoint",
`pairwise (RC (inv_image DISJOINT FST)) (compactify meqs)`,
srw_tac [][pairwise_def,RC_DEF,inv_image_def] >>
Cases_on `e1 = e2` >> srw_tac [][] >>
fsrw_tac [DNF_ss][compactify_def] >>
srw_tac [][] >>
qmatch_assum_abbrev_tac `f (R^= tmp1) ≠ f (R^= tmp2)` >>
qmatch_assum_rename_tac `Abbrev (tmp1 = meq1)` [] >>
qmatch_assum_rename_tac `Abbrev (tmp2 = meq2)` [] >>
map_every Q.UNABBREV_TAC [`tmp1`,`tmp2`] >>
`equivalence R^=` by (MATCH_ACCEPT_TAC EQC_EQUIVALENCE) >>
`¬ R^= meq1 meq2` by metis_tac [ALT_equivalence] >>
qpat_assum `f X ≠ f Y` (K ALL_TAC) >>
fsrw_tac [DNF_ss][Abbr`f`,meq_merge_all_def] >>
simp_tac (srw_ss()) [IN_DEF,AND_IMP_INTRO] >>
map_every qx_gen_tac [`meq1'`,`meq2'`] >>
rpt strip_tac >>
spose_not_then strip_assume_tac >>
`R meq1' meq2'` by metis_tac [meqs_share_vars_def] >>
metis_tac [EQC_TRANS,EQC_SYM,EQC_R]);

val eqs_correspond_to_compactify_meqs

val compactify_sound = Q.store_thm(
"compactify_sound",
`meqs_unifier (compactify meqs) = meqs_unifier meqs`,
set_unifier
meq_unifier_corresponds_set_unifier
srw_tac [DNF_ss][meqs_unifier_def,EXTENSION,compactify_def]

val _ = export_theory ()
