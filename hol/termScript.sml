open HolKernel boolLib bossLib prim_recTheory relationTheory listTheory lcsymtacs

val _ = new_theory "term"

val _ = Hol_datatype`term =
   Var of 'a
 | App of 'b => term list`;
val term_size_def = definition "term_size_def";
val term_induction = theorem "term_induction";

val subterms_smaller = Q.store_thm(
"subterms_smaller",
`∀ts t. MEM t ts ⇒ measure (term_size f1 f2) t (App f ts)`,
Induct >> srw_tac [][] >>
full_simp_tac (srw_ss()++ARITH_ss)
  [prim_recTheory.measure_thm,term_size_def] >>
res_tac >> DECIDE_TAC);

(*val vars_def = Define*)
val vars_def = TotalDefn.tDefine "vars"`
  (vars (Var x) = {x}) ∧
  (vars (App f ts) = BIGUNION (set (MAP vars ts)))`
(metis_tac [subterms_smaller,prim_recTheory.WF_measure]);
val _ = export_rewrites ["vars_def"];

val term_ind = Q.store_thm(
"term_ind",
`∀P. (∀v. P (Var v)) ∧
     (∀f ts. EVERY P ts ⇒ P (App f ts))
     ⇒ ∀t. P t`,
gen_tac >>
Q.SPECL_THEN [`P`,`EVERY P`] mp_tac term_induction >>
srw_tac [][]);

val (psubterm_rules,psubterm_ind,psubterm_cases) = Hol_reln`
  (MEM t ts ⇒ psubterm t (App f ts))`;

val vars_cases = Q.store_thm(
"vars_cases",
`v ∈ vars t ⇔
 (t = Var v) ∨
 ∃f u ts. (t = App f ts) ∧ MEM u ts ∧ v ∈ vars u`,
Q.ID_SPEC_TAC `t` >>
ho_match_mp_tac term_ind >>
srw_tac [][EQ_IMP_THM] >- (
  full_simp_tac (srw_ss()) [MEM_MAP] >>
  srw_tac [][] >>
  Q.MATCH_ASSUM_RENAME_TAC `MEM u ts` [] >>
  qexists_tac `u` >>
  srw_tac [][] ) >>
srw_tac [][MEM_MAP] >>
qexists_tac `vars u` >> srw_tac [][] >>
qexists_tac `u` >> srw_tac [][]);

val vars_RTC_psubterm = Q.store_thm(
"vars_RTC_psubterm",
`v ∈ vars t ⇔ psubterm^* (Var v) t`,
Q.ID_SPEC_TAC `t` >>
ho_match_mp_tac term_ind >>
srw_tac [][EQ_IMP_THM] >- (
  full_simp_tac (srw_ss()) [Once RTC_CASES2,psubterm_cases] )
>- (
  full_simp_tac (srw_ss()) [MEM_MAP,EVERY_MEM] >>
  srw_tac [][] >>
  `psubterm a (App f ts)` by (
    srw_tac [][psubterm_cases] ) >>
  metis_tac [RTC_RULES_RIGHT1] ) >>
full_simp_tac (srw_ss()) [MEM_MAP,EVERY_MEM] >>
full_simp_tac (srw_ss()) [Once RTC_CASES2] >>
full_simp_tac (srw_ss()) [psubterm_cases] >>
res_tac >>
full_simp_tac (srw_ss()) [] >> srw_tac [][] >>
metis_tac []);

val WF_psubterm = Q.store_thm(
"WF_psubterm",
`WF psubterm`,
SIMP_TAC bool_ss [WF_EQ_WFP] >>
ho_match_mp_tac term_ind >>
srw_tac [][] >>
match_mp_tac WFP_RULES >>
srw_tac [][psubterm_cases] >>
full_simp_tac (srw_ss()) [EVERY_MEM]);

val _ = export_theory ();
