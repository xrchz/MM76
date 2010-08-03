open HolKernel boolLib bossLib prim_recTheory relationTheory listTheory lcsymtacs

val _ = new_theory "term"

val _ = Hol_datatype`term =
   Var of 'a
 | App of 'b => term list`;
val term_size_def = definition "term_size_def";
val term_induction = theorem "term_induction";

val term_ind = Q.store_thm(
"term_ind",
`∀P. (∀v. P (Var v)) ∧
     (∀f ts. EVERY P ts ⇒ P (App f ts))
     ⇒ ∀t. P t`,
gen_tac >>
Q.SPECL_THEN [`P`,`EVERY P`] mp_tac term_induction >>
srw_tac [][]);

val term_ax' = store_thm(
  "term_ax'",
  ``∀vf af. ∃h:(α,β)term -> γ.
      (∀v. h (Var v) = vf v) ∧
      (∀f ts. h (App f ts) = af f ts (MAP h ts))``,
  rpt gen_tac >>
  ASSUME_TAC (INST_TYPE [delta |-> ``:γ list``] (theorem "term_Axiom")) >>
  POP_ASSUM (Q.SPECL_THEN [`vf`, `af`, `[]`, `λt ts g glist. g::glist`]
                           MP_TAC) >> strip_tac >>
  qexists_tac `fn0` >> srw_tac [][] >>
  qsuff_tac `∀ts. fn1 ts = MAP fn0 ts` >- srw_tac [][] >>
  Induct >> srw_tac [][])

val vars_def = new_recursive_definition {
  def = ``(vars (Var x) = {x}) ∧
          (vars (App f ts) = BIGUNION (set (MAP vars ts)))``,
  name = "vars_def",
  rec_axiom = term_ax'
};
val _ = export_rewrites ["vars_def"];

val subterms_smaller = Q.store_thm(
"subterms_smaller",
`∀ts t. MEM t ts ⇒ measure (term_size f1 f2) t (App f ts)`,
Induct >> srw_tac [][] >>
full_simp_tac (srw_ss()++ARITH_ss)
  [prim_recTheory.measure_thm,term_size_def] >>
res_tac >> DECIDE_TAC);

val FINITE_vars = Q.store_thm(
"FINITE_vars",
`FINITE (vars t)`,
Q.ID_SPEC_TAC `t` >>
ho_match_mp_tac term_ind >>
srw_tac [][EVERY_MEM,MEM_MAP] >>
srw_tac [][]);
val _ = export_rewrites ["FINITE_vars"];

val fsym_count_def = new_recursive_definition {
  name = "fsym_count_def",
  def = ``(fsym_count (Var x) = 0) ∧
          (fsym_count (App f ts) = 1 + (SUM (MAP fsym_count ts)))``,
  rec_axiom = term_ax'}
val _ = export_rewrites ["fsym_count_def"];

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

val RTC_psubterm_thm = store_thm(
  "RTC_psubterm_thm",
  ``(psubterm^* x (Var v) ⇔ (x = Var v))  ∧
    (psubterm^* x (App f ts) ⇔
       (x = App f ts) ∨ ∃t. MEM t ts ∧ psubterm^* x t)``,
  conj_tac >> srw_tac [][Once RTC_CASES2, psubterm_cases, SimpLHS] >>
  metis_tac []);
val _ = export_rewrites ["RTC_psubterm_thm"]

val vars_RTC_psubterm = Q.store_thm(
"vars_RTC_psubterm",
`v ∈ vars t ⇔ psubterm^* (Var v) t`,
Q.ID_SPEC_TAC `t` >>
ho_match_mp_tac term_ind >>
conj_tac >- srw_tac [][] >>
map_every qx_gen_tac [`f`, `ts`] >>
simp_tac (srw_ss() ++ boolSimps.DNF_ss) [MEM_MAP,EVERY_MEM] >>
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
