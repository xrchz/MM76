open HolKernel boolLib bossLib Parse listTheory pred_setTheory relationTheory prim_recTheory arithmeticTheory bagTheory lcsymtacs

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

val varb_def = new_recursive_definition {
  def = ``(varb (Var x) = {|x|}) ∧
          (varb (App f ts) = BIG_BAG_UNION (set (MAP varb ts)))``,
  name = "varb_def",
  rec_axiom = term_ax'
};
val _ = export_rewrites ["varb_def"];

val subterms_smaller = Q.store_thm(
"subterms_smaller",
`∀ts t. MEM t ts ⇒ measure (term_size f1 f2) t (App f ts)`,
Induct >> srw_tac [][] >>
fsrw_tac [ARITH_ss] [measure_thm,term_size_def] >>
res_tac >> DECIDE_TAC);

val FINITE_vars = Q.store_thm(
"FINITE_vars",
`FINITE (vars t)`,
Q.ID_SPEC_TAC `t` >>
ho_match_mp_tac term_ind >>
srw_tac [][EVERY_MEM,MEM_MAP] >>
srw_tac [][]);
val _ = export_rewrites ["FINITE_vars"];

val FINITE_BAG_varb = Q.store_thm(
"FINITE_BAG_varb",
`FINITE_BAG (varb t)`,
qid_spec_tac `t` >>
ho_match_mp_tac term_ind >>
srw_tac [][EVERY_MEM,MEM_MAP,LIST_TO_SET_MAP] >>
match_mp_tac FINITE_BIG_BAG_UNION >>
srw_tac [][] >> srw_tac [][]);
val _ = export_rewrites ["FINITE_BAG_varb"];

val IN_varb_vars = Q.store_thm(
"IN_varb_vars",
`BAG_IN e (varb t) ⇔ e ∈ vars t`,
qid_spec_tac `t` >>
ho_match_mp_tac term_ind >>
srw_tac [][EVERY_MEM,MEM_MAP] >>
PROVE_TAC []);
val _ = export_rewrites ["IN_varb_vars"];

val fsym_count_def = new_recursive_definition {
  name = "fsym_count_def",
  def = ``(fsym_count (Var x) = 0) ∧
          (fsym_count (App f ts) = 1 + (SUM (MAP fsym_count ts)))``,
  rec_axiom = term_ax'}
val _ = export_rewrites ["fsym_count_def"];

val (psubterm1_rules,psubterm1_ind,psubterm1_cases) = Hol_reln`
  (MEM t ts ⇒ psubterm1 t (App f ts))`;

val _ = overload_on("psubterm",``TC psubterm1``);
val _ = overload_on("subterm",``RTC psubterm1``);

val psubterm1_term_size = Q.store_thm(
"psubterm1_term_size",
`psubterm1 t1 t2 ⇒ measure (term_size f1 f2) t1 t2`,
srw_tac [][psubterm1_cases] >>
match_mp_tac subterms_smaller >>
srw_tac [][]);

val psubterm_term_size = save_thm(
"psubterm_term_size",
  TC_lifts_transitive_relations |>
  let val t = `:('a,'b) term` in Q.INST_TYPE [`:'a`|->t,`:'b`|->t] end
  |> Q.GEN `R` |> Q.SPEC `psubterm1`
  |> Q.GEN `Q` |> Q.SPEC `measure (term_size f1 f2)`
  |> Q.GEN `f` |> Q.SPEC `I`
  |> SIMP_RULE std_ss [psubterm1_term_size,transitive_measure]
  |> Q.SPECL [`t1`,`t2`]);

val subterm_term_size = Q.store_thm(
"subterm_term_size",
`subterm t1 t2 ⇒ (term_size f1 f2 t1) ≤ (term_size f1 f2 t2)`,
metis_tac [RTC_CASES_TC,psubterm_term_size,measure_thm,LESS_OR_EQ]);

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

val subterm_thm = store_thm(
  "subterm_thm",
  ``(subterm x (Var v) ⇔ (x = Var v))  ∧
    (subterm x (App f ts) ⇔
       (x = App f ts) ∨ ∃t. MEM t ts ∧ subterm x t)``,
  conj_tac >> srw_tac [][Once RTC_CASES2, psubterm1_cases, SimpLHS] >>
  metis_tac []);
val _ = export_rewrites ["subterm_thm"]

val vars_subterm = Q.store_thm(
"vars_subterm",
`v ∈ vars t ⇔ subterm (Var v) t`,
Q.ID_SPEC_TAC `t` >>
ho_match_mp_tac term_ind >>
conj_tac >- srw_tac [][] >>
map_every qx_gen_tac [`f`, `ts`] >>
simp_tac (srw_ss() ++ boolSimps.DNF_ss) [MEM_MAP,EVERY_MEM] >>
metis_tac []);

val subterm_vars_SUBSET = Q.store_thm(
"subterm_vars_SUBSET",
`subterm t1 t2 ⇒ vars t1 ⊆ vars t2`,
map_every qid_spec_tac [`t1`,`t2`] >>
ho_match_mp_tac term_ind >>
ntac 2 (srw_tac [][LIST_TO_SET_MAP]) >>
fsrw_tac [][EVERY_MEM,SUBSET_DEF] >>
PROVE_TAC [IN_LIST_TO_SET]);

val WF_psubterm1 = Q.store_thm(
"WF_psubterm1",
`WF psubterm1`,
SIMP_TAC bool_ss [WF_EQ_WFP] >>
ho_match_mp_tac term_ind >>
srw_tac [][] >>
match_mp_tac WFP_RULES >>
srw_tac [][psubterm1_cases] >>
full_simp_tac (srw_ss()) [EVERY_MEM]);

val psubterm_irrefl = Q.store_thm(
"psubterm_irrefl",
`¬ psubterm t t`,
metis_tac [WF_TC,WF_psubterm1,WF_NOT_REFL]);
val _ = export_rewrites ["psubterm_irrefl"];

val (subterm_at_rules,subterm_at_ind,subterm_at_cases) = Hol_reln`
  (subterm_at t [] t) ∧
  (n < LENGTH ts ∧
   subterm_at t ns (EL n ts)
   ⇒ subterm_at t (n::ns) (App f ts))`;

val subterm_eq_subterm_at = Q.store_thm(
"subterm_eq_subterm_at",
`subterm t1 t2 ⇔ ∃ls. subterm_at t1 ls t2`,
EQ_TAC >- (
  map_every qid_spec_tac [`t2`,`t1`] >>
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
  srw_tac [][psubterm1_cases] >-
    srw_tac [SatisfySimps.SATISFY_ss][subterm_at_rules] >>
  fsrw_tac [][MEM_EL] >>
  qexists_tac `n::ls` >>
  srw_tac [][subterm_at_rules] ) >>
simp_tac (bool_ss++boolSimps.DNF_ss) [] >>
qid_spec_tac `t2` >>
simp_tac bool_ss [Once SWAP_FORALL_THM] >>
ho_match_mp_tac subterm_at_ind >>
srw_tac [][MEM_EL] >>
metis_tac []);

val subterm_at_nil = Q.store_thm(
"subterm_at_nil",
`(subterm_at t1 [] t2 ⇔ (t1 = t2)) ∧
 (subterm_at t ls t ⇔ (ls = []))`,
srw_tac [][EQ_IMP_THM,subterm_at_rules] >>
fsrw_tac [][Once subterm_at_cases] >>
imp_res_tac subterm_eq_subterm_at >>
imp_res_tac subterm_term_size >>
srw_tac [][] >> fsrw_tac [][] >>
Q.ISPECL_THEN [`ts`,`EL n ts`] mp_tac subterms_smaller >>
srw_tac [][MEM_EL,measure_thm,NOT_LESS] >>
qexists_tac `n` >> srw_tac [][]);
val _ = export_rewrites ["subterm_at_nil"];

val psubterm_eq_subterm_at = Q.store_thm(
"psubterm_eq_subterm_at",
`psubterm t1 t2 ⇔ ∃n ns. subterm_at t1 (n::ns) t2`,
ASSUME_TAC subterm_eq_subterm_at >>
fsrw_tac [][RTC_CASES_TC] >>
Cases_on `t1 = t2` >> fsrw_tac [][] >>
metis_tac [NOT_NIL_CONS,subterm_at_nil,list_CASES]);

val subterm_at_thm = Q.store_thm(
"subterm_at_thm",
`(subterm_at t ns (Var x) ⇔ (t = Var x) ∧ (ns = [])) ∧
 (subterm_at t (n::ns) (App f ts) ⇔ n < LENGTH ts ∧  subterm_at t ns (EL n ts))`,
reverse (srw_tac [][Once subterm_at_cases,EQ_IMP_THM]) >-
  metis_tac [subterm_at_rules] >>
fsrw_tac [][Once subterm_at_cases]);
val _ = export_rewrites["subterm_at_thm"];

val _ = export_theory ();
