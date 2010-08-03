open HolKernel boolLib bossLib Parse termTheory listTheory finite_mapTheory relationTheory lcsymtacs

val _ = new_theory "subst";

val _ = type_abbrev("subst", ``:'a |-> ('a,'b) term``);

(*val SAPPLY_def = Define*)
val SAPPLY_def = TotalDefn.tDefine "SAPPLY"`
  (SAPPLY s (Var v) = case FLOOKUP s v of SOME t -> t || NONE -> (Var v)) ∧
  (SAPPLY s (App f xs) = App f (MAP (SAPPLY s) xs))`
( WF_REL_TAC `measure (term_size ARB ARB o SND)` >>
  metis_tac [subterms_smaller,prim_recTheory.measure_thm,term_size_def] );
val _ = export_rewrites ["SAPPLY_def"];

val psubterm_mono_SAPPLY = Q.store_thm(
"psubterm_mono_SAPPLY",
`∀t u. psubterm t u ⇒ psubterm (SAPPLY s t) (SAPPLY s u)`,
gen_tac >> ho_match_mp_tac psubterm_ind >>
srw_tac [][psubterm_cases,MEM_MAP] >>
metis_tac []);

val TC_psubterm_mono_SAPPLY = save_thm(
"TC_psubterm_mono_SAPPLY",
TC_lifts_monotonicities |>
Q.GEN `f` |> Q.ISPEC `SAPPLY s` |>
Q.GEN `R` |> Q.ISPEC `psubterm` |>
C MATCH_MP psubterm_mono_SAPPLY);

val rangevars_def = Define`
  rangevars s = BIGUNION (IMAGE vars (FRANGE s))`;

val _ = export_theory ();
