open HolKernel boolLib Parse bossLib pairTheory state_optionTheory lcsymtacs

val _ = new_theory "state_option_cong"

val STATE_OPTION_BIND_cong = Q.store_thm(
"STATE_OPTION_BIND_cong",
`(s = s') ∧
 (∀s''. (s'' = s') ⇒ (m s'' = m' s'')) ∧
 (∀v s''. (m' s' = SOME (v,s'')) ⇒ (f v s'' = f' v s''))
 ⇒ (STATE_OPTION_BIND m f s = STATE_OPTION_BIND m' f' s')`,
Cases_on `m' s'` >> srw_tac [][STATE_OPTION_BIND_def,UNCURRY]);
val _ = DefnBase.export_cong "STATE_OPTION_BIND_cong";

val STATE_OPTION_IGNORE_BIND_cong = Q.store_thm(
"STATE_OPTION_IGNORE_BIND_cong",
`(s = s') ∧
 (∀s''. (s'' = s') ⇒ (m1 s'' = m1' s'')) ∧
 (∀s''. (OPTION_MAP SND (m1' s') = SOME s'') ⇒ (m2 s'' = m2' s''))
⇒ (STATE_OPTION_IGNORE_BIND m1 m2 s = STATE_OPTION_IGNORE_BIND m1' m2' s')`,
Cases_on `m1' s'` >> srw_tac [][STATE_OPTION_IGNORE_BIND_def]);
val _ = DefnBase.export_cong "STATE_OPTION_IGNORE_BIND_cong";

val _ = export_theory ()
