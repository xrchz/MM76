open HolKernel boolLib bossLib Parse state_optionTheory
open pairTheory

val _ = new_theory "reduce"

val STATE_OPTION_BIND_cong = Q.store_thm(
"STATE_OPTION_BIND_cong",
`(s = s') ∧
 (∀s''. (s'' = s') ⇒ (m s'' = m' s'')) ∧
 (∀v s''. (m' s' = SOME (v,s'')) ⇒ (f v s'' = f' v s''))
 ⇒ (STATE_OPTION_BIND m f s = STATE_OPTION_BIND m' f' s')`,
Cases_on `m' s'` THEN SRW_TAC [][STATE_OPTION_BIND_def,UNCURRY]);
val _ = DefnBase.export_cong "STATE_OPTION_BIND_cong";

val STATE_OPTION_IGNORE_BIND_cong = Q.store_thm(
"STATE_OPTION_IGNORE_BIND_cong",
`(s = s') ∧
 (∀s''. (s'' = s') ⇒ (m1 s'' = m1' s'')) ∧
 (∀s''. (OPTION_MAP SND (m1' s') = SOME s'') ⇒ (m2 s'' = m2' s''))
⇒ (STATE_OPTION_IGNORE_BIND m1 m2 s = STATE_OPTION_IGNORE_BIND m1' m2' s')`,
Cases_on `m1' s'` THEN SRW_TAC [][STATE_OPTION_IGNORE_BIND_def]);
val _ = DefnBase.export_cong "STATE_OPTION_IGNORE_BIND_cong";

val q = `plen M s =
  STATE_OPTION_IGNORE_BIND
    (λs. STATE_OPTION_LIFT (OPTION_GUARD (ARB M s)) s)
    (λs.
       STATE_OPTION_BIND (λs. ARB M s)
         (λb s.
            if ¬b then
              STATE_OPTION_BIND (λs. ARB M s)
                (λM s.
                   STATE_OPTION_BIND (\s. plen M s) (λn s. STATE_OPTION_UNIT (n + 1) s) s)
                s
            else
              STATE_OPTION_UNIT 0 s) s) s`;


val plen_defn = Hol_defn "plen" q
val plen_defn' = Hol_defn "plen" q

val _ = export_theory()
