open HolKernel boolLib bossLib Parse ptypes_definitionsTheory lcsymtacs state_optionTheory option_guardTheory

val _ = new_theory "reduce"

val q = `plen M s =
  STATE_OPTION_IGNORE_BIND
    (λs.
       STATE_OPTION_LIFT
         (OPTION_GUARD
            (wfstate s ∧ ∃ls. list_of_List embed_Term s M ls)) s)
    (λs.
       STATE_OPTION_BIND (λs. EmptyListOfTerms M s)
         (λb s.
            if ¬b then
              STATE_OPTION_BIND (λs. TailOfListOfTerms M s)
                (λM s.
                   STATE_OPTION_BIND (\s. plen M s) (λn s. STATE_OPTION_UNIT (n + 1) s) s)
                s
            else
              STATE_OPTION_UNIT 0 s) s) s`;


val plen_defn = Hol_defn "plen" q
val plen_defn' = Hol_defn "plen" q

val _ = export_theory()
