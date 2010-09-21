open HolKernel boolLib bossLib Parse monadsyntax ptypes_definitionsTheory lcsymtacs state_optionTheory option_guardTheory

val _ = new_theory "reduce"

val q = `plen M s =
  monad_unitbind
    (λs.
       STATE_OPTION_LIFT
         (OPTION_GUARD
            (wfstate s ∧ ∃ls. list_of_List embed_Term s M ls)) s)
    (λs.
       monad_bind (λs. EmptyListOfTerms M s)
         (λb s.
            if ¬b then
              monad_bind (λs. TailOfListOfTerms M s)
                (λM s.
                   monad_bind (\s. plen M s) (λn s. return (n + 1) s) s)
                s
            else
              return 0 s) s) s`;


val plen_defn = Hol_defn "plen" q
val plen_defn' = Hol_defn "plen" q

val _ = export_theory()
