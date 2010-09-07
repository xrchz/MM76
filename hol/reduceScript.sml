open HolKernel boolLib bossLib Parse monadsyntax ptypesTheory
open lcsymtacs

val _ = new_theory "reduce"

val fWHILE_def = Define`
  fWHILE Guard Body s =
    WHILE (λ(b,s). b ∧ Guard s)
          (λ(b,s). case Body s of NONE -> (F, s)
                               || SOME s' -> (T, s'))
          (T,s)
`;

val fWHILE_EQN = store_thm(
  "fWHILE_EQN",
  ``fWHILE P B s = if P s then
                     case B s of
                        NONE -> NONE
                     || SOME s' -> fWHILE P B s'
                   else SOME s``,
  srw_tac [][fWHILE_def, SimpLHS] >|[
    asm_simp_tac (srw_ss())[Ntimes whileTheory.WHILE 2] >>
    Cases_on `B s` >> srw_tac [][] >>
    srw_tac [][fWHILE_def] >> srw_tac [][SimpRHS, Once whileTheory.WHILE],
    srw_tac [][Once whileTheory.WHILE]
  ]);

val segWHILE_def = Define`
  segWHILE (Guard : α -> (bool # α) option)
           (Body  : α -> (unit # α) option)
           (s:α) : unit option # α =
    case Guard s of
       NONE -> (NONE, s)
    || SOME g0 ->
         fWHILE FST (λ(g0,s). case (do Body ; Guard od) s of
                                 (NONE, s') -> NONE
                              || (SOME g, s') -> SOME (g,s'))

val repeat_def = Define`
  repeat block until = do
    block ;
    b <- until ;
    if b then return () else
    (λs. ((λy. if ISL y
               then OUTL y
               else OPTION_MAP (K ()) (OUTR y)) ## I)
           (WHILE (λx. if ISL (FST x)
                       then IS_SOME (OUTL (FST x))
                       else IS_SOME (OUTR (FST x)) ∧ ¬ (THE (OUTR (FST x))))
                  (λx. if ISL (FST x)
                       then (INR ## I) (until (SND x))
                       else (INL ## I) (block (SND x)))
                  (INR (SOME F), s)))
  od`;

val while_def = Define`
  while condition block s =
    WHILE (λx. if ISL (FST x)
               then IS_SOME (OUTL (FST x))
               else IS_SOME (OUTR (FST x)) ∧ THE (OUTR (FST x)))
          (λx. if ISL (FST x)
               then (INR ## I) (condition (SND x))
               else (INL ## I) (block (SND x)))
          (INL (SOME ()), s)`;

val reduce_def = Define`
  reduce M = do
    frontier <- CreateListOfTempMulteq ;
    argsofcp <- CreateListOfTerms ;
    argsofm <- CreateListOfTempMulteq ;
    t <- new (ARB : Term) ;
    t <- HeadOfListOfTerms M ;
    t' <- lookup t ;
    fs <- return (if ISL t' then ARB else (OUTR t').fsymb) ;
    repeat do
      argsofm1 <- CreateListOfTempMulteq ;
      t <- HeadOfListOfTerms M ;
      x0 <- TailOfListOfTerms M ;
      x0' <- lookup x0 ;
      assign M x0' ;
      t' <- lookup t ;
      if ISR t' ∧ ((OUTR t').fsymb = fs) then return () else OPTIONT_FAIL ;
      argsoft <- return (OUTR t').args ;
      while (do b <- EmptyListOfTerms argsoft ; return not b od) do
        x1 <- HeadOfListOfTerms argsoft ;
        AddTerm x1 argsofm argsofm1 ;
        argsoft <- NEED TO STORE VARIABLES IN THE STATE
      od
      argsofm1' <- lookup argsofm1 ;
      assign argsofm argsofm1' ;
      return ()
    od (EmptyListOfTerms M) ;
    return ()
  od`;

val _ = export_theory ()
