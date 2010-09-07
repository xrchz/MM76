open HolKernel boolLib bossLib Parse monadsyntax ptypesTheory
open lcsymtacs

val _ = new_theory "reduce"

val while_def = Define`
  while ((inj,prj) : ('a -> 'b) # ('b -> 'a))
        (guard  : 'b -> (bool # 'b) option)
        (block  : 'b -> (unit # 'b) option)
        s =
  OPTION_MAP ($, () o prj o SND)
    (WHILE (λx. OPTION_MAP FST x = SOME T)
           (λx. OPTION_BIND x (do block ; guard od o SND))
           (guard (inj s)))`;

val repeat_def = Define`
  repeat ((inj,prj) : ('a -> 'b) # ('b -> 'a))
         (block  : 'b -> (unit # 'b) option)
         (guard  : 'b -> (bool # 'b) option)
         s =
  OPTION_MAP ($, () o prj o SND)
    (WHILE (λx. OPTION_MAP FST x = SOME F)
           (λx. OPTION_BIND x (do block ; guard od o SND))
           (SOME (F, inj s)))`;

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
