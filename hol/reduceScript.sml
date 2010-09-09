open HolKernel boolLib bossLib Parse monadsyntax ptypesTheory lcsymtacs

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

val OPTION_GUARD_def = Define`
  OPTION_GUARD b x = if b then SOME x else NONE`;

val loop_lift = Define`
  loop_lift : ('a -> ('b # 'a) option) -> ('c # 'a) -> ('b # ('c # 'a)) option
  m = λ(c,a). OPTION_BIND (m a) (λ(b,a). SOME (b,(c,a)))`;
val _ = inferior_overload_on("monad_bind", ``STATE_OPTION_BIND o loop_lift``);
val _ = inferior_overload_on("monad_unitbind", ``STATE_OPTION_IGNORE_BIND o loop_lift``);

val loop_get = Define`
  loop_get : ('c # 'a) -> ('c # ('c # 'a)) option
  (c,a) = SOME (c,(c,a))`;

val loop_put = Define`
  loop_put : 'c -> ('c # 'a) -> (unit # ('c # 'a)) option
  c (_,a) = SOME ((),(c,a))`;

val AddTerm_def = Define`
  AddTerm t1 argsofm argsofm1 = do
    b <- EmptyListOfTempMulteq argsofm ;
    if b then do
      l1 <- CreateListOfTerms ;
      l2 <- CreateListOfTerms ;
      temp <- new (TempMultiequation l1 l2) ;
      return (argsofm,argsofm1)
    od else do
      temp <- HeadOfListOfTempMulteq argsofm ;
      argsofm <- TailOfListOfTempMulteq argsofm ;
      t1' <- lookup t1 ;
      if ISR t1' then do
        temp' <- lookup temp ;
        l3 <- AddToEndOfListOfTerms t1 temp'.M ;
        assign temp (temp' with M := l3)
      od else do
        temp' <- lookup temp ;
        l3 <- AddToEndOfListOfTerms t1 temp'.S ;
        assign temp (temp' with S := l3)
      od ;
      argsofm1 <- AddToEndOfListOfTempMulteq temp argsofm1 ;
      return (argsofm,argsofm1)
    od
  od`;

val reduce_def = Define`
  reduce M = do
    frontier <- CreateListOfTempMulteq ;
    argsofcp <- CreateListOfTerms ;
    argsofm <- CreateListOfTempMulteq ;
    t <- HeadOfListOfTerms M ;
    t' <- lookup t ;
    fs <- OPTION_GUARD (ISR t') (OUTR t').fsymb ;
    repeat ($, argsofm, SND) do
      argsofm1 <- CreateListOfTempMulteq ;
      t <- HeadOfListOfTerms M ;
           TailOfListOfTerms M ;
      t' <- lookup t ;
      OPTION_GUARD (ISR t' ∧ ((OUTR t').fsymb = fs)) () ;
      argsoft <- return (OUTR t').args ;
      argsofm <- loop_get ;
      while ($, (argsofm,argsoft), SND)
        (do (argsofm,argsoft) <- loop_get ; b <- EmptyListOfTerms argsoft ; return (¬ b) od)
      do
        (argsofm,argsoft) <- loop_get ;
        tmp0 <- HeadOfListOfTerms argsoft ;
        (argsofm,argsofm1) <- AddTerm tmp0 argsofm argsofm1 ;
        argsoft <- TailOfListOfTerms argsoft ;
        loop_put (argsofm,argsoft)
      od ;
      loop_put argsofm1
    od (loop_lift (EmptyListOfTerms M))
  od`;

val _ = export_theory ()
