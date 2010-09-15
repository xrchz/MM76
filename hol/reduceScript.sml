open HolKernel boolLib bossLib Parse monadsyntax ptypes_definitionsTheory lcsymtacs state_optionTheory option_guardTheory

val _ = new_theory "reduce"

val foo_def = tDefine "foo"`
  foo M =
  STATE_OPTION_BIND (STATE_OPTION_UNIT F)
  (λb. STATE_OPTION_IGNORE_BIND
         (if b then foo M else STATE_OPTION_UNIT ())
         (STATE_OPTION_UNIT ()))`
(WF_REL_TAC `REMPTY` >> srw_tac [][STATE_OPTION_UNIT_def]);

Hol_defn "plen" `
  plen M = do
    (λs. STATE_OPTION_LIFT (OPTION_GUARD (∃ls. list_of_List embed_Term s M ls)) s) ;
    b <- EmptyListOfTerms M ;
    n <- if ¬ b then do
      M <- TailOfListOfTerms M ;
      plen M
    od else return 0 ;
    return (n + 1)
  od`
(*
val STATE_OPTION_GET_def = Define`
  STATE_OPTION_GET : ('a,'a) state_option
  s = SOME (s,s)`;

Hol_defn "plen"
(*(print_backend_term_without_overloads_on["monad_bind","monad_unitbind"] o Term)*)
`
  plen M = do
    s <- STATE_OPTION_GET ;
    STATE_OPTION_LIFT (OPTION_GUARD (∃ls. list_of_List embed_Term s M ls) ()) ;
    b <- EmptyListOfTerms M ;
    n <- if ¬ b then do
      M <- TailOfListOfTerms M ;
      plen M
    od else return 0 ;
    return (n + 1)
  od`

app ((fn x => print_backend_term_without_overloads_on["monad_bind","monad_unitbind"] x before print"\n") o concl) (DefnBase.read_congs())
*)

val raw_while_def = Define`
  raw_while ((inj,prj) : ('a -> 'b) # ('b -> 'c # 'a))
        (guard  : 'b -> (bool # 'b) option)
        (block  : 'b -> (unit # 'b) option)
        s =
  OPTION_MAP (prj o SND)
    (WHILE (λx. OPTION_MAP FST x = SOME T)
           (λx. OPTION_BIND x (do block ; guard od o SND))
           (guard (inj s)))`;

val raw_repeat_def = Define`
  raw_repeat ((inj,prj) : ('a -> 'b) # ('b -> 'c # 'a))
         (block  : 'b -> (unit # 'b) option)
         (guard  : 'b -> (bool # 'b) option)
         s =
  OPTION_MAP (prj o SND)
    (WHILE (λx. OPTION_MAP FST x = SOME F)
           (λx. OPTION_BIND x (do block ; guard od o SND))
           (SOME (F, inj s)))`;

val _ = overload_on("while",``λt. raw_while ($, t, I)``);
val _ = overload_on("repeat",``λt. raw_repeat ($, t, I)``);

val loop_lift_def = Define`
  loop_lift : ('a -> ('b # 'a) option) -> ('c # 'a) -> ('b # ('c # 'a)) option
  m = λ(c,a). OPTION_BIND (m a) (λ(b,a). SOME (b,(c,a)))`;
val _ = inferior_overload_on("monad_bind", ``STATE_OPTION_BIND o loop_lift``);
val _ = inferior_overload_on("monad_unitbind", ``STATE_OPTION_IGNORE_BIND o loop_lift``);

val STATE_OPTION_BIND_o_loop_lift_cong = Q.store_thm(
"STATE_OPTION_BIND_o_loop_lift_cong",
`(m = m') ∧ (∀s a. (OPTION_MAP FST (m' s) = SOME a) ⇒ (f a = f' a))
 ⇒ ((STATE_OPTION_BIND o loop_lift) m f = (STATE_OPTION_BIND o loop_lift) m' f')`,
strip_tac >> fsrw_tac [][FUN_EQ_THM] >> qx_gen_tac `s'` >>
Cases_on `m' (SND s')` >> srw_tac [][state_optionTheory.STATE_OPTION_BIND_def,loop_lift_def,pairTheory.UNCURRY] >>
first_x_assum match_mp_tac >> qexists_tac `SND s'` >> srw_tac [][]);
val _ = DefnBase.export_cong "STATE_OPTION_BIND_o_loop_lift_cong";

val STATE_OPTION_IGNORE_BIND_o_loop_lift_cong = Q.store_thm(
"STATE_OPTION_IGNORE_BIND_o_loop_lift_cong",
`(m1 = m1') ∧ (∀s s' a. (OPTION_MAP SND (m1' s) = SOME s') ⇒ (m2 (a,s') = m2' (a,s')))
 ⇒ ((STATE_OPTION_IGNORE_BIND o loop_lift) m1 m2 = (STATE_OPTION_IGNORE_BIND o loop_lift) m1' m2')`,
strip_tac >> fsrw_tac [][FUN_EQ_THM] >> qx_gen_tac `s` >>
Cases_on `m1' (SND s)` >> Cases_on `s` >> fsrw_tac [][] >>
srw_tac [][state_optionTheory.STATE_OPTION_IGNORE_BIND_def,loop_lift_def] >>
qmatch_assum_rename_tac `m1' s2 = SOME x` [] >>
Cases_on `x` >> srw_tac [][] >>
first_x_assum match_mp_tac >> qexists_tac `s2` >> srw_tac [][]);
val _ = DefnBase.export_cong "STATE_OPTION_IGNORE_BIND_o_loop_lift_cong";

val loop_get_def = Define`
  loop_get : ('c # 'a) -> ('c # ('c # 'a)) option
  (c,a) = SOME (c,(c,a))`;

val loop_put_def = Define`
  loop_put : 'c -> ('c # 'a) -> (unit # ('c # 'a)) option
  c (_,a) = SOME ((),(c,a))`;

val _ = xDefine "mini_reduce"`
  mini_reduce M = do
    while 1
      (do n <- loop_get ; return (n = 2) od)
    do
      b <- EmptyListOfTerms M ;
      n <- loop_lift
        if ¬ b then do
          M <- TailOfListOfTerms M ;
          mini_reduce M
        od else return 2 ;
      loop_put n
    od ;
  return 2
  od`

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

val BuildFunctionTerm_def = Define`
  BuildFunctionTerm fs args = new (INR (FunTerm fs args))`;

val reduce_def = xDefine "reduce"`
  reduce M = do
    frontier <- CreateListOfTempMulteq ;
    argsofcp <- CreateListOfTerms ;
    argsofm <- CreateListOfTempMulteq ;
    t <- HeadOfListOfTerms M ;
    t' <- lookup t ;
    OPTION_GUARD (ISR t') ;
    fs <- return (OUTR t').fsymb ;
    (M,argsofm) <-
      repeat (M,argsofm) do
        argsofm1 <- CreateListOfTempMulteq ;
        (M,argsofm) <- loop_get ;
        t <- HeadOfListOfTerms M ;
        M <- TailOfListOfTerms M ;
        t' <- lookup t ;
        OPTION_GUARD (ISR t' ∧ ((OUTR t').fsymb = fs)) ;
        argsoft <- return (OUTR t').args ;
        (argsoft,argsofm,argsofm1) <-
          while (argsoft,argsofm,argsofm1)
            (do (argsoft,argsofm,argsofm1) <- loop_get ; b <- EmptyListOfTerms argsoft ; return (¬ b) od)
          do
            (argsoft,argsofm,argsofm1) <- loop_get ;
            tmp0 <- HeadOfListOfTerms argsoft ;
            (argsofm,argsofm1) <- AddTerm tmp0 argsofm argsofm1 ;
            argsoft <- TailOfListOfTerms argsoft ;
            loop_put (argsoft,argsofm,argsofm1)
          od ;
        loop_put (M,argsofm1)
      od do (M,argsofm1) <- loop_get ; loop_lift (EmptyListOfTerms M) od ;
    (argsofm,argsofcp,frontier) <-
      while (argsofm,argsofcp,frontier)
        (do (argsofm,argsofcp,frontier) <- loop_get ; b <- EmptyListOfTempMulteq argsofm ; return (¬ b) od)
      do
        (argsofm,argsofcp,frontier) <- loop_get ;
        temp <- HeadOfListOfTempMulteq argsofm ;
        argsofm <- TailOfListOfTempMulteq argsofm ;
        temp' <- lookup temp ;
        b <- EmptyListOfTerms temp'.S ;
        (newcommonpart,newfrontier) <- loop_lift
          if ¬ b then do
            newcommonpart <- HeadOfListOfTerms temp'.S ;
            tmp1 <- CreateListOfTempMulteq ;
            newfrontier <- AddToEndOfListOfTempMulteq temp tmp1 ;
            return (newcommonpart,newfrontier)
          od else reduce temp'.M ;
        argsofcp <- AddToEndOfListOfTerms newcommonpart argsofcp ;
        frontier <- AppendListsOfTempMulteq frontier newfrontier ;
        loop_put (argsofm,argsofcp,frontier)
      od ;
    commonpart <- BuildFunctionTerm fs argsofcp ;
    return (commonpart, frontier)
  od`
(FAIL_TAC "no proof yet");

val _ = export_theory ()
