open HolKernel boolLib boolSimps SatisfySimps bossLib Parse monadsyntax ptypesTheory lcsymtacs state_optionTheory state_option_congTheory

val _ = new_theory "reduce"

val plen_defn = Hol_defn "plen"
`plen M s =
  monad_unitbind
    (λs1.
       STATE_OPTION_LIFT
         (OPTION_GUARD
            (wfstate s1 ∧ ∃ls. list_of_List embed_Term s1 M ls)) s1)
    (λs2.
       monad_bind (λs3. EmptyListOfTerms M s3)
         (λb s4.
            if ¬b then
              monad_bind (λs5. TailOfListOfTerms M s5)
                (λM s6.
                   monad_bind (\s7. plen M s7) (λn s8. return (n + 1) s8) s6)
                s4
            else
              return 0 s4) s2) s`;

val thms = Defn.tprove(plen_defn,
srw_tac [DNF_ss][pairTheory.FORALL_PROD] >>
srw_tac [][STATE_OPTION_LIFT_def,optionTheory.OPTION_GUARD_def] >>
WF_REL_TAC `measure (λ(M,s). LENGTH (@ls. list_of_List embed_Term s M ls))` >>
srw_tac [][] >>
imp_res_tac EmptyList_NULL >>
fsrw_tac [][] >> srw_tac [][] >>
Cases_on `ls` >> fsrw_tac [][] >> srw_tac [][] >>
qmatch_assum_rename_tac `list_of_List embed_Term s M (h::ls)` [] >>
qmatch_assum_rename_tac `TailOfListOfTerms M s = SOME (M',s')` [] >>
`list_of_List embed_Term s' M' ls` by (
  ASSUME_TAC is_embed_Term >>
  imp_res_tac TailOfList_TL >>
  fsrw_tac [][] >> srw_tac [][] ) >>
ntac 2 SELECT_ELIM_TAC >>
srw_tac [SATISFY_ss][] >>
imp_res_tac list_of_List_unique >>
srw_tac [][]);

fun UNETA_CONV x t =
  let val (dom,rng) = dom_rng (type_of t)
      val tysubst = [alpha |-> dom, beta |-> rng]
      val th = SYM (SPEC t (INST_TYPE tysubst ETA_AX))
      val tm = mk_abs (x,(mk_comb(t,x)))
  in
    TRANS th (ALPHA (rhs (concl th)) tm)
  end
  handle e => raise wrap_exn "" "UNETA_CONV" e

(* make sure tm is an abstraction of at least (length vs) variables, using
variables from vs (in reverse order) for inverse eta-expansion if necessary.
if an element of vs is NONE, use a genvar instead *)
local
  fun GEN_UNETA_CONV NONE tm = let
    val (dom,_) = dom_rng (type_of tm)
  in UNETA_CONV (genvar dom) tm end
    | GEN_UNETA_CONV (SOME x) tm = UNETA_CONV x tm
in
  fun VLIST_CONV vs tm = let
    val (ws,m) = strip_abs tm
    val vs = List.drop(vs,length ws)
  in
    STRIP_BINDER_CONV NONE (EVERY_CONV (map GEN_UNETA_CONV vs)) tm
  end
end

local
  val unitbind = ``STATE_OPTION_IGNORE_BIND :
    ('a,'b) state_option -> ('a,'c) state_option -> ('a,'c) state_option``
  val bind = ``STATE_OPTION_BIND :
    ('a,'b) state_option -> ('b -> ('a,'c) state_option) -> ('a,'c) state_option``
  fun f (ls,bind) s (rator,(_::_::rest)) = let
    val _ = assert (can (match_term bind)) rator
    val conv = RAND_CONV (VLIST_CONV (ls@[SOME s])) THENC
               RATOR_CONV (RAND_CONV (VLIST_CONV [SOME s]))
  in
    case rest of
      [] => conv THENC (UNETA_CONV s)
    | _  => conv
  end
in
  fun uneta_bind_conv s tm = let
    val p as (rator,_) = strip_comb tm
    val _ = assert is_const rator
  in
    trye (f ([],unitbind) s) p handle HOL_ERR _ =>
    with_exn (f ([NONE],bind) s) p
    (mk_HOL_ERR "" "uneta_bind_conv" "Not an application of a state_option bind")
  end tm
end

fun eta_bind_conv x = let
  val (s,ty) = dest_var x
  fun check_eta tm = let
    val (v,m) = dest_abs tm
    val (vs,vt) = dest_var v
  in if String.isPrefix s vs andalso vt = ty
     then ETA_CONV tm else fail()
  end
in
  check_eta ORELSEC (ABS_CONV check_eta)
end

val APPLY_COND_THM = Q.store_thm(
"APPLY_COND_THM",
`(if b then c else a) x = if b then c x else a x`,
srw_tac [][]);

val ETA_COND = Q.store_thm(
"ETA_COND",
`((if b then (λx. cf x) x else a) = (if b then cf x else a)) ∧
 ((if b then c else (λx. af x) x) = (if b then c else af x))`,
srw_tac [][]);

fun qrule x q = let
  val (t,_) = Defn.parse_absyn (Parse.Absyn q)
  fun term_to_quote t = [QUOTE (term_to_string t) : term frag]
  val conv = DEPTH_CONV (uneta_bind_conv x) THENC
             PURE_REWRITE_CONV [APPLY_COND_THM,ETA_COND] THENC
             (X_FUN_EQ_CONV x) THENC
             QUANT_CONV (RAND_CONV LIST_BETA_CONV)
  val th = conv t handle UNCHANGED => REFL t
  val (_,t) = strip_forall (rhs (concl th))
  val _ = say(term_to_backend_string t^"\n")
in
  term_to_quote t
end

fun unconv_ind x = CONV_RULE (PURE_REWRITE_CONV [SYM APPLY_COND_THM] THENC DEPTH_CONV (eta_bind_conv x))
fun unconv_def x = EXT o GEN x o (unconv_ind x)

val STATE_OPTION_GET_def = Define`
  STATE_OPTION_GET : ('a,'a) state_option
  s = SOME (s,s)`;

val sfoo_defn = Hol_defn "sfoo"(
qrule ``s:'a``
`sfoo = do
  s1 <- STATE_OPTION_GET ;
  s2 <- STATE_OPTION_GET ;
  if s1 = s2 then return () else sfoo ;
  return ()
od`);
val p = Defn.tprove(sfoo_defn,
WF_REL_TAC `REMPTY` >>
srw_tac [][STATE_OPTION_GET_def] >>
METIS_TAC []);
val (sfoo_def,sfoo_ind) = (unconv_def ``s:'a`` ## unconv_ind ``s:'a``) p;

val foo_defn = Defn.Hol_defn "foo" (
qrule ``s:'a`` `
foo M =
  STATE_OPTION_BIND (STATE_OPTION_UNIT F)
  (λb. STATE_OPTION_IGNORE_BIND
         (if b then foo M else STATE_OPTION_UNIT ())
         (STATE_OPTION_UNIT ()))`);
val p = Defn.tprove (foo_defn,
WF_REL_TAC `REMPTY` >>
srw_tac [][STATE_OPTION_UNIT_def]);
val (foo_def,foo_ind) = (unconv_def ``s:'a`` ## unconv_ind ``s:'a``) p;

val s = ``s:bool->bool``;
val ignore_rec_defn = Defn.Hol_defn "ignore_rec" (
qrule s `
  ignore_rec = STATE_OPTION_IGNORE_BIND
               (λs. OPTION_MAP (combin$C $, s) (OPTION_GUARD (s T)))
               (λs. ignore_rec ((T =+ ¬(s T)) s))`);
val p = Defn.tprove (ignore_rec_defn,
WF_REL_TAC `measure (λs. if s T then 1 else 0)` >>
srw_tac [][combinTheory.APPLY_UPDATE_THM,optionTheory.OPTION_GUARD_def]);
val (ignore_rec_def,ignore_rec_ind) = (unconv_def s ## unconv_ind s) p;

val s = ``s:state``;
val plen_defn = Defn.Hol_defn "plen" (
qrule s `
  plen M = do
    (λs. STATE_OPTION_LIFT (OPTION_GUARD (wfstate s ∧ ∃ls. list_of_List embed_Term s M ls)) s) ;
    b <- EmptyListOfTerms M ;
    if ¬ b then do
      M <- TailOfListOfTerms M ;
      n <- plen M ;
      return (n + 1)
    od else return 0
  od`)
val p = Defn.tprove (plen_defn,

val (plen_def,plen_ind) =
W (curry op ##) (unconv_rule state_option_consts) p;

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
