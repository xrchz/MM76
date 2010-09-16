open HolKernel boolLib bossLib Parse monadsyntax ptypes_definitionsTheory lcsymtacs state_optionTheory option_guardTheory

val _ = new_theory "reduce"

(*
val STATE_OPTION_IGNORE_BIND_weak_cong = Q.store_thm(
"STATE_OPTION_IGNORE_BIND_weak_cong",
`(m1 = m1') ∧
 (!s''. (∃s. OPTION_MAP SND (m1' s) = SOME s'') ⇒ (m2 s'' = m2' s'')) ⇒
 (STATE_OPTION_IGNORE_BIND m1 m2 = STATE_OPTION_IGNORE_BIND m1' m2')`,
srw_tac [boolSimps.DNF_ss][STATE_OPTION_IGNORE_BIND_def,FUN_EQ_THM] >>
Cases_on `m1' x` >> srw_tac [][] >> PROVE_TAC []);
val () = DefnBase.add_cong STATE_OPTION_IGNORE_BIND_weak_cong;
(* fix drop_cong if there are going to be multiple congruences... *)

val STATE_OPTION_BIND_weak_cong = Q.store_thm(
"STATE_OPTION_BIND_weak_cong",
`(m = m') ∧
 (∀v s''. (∃s. (m' s = SOME (v,s''))) ⇒ (f v s'' = f' v s'')) ⇒
 (STATE_OPTION_BIND m f = STATE_OPTION_BIND m' f')`,
srw_tac [boolSimps.DNF_ss][STATE_OPTION_BIND_def,FUN_EQ_THM] >>
Cases_on `m' x` >> srw_tac [][pairTheory.UNCURRY] >>
first_x_assum match_mp_tac >> srw_tac [][pairTheory.EXISTS_PROD] >>
PROVE_TAC [] );
val () = DefnBase.add_cong STATE_OPTION_BIND_weak_cong;
*)

(*
val tm = ``foo a1 a2``
val (rator,rand) = dest_comb tm
val th = SIMP_CONV pure_ss [Ntimes (GSYM BETA_THM) 2] ``bar a1 a2 a3``;

val INVERSE_ETA_THM = save_thm(
"INVERSE_ETA_THM",
FUN_EQ_THM |>  Q.SPEC `f` |> Q.SPEC `\x. f x` |> EQ_IMP_RULE |> snd
|> UNDISCH |> PROVE_HYP (BETA_THM |> GSYM |> Q.SPEC `f`)
|> Q.GEN `f`);

val th1 = 
((RATOR_CONV (SIMP_CONV pure_ss [Once INVERSE_ETA_THM])) THENC
(fn tm => RATOR_CONV (ALPHA_CONV (snd(dest_comb tm))) tm))
``bar a1``

val th2 =
((RATOR_CONV (SIMP_CONV pure_ss [Once INVERSE_ETA_THM])) THENC
(fn tm => RATOR_CONV (ALPHA_CONV (snd(dest_comb tm))) tm))
``bar a1 a2``

SIMP_CONV pure_ss [Once th1] ``bar a1 a2``
INVERSE_ETA_THM
th2
SUBS [th1] th2
SUBS_OCCS [([2],th1)] th2
GSYM (SUBST_MATCH th1 (GSYM th2))

ONCE_REWRITE_RULE [th1] th2
help"SUBS_OCCS";

CONV_RULE BETA_CONV it
help"SimpRHS"

CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV ETA_CONV)) th
ETA_CONV
ETA_RULE
ETA
*)

(*
val () = use "/home/ramana/HOL/src/tfl/src/RW.sml";
val () = use "/home/ramana/HOL/src/tfl/src/Defn.sml";
val () = RW.monitoring := true;
*)

(*
fun GNOT_ABS_INVERSE_ETA_CONV t = let
  val _ = assert (not o pairLib.is_pabs) t
in
  INVERSE_ETA_CONV (genvar(#1(dom_rng(type_of t)))) t
end handle e => raise wrap_exn "" "GNOT_ABS_INVERSE_ETA_CONV" e

fun VNOT_ABS_INVERSE_ETA_CONV s t = let
  val _ = assert (not o pairLib.is_pabs) t
  val vs = free_vars t
in
  INVERSE_ETA_CONV (prim_variant vs (mk_var (s,(#1(dom_rng(type_of t)))))) t
end handle e => raise wrap_exn "" "VNOT_ABS_INVERSE_ETA_CONV" e

fun VCOMB_INVERSE_ETA_CONV s t = let
  val _ = assert is_comb t
  val vs = free_vars t
in
  INVERSE_ETA_CONV (prim_variant vs (mk_var (s,(#1(dom_rng(type_of t)))))) t
end handle e => raise wrap_exn "" "VCOMB_INVERSE_ETA_CONV" e
*)


(* Conversions for selectively applying (inverse) eta on certain constants *)

fun UNETA_CONV x t =
  let val (dom,rng) = dom_rng (type_of t)
      val tysubst = [alpha |-> dom, beta |-> rng]
      val th = SYM (SPEC t (INST_TYPE tysubst ETA_AX))
      val tm = mk_abs (x,(mk_comb(t,x)))
  in
    TRANS th (ALPHA (rhs (concl th)) tm)
  end
  handle e => raise wrap_exn "" "UNETA_CONV" e

fun UNETA_THESE_CONV ts x t = let
  val (rator,_) = strip_comb t
  val _ = assert (exists (can (C match_term rator))) ts
in
  UNETA_CONV x t
end handle e => raise wrap_exn "" "UNETA_THESE_CONV" e

fun ETA_THESE_CONV ts t = let
  val (rator,_) = strip_comb (#2(dest_abs t))
  val _ = assert (exists (can (C match_term rator))) ts
in
  ETA_CONV t
end handle e => raise wrap_exn "" "ETA_THESE_CONV" e

local
  (* Insert all definitions required to get Defn.parse_from_absyn here.
     Alternatively just expose parse_from_absyn, or put a version of Hol_defn
     that takes a list of terms to uneta into Defn.

     Would actually need Defn.parse_quote in order to deal with multiple
     definitions at once (for mutual recursion). *)
  val ERRloc = mk_HOL_ERRloc "myDefn"

  local fun underscore #"_" = true  | underscore   _  = false
  in
  fun wildcard s =
    let val ss = Substring.full s
    in if Substring.isEmpty ss then false
       else Substring.isEmpty (Substring.dropl underscore ss)
    end
  end

  fun vary s S =
   let fun V n =
        let val s' = s^Lib.int_to_string n
        in if mem s' S then V (n+1) else (s',s'::S)
        end
   in V 0 end

  local
    val v_vary = vary "v"
    fun tm_exp tm S =
      case dest_term tm
      of VAR(s,Ty) =>
           if wildcard s then
             let val (s',S') = v_vary S in (Term.mk_var(s',Ty),S') end
           else (tm,S)
       | CONST _  => (tm,S)
       | COMB(Rator,Rand) =>
          let val (Rator',S')  = tm_exp Rator S
              val (Rand', S'') = tm_exp Rand S'
          in (mk_comb(Rator', Rand'), S'')
          end
       | LAMB _ => raise ERR "tm_exp" "abstraction in pattern"
    open Absyn
  in
  fun exp (AQ(locn,tm)) S =
        let val (tm',S') = tm_exp tm S in (AQ(locn,tm'),S') end
    | exp (IDENT (p as (locn,s))) S =
        if wildcard s
          then let val (s',S') = v_vary S in (IDENT(locn,s'), S') end
          else (IDENT p, S)
    | exp (QIDENT (p as (locn,s,_))) S =
        if wildcard s
         then raise ERRloc "exp" locn "wildcard in long id. in pattern"
         else (QIDENT p, S)
    | exp (APP(locn,M,N)) S =
        let val (M',S')   = exp M S
            val (N', S'') = exp N S'
        in (APP (locn,M',N'), S'')
        end
    | exp (TYPED(locn,M,pty)) S =
        let val (M',S') = exp M S in (TYPED(locn,M',pty),S') end
    | exp (LAM(locn,_,_)) _ = raise ERRloc "exp" locn "abstraction in pattern"

  fun expand_wildcards asy (asyl,S) =
     let val (asy',S') = exp asy S in (asy'::asyl, S') end
  end

  local open Absyn
  in
  fun vnames_of (VAQ(_,tm)) S = union (map (fst o Term.dest_var) (all_vars tm)) S
    | vnames_of (VIDENT(_,s)) S = union [s] S
    | vnames_of (VPAIR(_,v1,v2)) S = vnames_of v1 (vnames_of v2 S)
    | vnames_of (VTYPED(_,v,_)) S = vnames_of v S

  fun names_of (AQ(_,tm)) S = union (map (fst o Term.dest_var) (all_vars tm)) S
    | names_of (IDENT(_,s)) S = union [s] S
    | names_of (APP(_,IDENT(_,"case_arrow__magic"), _)) S = S
    | names_of (APP(_,M,N)) S = names_of M (names_of N S)
    | names_of (LAM(_,v,M)) S = names_of M (vnames_of v S)
    | names_of (TYPED(_,M,_)) S = names_of M S
    | names_of (QIDENT(_,_,_)) S = S
  end

  local
    fun dest_pvar (Absyn.VIDENT(_,s)) = s
      | dest_pvar other = raise ERRloc "munge" (Absyn.locn_of_vstruct other)
                                       "dest_pvar"
    fun dest_atom tm = (dest_const tm handle HOL_ERR _ => dest_var tm);
    fun dest_head (Absyn.AQ(_,tm)) = fst(dest_atom tm)
      | dest_head (Absyn.IDENT(_,s)) = s
      | dest_head (Absyn.TYPED(_,a,_)) = dest_head a
      | dest_head (Absyn.QIDENT(locn,_,_)) =
              raise ERRloc "dest_head" locn "qual. ident."
      | dest_head (Absyn.APP(locn,_,_)) =
              raise ERRloc "dest_head" locn "app. node"
      | dest_head (Absyn.LAM(locn,_,_)) =
              raise ERRloc "dest_head" locn "lam. node"
    fun strip_tyannote0 acc absyn =
        case absyn of
          Absyn.TYPED(locn, a, ty) => strip_tyannote0 ((ty,locn)::acc) a
        | x => (List.rev acc, x)
    val strip_tyannote = strip_tyannote0 []
    fun list_mk_tyannote(tyl,a) =
        List.foldl (fn ((ty,locn),t) => Absyn.TYPED(locn,t,ty)) a tyl
  in
  fun munge eq (eqs,fset,V) =
   let val (vlist,body) = Absyn.strip_forall eq
       val (lhs0,rhs)   = Absyn.dest_eq body
       val   _          = if exists wildcard (names_of rhs []) then
                           raise ERRloc "munge" (Absyn.locn_of_absyn rhs)
                                        "wildcards on rhs" else ()
       val (tys, lhs)   = strip_tyannote lhs0
       val (f,pats)     = Absyn.strip_app lhs
       val (pats',V')   = rev_itlist expand_wildcards pats
                              ([],Lib.union V (map dest_pvar vlist))
       val new_lhs0     = Absyn.list_mk_app(f,rev pats')
       val new_lhs      = list_mk_tyannote(tys, new_lhs0)
       val new_eq       = Absyn.list_mk_forall(vlist, Absyn.mk_eq(new_lhs, rhs))
       val fstr         = dest_head f
   in
      (new_eq::eqs, insert fstr fset, V')
   end
  end

  fun elim_wildcards eqs =
   let val names = names_of eqs []
       val (eql,fset,_) = rev_itlist munge (Absyn.strip_conj eqs) ([],[],names)
   in
     (Absyn.list_mk_conj (rev eql), rev fset)
   end

  fun parse_absyn absyn0 =
   let val (absyn,fn_names) = elim_wildcards absyn0
       val restore_these = map (fn s => (s, Parse.hide s)) fn_names
       fun restore() =
         List.app (fn (s, data) => Parse.update_overload_maps s data)
                  restore_these
       val tm  = Parse.absyn_to_term (Parse.term_grammar()) absyn
                 handle e => (restore(); raise e)
   in
     restore();
     (tm, fn_names)
   end
in
  fun qrule ts x q = let
    val (t,_) = parse_absyn (Parse.Absyn q)
    fun term_to_quote t = [QUOTE (term_to_string t) : term frag]
    val th = DEPTH_CONV (UNETA_THESE_CONV ts x) t handle UNCHANGED => REFL t
    val t = rhs (concl th)
  in
    term_to_quote t
  end
  fun unconv_rule ts = CONV_RULE (DEPTH_CONV (ETA_THESE_CONV ts))
end

val state_option_consts =
[``STATE_OPTION_BIND``,
 ``STATE_OPTION_IGNORE_BIND``,
 ``STATE_OPTION_UNIT`` ];

(* Define foo using the quote the user wants to write. But the user must use
qrule and know the constants to pass, and the (type of the) variable to use  *)
val foo_defn = Defn.Hol_defn "foo" (
qrule state_option_consts ``s:'a`` `
foo M =
  STATE_OPTION_BIND (STATE_OPTION_UNIT F)
  (λb. STATE_OPTION_IGNORE_BIND
         (if b then foo M else STATE_OPTION_UNIT ())
         (STATE_OPTION_UNIT ()))`);
(* prove the termination goal *)
val p = Defn.tprove (foo_defn,
WF_REL_TAC `REMPTY` >>
srw_tac [][STATE_OPTION_UNIT_def]);
(* extract the theorems the user wants to see *)
val (foo_def,foo_ind) = W (curry op ##) (unconv_rule state_option_consts) p;

(* Same procedure works for this example.
A separate bug is that you can't remove the s argument from both sides of this
quote. *)
val ignore_rec_defn = Defn.Hol_defn "ignore_rec" (
qrule state_option_consts ``s:'a`` `
  ignore_rec s = STATE_OPTION_IGNORE_BIND
                 (λs. OPTION_MAP (combin$C $, s) (OPTION_GUARD (s T)))
                 (λs. ignore_rec ((T =+ ¬(s T)) s))
                 s`);
val p = Defn.tprove (ignore_rec_defn,
WF_REL_TAC `measure (λs. if s T then 1 else 0)` >>
srw_tac [][combinTheory.APPLY_UPDATE_THM,OPTION_GUARD_def]);
val (ignore_rec_def,ignore_rec_ind) =
W (curry op ##) (unconv_rule state_option_consts) p;

val plen_defn = Defn.Hol_defn "plen" (
qrule state_option_consts ``s:state`` `
  plen M = do
    (λs. STATE_OPTION_LIFT (OPTION_GUARD (∃ls. list_of_List embed_Term s M ls)) s) ;
    b <- EmptyListOfTerms M ;
    n <- if ¬ b then do
      M <- TailOfListOfTerms M ;
      plen M
    od else return 0 ;
    return (n + 1)
  od`)
val p = Defn.tprove (plen_defn,
(* I haven't proved termination here yet, because it's a lot more difficult
here, but I am semi-confident that the termination goal is (at last) provable
*)
)
val (plen_def,plen_ind) =
W (curry op ##) (unconv_rule state_option_consts) p;

(* You can then use save_thm to save the right form of the definition and
induction. There are no extra flags or tags necessary to completely emulate
Define, right? *)

(*
val fail = Hol_defn "ignore_rec" Term`
  ignore_rec = STATE_OPTION_IGNORE_BIND
                 (λs. OPTION_BIND (FLOOKUP s 0)
                       (OPTION_MAP (C $, s) o OPTION_GUARD o ($<> 0)))
                 (λs. ignore_rec (s |+ (0, s ' 0 - 1)))`;

val _ = Hol_defn "foo0" `foo0 = (λs. s ≠ 0 ∧ foo0 (s - 1))`;
val _ = Hol_defn "foo1" `foo1 x = (λs. s ≤ x ∧ foo1 x (SUC s))`;
*)

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
