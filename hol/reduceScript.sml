open HolKernel boolLib bossLib Parse monadsyntax ptypes_definitionsTheory lcsymtacs state_optionTheory option_guardTheory

val _ = new_theory "reduce"

Hol_defn "plen"
`plen M s =
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
              return 0 s) s) s`

val _ = delete_const "plen";
val _ = delete_binding "plen_curried_def";
val _ = delete_binding "plen_tupled_primitive_def";

Hol_defn "plen"
`plen M s =
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
              return 0 s) s) s`

(*
HOW DO YOU TURN

`plen M =
 STATE_OPTION_IGNORE_BIND
 (λs. STATE_OPTION_LIFT (OPTION_GUARD (∃ls. list_of_List embed_Term s M ls)) s)
 (STATE_OPTION_BIND (EmptyListOfTerms M)
   (λb. if ¬b then
          STATE_OPTION_BIND (TailOfListOfTerms M)
          (λM. STATE_OPTION_BIND (plen M)
               (λn. STATE_OPTION_UNIT (n + 1)))
        else STATE_OPTION_UNIT 0))`

INTO

`plen M = \s.
 STATE_OPTION_IGNORE_BIND
 (λs. STATE_OPTION_LIFT (OPTION_GUARD (∃ls. list_of_List embed_Term s M ls)) s)
 (\s. STATE_OPTION_BIND (EmptyListOfTerms M)
      (λb.\s. if ¬ b
             then STATE_OPTION_BIND (TailOfListOfTerms M)
                  (λM. \s. STATE_OPTION_BIND (plen M)
                         (λn.\s. STATE_OPTION_UNIT (n+1) s)
                         s)
                  s
             else (STATE_OPTION_UNIT 0 s))
      s)
 s`

GENERICALLY?

is COND the only special case?
i.e. use this
`if b then c else a = (λx. if b then c x else a x)
instead of ETA_AX whenever it applies

or alternatively, run a simplification phase with
`(if b then c else a) x = if b then c x else a x`
after doing normal uneta
*)

(*
(* Examples of desired definitions *)
val sfoo_defn = Hol_defn "sfoo"
`sfoo = do
  s1 <- STATE_OPTION_GET ;
  s2 <- STATE_OPTION_GET ;
  if s1 = s2 then return () else sfoo ;
  return ()
od`;

val foo_defn = Hol_defn "foo"
`foo M = do
  b <- return F ;
  if b then foo M else return () ;
  return ()
od`;

val ignore_rec_defn = Hol_defn "ignore_rec"
`ignore_rec = STATE_OPTION_IGNORE_BIND
              (λs. OPTION_MAP (combin$C $, s) (OPTION_GUARD (s T)))
              (λs. ignore_rec ((T =+ ¬(s T)) s))`;

val plen_defn = Hol_defn "plen"
`plen M = do
  (λs. STATE_OPTION_LIFT (OPTION_GUARD (∃ls. list_of_List embed_Term s M ls)) s) ;
  b <- EmptyListOfTerms M ;
  if ¬b then do
    M <- TailOfListOfTerms M ;
    n <- plen M ;
    return (n + 1)
  od else return 0
od`;
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

(*
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
*)

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
in
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
end

(*
fun qrule ts x q = let
  val (t,_) = parse_absyn (Parse.Absyn q)
  fun term_to_quote t = [QUOTE (term_to_string t) : term frag]
  val th = DEPTH_CONV (UNETA_THESE_CONV ts x) t handle UNCHANGED => REFL t
  val t = rhs (concl th)
in
  term_to_quote t
end
fun unconv_rule ts = CONV_RULE (DEPTH_CONV (ETA_THESE_CONV ts))

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

task: write a conversion that recursively makes sure any occurrence of
STATE_OPTION_BIND is of the form STATE_OPTION_BIND m (\v s. f) s, and any occurrence of
STATE_OPTION_IGNORE_BIND is of the form STATE_OPTION_IGNORE_BIND m1 (\s. m2) s

possible algorithm (do DEPTH_CONV on this):
if you encounter an application of (unit)bind in the wrong form:
if it has only 2 arguments, inverse eta yourself.
if the second argument doesn't have enough bound variables, inverse eta as appropriate.

better algorithm (incorporated DEPTH_CONV):
entry point with no current argument:
  perform inverse eta then recurse on rator with introduce variable as current argument
entry point with a current argument s:
  if tm = BIND m f then
    m' <- recurse on m with no current argument
    ensure f is of the form (\v s'. g) by inverse eta if necessary
    g' <- recurse on g with current argument s'
    return BIND m (\v s'. g') s
  else if tm = IGNORE_BIND m1 m2 then
    m1' <- recurse on m with no current argument
    ensure m2 is of the form (\s'. g) by inverse eta if necessary
    g' <- recurse on g with current argument s'
    return IGNORE_BIND m1' (\s'. g') s
  else if tm = (λx. f) then return f s
  else if tm = x then return x s
  else if tm = con then return con s
  else if tm = (rator rand) then
    ??????

keep track of the current state argument
if initially there is no state argument, do an inverse eta to get one, then recurse on rator and current argument
if rator is a BIND form, do something special:
  BIND m f s - recurse on m with no current argument
               make sure f is of the form (\v s. g) by inverse eta if necessary
               recurse on g with current argument s
otherwise, remove the argument and push it into the recursion on the rator instead


test on this:
`plen M = do
  (λs. STATE_OPTION_LIFT (OPTION_GUARD (∃ls. list_of_List embed_Term s M ls)) s) ;
  b <- EmptyListOfTerms M ;
  if ¬b then do
    M <- TailOfListOfTerms M ;
    n <- plen M ;
    return (n + 1)
  od else return 0
od`

aka:
`plen M =
 STATE_OPTION_IGNORE_BIND
 (λs. STATE_OPTION_LIFT (OPTION_GUARD (∃ls. list_of_List embed_Term s M ls)) s)
 (STATE_OPTION_BIND (EmptyListOfTerms M)
   (λb. if ¬b then
          STATE_OPTION_BIND (TailOfListOfTerms M)
          (λM. STATE_OPTION_BIND (plen M)
               (λn. STATE_OPTION_UNIT (n + 1)))
        else STATE_OPTION_UNIT 0))`

algorithm should give:
`plen M =
\s. STATE_OPTION_IGNORE_BIND
 (λs. STATE_OPTION_LIFT (OPTION_GUARD (∃ls. list_of_List embed_Term s M ls)) s)
 (\s.
  STATE_OPTION_BIND (EmptyListOfTerms M)
   (λb. \s.
        (if ¬b then
           \s.
           STATE_OPTION_BIND (TailOfListOfTerms M)
           (λM. \s.
                STATE_OPTION_BIND (plen M)
                (λn. \s. STATE_OPTION_UNIT (n + 1) s)
                s)
           s
         else STATE_OPTION_UNIT 0)
        s)
  s)
s`
but this isn't good enough!
need to BETA_RULE through the if !
*)

(*
fun strip_type ty = let
  val (dom,rng) = dom_rng ty
in dom::(strip_type rng)
end handle HOL_ERR _ => [ty]

val arity = let
  fun loop n ty = let
    val (dom,rng) = dom_rng ty
  in loop (n+1) rng end
  handle HOL_ERR _ => n
in loop 0 end
*)

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

(*
fun add_state_arg_conv x tm = let
  val call = lhs tm
  val (f,args) = strip_comb call
  fun uneta_f tm = let
    val (f',_) = strip_comb tm
    val _ = assert (equal f) f'
  in UNETA_CONV x end tm
in
  (RAND_CONV (DEPTH_CONV uneta_f)) THENC
  (X_FUN_EQ_CONV x)
end tm
*)

(*
fun basename s = let open Substring Char in
  case !Globals.priming of
    NONE => string (dropr (equal #"'") (full s))
  | SOME u => let
      val b = dropr isDigit (full s)
    in
      if isSuffix u b then let
        val bz = size b
      in if String.size s <> bz then
           string (slice (b, 0, SOME (bz - String.size u)))
         else s
      end else s
    end
end
*)

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
  val (t,_) = parse_absyn (Parse.Absyn q)
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

(*
why does this fail?
val sfoo_defn = Hol_defn "sfoo"
`sfoo s = STATE_OPTION_BIND STATE_OPTION_GET
          (λs1 s. STATE_OPTION_BIND STATE_OPTION_GET
          (λs2 s. STATE_OPTION_IGNORE_BIND
                (\s. if s1 = s2 then STATE_OPTION_UNIT () s else sfoo s)
                (STATE_OPTION_UNIT ()) s) s) s`
*)

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
srw_tac [][combinTheory.APPLY_UPDATE_THM,OPTION_GUARD_def]);
val (ignore_rec_def,ignore_rec_ind) = (unconv_def s ## unconv_ind s) p;

(*
Ideally, TFL would automatically try inverse eta to match congruences itself!

  val conv = DEPTH_CONV (uneta_bind_conv x) THENC
             PURE_REWRITE_CONV [APPLY_COND_THM] THENC
             (X_FUN_EQ_CONV x) THENC
             QUANT_CONV (RAND_CONV LIST_BETA_CONV)
Parse.hide"plen"
((DEPTH_CONV (uneta_bind_conv s) THENC
  PURE_REWRITE_CONV [APPLY_COND_THM] THENC
  (X_FUN_EQ_CONV s) THENC
  QUANT_CONV (RAND_CONV LIST_BETA_CONV)) o Term ) `
  plen M = do
    (λs. STATE_OPTION_LIFT (OPTION_GUARD (wfstate s ∧ ∃ls. list_of_List embed_Term s M ls)) s) ;
    b <- EmptyListOfTerms M ;
    if ¬ b then do
      M <- TailOfListOfTerms M ;
      n <- plen M ;
      return (n + 1)
    od else return 0
  od`
Parse.reveal"plen"

val plen_defn = Defn.Hol_defn "plen"
`plen M s =
 STATE_OPTION_IGNORE_BIND
 (λs. STATE_OPTION_LIFT (OPTION_GUARD (wfstate s ∧ ∃ls. list_of_List embed_Term s M ls))
      s)
 (λs. STATE_OPTION_BIND
      (EmptyListOfTerms M)
      (λb s. if ¬ b
             then STATE_OPTION_BIND
                  (TailOfListOfTerms M)
                  (λM s. STATE_OPTION_BIND
                         (plen M)
                         (λn s. STATE_OPTION_UNIT (n+1) s)
                         s)
                  s
             else (STATE_OPTION_UNIT 0 s))
      s)
 s`
STATE_OPTION_BIND_cong
val plen_defn = Defn.Hol_defn "plen"
`plen M = \s.
 STATE_OPTION_IGNORE_BIND
 (λs. STATE_OPTION_LIFT (OPTION_GUARD (wfstate s ∧ ∃ls. list_of_List embed_Term s M ls))
      s)
 (λs. STATE_OPTION_BIND
      (EmptyListOfTerms M)
      (λb s. if ¬ b
             then STATE_OPTION_BIND
                  (TailOfListOfTerms M)
                  (λM s. STATE_OPTION_BIND
                         (plen M)
                         (λn s. STATE_OPTION_UNIT (n+1) s)
                         s)
                  s
             else (STATE_OPTION_UNIT 0 s))
      s)
 s`
*)

val s = ``s:state``;
(*
val _ = delete_const "plen";
val _ = delete_binding "plen_curried_def";
val _ = delete_binding "plen_tupled_primitive_def";
*)
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
srw_tac [boolSimps.DNF_ss][pairTheory.FORALL_PROD] >>
srw_tac [][STATE_OPTION_LIFT_def,OPTION_GUARD_def] >>
qho_match_abbrev_tac `?R. WF R ∧ !l1 s0 s1 l2 s2. P s0 s1 s2 l2 l1 ⇒ R l2 l1` >>
reverse (WF_REL_TAC `λl1 l2. ∃s0 s1 s2. P s0 s1 s2 l1 l2`) >-
  srw_tac [SatisfySimps.SATISFY_ss][] >>
srw_tac [boolSimps.DNF_ss][Abbr`P`] >>

match_mp_tac relationTheory.WF_SUBSET >>

match_mp_tac relationTheory.WF_inv_image
WF_REL_TAC `measure (λl2. LEAST n. (∃s0 s1 s2 l1. P s0 s1 s2 l1 l2) ∧ (∃ls. list_of_List embed_Term s0 l2 ls ∧ (n = LENGTH ls)))` >>
srw_tac [][Abbr`P`] >>
numLib.LEAST_ELIM_TAC >>
srw_tac [][] >- 

WF_REL_TAC `measure (λM. LEAST n. ∃s ls. wfstate s ∧ list_of_List embed_Term s M ls ∧ (n = LENGTH ls))` >>
srw_tac [][] >>
numLib.LEAST_ELIM_TAC >>
srw_tac [][] >- metis_tac [] >>
fsrw_tac [boolSimps.DNF_ss][] >>
`¬ (LENGTH ls < LENGTH ls')` by METIS_TAC [] >>
numLib.LEAST_ELIM_TAC >>
srw_tac [][] >- (
  fsrw_tac [][TailOfList_def,STATE_OPTION_BIND_def,pairTheory.UNCURRY] >>
  Cases_on `M` >> fsrw_tac [][raw_lookup_def,STATE_OPTION_IGNORE_BIND_def] >>
  fsrw_tac [][STATE_OPTION_UNIT_def] >>
  METIS_TAC [] ) >>
fsrw_tac [boolSimps.DNF_ss][] >>
ptypesTheory.TailOfList_TL
would want some TailOfList correctness results here to make things easier...

)
val (plen_def,plen_ind) =
W (curry op ##) (unconv_rule state_option_consts) p;

(* You can then use save_thm to save the right form of the definition and
induction. There are no extra flags or tags necessary to completely emulate
Define, right? *)

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
