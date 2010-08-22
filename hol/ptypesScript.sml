open HolKernel bossLib boolLib Parse optionTheory stringTheory finite_mapTheory sumTheory state_transformerTheory monadsyntax lcsymtacs

val _ = new_theory "ptypes"

val OPTIONT_FAIL_def = Define`
  OPTIONT_FAIL = UNIT NONE`;

val OPTIONT_UNIT_def = Define`
  OPTIONT_UNIT a = UNIT (SOME a)`;

val OPTIONT_LIFT_def = Define`
  OPTIONT_LIFT m = BIND m OPTIONT_UNIT`;

val OPTIONT_BIND_def = Define`
  OPTIONT_BIND m f = BIND m (λa. case a of NONE -> UNIT NONE || SOME a' -> f a')`;

val _ = overload_on("monad_bind", ``OPTIONT_BIND``);
val _ = overload_on("monad_bind", ``BIND``);
val _ = overload_on("return", ``OPTIONT_UNIT``);
val _ = overload_on("return", ``UNIT``);

val _ = type_abbrev ("varname",``:string``);
val _ = type_abbrev ("funname",``:string``);
val _ = Hol_datatype `ptr = pnil of 'a | addr of num`;

val _ = Hol_datatype `AuxList = <| head : 'a ptr ; tail : AuxList ptr |>`;
val _ = Hol_datatype `List = <| first : 'a AuxList ptr ; last : 'a AuxList ptr |> ` ;

val _ = Hol_datatype `
  SetOfVariables = <| counter : num ; varnumb : num ; vars : Variable List ptr |> ;
  Multiequation = <| erased : bool ; S : SetOfVariables ptr ; M : (VarTerm + FunTerm) List ptr |> ;
  Variable = <| name : varname ; m : Multiequation ptr |> ;
  FunTerm = <| fsymb : funname ; args : (VarTerm + FunTerm) List ptr |> ;
  VarTerm = <| v : Variable ptr |> ` ;
val _ = type_abbrev("Term", ``:(VarTerm + FunTerm)``);
val _ = Hol_datatype `TempMultiequation = <| S : Term List ptr ; M : Term List ptr |>`;
val _ = Hol_datatype `System = <| T : Multiequation List ptr ; U : Multiequation List ptr |>`;

val _ = type_abbrev ("value",
``:Variable
 + SetOfVariables
 + Term
 + Term AuxList
 + Term List
 + Multiequation
 + Multiequation AuxList
 + Multiequation List
 + TempMultiequation
 + TempMultiequation AuxList
 + TempMultiequation List
 + System``);

val _ = type_abbrev("store", ``:num |-> value``);

val embed_def = Define`
  embed = @p. ∀x. (SND p) ((FST p) x : value) = x`
val _ = overload_on ("inject", ``FST embed``);
val _ = overload_on ("eject", ``SND embed``);

val embed_Term_thm = Q.store_thm(
"embed_Term_thm",
`eject (inject (v:Term)) = v`,
srw_tac [][embed_def] >>
SELECT_ELIM_TAC >> srw_tac [][] >>
qexists_tac `(INR o INR o INL, OUTL o OUTR o OUTR)` >>
srw_tac [][]);

val embed_Term_List_thm = Q.store_thm(
"embed_Term_List_thm",
`eject (inject (v:Term List)) = v`,
srw_tac [][embed_def] >>
SELECT_ELIM_TAC >> srw_tac [][] >>
qexists_tac `(INR o INR o INR o INR o INL, OUTL o OUTR o OUTR o OUTR o OUTR)` >>
srw_tac [][]);

val lookup_def = Define`
  (lookup (addr n : 'a ptr) = OPTIONT_BIND (λs. (FLOOKUP s n, s)) (λv. OPTIONT_UNIT (eject:value->'a v))) ∧
  (lookup pnil_ = OPTIONT_FAIL)`;

val assign_def = Define`
  (assign (addr n : 'a ptr) v = (λs:store. ((), s |+ (n, inject:'a->value v)))) ∧
  (assign pnil_ v = return ())`;

val dispose_def = Define`
  (dispose (addr n) = (λs:store. ((), s \\ n))) ∧
  (dispose _ = return ())`;

val free_addr_def = Define`
  free_addr = λs:store. (addr (@n. n ∉ FDOM s), s)`;

val new_def = Define`new v = do ptr <- free_addr ; assign ptr v ; return ptr od`;

val CreateList_def = Define`
  CreateList =
  do l <- new (AuxList (pnil ARB) (pnil ARB)) ;
     s <- new (List l l) ;
     return s
  od`;

val HeadOfList_def = Define`
  HeadOfList s =
  do s' <- lookup s ;
     s'first' <- lookup s'.first ;
     return s'first'.head
  od`;

val EmptyList_def = Define`
  EmptyList s =
  do s' <- lookup s ;
     return (s'.first = s'.last)
  od`;

val TailOfList_def = Define`
  TailOfList s =
  do s' <- lookup s ;
     l <- return s'.first ;
     l' <- lookup l;
     assign s (List l'.tail s'.last) ;
     dispose l ;
     return s
  od`;

val AddToEndOfList_def = Define`
  AddToEndOfList t s =
  do l <- new (AuxList (pnil ARB) (pnil ARB)) ;
     s' <- lookup s ;
     assign s'.last (AuxList t l) ;
     assign s (List s'.first l) ;
     return s
  od`;

val AddToFrontOfList_def = Define`
  AddToFrontOfList t s =
  do s' <- lookup s ;
     l <- new (AuxList t s'.first) ;
     assign s (List l s'.last) ;
     return s
  od`;

val AppendLists_def = Define`
  AppendLists t1 t2 =
  do t2' <- lookup t2 ;
     if t2'.first ≠ t2'.last then
        do t1' <- lookup t1 ;
           t2'first' <- lookup t2'.first ;
           assign t1'.last (AuxList t2'first'.head t2'first'.tail) ;
           assign t1 (List t1'.first t2'.last) ;
           return ()
        od
     else return () ;
     dispose t2'.first ;
     dispose t2 ;
     return t1
  od`;

val (corresponding_list_rules, corresponding_list_ind, corresponding_list_cases) = Hol_reln`
  (((EmptyList ptr) s = (SOME T, s')) ⇒ corresponding_list ptr s []) ∧
  (((do hd <- HeadOfList ptr ;
        tl <- TailOfList ptr ;
        (hd':'a) <- lookup hd ;
        return (hd',tl)
     od) s = (SOME (hd',tl),s')) ∧
   corresponding_list tl s' tl' ⇒
   corresponding_list ptr s (hd'::tl'))`;

val NOTIN_INFINITE_FDOM_exists = Q.store_thm(
"NOTIN_INFINITE_FDOM_exists",
`INFINITE (UNIV : 'a set) ⇒ ∃x. x ∉ (FDOM f : 'a set)`,
PROVE_TAC [pred_setTheory.IN_INFINITE_NOT_FINITE,FDOM_FINITE]);
val _ = export_rewrites["NOTIN_INFINITE_FDOM_exists"];

val free_addr_elim_thm = Q.store_thm(
"free_addr_elim_thm",
`∀P s. (∀n. n ∉ FDOM s ⇒ P (addr n,s)) ⇒ P (free_addr s)`,
srw_tac [][free_addr_def] >>
SELECT_ELIM_TAC >>
srw_tac [][]);

val CreateList_creates_empty = Q.store_thm(
"CreateList_creates_empty",
`(∀v. eject (inject (v:'a List)) = v) ⇒ (CreateList s0 = (ptr : 'a List ptr, s)) ⇒ corresponding_list ptr s []`,
strip_tac >>
simp_tac (srw_ss()) [CreateList_def,new_def,BIND_DEF] >>
qho_match_abbrev_tac `(UNCURRY f (UNCURRY g (free_addr s0)) = (ptr,s)) ⇒ X` >>
Q.ABBREV_TAC `P = (λx. (UNCURRY f (UNCURRY g x) = (ptr,s)) ⇒ X)` >>
qsuff_tac `P (free_addr s0)` >- srw_tac [][Abbr`P`] >>
ho_match_mp_tac free_addr_elim_thm >>
srw_tac [][Abbr`P`,Abbr`g`,Abbr`f`,IGNORE_BIND_DEF,BIND_DEF,UNIT_DEF,assign_def,pairTheory.UNCURRY,Abbr`X`] >>
Q.ABBREV_TAC `P = (λx. corresponding_list (FST x) (SND (assign (FST x) (List (addr n) (addr n)) (SND x))) [])`  >>
qsuff_tac `P (free_addr (s0 |+ (n,inject (AuxList (pnil (ARB:'a)) (pnil ARB)))))` >- srw_tac [][Abbr`P`] >>
ho_match_mp_tac free_addr_elim_thm >>
srw_tac [][Abbr`P`,assign_def,Once corresponding_list_cases,EmptyList_def,OPTIONT_BIND_def,BIND_DEF,lookup_def,OPTIONT_UNIT_def,UNIT_DEF,FLOOKUP_UPDATE]);

val _ = export_theory ()
