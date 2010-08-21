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

val _ = Hol_datatype `value
= injectVariable of Variable
| injectSetOfVariables of SetOfVariables
| injectTerm of Term
| injectTermAuxList of Term AuxList
| injectTermList of Term List
| injectMultiequation of Multiequation
| injectMultiequationAuxList of Multiequation AuxList
| injectMultiequationList of Multiequation List
| injectTempMultiequation of TempMultiequation
| injectTempMultiequationAuxList of TempMultiequation AuxList
| injectTempMultiequationList of TempMultiequation List
| injectSystem of System`;

val ejectVariable_def = Define `ejectVariable (injectVariable a) = a`;
val ejectSetOfVariables_def = Define `ejectSetOfVariables (injectSetOfVariables a) = a`;
val ejectTerm_def = Define `ejectTerm (injectTerm a) = a`;
val ejectTermAuxList_def = Define `ejectTermAuxList (injectTermAuxList a) = a`;
val ejectTermList_def = Define `ejectTermList (injectTermList a) = a`;
val ejectMultiequation_def = Define `ejectMultiequation (injectMultiequation a) = a`;
val ejectMultiequationAuxList_def = Define `ejectMultiequationAuxList (injectMultiequationAuxList a) = a`;
val ejectMultiequationList_def = Define `ejectMultiequationList (injectMultiequationList a) = a`;
val ejectTempMultiequation_def = Define `ejectTempMultiequation (injectTempMultiequation a) = a`;
val ejectTempMultiequationAuxList_def = Define `ejectTempMultiequationAuxList (injectTempMultiequationAuxList a) = a`;
val ejectTempMultiequationList_def = Define `ejectTempMultiequationList (injectTempMultiequationList a) = a`;
val ejectSystem_def = Define `ejectSystem (injectSystem a) = a`;

val _ = type_abbrev("store", ``:num |-> value``);

val raw_lookup_def = Define` raw_lookup n = (λs:store. (FLOOKUP s n, s))`;
val make_lookup_def = Define`
  (make_lookup (eject:value -> 'a) (addr n : 'a ptr) = OPTIONT_BIND (raw_lookup n) (λv. OPTIONT_UNIT (eject v))) ∧
  (make_lookup eject ptr = OPTIONT_FAIL)`;
val _ = type_abbrev("lookup", ``:'a ptr -> store -> 'a option # store``);

val raw_assign_def = Define`raw_assign n v = (λs:store. ((), s |+ (n,v)))`;
val make_assign_def = Define`
  (make_assign (inject:'a -> value) (addr n : 'a ptr) v = do raw_assign n (inject v) ; return (addr n) od) ∧
  (make_assign inject ptr v = return ptr)`;
val _ = type_abbrev("assign", ``:'a ptr -> 'a -> store -> 'a ptr # store``);

val _ = Hol_datatype `helpers = <| lookup : 'a lookup ; lookupList : 'a List lookup ; lookupAuxList : 'a AuxList lookup ;
                                   assign : 'a assign ; assignList : 'a List assign ; assignAuxList : 'a AuxList assign |>`;

val dispose_def = Define`
  (dispose (addr n) = (λs:store. ((), s \\ n))) ∧
  (dispose _ = return ())`;

val first_free_def = Define`
  first_free = λs:store. (addr (LEAST n. n ∉ FDOM s), s)`;

val new_def = Define`new assign v = do ptr <- first_free ; assign ptr v od`;

val CreateList_def = Define`
  CreateList h =
  do l <- new h.assignAuxList (AuxList (pnil ARB) (pnil ARB)) ;
     s <- new h.assignList (List l l) ;
     return s
  od`;

val HeadOfList_def = Define`
  HeadOfList h (s:'a List ptr) =
  do s' <- h.lookupList s ;
     s'first' <- h.lookupAuxList s'.first ;
     return s'first'.head
  od`;

val EmptyList_def = Define`
  EmptyList h (s : 'a List ptr) =
  do s' <- h.lookupList s ;
     return (s'.first = s'.last)
  od`;

val TailOfList_def = Define`
  TailOfList h (s : 'a List ptr) =
  do s' <- h.lookupList s ;
     l <- return s'.first ;
     l' <- h.lookupAuxList l;
     h.assignList s (List l'.tail s'.last) ;
     dispose l ;
     return s
  od`;

val AddToEndOfList_def = Define`
  AddToEndOfList h (t : 'a ptr) (s : 'a List ptr) =
  do l <- new h.assignAuxList (AuxList (pnil ARB) (pnil ARB)) ;
     s' <- h.lookupList s ;
     h.assignAuxList s'.last (AuxList t l) ;
     h.assignList s (List s'.first l) ;
     return s
  od`;

val AddToFrontOfList_def = Define`
  AddToFrontOfList h (t : 'a ptr) (s : 'a List ptr) =
  do s' <- h.lookupList s ;
     l <- new h.assignAuxList (AuxList t s'.first) ;
     h.assignList s (List l s'.last) ;
     return s
  od`;

val AppendLists_def = Define`
  AppendLists h (t1 : 'a List ptr) (t2 : 'a List ptr) =
  do t2' <- h.lookupList t2 ;
     if t2'.first ≠ t2'.last then
        do t1' <- h.lookupList t1 ;
           t2'first' <- h.lookupAuxList t2'.first ;
           h.assignAuxList t1'.last (AuxList t2'first'.head t2'first'.tail) ;
           h.assignList t1 (List t1'.first t2'.last) ;
           return ()
        od
     else return () ;
     dispose t2'.first ;
     dispose t2 ;
     return t1
  od`;

val OfTerms_def = Define`
  OfTerms = <|
  lookup := make_lookup ejectTerm ; lookupList := make_lookup ejectTermList ; lookupAuxList := make_lookup ejectTermAuxList ;
  assign := make_assign injectTerm ; assignList := make_assign injectTermList ; assignAuxList := make_assign injectTermAuxList |>`;

val (corresponding_list_rules, corresponding_list_ind, corresponding_list_cases) = Hol_reln`
  (((EmptyList h ptr) s = (SOME T, s')) ⇒ corresponding_list ptr s []) ∧
  (((do hd <- HeadOfList h ptr ;
        tl <- TailOfList h ptr ;
        (hd':'a) <- h.lookup hd ;
        return (hd',tl)
     od) s = (SOME (hd',tl),s')) ∧
   corresponding_list tl s' tl' ⇒
   corresponding_list ptr s (hd'::tl'))`;

val _ = export_theory ()
