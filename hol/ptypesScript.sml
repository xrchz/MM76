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

val dispose_def = Define`
  (dispose (addr n) = (λs:store. ((), s \\ n))) ∧
  (dispose _ = return ())`;

val first_free_def = Define`
  first_free = λs:store. (addr (LEAST n. n ∉ FDOM s), s)`;

val make_new_def = Define`make_new assign v = do ptr <- first_free ; assign ptr v od`;
val _ = type_abbrev("new", ``:'a -> store -> 'a ptr # store``);

val CreateList_def = Define`
  CreateList (newAuxList : 'a AuxList new) (newList : 'a List new) =
  do l <- newAuxList (AuxList (pnil ARB) (pnil ARB)) ;
     s <- newList (List l l) ;
     return s
  od`;

val HeadOfList_def = Define`
  HeadOfList (lookupList : 'a List lookup) (lookupAuxList : 'a AuxList lookup) (s:'a List ptr) =
  do s' <- lookupList s ;
     s'first' <- lookupAuxList s'.first ;
     return s'first'.head
  od`;

val EmptyList_def = Define`
  EmptyList (lookup : 'a List lookup) (s : 'a List ptr) =
  do s' <- lookup s ;
     return (s'.first = s'.last)
  od`;

val TailOfList_def = Define`
  TailOfList (lookupList : 'a List lookup) (lookupAuxList : 'a AuxList lookup) (assign : 'a List assign) (s : 'a List ptr) =
  do s' <- lookupList s ;
     l <- return s'.first ;
     l' <- lookupAuxList l;
     assign s (List l'.tail s'.last) ;
     dispose l ;
     return s
  od`;

val AddToEndOfList_def = Define`
  AddToEndOfList (newAuxList : 'a AuxList new) (lookupList : 'a List lookup) (assignAuxList : 'a AuxList assign) (assignList : 'a List assign) (t : 'a ptr) (s : 'a List ptr) =
  do l <- newAuxList (AuxList (pnil ARB) (pnil ARB)) ;
     s' <- lookupList s ;
     assignAuxList s'.last (AuxList t l) ;
     assignList s (List s'.first l) ;
     return s
  od`;

val AddToFrontOfList_def = Define`
  AddToFrontOfList (lookupList : 'a List lookup) (newAuxList : 'a AuxList new) (assign : 'a List assign) (t : 'a ptr) (s : 'a List ptr) =
  do s' <- lookupList s ;
     l <- newAuxList (AuxList t s'.first) ;
     assign s (List l s'.last) ;
     return s
  od`;

val AppendLists_def = Define`
  AppendLists (lookupList : 'a List lookup) (lookupAuxList : 'a AuxList lookup) (assignList : 'a List assign) (assignAuxList : 'a AuxList assign) (t1 : 'a List ptr) (t2 : 'a List ptr) =
  do t2' <- lookupList t2 ;
     if t2'.first ≠ t2'.last then
        do t1' <- lookupList t1 ;
           t2'first' <- lookupAuxList t2'.first ;
           assignAuxList t1'.last (AuxList t2'first'.head t2'first'.tail) ;
           assignList t1 (List t1'.first t2'.last) ;
           return ()
        od
     else return () ;
     dispose t2'.first ;
     dispose t2 ;
     return t1
  od`;

val List_to_list_def = Define`
  List_to_list (lookup : 'a lookup) (lookupList : 'a List lookup) (lookupAuxList : 'a AuxList lookup) (assignList : 'a List assign) (ptr : 'a List ptr) =
  do empty <- EmptyList lookupList ptr ;
     if empty then return []
     else do hd <- HeadOfList lookupList lookupAuxList ptr ;
             tl <- TailOfList lookupList lookupAuxList assignList ptr ;
             hd' <- lookup hd ;
             tl' <- List_to_list lookup lookupList lookupAuxList assignList tl ;
             return (hd'::tl')
          od
  od`;

val CreateListOfTerms_def = Define`
  CreateListOfTerms = CreateList (make_new (make_assign injectTermAuxList)) (make_new (make_assign injectTermList))`;
val HeadOfListOfTerms_def = Define`
  HeadOfListOfTerms = HeadOfList (make_lookup ejectTermList) (make_lookup ejectTermAuxList)`;
val EmptyListOfTerms_def = Define`
  EmptyListOfTerms = EmptyList (make_lookup ejectTermList)`;
val TailOfListOfTerms_def = Define`
  TailOfListOfTerms = TailOfList (make_lookup ejectTermList) (make_lookup ejectTermAuxList) (make_assign injectTermList)`;
val AddToEndOfListOfTerms_def = Define`
  AddToEndOfListOfTerms = AddToEndOfList (make_new (make_assign injectTermAuxList)) (make_lookup ejectTermList) (make_assign injectTermAuxList) (make_assign injectTermList)`;
val AddToFrontOfListOfTerms_def = Define`
  AddToFrontOfListOfTerms = AddToFrontOfList (make_lookup ejectTermList) (make_new (make_assign injectTermAuxList)) (make_assign injectTermList)`;

val _ = export_theory ()
