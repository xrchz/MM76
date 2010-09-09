open HolKernel bossLib boolLib Parse stringTheory finite_mapTheory state_optionTheory monadsyntax

val _ = new_theory "ptypes_definitions"

val _ = inferior_overload_on("=+", ``λk v f. f |+ (k,v)``);
val _ = overload_on("|+", ``λf kv. f |+ kv``);

val _ = Hol_datatype `ptr = addr of 'a itself => num`;
val num_to_ptr_def = Define `num_to_ptr n = addr (:'a) n`;
val ptr_to_num_def = Define `ptr_to_num (addr _ n) = n`;
val _ = export_rewrites ["num_to_ptr_def","ptr_to_num_def"];
val _ = overload_on("pnil",``addr (:'a) 0``);

val _ = type_abbrev ("varname",``:string``);
val _ = type_abbrev ("funname",``:string``);
val _ = Hol_datatype `AuxList = <| head : 'a ptr ; tail : AuxList ptr |>`;
val _ = Hol_datatype `List = <| first : 'a AuxList ptr ; last : 'a AuxList ptr |>` ;

val _ = Hol_datatype`
  SetOfVariables = <| counter : num ; varnumb : num ; vars : Variable List ptr |> ;
  Multiequation = <| erased : bool ; S : SetOfVariables ptr ; M : (VarTerm + FunTerm) List ptr |> ;
  Variable = <| name : varname ; m : Multiequation ptr |> ;
  FunTerm = <| fsymb : funname ; args : (VarTerm + FunTerm) List ptr |> ;
  VarTerm = <| v : Variable ptr |>`;
val _ = type_abbrev("Term", ``:(VarTerm + FunTerm)``);
val _ = Hol_datatype `TempMultiequation = <| S : Term List ptr ; M : Term List ptr |>`;
val _ = Hol_datatype `System = <| T : Multiequation List ptr ; U : Multiequation List ptr |>`;

val _ = Hol_datatype `
value = Variable_value of varname => num
      | SetOfVariables_value of num => num => num
      | Term_value of num + funname # num
      | Multiequation_value of bool => num => num
      | TempMultiequation_value of num => num
      | System_value of num => num
      | AuxList_value of num => num
      | List_value of num => num`;

val _ = type_abbrev("store", ``:num |-> value``);

val _ = Hol_datatype `
type = Variable_type
     | SetOfVariables_type
     | Term_type
     | Multiequation_type
     | TempMultiequation_type
     | System_type
     | AuxList_type of type
     | List_type of type`;

val _ = Hol_datatype `state = <| store : store ; cell_type : num -> type |>`;

val (has_type_rules, has_type_ind, has_type_cases) = Hol_reln`
  (typed_cell s c m ∧ (m ≠ 0 ⇒ (s.cell_type m = Multiequation_type)) ⇒
   has_type s c (Variable_value _ m) Variable_type) ∧
  (typed_cell s c m ∧ (m ≠ 0 ⇒ (s.cell_type m = List_type Variable_type)) ⇒
   has_type s c (SetOfVariables_value _ _ m) SetOfVariables_type) ∧
  (typed_cell s c m ∧ (m ≠ 0 ⇒ (s.cell_type m = Variable_type)) ⇒
   has_type s c (Term_value (INL m)) Term_type) ∧
  (typed_cell s c m ∧ (m ≠ 0 ⇒ (s.cell_type m = List_type Term_type)) ⇒
   has_type s c (Term_value (INR (_,m))) Term_type) ∧
  (typed_cell s c m1 ∧ (m1 ≠ 0 ⇒ (s.cell_type m1 = SetOfVariables_type)) ∧
   typed_cell s c m2 ∧ (m2 ≠ 0 ⇒ (s.cell_type m2 = List_type Term_type)) ⇒
   has_type s c (Multiequation_value _ m1 m2) Multiequation_type) ∧
  (typed_cell s c m1 ∧ (m1 ≠ 0 ⇒ (s.cell_type m1 = List_type Term_type)) ∧
   typed_cell s c m2 ∧ (m2 ≠ 0 ⇒ (s.cell_type m2 = List_type Term_type)) ⇒
   has_type s c (TempMultiequation_value m1 m2) TempMultiequation_type) ∧
  (typed_cell s c m1 ∧ (m1 ≠ 0 ⇒ (s.cell_type m1 = List_type Multiequation_type)) ∧
   typed_cell s c m2 ∧ (m2 ≠ 0 ⇒ (s.cell_type m2 = List_type Multiequation_type)) ⇒
   has_type s c (System_value m1 m2) System_type) ∧
  (typed_cell s c m1 ∧ (m1 ≠ 0 ⇒ (s.cell_type m1 = AuxList_type type)) ∧
   typed_cell s c m2 ∧ (m2 ≠ 0 ⇒ (s.cell_type m2 = AuxList_type type)) ⇒
   has_type s c (List_value m1 m2) (List_type type)) ∧
  (typed_cell s c m1 ∧ (m1 ≠ 0 ⇒ (s.cell_type m1 = type)) ∧
   typed_cell s c m2 ∧ (m2 ≠ 0 ⇒ (s.cell_type m2 = AuxList_type type)) ⇒
   has_type s c (AuxList_value m1 m2) (AuxList_type type)) ∧
  (m ∈ c ∧ m ∈ FDOM s.store ⇒ typed_cell s c m) ∧
  (0 ∉ FDOM s.store ⇒ typed_cell s c 0) ∧
  ((FLOOKUP s.store n = SOME v) ∧ has_type s (n INSERT c) v (s.cell_type n) ⇒ typed_cell s c n)`;

val typed_state_def = Define`
   typed_state s = ∀n. n ∈ FDOM s.store ⇒ typed_cell s {} n`;

val wfstate_def = Define`
  wfstate s = typed_state s ∧ 0 ∉ FDOM s.store`;

val _ = type_abbrev("inject", ``:'a -> value``);
val _ = type_abbrev("project", ``:value -> 'a option``);
val _ = Hol_datatype`embed = <| type : type ; inject : 'a inject ; project : 'a project |>`;
val inject_Variable_def = Define`
  inject_Variable a = Variable_value a.name (ptr_to_num a.m)`;
val project_Variable_def = Define`
  (project_Variable (Variable_value name vars) = SOME (Variable name (num_to_ptr vars))) ∧
  (project_Variable _ = NONE)`;
val _ = overload_on("embed_Variable",``embed Variable_type inject_Variable project_Variable : Variable embed``);
val inject_SetOfVariables_def = Define`
  inject_SetOfVariables a = SetOfVariables_value a.counter a.varnumb (ptr_to_num a.vars)`;
val project_SetOfVariables_def = Define`
  (project_SetOfVariables (SetOfVariables_value counter varnumb vars) = SOME (SetOfVariables counter varnumb (num_to_ptr vars))) ∧
  (project_SetOfVariables _ = NONE)`;
val _ = overload_on("embed_SetOfVariables",``embed SetOfVariables_type inject_SetOfVariables project_SetOfVariables : SetOfVariables embed``);
val inject_Term_def = Define`
  (inject_Term (INL al) = Term_value (INL (ptr_to_num al.v))) ∧
  (inject_Term (INR ar) = Term_value (INR (ar.fsymb, (ptr_to_num ar.args))))`;
val project_Term_def = Define`
  (project_Term (Term_value (INL v)) = SOME (INL (VarTerm (num_to_ptr v)))) ∧
  (project_Term (Term_value (INR (fsymb, args))) = SOME (INR (FunTerm fsymb (num_to_ptr args)))) ∧
  (project_Term _ = NONE)`;
val _ = overload_on("embed_Term",``embed Term_type inject_Term project_Term : Term embed``);
val inject_Multiequation_def = Define`
  inject_Multiequation a = Multiequation_value a.erased (ptr_to_num a.S) (ptr_to_num a.M)`;
val project_Multiequation_def = Define`
  (project_Multiequation (Multiequation_value erased S_ M) = SOME (Multiequation erased (num_to_ptr S_) (num_to_ptr M))) ∧
  (project_Multiequation _ = NONE)`;
val _ = overload_on("embed_Multiequation",``embed Multiequation_type inject_Multiequation project_Multiequation : Multiequation embed``);
val inject_TempMultiequation_def = Define`
  inject_TempMultiequation a = TempMultiequation_value (ptr_to_num a.S) (ptr_to_num a.M)`;
val project_TempMultiequation_def = Define`
  (project_TempMultiequation (TempMultiequation_value S_ M) = SOME (TempMultiequation (num_to_ptr S_) (num_to_ptr M))) ∧
  (project_TempMultiequation _ = NONE)`;
val _ = overload_on("embed_TempMultiequation",``embed TempMultiequation_type inject_TempMultiequation project_TempMultiequation : TempMultiequation embed``);
val inject_System_def = Define`
  inject_System a = System_value (ptr_to_num a.T) (ptr_to_num a.U)`;
val project_System_def = Define`
  (project_System (System_value T_ U) = SOME (System (num_to_ptr T_) (num_to_ptr U))) ∧
  (project_System _ = NONE)`;
val _ = overload_on("embed_System",``embed System_type inject_System project_System : System embed``);
val inject_AuxList_def = Define`
  inject_AuxList a = AuxList_value (ptr_to_num a.head) (ptr_to_num a.tail)`;
val project_AuxList_def = Define`
  (project_AuxList (AuxList_value head tail) = SOME (AuxList (num_to_ptr head) (num_to_ptr tail))) ∧
  (project_AuxList _ = NONE)`;
val _ = overload_on("embed_AuxList", ``λemb:'a embed. embed (AuxList_type emb.type) inject_AuxList project_AuxList : 'a AuxList embed``);
val inject_List_def = Define`
  inject_List a = List_value (ptr_to_num a.first) (ptr_to_num a.last)`;
val project_List_def = Define`
  (project_List (List_value first last) = SOME (List (num_to_ptr first) (num_to_ptr last))) ∧
  (project_List _ = NONE)`;
val _ = overload_on("embed_List", ``λemb:'a embed. embed (List_type emb.type) inject_List project_List : 'a List embed``);
val _ = export_rewrites["inject_Variable_def","project_Variable_def","inject_SetOfVariables_def","project_SetOfVariables_def","inject_Term_def","project_Term_def","inject_Multiequation_def","project_Multiequation_def","inject_TempMultiequation_def","project_TempMultiequation_def","inject_System_def","project_System_def","inject_AuxList_def","project_AuxList_def","inject_List_def","project_List_def"];

val is_embed_def = Define`
  is_embed emb = ∀a v. (emb.inject a = v) ⇔ (emb.project v = SOME a)`;

val raw_lookup_def = Define`
  raw_lookup (emb:'a embed) (addr _ n : 'a ptr) =
   (λs.
     OPTION_BIND (FLOOKUP s.store n)
                 (λv. if s.cell_type n = emb.type then
                        OPTION_BIND (emb.project v) (λpv. SOME (pv, s))
                      else NONE))
`;
val _ = overload_on("lookup", ``λp:Variable ptr. raw_lookup embed_Variable p``);
val _ = overload_on("lookup", ``λp:SetOfVariables ptr. raw_lookup embed_SetOfVariables p``);
val _ = overload_on("lookup", ``λp:Term ptr. raw_lookup embed_Term p``);
val _ = overload_on("lookup", ``λp:Multiequation ptr. raw_lookup embed_Multiequation p``);
val _ = overload_on("lookup", ``λp:TempMultiequation ptr. raw_lookup embed_TempMultiequation p``);
val _ = overload_on("lookup", ``λp:System ptr. raw_lookup embed_System p``);
val _ = overload_on("lookup", ``λemb. raw_lookup (embed_AuxList emb)``);
val _ = overload_on("lookup", ``λemb. raw_lookup (embed_List emb)``);
val _ = overload_on("lookup", ``λp:Term AuxList ptr. lookup embed_Term p``);
val _ = overload_on("lookup", ``λp:Multiequation AuxList ptr. lookup embed_Multiequation p``);
val _ = overload_on("lookup", ``λp:TempMultiequation AuxList ptr. lookup embed_TempMultiequation p``);
val _ = overload_on("lookup", ``λp:Variable AuxList ptr. lookup embed_Variable p``);
val _ = overload_on("lookup", ``λp:Term List ptr. lookup embed_Term p``);
val _ = overload_on("lookup", ``λp:Multiequation List ptr. lookup embed_Multiequation p``);
val _ = overload_on("lookup", ``λp:TempMultiequation List ptr. lookup embed_TempMultiequation p``);
val _ = overload_on("lookup", ``λp:Variable List ptr. lookup embed_Variable p``);

val raw_assign_def = Define`
  raw_assign (emb:'a embed) (addr _ n : 'a ptr) v =
  λs. SOME ((), s with <| store updated_by (n =+ (emb.inject v)) ;
                          cell_type updated_by (n =+ emb.type) |>)`;
val _ = overload_on("assign", ``λp:Variable ptr. raw_assign embed_Variable p``);
val _ = overload_on("assign", ``λp:SetOfVariables ptr. raw_assign embed_SetOfVariables p``);
val _ = overload_on("assign", ``λp:Term ptr. raw_assign embed_Term p``);
val _ = overload_on("assign", ``λp:Multiequation ptr. raw_assign embed_Multiequation p``);
val _ = overload_on("assign", ``λp:TempMultiequation ptr. raw_assign embed_TempMultiequation p``);
val _ = overload_on("assign", ``λp:System ptr. raw_assign embed_System p``);
val _ = overload_on("assign", ``λemb. raw_assign (embed_AuxList emb)``);
val _ = overload_on("assign", ``λemb. raw_assign (embed_List emb)``);
val _ = overload_on("assign", ``λp:Term AuxList ptr. assign embed_Term p``);
val _ = overload_on("assign", ``λp:Multiequation AuxList ptr. assign embed_Multiequation p``);
val _ = overload_on("assign", ``λp:TempMultiequation AuxList ptr. assign embed_TempMultiequation p``);
val _ = overload_on("assign", ``λp:Variable AuxList ptr. assign embed_Variable p``);
val _ = overload_on("assign", ``λp:Term List ptr. assign embed_Term p``);
val _ = overload_on("assign", ``λp:Multiequation List ptr. assign embed_Multiequation p``);
val _ = overload_on("assign", ``λp:TempMultiequation List ptr. assign embed_TempMultiequation p``);
val _ = overload_on("assign", ``λp:Variable List ptr. assign embed_Variable p``);

val dispose_def = Define`
  dispose (addr _ n) = λs. SOME ((), s with store updated_by (λs. s \\ n))`;

val free_addr_def = Define`
  free_addr = λs. SOME (addr (:'a) (@n. n ≠ 0 ∧ n ∉ FDOM s.store), s)`;

val raw_new_def = Define`raw_new emb v = do ptr <- free_addr ; raw_assign emb ptr v ; return ptr od`;
val _ = overload_on("new", ``λv:Variable. raw_new embed_Variable v``);
val _ = overload_on("new", ``λv:SetOfVariables. raw_new embed_SetOfVariables v``);
val _ = overload_on("new", ``λv:Term. raw_new embed_Term v``);
val _ = overload_on("new", ``λv:Multiequation. raw_new embed_Multiequation v``);
val _ = overload_on("new", ``λv:TempMultiequation. raw_new embed_TempMultiequation v``);
val _ = overload_on("new", ``λv:System. raw_new embed_System v``);
val _ = overload_on("new", ``λemb. raw_new (embed_AuxList emb)``);
val _ = overload_on("new", ``λemb. raw_new (embed_List emb)``);
val _ = overload_on("new", ``λv:Term AuxList. new embed_Term v``);
val _ = overload_on("new", ``λv:Multiequation AuxList. new embed_Multiequation v``);
val _ = overload_on("new", ``λv:TempMultiequation AuxList. new embed_TempMultiequation v``);
val _ = overload_on("new", ``λv:Variable AuxList. new embed_Variable v``);
val _ = overload_on("new", ``λv:Term List. new embed_Term v``);
val _ = overload_on("new", ``λv:Multiequation List. new embed_Multiequation v``);
val _ = overload_on("new", ``λv:TempMultiequation List. new embed_TempMultiequation v``);
val _ = overload_on("new", ``λv:Variable List. new embed_Variable v``);

val _ = export_rewrites["raw_lookup_def","raw_assign_def","dispose_def","raw_new_def"];

val CreateList_def = Define`
  CreateList emb =
  do l <- new emb (AuxList pnil pnil) ;
     s <- new emb (List l l) ;
     return s
  od`;
val _ = overload_on("CreateListOfTerms", ``CreateList embed_Term``);
val _ = overload_on("CreateListOfMulteq", ``CreateList embed_Multiequation``);
val _ = overload_on("CreateListOfTempMulteq", ``CreateList embed_TempMultiequation``);
val _ = overload_on("CreateListOfVariables", ``CreateList embed_Variable``);

val HeadOfList_def = Define`
  HeadOfList emb s =
  do s' <- lookup emb s ;
     s'first' <- lookup emb s'.first ;
     return s'first'.head
  od`;
val _ = overload_on("HeadOfListOfTerms", ``HeadOfList embed_Term``);
val _ = overload_on("HeadOfListOfMulteq", ``HeadOfList embed_Multiequation``);
val _ = overload_on("HeadOfListOfTempMulteq", ``HeadOfList embed_TempMultiequation``);
val _ = overload_on("HeadOfListOfVariables", ``HeadOfList embed_Variable``);

val EmptyList_def = Define`
  EmptyList emb s =
  do s' <- lookup emb s ;
     return (s'.first = s'.last)
  od`;
val _ = overload_on("EmptyListOfTerms", ``EmptyList embed_Term``);
val _ = overload_on("EmptyListOfMulteq", ``EmptyList embed_Multiequation``);
val _ = overload_on("EmptyListOfTempMulteq", ``EmptyList embed_TempMultiequation``);
val _ = overload_on("EmptyListOfVariables", ``EmptyList embed_Variable``);

val TailOfList_def = Define`
  TailOfList emb s =
  do s' <- lookup emb s ;
     l <- return s'.first ;
     l' <- lookup emb l;
     assign emb s (List l'.tail s'.last) ;
     dispose l ;
     return s
  od`;
val _ = overload_on("TailOfListOfTerms", ``TailOfList embed_Term``);
val _ = overload_on("TailOfListOfMulteq", ``TailOfList embed_Multiequation``);
val _ = overload_on("TailOfListOfTempMulteq", ``TailOfList embed_TempMultiequation``);
val _ = overload_on("TailOfListOfVariables", ``TailOfList embed_Variable``);

val AddToEndOfList_def = Define`
  AddToEndOfList emb t s =
  do l <- new emb (AuxList pnil pnil) ;
     s' <- lookup emb s ;
     assign emb s'.last (AuxList t l) ;
     assign emb s (List s'.first l) ;
     return s
  od`;
val _ = overload_on("AddToEndOfListOfTerms", ``AddToEndOfList embed_Term``);
val _ = overload_on("AddToEndOfListOfMulteq", ``AddToEndOfList embed_Multiequation``);
val _ = overload_on("AddToEndOfListOfTempMulteq", ``AddToEndOfList embed_TempMultiequation``);
val _ = overload_on("AddToEndOfListOfVariables", ``AddToEndOfList embed_Variable``);

val AddToFrontOfList_def = Define`
  AddToFrontOfList emb t s =
  do s' <- lookup emb s ;
     l <- new emb (AuxList t s'.first) ;
     assign emb s (List l s'.last) ;
     return s
  od`;
val _ = overload_on("AddToFrontOfListOfTerms", ``AddToFrontOfList embed_Term``);
val _ = overload_on("AddToFrontOfListOfMulteq", ``AddToFrontOfList embed_Multiequation``);
val _ = overload_on("AddToFrontOfListOfTempMulteq", ``AddToFrontOfList embed_TempMultiequation``);
val _ = overload_on("AddToFrontOfListOfVariables", ``AddToFrontOfList embed_Variable``);

val AppendLists_def = Define`
  AppendLists emb t1 t2 =
  do t2' <- lookup emb t2 ;
     if t2'.first ≠ t2'.last then
        do t1' <- lookup emb t1 ;
           t2'first' <- lookup emb t2'.first ;
           assign emb t1'.last (AuxList t2'first'.head t2'first'.tail) ;
           assign emb t1 (List t1'.first t2'.last) ;
           return ()
        od
     else return () ;
     dispose t2'.first ;
     dispose t2 ;
     return t1
  od`;
val _ = overload_on("AppendListsOfTerms", ``AppendLists embed_Term``);
val _ = overload_on("AppendListsOfMulteq", ``AppendLists embed_Multiequation``);
val _ = overload_on("AppendListsOfTempMulteq", ``AppendLists embed_TempMultiequation``);
val _ = overload_on("AppendListsOfVariables", ``AppendLists embed_Variable``);

val (list_of_AuxList_rules, list_of_AuxList_ind, list_of_AuxList_cases) = Hol_reln`
  (list_of_AuxList emb s last last []) ∧
  (al ≠ last ∧
   (OPTION_MAP FST
       (do al' <- lookup emb al ;
           (hd':'a) <- raw_lookup emb al'.head ;
           return (hd',al'.tail)
        od s)
    = SOME (hd',tl)) ∧
   list_of_AuxList emb s last tl tl' ⇒
   list_of_AuxList emb s last al (hd'::tl'))`;

val list_of_List_def = Define`
  list_of_List emb s l al' =
     ∃l'. (OPTION_MAP FST (lookup emb l s) = SOME l') ∧
          list_of_AuxList emb s l'.last l'.first al'`;

val _ = export_theory ()
