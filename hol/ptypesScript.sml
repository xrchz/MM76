open HolKernel bossLib boolLib boolSimps SatisfySimps Parse pairTheory optionTheory stringTheory finite_mapTheory sumTheory state_transformerTheory option_transformerTheory monadsyntax combinTheory lcsymtacs relationTheory

val _ = new_theory "ptypes"

val _ = overload_on("=+", ``λk v f. f |+ (k,v)``);
val _ = overload_on("=+", ``UPDATE``);
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
local
  fun Cases_on_if p (g as (asl,tm)) = let
    val tm = find_term p tm handle HOL_ERR _ =>
             Lib.tryfind (find_term p) asl
  in Cases_on [QUOTE (term_to_string tm)] end g
  fun is_var' v = let
    val (_,ty) = dest_var v
    val (tyname,_) = dest_type ty
  in
    not (Lib.mem tyname ["num","list"])
  end handle HOL_ERR _ => false | Bind => false
  val tac = srw_tac [][EQ_IMP_THM,is_embed_def] >> rpt (Cases_on_if is_var' >> fsrw_tac [][])
in
  val is_embed_Variable = Q.store_thm("is_embed_Variable", `is_embed embed_Variable`, tac);
  val is_embed_SetOfVariables = Q.store_thm("is_embed_SetOfVariables", `is_embed embed_SetOfVariables`, tac);
  val is_embed_Term = Q.store_thm("is_embed_Term", `is_embed embed_Term`, tac);
  val is_embed_Multiequation = Q.store_thm("is_embed_Multiequation", `is_embed embed_Multiequation`, tac);
  val is_embed_TempMultiequation = Q.store_thm("is_embed_TempMultiequation", `is_embed embed_TempMultiequation`, tac);
  val is_embed_System = Q.store_thm("is_embed_System", `is_embed embed_System`, tac);
  val is_embed_AuxList = Q.store_thm("is_embed_AuxList", `is_embed (embed_AuxList emb)`, tac);
  val is_embed_List = Q.store_thm("is_embed_List", `is_embed (embed_List emb)`, tac);
end

val raw_lookup_def = Define`
  raw_lookup (emb:'a embed) (addr _ n : 'a ptr) =
  do v <- (λs. (FLOOKUP s.store n, s)) ;
     t <- (λs. (SOME (s.cell_type n), s)) ;
     if t = emb.type then return (emb.project v) else OPTIONT_FAIL
  od`;
val _ = overload_on("lookup", ``λp:Variable ptr. raw_lookup embed_Variable p``);
val _ = overload_on("lookup", ``λp:SetOfVariables ptr. raw_lookup embed_SetOfVariables p``);
val _ = overload_on("lookup", ``λp:Term ptr. raw_lookup embed_Term p``);
val _ = overload_on("lookup", ``λp:Multiequation ptr. raw_lookup embed_Multiequation p``);
val _ = overload_on("lookup", ``λp:TempMultiequation ptr. raw_lookup embed_TempMultiequation p``);
val _ = overload_on("lookup", ``λp:System ptr. raw_lookup embed_System p``);
val _ = overload_on("lookup", ``λemb. raw_lookup (embed_AuxList emb)``);
val _ = overload_on("lookup", ``λemb. raw_lookup (embed_List emb)``);

val raw_assign_def = Define`
  raw_assign (emb:'a embed) (addr _ n : 'a ptr) v =
  λs. ((), s with <| store updated_by (n =+ (emb.inject v)) ;
                     cell_type updated_by (n =+ emb.type) |>)`;
val _ = overload_on("assign", ``λp:Variable ptr. raw_assign embed_Variable p``);
val _ = overload_on("assign", ``λp:SetOfVariables ptr. raw_assign embed_SetOfVariables p``);
val _ = overload_on("assign", ``λp:Term ptr. raw_assign embed_Term p``);
val _ = overload_on("assign", ``λp:Multiequation ptr. raw_assign embed_Multiequation p``);
val _ = overload_on("assign", ``λp:TempMultiequation ptr. raw_assign embed_TempMultiequation p``);
val _ = overload_on("assign", ``λp:System ptr. raw_assign embed_System p``);
val _ = overload_on("assign", ``λemb. raw_assign (embed_AuxList emb)``);
val _ = overload_on("assign", ``λemb. raw_assign (embed_List emb)``);

val dispose_def = Define`
  dispose (addr _ n) = λs. ((), s with store updated_by (λs. s \\ n))`;

val free_addr_def = Define`
  free_addr = λs. (addr (:'a) (@n. n ≠ 0 ∧ n ∉ FDOM s.store), s)`;

val raw_new_def = Define`raw_new emb v = do ptr <- free_addr ; raw_assign emb ptr v ; return ptr od`;
val _ = overload_on("new", ``λv:Variable. raw_new embed_Variable v``);
val _ = overload_on("new", ``λv:SetOfVariables. raw_new embed_SetOfVariables v``);
val _ = overload_on("new", ``λv:Term. raw_new embed_Term v``);
val _ = overload_on("new", ``λv:Multiequation. raw_new embed_Multiequation v``);
val _ = overload_on("new", ``λv:TempMultiequation. raw_new embed_TempMultiequation v``);
val _ = overload_on("new", ``λv:System. raw_new embed_System v``);
val _ = overload_on("new", ``λemb. raw_new (embed_AuxList emb)``);
val _ = overload_on("new", ``λemb. raw_new (embed_List emb)``);

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
   (FST ((do al' <- lookup emb al ;
             (hd':'a) <- raw_lookup emb al'.head ;
             return (hd',al'.tail)
          od) s) =
    SOME (hd',tl)) ∧
   list_of_AuxList emb s last tl tl' ⇒
   list_of_AuxList emb s last al (hd'::tl'))`;

val list_of_List_def = Define`
  list_of_List emb s l al' = ∃l'. (FST (lookup emb l s) = SOME l') ∧ list_of_AuxList emb s l'.last l'.first al'`;

val NOTIN_INFINITE_FDOM_exists = Q.store_thm(
"NOTIN_INFINITE_FDOM_exists",
`INFINITE (UNIV : 'a set) ⇒ ∃x. x ∉ (FDOM f : 'a set)`,
PROVE_TAC [pred_setTheory.IN_INFINITE_NOT_FINITE,FDOM_FINITE]);
val _ = export_rewrites["NOTIN_INFINITE_FDOM_exists"];

val free_addr_elim_thm = Q.store_thm(
"free_addr_elim_thm",
`∀P s. (∀n. n ≠ 0 ∧ n ∉ FDOM s.store ⇒ P (addr (:'a) n,s)) ⇒ P (free_addr s)`,
srw_tac [][free_addr_def] >>
SELECT_ELIM_TAC >>
`∃x. x ∉ FDOM (s.store|+(0,ARB))` by srw_tac [][] >>
fsrw_tac [SATISFY_ss][]);

fun is_free_addr tm = let
  val (f,_) = dest_comb tm
  val ("free_addr",ty) = dest_const f
in
  can (match_type ``:state -> 'a ptr # state``) ty
end handle HOL_ERR _ => false | Bind => false

fun free_addr_elim_tac (g as (_, w)) = let
  val t = find_term is_free_addr w
in
  CONV_TAC (UNBETA_CONV t) THEN
  MATCH_MP_TAC free_addr_elim_thm THEN BETA_TAC
end g

val _ = augment_srw_ss [rewrites [BIND_DEF,IGNORE_BIND_DEF,UNIT_DEF,OPTIONT_BIND_def,OPTIONT_FAIL_def,OPTIONT_UNIT_def]]

val CreateList_empty = Q.store_thm(
"CreateList_empty",
`(CreateList emb s0 = (l, s)) ⇒ list_of_List emb s l []`,
simp_tac (srw_ss()) [CreateList_def,raw_new_def] >>
free_addr_elim_tac >> srw_tac [][UNCURRY] >>
free_addr_elim_tac >>
srw_tac [][list_of_List_def,Once list_of_AuxList_cases,EmptyList_def,FLOOKUP_UPDATE,APPLY_UPDATE_THM]);

val lookup_state = Q.store_thm(
"lookup_state",
`SND (raw_lookup emb ptr s) = s`,
Cases_on `emb` >> Cases_on `ptr` >>
srw_tac [][FLOOKUP_DEF] >> srw_tac [][]);
val _ = export_rewrites["lookup_state"];

val HeadOfList_state = Q.store_thm(
"HeadOfList_state",
`SND (HeadOfList emb l s) = s`,
`SND (lookup emb l s) = s` by MATCH_ACCEPT_TAC lookup_state >>
srw_tac [][HeadOfList_def,lookup_state,UNCURRY] >>
Cases_on `FST (lookup emb l s)` >> srw_tac [][] >>
`SND (lookup emb x.first s) = s` by MATCH_ACCEPT_TAC lookup_state >>
srw_tac [][UNCURRY] >>
Cases_on `FST (lookup emb x.first s)` >> srw_tac [][]);
val _ = export_rewrites["HeadOfList_state"];

val TailOfList_store = Q.store_thm(
"TailOfList_store",
`(lookup emb l s = (SOME l', s')) ⇒ ((SND (TailOfList emb l s)).store \\ (ptr_to_num l) \\ (ptr_to_num l'.first) = s.store \\ (ptr_to_num l) \\ (ptr_to_num l'.first))`,
srw_tac [][TailOfList_def,UNCURRY] >>
`s' = s` by PROVE_TAC [lookup_state,SND] >>
`SND (lookup emb l'.first s) = s` by PROVE_TAC [lookup_state,SND] >>
Cases_on `FST (lookup emb l'.first s)` >> srw_tac [][] >>
Cases_on `l` >> Cases_on `l'.first` >>
srw_tac [][DOMSUB_COMMUTES]);

val EmptyList_state = Q.store_thm(
"EmptyList_state",
`SND (EmptyList emb l s) = s`,
srw_tac [][EmptyList_def,lookup_state,UNCURRY] >>
Cases_on `FST (lookup emb l s) ` >> srw_tac [][]);
val _ = export_rewrites["EmptyList_state"];

val dispose_store = Q.store_thm(
"dispose_store",
`s.store \\ ptr_to_num p = (SND (dispose p s)).store \\ ptr_to_num p`,
Cases_on `p` >> srw_tac [][]);

val dispose_cell_type = Q.store_thm(
"dispose_cell_type",
`(SND (dispose p s)).cell_type = s.cell_type`,
Cases_on `p` >> srw_tac [][]);

val lookup_dispose = Q.store_thm(
"lookup_dispose",
`raw_lookup emb p2 (SND (dispose p1 s)) = (if ptr_to_num p1 = ptr_to_num p2 then NONE else (FST (raw_lookup emb p2 s)), (SND (dispose p1 s)))`,
Cases_on `p1` >> Cases_on `p2` >> srw_tac [][] >>
fsrw_tac [][DOMSUB_FLOOKUP_THM] >>
srw_tac [][FLOOKUP_DEF] >> srw_tac [][]);

val lookup_fails = Q.store_thm(
"lookup_fails",
`(FST (raw_lookup emb p s) = NONE) ⇔ (∀v. (FLOOKUP s.store (ptr_to_num p) = SOME v) ⇒ (s.cell_type (ptr_to_num p) = emb.type) ⇒ (emb.project v = NONE))`,
Cases_on `p` >> srw_tac [][FLOOKUP_DEF] >> srw_tac [][]);

val lookup_succeeds = Q.store_thm(
"lookup_succeeds",
`(FST (raw_lookup emb p s) = SOME a) ⇔ ∃v. (FLOOKUP s.store (ptr_to_num p) = SOME v) ∧ (s.cell_type (ptr_to_num p) = emb.type) ∧ (emb.project v = SOME a)`,
Cases_on `FST (raw_lookup emb p s)` >- (
  PROVE_TAC [lookup_fails,NOT_SOME_NONE] ) >>
Cases_on `FLOOKUP s.store (ptr_to_num p)` >>
Cases_on `p` >> fsrw_tac [][] >>
Cases_on `s.cell_type n = emb.type` >> fsrw_tac [][]);

val lookup_assign = Q.store_thm(
"lookup_assign",
`is_embed emb ⇒ (FST (raw_lookup emb p (SND (raw_assign emb p a s))) = SOME a)`,
Cases_on `p` >> srw_tac [][FLOOKUP_UPDATE,APPLY_UPDATE_THM,is_embed_def] >> PROVE_TAC []);

val assign_store = Q.store_thm(
"assign_store",
`(SND (raw_assign emb p v s)).store \\ ptr_to_num p = s.store \\ ptr_to_num p`,
Cases_on `p` >> srw_tac [][]);

val assign_cell_type = Q.store_thm(
"assign_cell_type",
`(SND (raw_assign emb p v s)).cell_type = ((ptr_to_num p) =+ emb.type) s.cell_type`,
Cases_on `p` >> srw_tac [][]);
val _ = export_rewrites["assign_cell_type"];

val lookup_unbound = Q.store_thm(
"lookup_unbound",
`ptr_to_num p ∉ FDOM s.store ⇒ (lookup p s = (NONE, s))`,
Cases_on `p` >> srw_tac [][FLOOKUP_DEF]);

val HeadOfList_unbound = Q.store_thm(
"HeadOfList_unbound",
`ptr_to_num p ∉ FDOM s.store ⇒ (HeadOfList emb p s = (NONE, s))`,
Cases_on `p` >> srw_tac [][FLOOKUP_DEF,HeadOfList_def]);

val TailOfList_unbound = Q.store_thm(
"TailOfList_unbound",
`ptr_to_num p ∉ FDOM s.store ⇒ (TailOfList emb p s = (NONE, s))`,
Cases_on `p` >> srw_tac [][FLOOKUP_DEF,TailOfList_def]);

val type_inductive = Q.store_thm(
"type_inductive",
`∀t. t ≠ List_type t ∧ t ≠ AuxList_type t`,
Induct >> srw_tac [][]);

val typed_cell_bound = Q.store_thm(
"typed_cell_bound",
`typed_cell s ms n ⇒ (n = 0) ∨ n ∈ ms ∨ n ∈ FDOM s.store`,
srw_tac [][Once has_type_cases,FLOOKUP_DEF] >> srw_tac [][]);

val assign_comm = Q.store_thm(
"assign_comm",
`ptr_to_num p1 ≠ ptr_to_num p2 ⇒
 (SND (raw_assign emb1 p1 v1 (SND (raw_assign emb2 p2 v2 s))) =
  SND (raw_assign emb2 p2 v2 (SND (raw_assign emb1 p1 v1 s))))`,
Cases_on `p1` >> Cases_on `p2` >> srw_tac [][] >>
srw_tac [][theorem "state_component_equality",FUN_EQ_THM,APPLY_UPDATE_THM] >>
srw_tac [][GSYM fmap_EQ,pred_setTheory.INSERT_COMM] >>
srw_tac [][FUN_EQ_THM,FAPPLY_FUPDATE_THM] >>
srw_tac [][]);

val free_addr_state = Q.store_thm(
"free_addr_state",
`SND (free_addr s) = s`,
srw_tac [][free_addr_def]);
val _ = export_rewrites["free_addr_state"];

val lookup_assign_neq = Q.store_thm(
"lookup_assign_neq",
`ptr_to_num p1 ≠ ptr_to_num p2 ⇒
 (FST (raw_lookup emb1 p1 (SND (raw_assign emb2 p2 v s))) = FST (raw_lookup emb1 p1 s))`,
Cases_on `FST (raw_lookup emb1 p1 s)` >>
Cases_on `p2` >> fsrw_tac [][FLOOKUP_UPDATE,APPLY_UPDATE_THM,lookup_succeeds,lookup_fails]);

val ptr_equality = Q.store_thm(
"ptr_equality",
`(ptr_to_num p1 = ptr_to_num p2) ⇔ (p1 = p2)`,
Cases_on `p1` >> Cases_on `p2` >> srw_tac [][] >>
PROVE_TAC [ITSELF_UNIQUE]);

val (reach1_rules, reach1_ind, reach1_cases) = Hol_reln`
  (reach1 m (Variable_value _ m)) ∧
  (reach1 m (SetOfVariables_value _ _ m)) ∧
  (reach1 m (Term_value (INL m))) ∧
  (reach1 m (Term_value (INR (_,m)))) ∧
  (reach1 m (Multiequation_value _ m _)) ∧
  (reach1 m (Multiequation_value _ _ m)) ∧
  (reach1 m (TempMultiequation_value m _)) ∧
  (reach1 m (TempMultiequation_value _ m)) ∧
  (reach1 m (System_value m _)) ∧
  (reach1 m (System_value _ m)) ∧
  (reach1 m (List_value m _)) ∧
  (reach1 m (List_value _ m)) ∧
  (reach1 m (AuxList_value m _)) ∧
  (reach1 m (AuxList_value _ m))`;

val cell_reach1_def = Define`
  cell_reach1 (s:store) m n = ∃v. (FLOOKUP s n = SOME v) ∧ reach1 m v`;
val _ = overload_on("cell_reach",``λs. RTC (cell_reach1 s)``);

val reach_def = Define`
  reach s m v = ∃n. reach1 n v ∧ cell_reach s m n`;

val cell_reach_FUPDATE_end = Q.store_thm(
"cell_reach_FUPDATE_end",
`cell_reach (s |+ (m,w)) m n ⇔ cell_reach s m n`,
reverse EQ_TAC >- (
  map_every qid_spec_tac [`n`,`m`] >>
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
  srw_tac [][cell_reach1_def] >>
  qmatch_assum_rename_tac `FLOOKUP s p = SOME v` [] >>
  Cases_on `m = p` >- PROVE_TAC [RTC_REFL] >>
  `FLOOKUP (s |+ (m,w)) p = SOME v` by PROVE_TAC [FLOOKUP_UPDATE] >>
  PROVE_TAC [cell_reach1_def,RTC_RULES_RIGHT1] ) >>
qsuff_tac `!s0 s m n. cell_reach s m n ⇒ (s = s0 |+ (m,w)) ⇒ cell_reach s0 m n`
>- srw_tac [][] >>
ntac 2 gen_tac >>
ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
srw_tac [][cell_reach1_def] >>
qmatch_assum_rename_tac `FLOOKUP (s0 |+ (m,w)) p = SOME v` [] >>
Cases_on `m=p` >- PROVE_TAC [RTC_REFL] >>
`FLOOKUP s0 p = SOME v` by PROVE_TAC [FLOOKUP_UPDATE] >>
PROVE_TAC [cell_reach1_def,RTC_RULES_RIGHT1]);

val reach_FUPDATE_end = Q.store_thm(
"reach_FUPDATE_end",
`reach (s |+ (m,w)) m v ⇔ reach s m v`,
srw_tac [][reach_def,cell_reach_FUPDATE_end]);

val cell_reach_bound = Q.store_thm(
"cell_reach_bound",
`cell_reach s m n ∧ n ≠ m ⇒ n ∈ FDOM s`,
srw_tac [][Once RTC_CASES2,cell_reach1_def,FLOOKUP_DEF]);

val FLOOKUP_reach_imp_cell_reach = Q.store_thm(
"FLOOKUP_reach_imp_cell_reach",
`(FLOOKUP s n = SOME v) ∧ reach s m v ⇒ cell_reach s m n`,
srw_tac [][reach_def] >>
srw_tac [SATISFY_ss][Once RTC_CASES2,cell_reach1_def]);

val has_type_assign_unreachable = Q.store_thm(
"has_type_assign_unreachable",
`(∀c v t. has_type s c v t ⇒ ¬ reach s.store m v ⇒ has_type (s with store updated_by (m =+ w)) c v t) ∧
 (∀c n. typed_cell s c n ⇒ ¬ cell_reach s.store m n ⇒ typed_cell (s with store updated_by (m =+ w)) c n)`,
ho_match_mp_tac has_type_ind >>
reverse (srw_tac [][]) >- (
  srw_tac [][Once has_type_cases,FLOOKUP_UPDATE] >>
  PROVE_TAC [RTC_REFL,FLOOKUP_reach_imp_cell_reach] )
>- (
  srw_tac [][Once has_type_cases] >>
  PROVE_TAC [RTC_REFL] )
>- srw_tac [][Once has_type_cases] >>
fsrw_tac [][reach_def,reach1_cases] >>
srw_tac [][Once has_type_cases] >>
first_x_assum match_mp_tac >>
PROVE_TAC []);

val has_type_remove_unreachable = Q.store_thm(
"has_type_remove_unreachable",
`(∀c v t. has_type s c v t ⇒ ¬ reach s.store m v ⇒ has_type (s with store updated_by combin$C $\\ m) c v t) ∧
 (∀c n. typed_cell s c n ⇒ ¬ cell_reach s.store m n ⇒ typed_cell (s with store updated_by combin$C $\\ m) c n)`,
ho_match_mp_tac has_type_ind >>
reverse (srw_tac [][]) >- (
  srw_tac [][Once has_type_cases,DOMSUB_FLOOKUP_THM] >>
  PROVE_TAC [RTC_REFL,FLOOKUP_reach_imp_cell_reach] ) >>
srw_tac [][Once has_type_cases] >>
fsrw_tac [][reach_def,reach1_cases] >>
PROVE_TAC [RTC_RULES]);

val typed_cell_def = Q.store_thm(
"typed_cell_def",
`typed_cell s c n =
   n ∈ FDOM s.store ∧ n ∈ c ∨
   case FLOOKUP s.store n of SOME v -> has_type s (n INSERT c) v (s.cell_type n) || NONE -> (n = 0)`,
srw_tac [][Once has_type_cases] >>
Cases_on `FLOOKUP s.store n` >> srw_tac [][] >>
fsrw_tac [][FLOOKUP_DEF] >>
PROVE_TAC []);

val has_type_INSERT_cached = Q.store_thm(
"has_type_INSERT_cached",
`(∀c v t. has_type s c v t ⇒ has_type s (m INSERT c) v t) ∧
 (∀c n. typed_cell s c n ⇒ typed_cell s (m INSERT c) n)`,
ho_match_mp_tac has_type_ind >>
reverse (srw_tac [][])
>- srw_tac [][typed_cell_def,pred_setTheory.INSERT_COMM]
>- srw_tac [][typed_cell_def,FLOOKUP_DEF]
>- srw_tac [][typed_cell_def] >>
srw_tac [][Once has_type_cases]);

val has_type_assign_unbound = Q.store_thm(
"has_type_assign_unbound",
`(∀c v t. has_type s c v t ⇒ m ≠ 0 ∧ m ∉ FDOM s.store ∧ m ∉ c ⇒
          has_type (s with <|store updated_by (m =+ w); cell_type updated_by (m =+ a)|>) c v t) ∧
 (∀c n. typed_cell s c n ⇒ m ≠ 0 ∧ m ∉ FDOM s.store ∧ m ∉ c ⇒
        typed_cell (s with <|store updated_by (m =+ w); cell_type updated_by (m =+ a)|>) c n)`,
ho_match_mp_tac (theorem "has_type_strongind") >>
reverse (srw_tac [][]) >- (
  fsrw_tac [][] >>
  srw_tac [][Once has_type_cases,FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
  fsrw_tac [][FLOOKUP_DEF] )
>- srw_tac [][Once has_type_cases,FLOOKUP_UPDATE]
>- srw_tac [][Once has_type_cases] >>
srw_tac [][Once has_type_cases,APPLY_UPDATE_THM] >>
fsrw_tac [][typed_cell_def,type_inductive,FLOOKUP_UPDATE] >>
fsrw_tac [][FLOOKUP_DEF]);

val has_type_assign_cached = Q.store_thm(
"has_type_assign_cached",
`(∀c v t. has_type s c v t ⇒ m ∈ c ⇒
          has_type (s with <|store updated_by (m =+ w)|>) c v t) ∧
 (∀c n. typed_cell s c n ⇒ m ∈ c ⇒
        typed_cell (s with <|store updated_by (m =+ w)|>) c n)`,
ho_match_mp_tac has_type_ind >>
reverse (srw_tac [][]) >- (
  srw_tac [][typed_cell_def,FLOOKUP_UPDATE] >>
  fsrw_tac [][APPLY_UPDATE_THM] )
>- srw_tac [][typed_cell_def,FLOOKUP_UPDATE,FLOOKUP_DEF]
>- srw_tac [][typed_cell_def] >>
srw_tac [][Once has_type_cases]);

val has_type_assign_cached_unbound = Q.store_thm(
"has_type_assign_cached_unbound",
`(∀c v t. has_type s c v t ⇒ m ∈ c ∧ m ∉ FDOM s.store ⇒
          has_type (s with <|store updated_by (m =+ w); cell_type updated_by (m =+ a)|>) c v t) ∧
 (∀c n. typed_cell s c n ⇒ m ∈ c ∧ m ∉ FDOM s.store ⇒
        typed_cell (s with <|store updated_by (m =+ w); cell_type updated_by (m =+ a)|>) c n)`,
ho_match_mp_tac (theorem "has_type_strongind") >>
reverse (srw_tac [][]) >- (
  fsrw_tac [][] >>
  srw_tac [][typed_cell_def,FLOOKUP_UPDATE,APPLY_UPDATE_THM] >>
  srw_tac [][] )
>- srw_tac [][typed_cell_def,FLOOKUP_UPDATE,FLOOKUP_DEF]
>- srw_tac [][typed_cell_def] >>
fsrw_tac [][] >>
srw_tac [][Once has_type_cases,APPLY_UPDATE_THM] >>
fsrw_tac [][type_inductive,typed_cell_def,FLOOKUP_DEF]);

val has_type_assign_bound = Q.store_thm(
"has_type_assign_bound",
`(∀c v t. has_type s c v t ⇒ m ≠ 0 ∧ m ∈ FDOM s.store ∧ has_type s c w (s.cell_type m) ⇒
          has_type (s with <|store updated_by (m =+ w) |>) c v t) ∧
 (∀c n. typed_cell s c n ⇒ m ≠ 0 ∧ m ∈ FDOM s.store ∧ has_type s c w (s.cell_type m) ⇒
        typed_cell (s with <|store updated_by (m =+ w) |>) c n)`,
ho_match_mp_tac has_type_ind >>
reverse (srw_tac [][]) >- (
  fsrw_tac [][has_type_INSERT_cached] >>
  srw_tac [][typed_cell_def] >>
  Cases_on `n ∈ c` >> srw_tac [][] >>
  srw_tac [][FLOOKUP_UPDATE] >> srw_tac [][] >>
  (has_type_assign_cached |> CONJUNCT1 |> MP_CANON |> MATCH_MP_TAC) >>
  srw_tac [][has_type_INSERT_cached] )
>- srw_tac [][Once has_type_cases,FLOOKUP_UPDATE]
>- srw_tac [][typed_cell_def] >>
srw_tac [][Once has_type_cases]);

val assign_FDOM = Q.store_thm(
"assign_FDOM",
`FDOM (SND (raw_assign emb p v s)).store = (ptr_to_num p) INSERT (FDOM s.store)`,
Cases_on `p` >> srw_tac [][]);
val _ = export_rewrites["assign_FDOM"];

val wfstate_def = Define`
  wfstate s = typed_state s ∧ 0 ∉ FDOM s.store`;

val free_addr_neq_0 = Q.store_thm(
"free_addr_neq_0",
`ptr_to_num (FST (free_addr s)) ≠ 0`,
free_addr_elim_tac >> srw_tac [][]);
val _ = export_rewrites["free_addr_neq_0"];

val CreateList_wfstate = Q.store_thm(
"CreateList_wfstate",
`wfstate s ⇒ wfstate (SND (CreateList emb s))`,
srw_tac [][CreateList_def,UNCURRY,wfstate_def] >>
free_addr_elim_tac >> qx_gen_tac `f1` >> fsrw_tac [][] >>
free_addr_elim_tac >> qx_gen_tac `f2` >> fsrw_tac [][] >>
strip_tac >> strip_tac >>
srw_tac [][typed_state_def,APPLY_UPDATE_THM] >- (
  ntac 5 (srw_tac [][Once has_type_cases,FLOOKUP_UPDATE,APPLY_UPDATE_THM]) )
>- (
  ntac 3 (srw_tac [][Once has_type_cases,FLOOKUP_UPDATE,APPLY_UPDATE_THM]) ) >>
`f1 ≠ n ∧ f2 ≠ n` by PROVE_TAC [] >>
srw_tac [][] >>
qmatch_abbrev_tac `typed_cell (s with <|store updated_by x1 o x2; cell_type updated_by x3 o x4|>) {} n` >>
qsuff_tac `typed_cell ((s with <|store updated_by x2; cell_type updated_by x4|>) with <|store updated_by x1; cell_type updated_by x3|>) {} n` >- srw_tac [][] >>
unabbrev_all_tac >>
(has_type_assign_unbound |> CONJUNCT2 |> MP_CANON |> match_mp_tac) >>
srw_tac [][] >>
(has_type_assign_unbound |> CONJUNCT2 |> MP_CANON |> match_mp_tac) >>
srw_tac [][] >>
fsrw_tac [][typed_state_def]);

val cell_reach_typed_state_unbound_eq_0 = Q.store_thm(
"cell_reach_typed_state_unbound_eq_0",
`typed_state s ∧ cell_reach s.store m n ∧ m ≠ n ∧ m ∉ FDOM s.store ⇒ (m = 0)`,
REWRITE_TAC [GSYM AND_IMP_INTRO] >>
strip_tac >>
map_every qid_spec_tac [`n`,`m`] >>
ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
srw_tac [][] >>
fsrw_tac [][cell_reach1_def] >>
qmatch_assum_rename_tac `FLOOKUP s.store p = SOME v` [] >>
`p ∈ FDOM s.store` by fsrw_tac [][FLOOKUP_DEF] >>
Cases_on `m = n` >> srw_tac [][] >>
imp_res_tac typed_state_def >>
fsrw_tac [][Once has_type_cases] >>
fsrw_tac [][] >> srw_tac [][] >>
fsrw_tac [][reach1_cases] >> srw_tac [][] >>
fsrw_tac [][Once has_type_cases] >>
fsrw_tac [][Once has_type_cases] >>
fsrw_tac [][FLOOKUP_DEF] );

val _ = export_theory ()
