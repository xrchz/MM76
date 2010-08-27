open HolKernel bossLib boolLib boolSimps SatisfySimps Parse pairTheory optionTheory stringTheory finite_mapTheory sumTheory state_transformerTheory option_transformerTheory monadsyntax lcsymtacs

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

val _ = Hol_datatype `state = <| store : store |>`;

val _ = Hol_datatype `
type = Variable_type
     | SetOfVariables_type
     | Term_type
     | Multiequation_type
     | TempMultiequation_type
     | System_type
     | AuxList_type of type
     | List_type of type`;

val (has_type_rules, has_type_ind, has_type_cases) = Hol_reln`
  ((FLOOKUP s n = NONE) ⇒ has_type s n t) ∧
  ((FLOOKUP s n = SOME (Variable_value _ m)) ∧ has_type s m Multiequation_type ⇒
   has_type s n Variable_type) ∧
  ((FLOOKUP s n = SOME (SetOfVariables_value _ _ m)) ∧ has_type s m (List_type Variable_type) ⇒
   has_type s n SetOfVariables_type) ∧
  ((FLOOKUP s n = SOME (Term_value (INL m))) ∧ has_type s m Variable_type ⇒
   has_type s n Term_type) ∧
  ((FLOOKUP s n = SOME (Term_value (INR (_,m)))) ∧ has_type s m (List_type Term_type) ⇒
   has_type s n Term_type) ∧
  ((FLOOKUP s n = SOME (Multiequation_value _ m1 m2)) ∧ has_type s m1 SetOfVariables_type ∧ has_type s m2 (List_type Term_type) ⇒
   has_type s n Multiequation_type) ∧
  ((FLOOKUP s n = SOME (TempMultiequation_value m1 m2)) ∧ has_type s m1 (List_type Term_type) ∧ has_type s m2 (List_type Term_type) ⇒
   has_type s n TempMultiequation_type) ∧
  ((FLOOKUP s n = SOME (System_value m1 m2)) ∧ has_types s m1 (List_type Multiequation_type) ∧ has_type s m2 (List_type Multiequation_type) ⇒
   has_type s n System_type) ∧
  ((FLOOKUP s n = SOME (List_value m1 m2)) ∧ has_type s m1 (AuxList_type type) ∧ has_type s m2 (AuxList_type type) ⇒
   has_type s n (List_type type)) ∧
  ((FLOOKUP s n = SOME (AuxList_value m1 m2)) ∧ has_type s m1 type ∧ has_type s m2 (AuxList_type type) ⇒
   has_type s n (AuxList_type type))`;

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
  is_embed emb = ∀a. emb.project (emb.inject a) = SOME a`;
local
  fun Cases_on_rhs (g as (asl,tm)) = let
    val (_,rhs) = dest_eq tm
    val var = if is_var rhs then rhs else snd (dest_comb rhs)
  in Cases_on [QUOTE (term_to_string var)] end g
  val tac = srw_tac [][is_embed_def] >> rpt (Cases_on_rhs >> srw_tac [][])
in
  val is_embed_Variable = Q.store_thm("is_embed_Variable", `is_embed embed_Variable`, tac);
  val is_embed_SetOfVariables = Q.store_thm("is_embed_SetOfVariables", `is_embed embed_SetOfVariables`, tac);
  val is_embed_Term = Q.store_thm("is_embed_Term", `is_embed embed_Term`, tac);
  val is_embed_Multiequation = Q.store_thm("is_embed_Multiequation", `is_embed embed_Multiequation`, tac);
  val is_embed_TempMultiequation = Q.store_thm("is_embed_TempMultiequation", `is_embed embed_TempMultiequation`, tac);
  val is_embed_System = Q.store_thm("is_embed_System", `is_embed embed_System`, tac);
  val is_embed_AuxList = Q.store_thm("is_embed_AuxList", `is_embed emb ⇒ is_embed (embed_AuxList emb)`, tac);
  val is_embed_List = Q.store_thm("is_embed_List", `is_embed emb ⇒ is_embed (embed_List emb)`, tac);
end

val raw_lookup_def = Define`
  raw_lookup (emb:'a embed) (addr _ n : 'a ptr) = OPTIONT_BIND (λs. (FLOOKUP s.store n, s)) (λv. UNIT (emb.project v))`;
val _ = overload_on("lookup", ``λp:Variable ptr. raw_lookup embed_Variable p``);
val _ = overload_on("lookup", ``λp:SetOfVariables ptr. raw_lookup embed_SetOfVariables p``);
val _ = overload_on("lookup", ``λp:Term ptr. raw_lookup embed_Term p``);
val _ = overload_on("lookup", ``λp:Multiequation ptr. raw_lookup embed_Multiequation p``);
val _ = overload_on("lookup", ``λp:TempMultiequation ptr. raw_lookup embed_TempMultiequation p``);
val _ = overload_on("lookup", ``λp:System ptr. raw_lookup embed_System p``);
val _ = overload_on("lookup", ``λemb. raw_lookup (embed_AuxList emb)``);
val _ = overload_on("lookup", ``λemb. raw_lookup (embed_List emb)``);

val raw_assign_def = Define`
  raw_assign (emb:'a embed) (addr _ n : 'a ptr) v = λs. ((), s with store updated_by (n =+ (emb.inject v)))`;
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

val (corresponding_list_rules, corresponding_list_ind, corresponding_list_cases) = Hol_reln`
  (((EmptyList emb ptr) s = (SOME T, s')) ⇒ corresponding_list emb ptr s []) ∧
  (((do hd <- HeadOfList emb ptr ;
        tl <- TailOfList emb ptr ;
        (hd':'a) <- raw_lookup emb hd ;
        return (hd',tl)
     od) s = (SOME (hd',tl),s')) ∧
   corresponding_list emb tl s' tl' ⇒
   corresponding_list emb ptr s (hd'::tl'))`;

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

val CreateList_creates_empty = Q.store_thm(
"CreateList_creates_empty",
`(CreateList emb s0 = (ptr, s)) ⇒ corresponding_list emb ptr s []`,
simp_tac (srw_ss()) [CreateList_def,raw_new_def] >>
free_addr_elim_tac >> srw_tac [][UNCURRY] >>
free_addr_elim_tac >>
srw_tac [][Once corresponding_list_cases,EmptyList_def,FLOOKUP_UPDATE]);

val lookup_preserves_store = Q.store_thm(
"lookup_preserves_store",
`SND (raw_lookup emb ptr s) = s`,
Cases_on `emb` >> Cases_on `ptr` >> srw_tac [][FLOOKUP_DEF]);

val HeadOfList_preserves_store = Q.store_thm(
"HeadOfList_preserves_store",
`SND (HeadOfList emb l s) = s`,
`SND (lookup emb l s) = s` by MATCH_ACCEPT_TAC lookup_preserves_store >>
srw_tac [][HeadOfList_def,lookup_preserves_store,UNCURRY] >>
Cases_on `FST (lookup emb l s)` >> srw_tac [][] >>
`SND (lookup emb x.first s) = s` by MATCH_ACCEPT_TAC lookup_preserves_store >>
srw_tac [][UNCURRY] >>
Cases_on `FST (lookup emb x.first s)` >> srw_tac [][]);

val TailOfList_preserves_store = Q.store_thm(
"TailOfList_preserves_store",
`(lookup emb l s = (SOME l', s')) ⇒ ((SND (TailOfList emb l s)).store \\ (ptr_to_num l) \\ (ptr_to_num l'.first) = s.store \\ (ptr_to_num l) \\ (ptr_to_num l'.first))`,
srw_tac [][TailOfList_def,UNCURRY] >>
`s' = s` by PROVE_TAC [lookup_preserves_store,SND] >>
`SND (lookup emb l'.first s) = s` by PROVE_TAC [lookup_preserves_store,SND] >>
Cases_on `FST (lookup emb l'.first s)` >> srw_tac [][] >>
Cases_on `l` >> Cases_on `l'.first` >>
srw_tac [][DOMSUB_COMMUTES]);

val EmptyList_preserves_store = Q.store_thm(
"EmptyList_preserves_store",
`SND (EmptyList emb l s) = s`,
srw_tac [][EmptyList_def,lookup_preserves_store,UNCURRY] >>
Cases_on `FST (lookup emb l s) ` >> srw_tac [][]);

val dispose_preserves_store = Q.store_thm(
"dispose_preserves_store",
`s.store \\ ptr_to_num p = (SND (dispose p s)).store \\ ptr_to_num p`,
Cases_on `p` >> srw_tac [][]);

val lookup_dispose = Q.store_thm(
"lookup_dispose",
`raw_lookup emb p2 (SND (dispose p1 s)) = (if ptr_to_num p1 = ptr_to_num p2 then NONE else (FST (raw_lookup emb p2 s)), (SND (dispose p1 s)))`,
Cases_on `p1` >> Cases_on `p2` >> Cases_on `emb` >> srw_tac [][] >>
fsrw_tac [][DOMSUB_FLOOKUP_THM] >>
srw_tac [][FLOOKUP_DEF]);

val lookup_assign = Q.store_thm(
"lookup_assign",
`is_embed emb ⇒
 ∀ptr v s s'. (raw_assign emb ptr v s = ((), s')) ⇒ (raw_lookup emb ptr s' = (SOME v, s'))`,
srw_tac [][] >> Cases_on `ptr` >> Cases_on `emb` >>
fsrw_tac [][is_embed_def] >> srw_tac [][FLOOKUP_UPDATE]);

(* only true for "well-formed" stores that don't bind 0. But maybe lookup should have this property for all stores anyway?
val lookup_pnil = Q.store_thm(
"lookup_pnil",
`lookup pnil s = (NONE, s)`,
srw_tac [][]);
val _ = export_rewrites ["lookup_pnil"];

val HeadOfList_pnil = Q.store_thm(
"HeadOfList_pnil",
`HeadOfList (pnil a) s = (NONE, s)`,
srw_tac [][HeadOfList_def,OPTIONT_BIND_def,UNIT_DEF,BIND_DEF]);
val _ = export_rewrites["HeadOfList_pnil"];

val TailOfList_pnil = Q.store_thm(
"TailOfList_pnil",
`TailOfList (pnil a) s = (NONE, s)`,
srw_tac [][TailOfList_def,OPTIONT_BIND_def,BIND_DEF,UNIT_DEF]);
val _ = export_rewrites["TailOfList_pnil"];
*)

val _ = export_theory ()
