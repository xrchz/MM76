open HolKernel Parse bossLib

(* Non-monad problems with TFL isolated from
   trying to get monadic definitions through *)
val _ = new_theory "defn_failure"

val ifcong_defn = Hol_defn "ifcong"
  `ifcong n = (if n = 0 then EVERY ifcong else NULL) [1]`;

val ifcong2_defn = Hol_defn "ifcong2"
  `ifcong2 n = (if n = 0 then (λls. EVERY ifcong2 ls) else NULL) [1]`;

(* recommended solution is to use AND_CONG for this
val ifcong3_defn = Defn.Hol_defn "ifcong3"
  `ifcong3 n = (if n = 0 then (λls. (ls = [1]) ∧ EVERY ifcong3 ls) else NULL) [1]`;
*)

val foo0_defn = Hol_defn "foo0" `foo0 = (λs. s ≠ 0 ∧ foo0 (s - 1))`;

val foo1_defn = Hol_defn "foo1" `foo1 x = (λs. s ≤ x ∧ foo1 x (SUC s))`;

val _ = export_theory ();
