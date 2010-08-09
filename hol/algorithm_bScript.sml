open HolKernel boolLib bossLib boolSimps SatisfySimps Parse pairTheory stringTheory substitutionTheory multiequationTheory multiequation_systemTheory pred_setTheory listTheory relationTheory bagTheory finite_mapTheory lcsymtacs

val _ = new_theory "algorithm_b"

val (algb1_rules,algb1_ind,algb1_cases) = Hol_reln`
  wfsystem (t1,u1) ∧
  (s,m) ∈ u1 ∧
  DISJOINT s (BIGUNION (IMAGE FST f)) ∧
  meq_red u1 (s,m) (c,f) u2
    ⇒
  algb1 (t1,u1)
        (SNOC (s,{|c|}) t1,
         (IMAGE (λmeq. (FST meq, BAG_IMAGE (SAPPLY (FUN_FMAP (K c) s)) (SND meq))) (compactify u2))
         DELETE (s,{|c|}))`;

val algb_stop_def = Define`
  algb_stop sys1 sys2 = wfsystem sys1 ∧ algb1^* sys1 sys2 ∧ ∀sys3. ¬algb1 sys2 sys3`;

val algb_fail_def = Define`
  algb_fail (t,u) = ∃s m. (s,m) ∈ u ∧ m ≠ {||} ∧
                    ∀c f. common_part_frontier m (c,f) ⇒
                          ¬ DISJOINT s (BIGUNION (IMAGE FST f))`;

val _ = export_theory ()
