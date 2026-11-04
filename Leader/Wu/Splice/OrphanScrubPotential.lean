import Leader.Wu.Splice.ProvenanceTicketTable
import Leader.Wu.Splice.MovingFrontTable
import Leader.Wu.Splice.ReservedFrontTable


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceOrphanScrubV6


open PPLL
open Q11593SpliceControllerDesign
open B9SpliceControllerR1TableV3
open B9SpliceControllerR1TableV6


variable {n psi kappa tau : Nat}


/-- The V5-style orphan repair lifted to the V6 carrier: keep the left
endpoint and clear the orphan reserved controller on the right. -/
def orphanReservedFrontScrubWriteV6
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  (l, clearControlV6 r)


/-- On an orphan reserved front, clearing the right controller strictly lowers
its V6 controller weight.  The two possible before-weights are 8 (unticketed)
and 6 (ticketed); the cleared weight is 0. -/
theorem orphanReservedFront_clearControl_weight_drop_v6
    (l r : R1AgentStateV6 psi kappa tau)
    (h : OrphanReservedFrontGuardV3 l.carrier r.carrier) :
    controllerWeightV6 (clearControlV6 r) < controllerWeightV6 r := by
  rcases h with ⟨hr, _⟩
  unfold B9SpliceControllerR1TableV2.ReservedFrontHoldGuard at hr
  rcases hr with ⟨hrr, hrp⟩
  change r.carrier.splice.spliceRole = .front at hrr
  cases hrt : r.acquireTicket <;>
    simp [controllerWeightV6, clearControlV6, setControlV6,
      withCarrierClearTicketV6, B9SpliceControllerR1Table.setControl, B9SpliceControllerR1Table.role,
      hrr, hrp, hrt] <;> omega


/-- Exact V6 analogue of V5 `orphanReservedFront_write_drop`. -/
theorem orphanReservedFront_scrub_write_drop_v6
    (l r : R1AgentStateV6 psi kappa tau)
    (h : OrphanReservedFrontGuardV3 l.carrier r.carrier) :
    pairPotentialV6
        (orphanReservedFrontScrubWriteV6 l r).1
        (orphanReservedFrontScrubWriteV6 l r).2 <
      pairPotentialV6 l r := by
  change controllerWeightV6 l + controllerWeightV6 (clearControlV6 r) <
    controllerWeightV6 l + controllerWeightV6 r
  exact Nat.add_lt_add_left
    (orphanReservedFront_clearControl_weight_drop_v6 l r h)
    (controllerWeightV6 l)


/-- Configuration-level operation corresponding to executing only the proposed
orphan scrub at the right endpoint of edge `e`. -/
def orphanReservedFrontScrubAtV6
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) : R1ConfigV6 n psi kappa tau :=
  fun i =>
    if i = ring.rightNeighbor e then clearControlV6 (C i) else C i


private theorem ofFn_sum_le_scrub {m : Nat}
    (f g : Fin m -> Nat) (hfg : forall i, f i <= g i) :
    (List.ofFn f).sum <= (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))


private theorem ofFn_sum_lt_of_single_lt_scrub {m : Nat}
    (f g : Fin m -> Nat) (chosen : Fin m)
    (hle : forall i, f i <= g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction m with
  | zero => exact Fin.elim0 chosen
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hz : chosen = 0
      · subst chosen
        have ht := ofFn_sum_le_scrub
          (fun i : Fin m => f i.succ)
          (fun i => g i.succ) (fun i => hle i.succ)
        exact Nat.add_lt_add_of_lt_of_le hlt ht
      · have hz' : chosen.val ≠ 0 := fun h => hz (Fin.ext h)
        let p : Fin m := ⟨chosen.val - 1, by
          have hc := chosen.isLt
          omega⟩
        have hs : p.succ = chosen := Fin.ext (by simp [p]; omega)
        have ht := ih
          (fun i : Fin m => f i.succ)
          (fun i => g i.succ) p
          (fun i => hle i.succ)
          (by simpa only [hs] using hlt)
        have hh := hle 0
        omega


/-- If the proposed orphan scrub is actually applied to the configuration,
the global V6 controller potential strictly drops. -/
theorem orphanReservedFront_scrub_controllerPotential_drop_v6
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n)
    (h : OrphanReservedFrontGuardV3
      (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    controllerPotentialV6 (orphanReservedFrontScrubAtV6 ring C e) <
      controllerPotentialV6 C := by
  let j := ring.rightNeighbor e
  have hg : OrphanReservedFrontGuardV3 (C e).carrier (C j).carrier := by
    simpa only [j] using h
  have hlocal :=
    orphanReservedFront_clearControl_weight_drop_v6 (C e) (C j) hg
  have hlt :
      controllerWeightV6 (orphanReservedFrontScrubAtV6 ring C e j) <
        controllerWeightV6 (C j) := by
    simpa [orphanReservedFrontScrubAtV6, j] using hlocal
  have hleW : forall i,
      controllerWeightV6 (orphanReservedFrontScrubAtV6 ring C e i) <=
        controllerWeightV6 (C i) := by
    intro i
    by_cases hij : i = j
    · subst i
      exact Nat.le_of_lt hlt
    · simp [orphanReservedFrontScrubAtV6, j, hij]
  unfold controllerPotentialV6
  exact ofFn_sum_lt_of_single_lt_scrub _ _ j hleW hlt


end B9SpliceOrphanScrubV6


#print axioms B9SpliceOrphanScrubV6.orphanReservedFront_clearControl_weight_drop_v6
#print axioms B9SpliceOrphanScrubV6.orphanReservedFront_scrub_write_drop_v6
#print axioms B9SpliceOrphanScrubV6.orphanReservedFront_scrub_controllerPotential_drop_v6
