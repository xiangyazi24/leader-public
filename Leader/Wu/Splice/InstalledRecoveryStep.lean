import Leader.Wu.Splice.RecoveryFinalStepMass
import Leader.Wu.Splice.InstalledCarrier

set_option autoImplicit false
set_option Elab.async false

namespace ZZRecoveryJ3V3B

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
open B9SpliceTableHost B9SpliceV10hControllerRowsSafe
open B9ControllerRecovery B9FullCarrierRows B9SpliceTableV10g
open ZZFinalCarrierV3

variable {n ψ κ τ : Nat}

abbrev V3Cell (ψ κ τ : Nat) := ZZFinalCarrierV3.Cell ψ κ τ
abbrev V3Config (n ψ κ τ : Nat) := ZZFinalCarrierV3.Config n ψ κ τ

section GarbageProjection

/-- The recovery-only step already inlined in `stepFinalV3`.
This only names those two branches; it is not a second protocol. -/
noncomputable def recoveryStepV3
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : V3Config n ψ κ τ) (e : Fin n) : V3Config n ψ κ τ := by
  classical
  exact if ring.rightNeighbor e = e then
    if FinalGarbageV3 hψ (C e) (C e) then
      B9FullCarrierHost.writeAtP ring C e
        (clearFinalControlV3 (C e), C e)
    else C
  else
    B9FullCarrierHost.writeAtP ring C e
      (recoverPairV3 hψ (C e) (C (ring.rightNeighbor e)))

/-- Key equation (a): garbage has absolute priority in the final V3 action. -/
theorem finalActionV3_eq_recovery_of_finalGarbage
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : PortV3 (κ := κ) (τ := τ) hψ h2)
    (l r : V3Cell ψ κ τ)
    (hg : FinalGarbageV3 hψ l r) :
    finalActionV3 hψ h2 port l r = .recovery := by
  unfold finalActionV3
  rw [if_pos hg]

/-- Key equation (b): the recovery action executes `recoverPairV3`. -/
theorem rowFinalV3_eq_recoverPairV3_of_finalGarbage
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (port : PortV3 (κ := κ) (τ := τ) hψ h2)
    (l r : V3Cell ψ κ τ)
    (hg : FinalGarbageV3 hψ l r) :
    rowFinalV3 hψ h2 port l r = recoverPairV3 hψ l r := by
  unfold rowFinalV3
  rw [finalActionV3_eq_recovery_of_finalGarbage hψ h2 port l r hg]

/-- On a garbage edge, the exact installed V3 step is its inlined recovery. -/
theorem stepConcreteV3_eq_recoveryStepV3_of_finalGarbage
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : V3Config n ψ κ τ) (e : Fin n)
    (hg : FinalGarbageV3 hψ (C e) (C (ring.rightNeighbor e))) :
    stepConcreteV3 (κ := κ) (τ := τ) hψ h2 ring C e =
      recoveryStepV3 hψ ring C e := by
  classical
  by_cases hs : ring.rightNeighbor e = e
  · have hg0 : FinalGarbageV3 hψ (C e) (C e) := by
      simpa [hs] using hg
    unfold stepConcreteV3 stepFinalV3 recoveryStepV3
    simp only [if_pos hs, if_pos hg0]
  · have hrow :
        rowFinalV3 hψ h2
            (concretePortV3 (κ := κ) (τ := τ) hψ h2)
            (C e) (C (ring.rightNeighbor e)) =
          recoverPairV3 hψ (C e) (C (ring.rightNeighbor e)) :=
      rowFinalV3_eq_recoverPairV3_of_finalGarbage
        hψ h2
        (concretePortV3 (κ := κ) (τ := τ) hψ h2)
        (C e) (C (ring.rightNeighbor e)) hg
    unfold stepConcreteV3 stepFinalV3 recoveryStepV3
    simp only [if_neg hs]
    rw [hrow]

@[simp] private theorem oldCellV3_clearFinalControl_direct
    (u : V3Cell ψ κ τ) :
    oldCellV3 (clearFinalControlV3 u) =
      clearControlV6 (oldCellV3 u) := rfl

@[simp] private theorem oldCellV3_coverFinal_left_direct
    (l r : V3Cell ψ κ τ) :
    oldCellV3 (coverFinalV3 l r).1 =
      (coverWrite (oldCellV3 l) (oldCellV3 r)).1 := rfl

@[simp] private theorem oldCellV3_coverFinal_right_direct
    (l r : V3Cell ψ κ τ) :
    oldCellV3 (coverFinalV3 l r).2 =
      (coverWrite (oldCellV3 l) (oldCellV3 r)).2 := rfl

private theorem oldConfigV3_writeAtP_direct
    (ring : DirectedRing n) (C : V3Config n ψ κ τ) (e : Fin n)
    (w : V3Cell ψ κ τ × V3Cell ψ κ τ) :
    oldConfigV3 (B9FullCarrierHost.writeAtP ring C e w) =
      B9SpliceV10hControllerRowsSafe.writeAt ring (oldConfigV3 C) e
        (oldCellV3 w.1, oldCellV3 w.2) := by
  funext i
  by_cases hi : i = e
  · simp [oldConfigV3, B9FullCarrierHost.writeAtP,
      B9SpliceV10hControllerRowsSafe.writeAt, hi]
  · by_cases hj : i = ring.rightNeighbor e
    · by_cases hs : ring.rightNeighbor e = e
      · exact (hi (hj.trans hs)).elim
      · simp [oldConfigV3, B9FullCarrierHost.writeAtP,
          B9SpliceV10hControllerRowsSafe.writeAt, hi, hj, hs]
    · simp [oldConfigV3, B9FullCarrierHost.writeAtP,
        B9SpliceV10hControllerRowsSafe.writeAt, hi, hj]

/-- The lifted V3 recovery pair projects to the accepted old recovery row.
The old host is arbitrary: garbage fires before the fallback host row. -/
private theorem recoverPairV3_old_to_rowRecover_direct
    (oldHost : HostRow (OldPhys ψ κ τ)) (hψ : 0 < ψ)
    (l r : V3Cell ψ κ τ) (hg : FinalGarbageV3 hψ l r) :
    (oldCellV3 (recoverPairV3 hψ l r).1,
      oldCellV3 (recoverPairV3 hψ l r).2) =
      rowRecoverH oldHost hψ (oldCellV3 l) (oldCellV3 r) := by
  classical
  have href := B9FullCarrierRows.rowRecoverOldP_toOld oldHost hψ
    (B9FullCarrierHost.oldToP (oldCellV3 l))
    (B9FullCarrierHost.oldToP (oldCellV3 r))
  simp only [B9FullCarrierHost.toOld_oldToP] at href
  change Garbage hψ (oldCellV3 l) (oldCellV3 r) at hg
  calc
    (oldCellV3 (recoverPairV3 hψ l r).1,
      oldCellV3 (recoverPairV3 hψ l r).2) =
        (B9FullCarrierHost.toOld B9FullCarrierHost.oldLaws
            (B9FullCarrierRows.rowRecoverOldP oldHost hψ
              (B9FullCarrierHost.oldToP (oldCellV3 l))
              (B9FullCarrierHost.oldToP (oldCellV3 r))).1,
         B9FullCarrierHost.toOld B9FullCarrierHost.oldLaws
            (B9FullCarrierRows.rowRecoverOldP oldHost hψ
              (B9FullCarrierHost.oldToP (oldCellV3 l))
              (B9FullCarrierHost.oldToP (oldCellV3 r))).2) := by
      by_cases hL : BadTicket (oldCellV3 l)
      · simp [recoverPairV3, FinalBadTicketV3,
          B9FullCarrierRows.rowRecoverOldP,
          B9FullCarrierRows.exactOldRowP, rowRecoverH, hL]
      · by_cases hR : BadTicket (oldCellV3 r)
        · simp [recoverPairV3, FinalBadTicketV3,
            B9FullCarrierRows.rowRecoverOldP,
            B9FullCarrierRows.exactOldRowP, rowRecoverH, hL, hR]
        · by_cases hB : BadBacking (oldCellV3 l) (oldCellV3 r)
          · simp [recoverPairV3, FinalBadTicketV3, FinalBadBackingV3,
              B9FullCarrierRows.rowRecoverOldP,
              B9FullCarrierRows.exactOldRowP, rowRecoverH, hL, hR, hB]
          · have hH : Hole hψ (oldCellV3 l) (oldCellV3 r) := by
              rcases hg with (a | a | a) | a
              · exact (hL a).elim
              · exact (hR a).elim
              · exact (hB a).elim
              · exact a
            simp [recoverPairV3, FinalBadTicketV3, FinalBadBackingV3,
              FinalHoleV3, B9FullCarrierRows.rowRecoverOldP,
              B9FullCarrierRows.exactOldRowP, rowRecoverH,
              hL, hR, hB, hH]
    _ = rowRecoverH oldHost hψ (oldCellV3 l) (oldCellV3 r) := href

private theorem oldConfigV3_recoveryStepV3_eq_stepRecover_direct
    (oldHost : HostRow (OldPhys ψ κ τ))
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : V3Config n ψ κ τ) (e : Fin n)
    (hg : FinalGarbageV3 hψ (C e) (C (ring.rightNeighbor e))) :
    oldConfigV3 (recoveryStepV3 hψ ring C e) =
      stepRecover oldHost hψ ring (oldConfigV3 C) e := by
  classical
  by_cases hs : ring.rightNeighbor e = e
  · have hg0 : FinalGarbageV3 hψ (C e) (C e) := by
      simpa [hs] using hg
    have hgo :
        Garbage hψ ((oldConfigV3 C) e) ((oldConfigV3 C) e) := hg0
    unfold recoveryStepV3 stepRecover
    simp only [if_pos hs, if_pos hg0, if_pos hgo]
    rw [oldConfigV3_writeAtP_direct]
    simp only [oldCellV3_clearFinalControl_direct]
    rfl
  · unfold recoveryStepV3 stepRecover
    simp only [if_neg hs]
    rw [oldConfigV3_writeAtP_direct]
    apply congrArg (fun w =>
      B9SpliceV10hControllerRowsSafe.writeAt ring (oldConfigV3 C) e w)
    exact recoverPairV3_old_to_rowRecover_direct oldHost hψ
      (C e) (C (ring.rightNeighbor e)) hg

/-- Exact V3 analogue of
`B9RecoveryJ3Direct.stepConcrete_oldConfig_eq_stepRecover_of_finalGarbage`. -/
theorem stepConcreteV3_oldConfigV3_eq_stepRecover_of_finalGarbage
    (oldHost : HostRow (OldPhys ψ κ τ))
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : V3Config n ψ κ τ) (e : Fin n)
    (hg : FinalGarbageV3 hψ (C e) (C (ring.rightNeighbor e))) :
    oldConfigV3
        (stepConcreteV3 (κ := κ) (τ := τ) hψ h2 ring C e) =
      stepRecover oldHost hψ ring (oldConfigV3 C) e := by
  rw [stepConcreteV3_eq_recoveryStepV3_of_finalGarbage
    (κ := κ) (τ := τ) hψ h2 ring C e hg]
  exact oldConfigV3_recoveryStepV3_eq_stepRecover_direct
    oldHost hψ ring C e hg

#print axioms ZZRecoveryJ3V3B.finalActionV3_eq_recovery_of_finalGarbage
#print axioms ZZRecoveryJ3V3B.rowFinalV3_eq_recoverPairV3_of_finalGarbage
#print axioms ZZRecoveryJ3V3B.stepConcreteV3_eq_recoveryStepV3_of_finalGarbage
#print axioms ZZRecoveryJ3V3B.stepConcreteV3_oldConfigV3_eq_stepRecover_of_finalGarbage

end GarbageProjection
end ZZRecoveryJ3V3B
