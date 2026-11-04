import Leader.Wu.Splice.ZeroRefreshBlockMass

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceOneServiceBridge

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign FiniteUniformStoppingTree
open B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
open B9SpliceV10cLiveness B9SpliceBlockDrainMass

variable {n psi width kappa tau : Nat}

private theorem handoff_not_zero_refresh
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : HostFenceAdvanceGuardV10b hpsi l r) :
    ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r := by
  intro hz
  have hr : role (rowV10b hpsi hwidth hle l r).1.carrier = role l.carrier :=
    hz.2.2.2.1.2.1
  rw [show rowV10b hpsi hwidth hle l r = hostFenceHandoffWriteV10b l r by
    simp [rowV10b, hg]] at hr
  have hr' :
      role (setControl l.carrier SpliceRole.predecessorArmed false) =
        SpliceRole.none := by
    simpa [hostFenceHandoffWriteV10b, hg.1.1] using hr
  change SpliceRole.predecessorArmed = SpliceRole.none at hr'
  exact absurd hr' (by decide)

theorem handoff_v10c_then_v6_drop
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hg : HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e))) :
    let H := stepV10c hpsi hwidth hle ring C e
    controllerPotentialV6 (stepV6 hpsi hwidth hle ring H e) <
      controllerPotentialV6 H := by
  have hz := handoff_not_zero_refresh hpsi hwidth hle
    (C e) (C (ring.rightNeighbor e)) hg
  have heq : stepV10c hpsi hwidth hle ring C e =
      stepV10b hpsi hwidth hle ring C e := by
    funext i
    simp [stepV10c, stepV10b, rowV10c, hne, hz]
  dsimp only
  rw [heq]
  exact handoff_next_v6_service_drops hpsi hwidth hle ring C e hne hg

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private def bridgeRing3 : DirectedRing 3 := ⟨hThree⟩
private def handoffStart3 : R1ConfigV6 3 2 1 1 := q11874StartV10b
private def handoffAfter1 :=
  stepV10c hTwo hOne hOneTwo bridgeRing3 handoffStart3 (0 : Fin 3)
private def handoffAfter2 :=
  stepV10c hTwo hOne hOneTwo bridgeRing3 handoffAfter1 (0 : Fin 3)

set_option maxRecDepth 20000 in
theorem handoff_one_service_counterexample :
    LiveNonClearV10c hTwo bridgeRing3 handoffStart3 ∧
    HostFenceAdvanceGuardV10b hTwo
      (handoffStart3 (0 : Fin 3)) (handoffStart3 (1 : Fin 3)) ∧
    controllerPotentialV6 handoffStart3 = 1 ∧
    controllerPotentialV6 handoffAfter1 = 11 ∧
    controllerPotentialV6 handoffAfter2 = 9 ∧
    ¬ ControllerProductiveServiceV10c hTwo hOne hOneTwo
      bridgeRing3 handoffStart3 (0 : Fin 3) := by
  unfold LiveNonClearV10c HostFenceAdvanceGuardV10b ControllerProductiveServiceV10c
  decide

def samePortSerialStep {n : Nat} (p : ThreePortSerialCount.Ports n) :
    Bool -> Fin n -> StopNode Bool
  | false, e =>
      if e = p.a then .active true
      else if e = p.b then .failure
      else if e = p.c then .failure
      else .active false
  | true, e =>
      if e = p.a then .success
      else if e = p.b then .failure
      else if e = p.c then .failure
      else .active true

private theorem success_terminal_count {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S) (T : Nat) :
    treeWeight step successWeight (.success : StopNode S) T = n ^ T := by
  rw [treeWeight_success]
  change n ^ T * 1 = n ^ T
  exact Nat.mul_one _

private theorem failure_terminal_count {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S) (T : Nat) :
    treeWeight step successWeight (.failure : StopNode S) T = 0 := by
  rw [treeWeight_failure]
  change n ^ T * 0 = 0
  exact Nat.mul_zero _

/-- Fully typed terminal counts for any Bool-indexed matcher. -/
private theorem bool_terminal_counts {n : Nat}
    (step : Bool -> Fin n -> StopNode Bool) (T : Nat) :
    treeWeight step (successWeight : StopNode Bool -> Nat)
        (.success : StopNode Bool) T = n ^ T ∧
      treeWeight step (successWeight : StopNode Bool -> Nat)
        (.failure : StopNode Bool) T = 0 := by
  exact ⟨success_terminal_count step T, failure_terminal_count step T⟩

/-- Fully typed terminal counts for any Unit-indexed stage matcher. -/
private theorem unit_terminal_counts {n : Nat}
    (step : Unit -> Fin n -> StopNode Unit) (T : Nat) :
    treeWeight step (successWeight : StopNode Unit -> Nat)
        (.success : StopNode Unit) T = n ^ T ∧
      treeWeight step (successWeight : StopNode Unit -> Nat)
        (.failure : StopNode Unit) T = 0 := by
  exact ⟨success_terminal_count step T, failure_terminal_count step T⟩

private theorem samePort_second_eq_stage {n : Nat}
    (p : ThreePortSerialCount.Ports n) (T : Nat) :
    successCount (samePortSerialStep p) (.active true) T =
      successCount (ThreePortSerialCount.stageStep p) (.active ()) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      change (List.ofFn (fun e : Fin n => treeWeight (samePortSerialStep p)
        successWeight (samePortSerialStep p true e) T)).sum =
        (List.ofFn (fun e : Fin n => treeWeight (ThreePortSerialCount.stageStep p)
          successWeight (ThreePortSerialCount.stageStep p () e) T)).sum
      apply ofFn_sum_eq
      intro e
      have hba : p.b ≠ p.a := p.ab.symm
      have hca : p.c ≠ p.a := p.ac.symm
      have hcb : p.c ≠ p.b := p.bc.symm
      have hBool := bool_terminal_counts (samePortSerialStep p) T
      have hUnit := unit_terminal_counts (ThreePortSerialCount.stageStep p) T
      by_cases ha : e = p.a
      · subst e
        have hs : samePortSerialStep p true p.a = (.success : StopNode Bool) := by
          change (if p.a = p.a then (.success : StopNode Bool)
            else if p.a = p.b then .failure
            else if p.a = p.c then .failure else .active true) = .success
          exact if_pos rfl
        have ht : ThreePortSerialCount.stageStep p () p.a =
            (.success : StopNode Unit) := by
          change (if p.a = p.a then (.success : StopNode Unit)
            else if p.a = p.b then .failure
            else if p.a = p.c then .failure else .active ()) = .success
          exact if_pos rfl
        rw [hs, ht]
        exact hBool.1.trans hUnit.1.symm
      · by_cases hb : e = p.b
        · subst e
          have hs : samePortSerialStep p true p.b = (.failure : StopNode Bool) := by
            change (if p.b = p.a then (.success : StopNode Bool)
              else if p.b = p.b then .failure
              else if p.b = p.c then .failure else .active true) = .failure
            rw [if_neg hba]
            exact if_pos rfl
          have ht : ThreePortSerialCount.stageStep p () p.b =
              (.failure : StopNode Unit) := by
            change (if p.b = p.a then (.success : StopNode Unit)
              else if p.b = p.b then .failure
              else if p.b = p.c then .failure else .active ()) = .failure
            rw [if_neg hba]
            exact if_pos rfl
          rw [hs, ht]
          exact hBool.2.trans hUnit.2.symm
        · by_cases hc : e = p.c
          · subst e
            have hs : samePortSerialStep p true p.c = (.failure : StopNode Bool) := by
              change (if p.c = p.a then (.success : StopNode Bool)
                else if p.c = p.b then .failure
                else if p.c = p.c then .failure else .active true) = .failure
              rw [if_neg hca, if_neg hcb]
              exact if_pos rfl
            have ht : ThreePortSerialCount.stageStep p () p.c =
                (.failure : StopNode Unit) := by
              change (if p.c = p.a then (.success : StopNode Unit)
                else if p.c = p.b then .failure
                else if p.c = p.c then .failure else .active ()) = .failure
              rw [if_neg hca, if_neg hcb]
              exact if_pos rfl
            rw [hs, ht]
            exact hBool.2.trans hUnit.2.symm
          · have hs : samePortSerialStep p true e = .active true := by
              change (if e = p.a then (.success : StopNode Bool)
                else if e = p.b then .failure
                else if e = p.c then .failure else .active true) = .active true
              rw [if_neg ha, if_neg hb, if_neg hc]
            have ht : ThreePortSerialCount.stageStep p () e = .active () := by
              change (if e = p.a then (.success : StopNode Unit)
                else if e = p.b then .failure
                else if e = p.c then .failure else .active ()) = .active ()
              rw [if_neg ha, if_neg hb, if_neg hc]
            rw [hs, ht]
            change successCount (samePortSerialStep p) (.active true) T =
              successCount (ThreePortSerialCount.stageStep p) (.active ()) T
            exact ih

private theorem samePort_eq_serial_count {n : Nat}
    (p : ThreePortSerialCount.Ports n) (hn : 3 <= n) (T : Nat) :
    successCount (samePortSerialStep p) (.active false) T =
      successCount (ThreePortSerialCount.serialStep p) (.active false) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      have hp :
          successCount (samePortSerialStep p) (.active true) T =
            successCount (ThreePortSerialCount.serialStep p) (.active true) T :=
        (samePort_second_eq_stage p T).trans
          (ThreePortSerialCount.serial_second_eq_stage p hn T).symm
      change (List.ofFn (fun e : Fin n => treeWeight (samePortSerialStep p)
        successWeight (samePortSerialStep p false e) T)).sum =
        (List.ofFn (fun e : Fin n => treeWeight (ThreePortSerialCount.serialStep p)
          successWeight (ThreePortSerialCount.serialStep p false e) T)).sum
      apply ofFn_sum_eq
      intro e
      have hba : p.b ≠ p.a := p.ab.symm
      have hca : p.c ≠ p.a := p.ac.symm
      have hcb : p.c ≠ p.b := p.bc.symm
      have hSame := bool_terminal_counts (samePortSerialStep p) T
      have hSerial := bool_terminal_counts (ThreePortSerialCount.serialStep p) T
      by_cases ha : e = p.a
      · subst e
        have hs : samePortSerialStep p false p.a = .active true := by
          change (if p.a = p.a then (.active true : StopNode Bool)
            else if p.a = p.b then .failure
            else if p.a = p.c then .failure else .active false) = .active true
          exact if_pos rfl
        have ht : ThreePortSerialCount.serialStep p false p.a = .active true := by
          change (if p.a = p.a then (.active true : StopNode Bool)
            else if p.a = p.b then .failure
            else if p.a = p.c then .failure else .active false) = .active true
          exact if_pos rfl
        rw [hs, ht]
        change successCount (samePortSerialStep p) (.active true) T =
          successCount (ThreePortSerialCount.serialStep p) (.active true) T
        exact hp
      · by_cases hb : e = p.b
        · subst e
          have hs : samePortSerialStep p false p.b = (.failure : StopNode Bool) := by
            change (if p.b = p.a then (.active true : StopNode Bool)
              else if p.b = p.b then .failure
              else if p.b = p.c then .failure else .active false) = .failure
            rw [if_neg hba]
            exact if_pos rfl
          have ht : ThreePortSerialCount.serialStep p false p.b =
              (.failure : StopNode Bool) := by
            change (if p.b = p.a then (.active true : StopNode Bool)
              else if p.b = p.b then .failure
              else if p.b = p.c then .failure else .active false) = .failure
            rw [if_neg hba]
            exact if_pos rfl
          rw [hs, ht]
          exact hSame.2.trans hSerial.2.symm
        · by_cases hc : e = p.c
          · subst e
            have hs : samePortSerialStep p false p.c = (.failure : StopNode Bool) := by
              change (if p.c = p.a then (.active true : StopNode Bool)
                else if p.c = p.b then .failure
                else if p.c = p.c then .failure else .active false) = .failure
              rw [if_neg hca, if_neg hcb]
              exact if_pos rfl
            have ht : ThreePortSerialCount.serialStep p false p.c =
                (.failure : StopNode Bool) := by
              change (if p.c = p.a then (.active true : StopNode Bool)
                else if p.c = p.b then .failure
                else if p.c = p.c then .failure else .active false) = .failure
              rw [if_neg hca, if_neg hcb]
              exact if_pos rfl
            rw [hs, ht]
            exact hSame.2.trans hSerial.2.symm
          · have hs : samePortSerialStep p false e = .active false := by
              change (if e = p.a then (.active true : StopNode Bool)
                else if e = p.b then .failure
                else if e = p.c then .failure else .active false) = .active false
              rw [if_neg ha, if_neg hb, if_neg hc]
            have ht : ThreePortSerialCount.serialStep p false e = .active false := by
              change (if e = p.a then (.active true : StopNode Bool)
                else if e = p.b then .failure
                else if e = p.c then .failure else .active false) = .active false
              rw [if_neg ha, if_neg hb, if_neg hc]
            rw [hs, ht]
            change successCount (samePortSerialStep p) (.active false) T =
              successCount (ThreePortSerialCount.serialStep p) (.active false) T
            exact ih

theorem same_port_serial_sixteenth {n : Nat}
    (p : ThreePortSerialCount.Ports n) (hn : 3 <= n) :
    n ^ (4 * n) <= 16 *
      successCount (samePortSerialStep p) (.active false) (4 * n) := by
  rw [samePort_eq_serial_count p hn (4 * n)]
  exact ThreePortSerialCount.serial_sixteenth p hn

theorem handoff_serial_branch
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (p : ThreePortSerialCount.Ports n) (hn : 3 <= n) (ha : p.a = e)
    (hne : ring.rightNeighbor e ≠ e)
    (hg : HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e))) :
    p.a = e ∧
    (let H := stepV10c hpsi hwidth hle ring C e
     controllerPotentialV6 (stepV6 hpsi hwidth hle ring H e) <
       controllerPotentialV6 H) ∧
    n ^ (4 * n) <= 16 *
      successCount (samePortSerialStep p) (.active false) (4 * n) := by
  exact ⟨ha, handoff_v10c_then_v6_drop hpsi hwidth hle ring C e hne hg,
    same_port_serial_sixteenth p hn⟩

end B9SpliceOneServiceBridge

#print axioms B9SpliceOneServiceBridge.handoff_v10c_then_v6_drop
#print axioms B9SpliceOneServiceBridge.handoff_one_service_counterexample
#print axioms B9SpliceOneServiceBridge.same_port_serial_sixteenth
#print axioms B9SpliceOneServiceBridge.handoff_serial_branch
