import Leader.Wu.Birth.ControlledWrapCollisionLift

namespace BirthB1ControlledWrapAligned

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait
open BirthB1ControlledWrap BirthB1ControlledWrapCanonical
open BirthB1ControlledWrapDest BirthB1RightDrainProducer
open Q11632RightDrainCollar
open BirthShortDoneTerminalB1EntranceR2
open BirthShortDoneTerminalPassiveR4
open BirthB1ControlledWrapCollisionLift

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthB1ControlledWrapDest.FC n psi kappa tau

/-- The maximal reset edge is a literal successor-label edge. -/
def ClosingEdgeAligned (hpsi : 0 < psi) (ring : DirectedRing n)
    (current : FC n psi kappa tau) (a : Fin n)
    (corridorLen : Nat) : Prop :=
  let e := drainSite ring a corridorLen
  (raw (current (ring.rightNeighbor e))).label =
    ⟨((raw (current e)).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩

/-- R8: R6/Dest plus the only field relation missing from the audit. -/
def ControlledWrapInvariantAligned
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (initial current : FC n psi kappa tau)
    (a : Fin n) (corridorLen echoPos : Nat) : Prop :=
  ControlledWrapInvariantDest hpsi ring initial current a
      corridorLen echoPos ∧
    ClosingEdgeAligned hpsi ring current a corridorLen

private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private def ring4 : DirectedRing 4 := ⟨by decide⟩
abbrev C4 := FC 4 2 2 0

private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

private def regs (label : Fin 2) : Registers 2 where
  label := label
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

/-! Reconstruct the literal frontier. -/
private def qSourceRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell (regs 0)
  else if i = 1 then cell (regs 1)
  else if i = 2 then { cell (regs 0) with reset_cmd := true }
  else cell (regs 1)

private theorem qSourceRaw_domain (i : Fin 4) :
    (qSourceRaw i).inProtocolDomain 2 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    simp [qSourceRaw, regs, AgentState.inProtocolDomain,
      BirthWaitPassive.cell]

private def qSource : C4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain
      (qSourceRaw i) (qSourceRaw_domain i), false⟩, 0⟩

private def qFrontier : C4 :=
  currentRun hTwo hTwoLe ring4 qSource [(2 : Fin 4)]

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
/-- The existing R6 theorem is definitionally this reconstructed frontier;
    the new closing label equation is a literal finite check. -/
theorem q11694_frontier_aligned :
    ControlledWrapInvariantAligned hTwo ring4 qFrontier qFrontier
      (0 : Fin 4) 1 2 := by
  have hd := BirthB1ControlledWrapDest.q11694_frontier_dest
  change ControlledWrapInvariantDest hTwo ring4 qFrontier qFrontier
    (0 : Fin 4) 1 2 at hd
  refine ⟨hd, ?_⟩
  unfold ClosingEdgeAligned
  decide

/-! Literal representatives of the four successive counterexamples. -/
private def baseRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell (regs 0)
  else if i = 1 then cell (regs 1)
  else if i = 2 then cell (regs 0)
  else cell (regs 1)

private def weakRaw (i : Fin 4) : AgentState 2 :=
  if i = 3 then { baseRaw i with reset_cmd := true } else baseRaw i

private def activeShieldRaw (i : Fin 4) : AgentState 2 :=
  if i = 2 then { weakRaw i with echo := true, shield := true }
  else weakRaw i

private def nextShieldRaw (i : Fin 4) : AgentState 2 :=
  if i = 1 then { weakRaw i with shield := true }
  else if i = 2 then { weakRaw i with echo := true }
  else weakRaw i

private def closingRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then { cell (regs 0) with echo := true }
  else if i = 1 then cell (regs 1)
  else if i = 2 then cell (regs 0)
  else { cell (regs 0) with reset_cmd := true }

private theorem weakRaw_domain (i : Fin 4) :
    (weakRaw i).inProtocolDomain 2 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    simp [weakRaw, baseRaw, regs, AgentState.inProtocolDomain,
      BirthWaitPassive.cell]

private theorem activeShieldRaw_domain (i : Fin 4) :
    (activeShieldRaw i).inProtocolDomain 2 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    simp [activeShieldRaw, weakRaw, baseRaw, regs,
      AgentState.inProtocolDomain, BirthWaitPassive.cell]

private theorem nextShieldRaw_domain (i : Fin 4) :
    (nextShieldRaw i).inProtocolDomain 2 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    simp [nextShieldRaw, weakRaw, baseRaw, regs,
      AgentState.inProtocolDomain, BirthWaitPassive.cell]

private theorem closingRaw_domain (i : Fin 4) :
    (closingRaw i).inProtocolDomain 2 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    simp [closingRaw, regs, AgentState.inProtocolDomain,
      BirthWaitPassive.cell]

private def weak : C4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain (weakRaw i) (weakRaw_domain i), false⟩, 0⟩
private def activeShield : C4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain
      (activeShieldRaw i) (activeShieldRaw_domain i), false⟩, 0⟩
private def nextShield : C4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain
      (nextShieldRaw i) (nextShieldRaw_domain i), false⟩, 0⟩
private def closing : C4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain
      (closingRaw i) (closingRaw_domain i), false⟩, 0⟩

/-- Weak entry: no active echo. -/
theorem weak_entry_violates_aligned :
    ¬ ControlledWrapInvariantAligned hTwo ring4 weak weak
      (0 : Fin 4) 1 2 := by
  intro h
  rcases h.1.1 with ⟨_, _, _, _, _, _, _, he, _, _⟩
  have ht := he.2.1
  have hf :
      (raw (weak (groupOffset ring4 (0 : Fin 4) 2))).echo = false := by
    decide
  have hbad : (false : Bool) = true := hf.symm.trans ht
  cases hbad

/-- Active-echo shield witness. -/
theorem active_shield_violates_aligned :
    ¬ ControlledWrapInvariantAligned hTwo ring4 activeShield activeShield
      (0 : Fin 4) 1 2 := by
  intro h
  exact BirthB1ControlledWrapDest.protectedDestination_shield_false
    hTwo ring4 activeShield activeShield (0 : Fin 4) 1 2 2
    h.1 (by decide) (by decide) (by decide)

/-- Next-destination shield witness. -/
theorem next_shield_violates_aligned :
    ¬ ControlledWrapInvariantAligned hTwo ring4 nextShield nextShield
      (0 : Fin 4) 1 2 := by
  intro h
  exact BirthB1ControlledWrapDest.protectedDestination_shield_false
    hTwo ring4 nextShield nextShield (0 : Fin 4) 1 2 1
    h.1 (by decide) (by decide) (by decide)

/-- Closing-label witness: Dest passes, alignment fails. -/
theorem closing_label_violates_aligned :
    ¬ ControlledWrapInvariantAligned hTwo ring4 closing closing
      (0 : Fin 4) 1 0 := by
  intro h
  have hn :
      ¬ ClosingEdgeAligned hTwo ring4 closing (0 : Fin 4) 1 := by
    unfold ClosingEdgeAligned
    decide
  exact hn h.2

/-- Exact remaining local whole-host leaf. -/
abbrev AlignedCollisionLiftTarget : Prop :=
  FullTerminalRow2ResetEchoCollisionAlignedPreCapStatement

end BirthB1ControlledWrapAligned

#print axioms BirthB1ControlledWrapAligned.q11694_frontier_aligned
#print axioms BirthB1ControlledWrapAligned.weak_entry_violates_aligned
#print axioms BirthB1ControlledWrapAligned.active_shield_violates_aligned
#print axioms BirthB1ControlledWrapAligned.next_shield_violates_aligned
#print axioms BirthB1ControlledWrapAligned.closing_label_violates_aligned
