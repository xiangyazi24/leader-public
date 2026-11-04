import Leader.Wu.Birth.ControlledWrapGeneral

namespace BirthB1ControlledWrapConsumerLaws

open PPLL PPLLDomain
open BirthWaitPassive
open BirthB1ControlledWrap
open BirthB1ControlledWrapGeneral
open BirthB1RightDrainProducer
open Q11632RightDrainCollar
open BirthShortDoneTerminalB1EntranceR2
open BirthShortDoneTerminalPassiveR4

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private def ring4 : DirectedRing 4 := ⟨by decide⟩

abbrev C4 := BirthB1ControlledWrap.FC 4 2 2 0

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

/-- Weak-entry fixture: 0,1,0,1; reset only at site 3. -/
private def weakRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell (regs 0)
  else if i = 1 then cell (regs 1)
  else if i = 2 then cell (regs 0)
  else { cell (regs 1) with reset_cmd := true }

private theorem weakRaw_domain (i : Fin 4) :
    (weakRaw i).inProtocolDomain 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [weakRaw, AgentState.inProtocolDomain, BirthWaitPassive.cell, regs]

private def weak : C4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain (weakRaw i) (weakRaw_domain i), false⟩, 0⟩

private theorem front4_of
    (C : C4)
    (h0 : (raw (C (drainSite ring4 (0 : Fin 4) 0))).reset_cmd = false)
    (h1 : (raw (C (drainSite ring4 (0 : Fin 4) 1))).reset_cmd = true) :
    ResetFrontAt ring4 C C (0 : Fin 4) 1 := by
  refine ⟨by decide, h1, ?_, ?_⟩
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact h0
  · intro _ _ _
    rfl

private theorem noLeader_of_leaderless
    (C : C4) (h : BirthShortDoneTerminalFirstHit.Leaderless C) :
    ¬ HasLeader C := by
  intro hleader
  rcases hleader with ⟨i, hi⟩
  have hz := h i
  have hbad : true = false := hi.symm.trans hz
  cases hbad

private theorem weak_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless weak := by
  intro i
  revert i
  decide

private theorem weak_labels : TripleLabels hTwo ring4 weak (0 : Fin 4) := by
  unfold TripleLabels
  decide

private theorem weak_front : ResetFrontAt ring4 weak weak (0 : Fin 4) 1 :=
  front4_of weak (by decide) (by decide)

private theorem weak_fields :
    (∀ i : Fin 4, (raw (weak i)).echo = false) ∧
      (raw (weak 3)).reset_cmd = true ∧
      (raw (weak 0)).reset_cmd = false ∧
      (raw (weak 1)).reset_cmd = false ∧
      (raw (weak 2)).reset_cmd = false := by
  constructor
  · intro i
    revert i
    decide
  · decide

private theorem weak_not_invariant :
    ¬ ControlledWrapInvariant hTwo ring4 weak weak
      (0 : Fin 4) 1 2 1 := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, he, _, _⟩
  have ht := he.2.1
  have hf := weak_fields.1 (groupOffset ring4 (0 : Fin 4) 2)
  have hbad : false = true := hf.symm.trans ht
  cases hbad

/-- Exact weak-entry counterexample, including the raw reset/echo facts. -/
theorem weak_entry_bridge_counterexample :
    0 < (1 : Nat) ∧ 2 + 1 + 1 = 4 ∧
      BirthShortDoneTerminalFirstHit.Leaderless weak ∧
      TripleLabels hTwo ring4 weak (0 : Fin 4) ∧
      ResetFrontAt ring4 weak weak (0 : Fin 4) 1 ∧
      (∀ i : Fin 4, (raw (weak i)).echo = false) ∧
      (raw (weak 3)).reset_cmd = true ∧
      (raw (weak 0)).reset_cmd = false ∧
      (raw (weak 1)).reset_cmd = false ∧
      (raw (weak 2)).reset_cmd = false ∧
      ¬ ControlledWrapInvariant hTwo ring4 weak weak
        (0 : Fin 4) 1 2 1 := by
  exact ⟨by decide, by decide, weak_leaderless, weak_labels, weak_front,
    weak_fields.1, weak_fields.2.1, weak_fields.2.2.1,
    weak_fields.2.2.2.1, weak_fields.2.2.2.2, weak_not_invariant⟩

/-- Stronger form: the imported weak entry statement itself is false. -/
theorem controlledWrapEntryStatement_false :
    ¬ ControlledWrapEntryStatement
      (kappa := 2) (tau := 0) hTwo hTwoLe ring4 := by
  intro h
  have hs := h weak (0 : Fin 4) 1
    (by decide) (by decide) weak_leaderless weak_labels weak_front
  rcases hs with hl | hi
  · exact noLeader_of_leaderless weak weak_leaderless hl
  · exact weak_not_invariant hi

/-- Legal controlled-wrap state whose active echo also carries an unrelated
shield bit.  The current invariant does not forbid this. -/
private def echoRaw (i : Fin 4) : AgentState 2 :=
  if i = 2 then { weakRaw i with echo := true, shield := true }
  else weakRaw i

private theorem echoRaw_domain (i : Fin 4) :
    (echoRaw i).inProtocolDomain 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [echoRaw, weakRaw, AgentState.inProtocolDomain,
      BirthWaitPassive.cell, regs]

private def echoC : C4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain (echoRaw i) (echoRaw_domain i), false⟩, 0⟩

private theorem echo_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless echoC := by
  intro i
  revert i
  decide

private theorem echo_labels : TripleLabels hTwo ring4 echoC (0 : Fin 4) := by
  unfold TripleLabels
  decide

private theorem echo_front : ResetFrontAt ring4 echoC echoC (0 : Fin 4) 1 :=
  front4_of echoC (by decide) (by decide)

private theorem echo_unique :
    UniqueProtectedEchoAt ring4 echoC (0 : Fin 4) 2 := by
  refine ⟨by decide, by decide, ?_⟩
  intro q hq hne
  have hc : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hc with h0 | h12
  · subst q
    decide
  · rcases h12 with h1 | h2
    · subst q
      decide
    · exact (hne h2).elim

private theorem echo_invariant :
    ControlledWrapInvariant hTwo ring4 echoC echoC
      (0 : Fin 4) 1 2 1 := by
  refine ⟨by decide, by decide, by decide, by decide,
    echo_leaderless, echo_labels, echo_front, echo_unique, ?_, ?_⟩
  · intro q hgt hle
    omega
  · intro k hk hlt
    omega

private def echoEdge : Fin 4 :=
  echoTransportEdge ring4 (0 : Fin 4) 2

private theorem echo_open :
    PreparedOrdinaryOpen hTwo
      (echoC echoEdge) (echoC (ring4.rightNeighbor echoEdge)) := by
  unfold BirthShortDoneTerminalB1EntranceR2.PreparedOrdinaryOpen
  dsimp only
  decide

private theorem echo_precap :
    RowPreCap2 hTwo hTwoLe 2 ring4 echoC echoEdge := by
  unfold BirthShortDoneTerminalPassiveR4.RowPreCap2
    BirthShortDoneTerminalPassiveR4.RowCap2
  dsimp only
  decide

private def echoAfter : C4 :=
  BirthShortDoneTerminalConsumer.step
    hTwo (by decide : 0 < 2) hTwoLe ring4 echoC echoEdge

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem echo_after_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless echoAfter := by
  intro i
  revert i
  decide

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem echo_after_transport :
    (raw (echoAfter 1)).echo = true ∧
      (raw (echoAfter 2)).echo = false ∧
      (raw (echoAfter 2)).shield = true := by
  decide

private theorem not_passive_of_shield_true
    (u : AgentState 2) (hs : u.shield = true) :
    ¬ Passive u := by
  intro hp
  have hm := hp.1
  unfold Metadata at hm
  have hz := congrArg (fun v : AgentState 2 => v.shield) hm
  change u.shield = false at hz
  have hbad : true = false := hs.symm.trans hz
  cases hbad

private theorem echo_after_not_invariant :
    ¬ ControlledWrapInvariant hTwo ring4 echoC echoAfter
      (0 : Fin 4) 1 1 1 := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, _, hclear, _⟩
  have hp := hclear 2 (by decide) (by decide)
  have hoff : groupOffset ring4 (0 : Fin 4) 2 = (2 : Fin 4) := by decide
  rw [hoff] at hp
  exact (not_passive_of_shield_true _ echo_after_transport.2.2) hp

/-- The first requested full-consumer law is false under its stated gates. -/
theorem controlledWrapEchoConsumerStepStatement_false :
    ¬ ControlledWrapEchoConsumerStepStatement
      (kappa := 2) (tau := 0) hTwo hTwoLe ring4 := by
  intro h
  have hs := h echoC echoC (0 : Fin 4) 1 2 1
    echo_invariant (by decide) echo_open echo_precap
  have hs' :
      HasLeader echoAfter ∨
        ControlledWrapInvariant hTwo ring4 echoC echoAfter
          (0 : Fin 4) 1 1 1 := by
    simpa [echoAfter, echoEdge] using hs
  rcases hs' with hl | hi
  · exact noLeader_of_leaderless echoAfter echo_after_leaderless hl
  · exact echo_after_not_invariant hi

/-- Exact remaining imported reset-step target. -/
def ResetConsumerLawTarget
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  ControlledWrapResetConsumerStepStatement
    (kappa := kappa) (tau := tau) hpsi h2 ring

/-- Exact remaining imported collision target. -/
def CollisionConsumerLawTarget
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  ControlledWrapCollisionConsumerStepStatement
    (kappa := kappa) (tau := tau) hpsi h2 ring

end BirthB1ControlledWrapConsumerLaws

#print axioms BirthB1ControlledWrapConsumerLaws.weak_entry_bridge_counterexample
#print axioms BirthB1ControlledWrapConsumerLaws.controlledWrapEntryStatement_false
#print axioms BirthB1ControlledWrapConsumerLaws.controlledWrapEchoConsumerStepStatement_false
