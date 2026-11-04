import Leader.Wu.Birth.RightDrainProducer

namespace BirthB1CorridorAbsorption

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLWallSweepRepair
open BirthWaitPassive
open BirthShortDoneTerminalB1EntranceR2
open Q11632RightDrainCollar
open BirthB1RightDrainProducer

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

/-- Corrected Phase C for the controlled-wrap route.

The corridor is maximal, so its right endpoint is the predecessor of `a`.
Unlike `CorridorAbsorptionStatement`, protected sites may become temporarily
non-Passive while the echo moves counterclockwise through the triple.  The
ruler must remain aligned throughout, and the same strong final sanitation
requirements are retained. -/
def ControlledWrapAbsorptionStatement
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (current : BirthB1RightDrainProducer.FC n psi kappa tau)
      (a : Fin n) (corridorLen : Nat),
    0 < corridorLen →
    2 + corridorLen + 1 = n →
    BirthShortDoneTerminalFirstHit.Leaderless current →
    TripleLabels hpsi ring current a →
    ResetFrontAt ring current current a corridorLen →
    ∃ finish : List (Fin n),
      WordSupported ring a corridorLen finish ∧
      (let D := currentRun hpsi h2 ring current finish
       HasLeaderAlong hpsi h2 ring current finish ∨
        (LeaderlessAlong hpsi h2 ring current finish ∧
          AlignedAlong hpsi h2 ring current finish a ∧
          CorridorTerminated ring D a corridorLen ∧
          ThreeSiteSanitized hpsi ring D a))

/-! ## Minimal literal obstruction: n = 4, psi = 2 -/

private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 ≤ 2 := by decide

def ringFour : DirectedRing 4 := ⟨by decide⟩

abbrev E4 := ExpiringAgentState 2 2 0
abbrev FC4 := Fin 4 → E4

private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  omega

private def d0 : Registers 2 where
  label := 0
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

private def d1 : Registers 2 where
  label := 1
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

/-- Same smallest geometry as the frontier above: labels 0,1,0,1 and a reset command on
    protected tail site 2. -/
private def sourceRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell d0
  else if i = 1 then cell d1
  else if i = 2 then { cell d0 with reset_cmd := true }
  else cell d1

private theorem sourceRaw_domain (i : Fin 4) :
    (sourceRaw i).inProtocolDomain 2 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    simp [sourceRaw, d0, d1, AgentState.inProtocolDomain,
      BirthWaitPassive.cell]

private def source : FC4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain
      (sourceRaw i) (sourceRaw_domain i), false⟩, 0⟩

/-- Terminal reset-front state: execute 2 -> 3 once. -/
private def frontier : FC4 :=
  BirthShortDoneTerminalB1EntranceR2.currentRun
    hTwo hTwoLe ringFour source [(2 : Fin 4)]

/-- First reverse echo move: 1 -> 2. -/
private def leftStep : FC4 :=
  BirthShortDoneTerminalB1EntranceR2.currentRun
    hTwo hTwoLe ringFour frontier [(1 : Fin 4)]

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontier_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless frontier := by
  intro i
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontier_labels :
    TripleLabels hTwo ringFour frontier (0 : Fin 4) := by
  unfold TripleLabels
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- At the terminal one-site front, using `frontier` itself as the `initial`
    state is valid because the "strictly ahead" clause is vacuous. -/
private theorem frontier_reset_front :
    ResetFrontAt ringFour frontier frontier (0 : Fin 4) 1 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    decide
  · intro j hj hbound
    omega

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontier_tail_echo :
    (raw (frontier (2 : Fin 4))).echo = true := by
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontier_boundary_reset :
    (raw (frontier (3 : Fin 4))).reset_cmd = true := by
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- Site 1 has not participated in the 2 -> 3 row. -/
private theorem frontier_site1_passive :
    Passive (raw (frontier (1 : Fin 4))) := by
  unfold BirthWaitPassive.Passive BirthWaitPassive.Metadata
    BirthWaitPassive.InertWriter
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- The exact observer says that the first reverse-echo row is not a birth. -/
private theorem left_birth_false :
    BirthShortDoneTerminalObserver.birthEvent
      hTwo hTwo hTwoLe
      (frontier (1 : Fin 4))
      (frontier (ringFour.rightNeighbor (1 : Fin 4))) = false := by
  decide

/-- Therefore the literal current-consumer row stays physically leaderless. -/
private theorem leftStep_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless leftStep := by
  have h :=
    BirthShortDoneTerminalFirstHit.step_leaderless_of_no_birth
      hTwo hTwo hTwoLe ringFour frontier (1 : Fin 4)
      frontier_leaderless left_birth_false
  simpa [leftStep, BirthShortDoneTerminalB1EntranceR2.currentRun,
    LDSinkBoundedKernel.run] using h

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- Literal SUPPRESS direction on the complete current consumer: the echo is
    removed from responder site 2 and appears on initiator site 1. -/
private theorem leftStep_echo_transport :
    (raw (leftStep (2 : Fin 4))).echo = false ∧
      (raw (leftStep (1 : Fin 4))).echo = true := by
  decide

private theorem leftStep_site1_not_passive :
    ¬ Passive (raw (leftStep (1 : Fin 4))) := by
  intro hp
  have hf := Q11632RightDrainCollar.passive_echo_false hp
  have ht := leftStep_echo_transport.2
  have hbad : true = false := ht.symm.trans hf
  cases hbad

private theorem site1_protected :
    ProtectedSite ringFour (0 : Fin 4) (1 : Fin 4) := by
  unfold ProtectedSite
  exact Or.inr (Or.inl (by decide))

/-- Smallest literal no-reentry failure.  The exact no-birth echo-transfer row
    must dirty site 1, which was already Passive at prefix zero. -/
private theorem left_transport_breaks_no_reentry :
    ¬ PassiveNoReentry hTwo hTwoLe ringFour frontier
      [(1 : Fin 4)] (0 : Fin 4) := by
  intro h
  have hp0 :
      Passive
        (raw ((runPrefix hTwo hTwoLe ringFour frontier
          [(1 : Fin 4)] 0) (1 : Fin 4))) := by
    exact frontier_site1_passive
  have hp1 :=
    h 0 1 (by omega) (by decide) (1 : Fin 4) site1_protected hp0
  have hp1' : Passive (raw (leftStep (1 : Fin 4))) := by
    simpa [runPrefix, leftStep] using hp1
  exact leftStep_site1_not_passive hp1'

/-- The complete minimal counterexample fixture.  This refutes the intended
    leaderless/no-reentry Phase-C mechanism: the first reverse echo move is an
    actual no-birth current-consumer row, remains leaderless, but necessarily
    violates `PassiveNoReentry`. -/
theorem minimal_literal_no_reentry_obstruction :
    BirthShortDoneTerminalFirstHit.Leaderless frontier ∧
      TripleLabels hTwo ringFour frontier (0 : Fin 4) ∧
      ResetFrontAt ringFour frontier frontier (0 : Fin 4) 1 ∧
      (raw (frontier (2 : Fin 4))).echo = true ∧
      BirthShortDoneTerminalObserver.birthEvent
        hTwo hTwo hTwoLe
        (frontier (1 : Fin 4))
        (frontier (ringFour.rightNeighbor (1 : Fin 4))) = false ∧
      BirthShortDoneTerminalFirstHit.Leaderless leftStep ∧
      (raw (leftStep (2 : Fin 4))).echo = false ∧
      (raw (leftStep (1 : Fin 4))).echo = true ∧
      ¬ PassiveNoReentry hTwo hTwoLe ringFour frontier
        [(1 : Fin 4)] (0 : Fin 4) := by
  exact ⟨frontier_leaderless, frontier_labels, frontier_reset_front,
    frontier_tail_echo, left_birth_false, leftStep_leaderless,
    leftStep_echo_transport.1, leftStep_echo_transport.2,
    left_transport_breaks_no_reentry⟩

/-! ## Literal support already admits the closing wrap at n = 4 -/

/-- For corridorLen = 1 the declared drain region is the whole four-site ring,
    so the edge 3 -> 0 satisfies `WordSupported`.  This formally records that
    the current support predicate is not, literally, a no-wrap predicate. -/
theorem literal_support_allows_wrap :
    WordSupported ringFour (0 : Fin 4) 1 [(3 : Fin 4)] := by
  intro e he
  have heq : e = (3 : Fin 4) := by
    simpa using he
  subst e
  constructor
  · unfold InDrainRegion
    exact ⟨3, by decide, by decide⟩
  · unfold InDrainRegion
    exact ⟨0, by decide, by decide⟩

/-! ## Failure of sanitation is not a birth rule -/

/-- The declaration used in the route argument: a false physical observer
    event preserves literal leaderlessness.  Nothing about sanitation failure
    appears in the hypothesis. -/
theorem no_birth_event_preserves_physical_leaderlessness
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : BirthB1RightDrainProducer.FC n psi kappa tau)
    (e : Fin n)
    (hz : BirthShortDoneTerminalFirstHit.Leaderless C)
    (hb : BirthShortDoneTerminalObserver.birthEvent
      hpsi (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e)) = false) :
    BirthShortDoneTerminalFirstHit.Leaderless
      (BirthShortDoneTerminalConsumer.step
        hpsi (by decide : 0 < 2) h2 ring C e) := by
  exact
    BirthShortDoneTerminalFirstHit.step_leaderless_of_no_birth
      hpsi (by decide : 0 < 2) h2 ring C e hz hb

end BirthB1CorridorAbsorption

#print axioms BirthB1CorridorAbsorption.minimal_literal_no_reentry_obstruction
#print axioms BirthB1CorridorAbsorption.literal_support_allows_wrap
#print axioms BirthB1CorridorAbsorption.no_birth_event_preserves_physical_leaderlessness
