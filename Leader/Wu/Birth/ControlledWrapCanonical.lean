import Leader.Wu.Birth.ControlledWrapConsumerLaws

namespace BirthB1ControlledWrapCanonical

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

abbrev FC (n psi kappa tau : Nat) :=
  BirthB1ControlledWrap.FC n psi kappa tau

/-- Remove only the live echo scar. -/
def clearEchoScar (u : AgentState psi) : AgentState psi :=
  { u with echo := false }

/-- Remove only the live reset-command scar. -/
def clearResetScar (u : AgentState psi) : AgentState psi :=
  { u with reset_cmd := false }

/-- The requested active echo is otherwise a passive cell. -/
def CanonicalActiveEcho
    (ring : DirectedRing n) (current : FC n psi kappa tau)
    (a : Fin n) (echoPos : Nat) : Prop :=
  Passive (clearEchoScar
    (raw (current (groupOffset ring a echoPos))))

/-- On the maximal route the reset front is fixed at `corridorLen`; deleting
only that reset bit leaves no exported drain material. -/
def CanonicalActiveReset
    (ring : DirectedRing n) (current : FC n psi kappa tau)
    (a : Fin n) (corridorLen : Nat) : Prop :=
  DrainQuiescent (clearResetScar
    (raw (current (drainSite ring a corridorLen))))

/-- R5 invariant exactly as requested: maximal reset front plus canonical
active echo/reset scars. -/
def ControlledWrapInvariantCanonical
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (initial current : FC n psi kappa tau)
    (a : Fin n) (corridorLen echoPos : Nat) : Prop :=
  ControlledWrapInvariant hpsi ring initial current a
      corridorLen echoPos corridorLen ∧
    CanonicalActiveEcho ring current a echoPos ∧
    CanonicalActiveReset ring current a corridorLen

/-- With reset fixed at the maximal frontier, the rank is just echo position. -/
def controlledWrapCanonicalMeasure (echoPos : Nat) : Nat := echoPos

theorem controlledWrapCanonicalMeasure_step
    (echoPos : Nat) (hpos : 0 < echoPos) :
    controlledWrapCanonicalMeasure (echoPos - 1) <
      controlledWrapCanonicalMeasure echoPos := by
  unfold controlledWrapCanonicalMeasure
  omega

/-- The generic echo target that R5 asked to prove.  The theorem below
certifies that this target is still false for the active-only invariant. -/
def ControlledWrapCanonicalEchoConsumerStepStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (initial current : FC n psi kappa tau)
      (a : Fin n) (corridorLen echoPos : Nat),
    ControlledWrapInvariantCanonical hpsi ring initial current a
      corridorLen echoPos ->
    0 < echoPos ->
    let e := echoTransportEdge ring a echoPos
    PreparedOrdinaryOpen hpsi
        (current e) (current (ring.rightNeighbor e)) ->
    RowPreCap2 hpsi h2 kappa ring current e ->
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring current e
    HasLeader D ∨
      ControlledWrapInvariantCanonical hpsi ring initial D a
        corridorLen (echoPos - 1)

/-- Exact distance-zero collision target for the maximal-front route. -/
def ControlledWrapCanonicalCollisionConsumerStepStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (initial current : FC n psi kappa tau)
      (a : Fin n) (corridorLen : Nat),
    ControlledWrapInvariantCanonical hpsi ring initial current a
      corridorLen 0 ->
    let e := drainSite ring a corridorLen
    PreparedOrdinaryOpen hpsi
        (current e) (current (ring.rightNeighbor e)) ->
    RowPreCap2 hpsi h2 kappa ring current e ->
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring current e
    HasLeader D ∨
      (BirthShortDoneTerminalFirstHit.Leaderless D ∧
        TripleLabels hpsi ring D a ∧
        CorridorTerminated ring D a corridorLen ∧
        ThreeSiteSanitized hpsi ring D a)

/-- Strengthened producer handoff: the maximal right-drain frontier has the
canonical moving-pair invariant immediately, so no reset-step induction remains. -/
def RightDrainControlledWrapCanonicalEntryStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi) (_hn : 4 <= n)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n psi kappa tau) (a : Fin n),
    BirthShortDoneTerminalFirstHit.Leaderless C ->
    TripleLabels hpsi ring C a ->
    ∃ corridorLen : Nat, ∃ pre : List (Fin n),
      0 < corridorLen ∧
      2 + corridorLen + 1 = n ∧
      (let drain := rightDrainWord ring a corridorLen
       let w := pre ++ drain
       let frontier := currentRun hpsi h2 ring C w
       WordSupported ring a corridorLen w ∧
        (HasLeaderAlong hpsi h2 ring C w ∨
          (LeaderlessAlong hpsi h2 ring C w ∧
            AlignedAlong hpsi h2 ring C w a ∧
            ControlledWrapInvariantCanonical hpsi ring frontier frontier a
              corridorLen 2)))

/-! ## Active-only echo canonicality is not successor closed -/

private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private def ring4 : DirectedRing 4 := ⟨by decide⟩

abbrev C4 := FC 4 2 2 0

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

private def baseRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell (regs 0)
  else if i = 1 then cell (regs 1)
  else if i = 2 then cell (regs 0)
  else { cell (regs 1) with reset_cmd := true }

/-- Site 2 is the clean active echo; site 1 is the still-unconstrained next
counterclockwise destination and carries the shield obstruction. -/
private def destinationShieldRaw (i : Fin 4) : AgentState 2 :=
  if i = 1 then { baseRaw i with shield := true }
  else if i = 2 then { baseRaw i with echo := true }
  else baseRaw i

private theorem destinationShieldRaw_domain (i : Fin 4) :
    (destinationShieldRaw i).inProtocolDomain 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [baseRaw, destinationShieldRaw, regs, AgentState.inProtocolDomain, BirthWaitPassive.cell]

private def destinationShield : C4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain
      (destinationShieldRaw i) (destinationShieldRaw_domain i), false⟩, 0⟩

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

private theorem destination_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless destinationShield := by
  intro i
  revert i
  decide

private theorem destination_labels :
    TripleLabels hTwo ring4 destinationShield (0 : Fin 4) := by
  unfold TripleLabels
  decide

private theorem destination_front :
    ResetFrontAt ring4 destinationShield destinationShield (0 : Fin 4) 1 :=
  front4_of destinationShield (by decide) (by decide)

private theorem destination_unique :
    UniqueProtectedEchoAt ring4 destinationShield (0 : Fin 4) 2 := by
  refine ⟨by decide, by decide, ?_⟩
  intro q hq hne
  have hc : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hc with rfl | rfl | h2
  · decide
  · decide
  · exact (hne h2).elim

private theorem destination_old_invariant :
    ControlledWrapInvariant hTwo ring4 destinationShield destinationShield
      (0 : Fin 4) 1 2 1 := by
  refine ⟨by decide, by decide, by decide, by decide,
    destination_leaderless, destination_labels, destination_front,
    destination_unique, ?_, ?_⟩
  · intro q hgt hle
    omega
  · intro k hk hlt
    omega

private theorem destination_active_echo_canonical :
    CanonicalActiveEcho ring4 destinationShield (0 : Fin 4) 2 := by
  unfold CanonicalActiveEcho clearEchoScar
  unfold BirthWaitPassive.Passive BirthWaitPassive.Metadata
    BirthWaitPassive.InertWriter
  decide

private theorem destination_active_reset_canonical :
    CanonicalActiveReset ring4 destinationShield (0 : Fin 4) 1 := by
  unfold CanonicalActiveReset clearResetScar
  unfold DrainQuiescent BirthWaitPassive.Metadata BirthWaitPassive.InertWriter
  decide

private theorem destination_invariant :
    ControlledWrapInvariantCanonical hTwo ring4
      destinationShield destinationShield (0 : Fin 4) 1 2 :=
  ⟨destination_old_invariant, destination_active_echo_canonical,
    destination_active_reset_canonical⟩

private def destinationEdge : Fin 4 :=
  echoTransportEdge ring4 (0 : Fin 4) 2

private theorem destination_open :
    PreparedOrdinaryOpen hTwo
      (destinationShield destinationEdge)
      (destinationShield (ring4.rightNeighbor destinationEdge)) := by
  unfold BirthShortDoneTerminalB1EntranceR2.PreparedOrdinaryOpen
  dsimp only
  decide

private theorem destination_precap :
    RowPreCap2 hTwo hTwoLe 2 ring4 destinationShield destinationEdge := by
  unfold BirthShortDoneTerminalPassiveR4.RowPreCap2
    BirthShortDoneTerminalPassiveR4.RowCap2
  dsimp only
  decide

private def destinationAfter : C4 :=
  BirthShortDoneTerminalConsumer.step
    hTwo (by decide : 0 < 2) hTwoLe ring4 destinationShield destinationEdge

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem destination_after_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless destinationAfter := by
  intro i
  revert i
  decide

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
/-- Literal row: echo moves 2 -> 1 and the destination shield is framed. -/
theorem destination_after_fields :
    (raw (destinationAfter 1)).echo = true ∧
      (raw (destinationAfter 1)).shield = true ∧
      (raw (destinationAfter 2)).echo = false := by
  decide

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem destination_after_not_active_canonical :
    ¬ CanonicalActiveEcho ring4 destinationAfter (0 : Fin 4) 1 := by
  unfold CanonicalActiveEcho clearEchoScar
  unfold BirthWaitPassive.Passive BirthWaitPassive.Metadata
    BirthWaitPassive.InertWriter
  decide

private theorem destination_after_not_invariant :
    ¬ ControlledWrapInvariantCanonical hTwo ring4
      destinationShield destinationAfter (0 : Fin 4) 1 1 := by
  intro h
  exact destination_after_not_active_canonical h.2.1

private theorem noLeader_of_leaderless
    (C : C4) (h : BirthShortDoneTerminalFirstHit.Leaderless C) :
    ¬ HasLeader C := by
  intro hl
  rcases hl with ⟨i, hi⟩
  have hz := h i
  have hbad : true = false := hi.symm.trans hz
  cases hbad

/-- Second obstruction: the active-only canonical strengthening still does not
make the generic literal-consumer echo law true. -/
theorem controlledWrapCanonicalEchoConsumerStepStatement_false :
    ¬ ControlledWrapCanonicalEchoConsumerStepStatement
      (kappa := 2) (tau := 0) hTwo hTwoLe ring4 := by
  intro h
  have hs := h destinationShield destinationShield (0 : Fin 4) 1 2
    destination_invariant (by decide) destination_open destination_precap
  rcases hs with hl | hi
  · exact noLeader_of_leaderless destinationAfter
      destination_after_leaderless hl
  · exact destination_after_not_invariant hi

/-! ## Maximal frontier does satisfy the two active-scar clauses -/

private def qSourceRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell (regs 0)
  else if i = 1 then cell (regs 1)
  else if i = 2 then { cell (regs 0) with reset_cmd := true }
  else cell (regs 1)

private theorem qSourceRaw_domain (i : Fin 4) :
    (qSourceRaw i).inProtocolDomain 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [baseRaw, destinationShieldRaw, qSourceRaw, regs, AgentState.inProtocolDomain, BirthWaitPassive.cell]

private def qSource : C4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain
      (qSourceRaw i) (qSourceRaw_domain i), false⟩, 0⟩

private def qFrontier : C4 :=
  currentRun hTwo hTwoLe ring4 qSource [(2 : Fin 4)]

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem qFrontier_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless qFrontier := by
  intro i
  revert i
  decide

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem qFrontier_labels :
    TripleLabels hTwo ring4 qFrontier (0 : Fin 4) := by
  unfold TripleLabels
  decide

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem qFrontier_front :
    ResetFrontAt ring4 qFrontier qFrontier (0 : Fin 4) 1 :=
  front4_of qFrontier (by decide) (by decide)

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem qFrontier_unique :
    UniqueProtectedEchoAt ring4 qFrontier (0 : Fin 4) 2 := by
  refine ⟨by decide, by decide, ?_⟩
  intro q hq hne
  have hc : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hc with rfl | rfl | h2
  · decide
  · decide
  · exact (hne h2).elim

private theorem qFrontier_old_invariant :
    ControlledWrapInvariant hTwo ring4 qFrontier qFrontier
      (0 : Fin 4) 1 2 1 := by
  refine ⟨by decide, by decide, by decide, by decide,
    qFrontier_leaderless, qFrontier_labels, qFrontier_front,
    qFrontier_unique, ?_, ?_⟩
  · intro q hgt hle
    omega
  · intro k hk hlt
    omega

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
/-- These are the genuinely new R5 clauses, and the frontier passes
both by closed evaluation. -/
theorem q11694_frontier_active_scars_canonical :
    CanonicalActiveEcho ring4 qFrontier (0 : Fin 4) 2 ∧
      CanonicalActiveReset ring4 qFrontier (0 : Fin 4) 1 := by
  constructor
  · unfold CanonicalActiveEcho clearEchoScar
    unfold BirthWaitPassive.Passive BirthWaitPassive.Metadata
      BirthWaitPassive.InertWriter
    decide
  · unfold CanonicalActiveReset clearResetScar
    unfold DrainQuiescent BirthWaitPassive.Metadata BirthWaitPassive.InertWriter
    decide

/-- Full strengthened maximal-frontier check for the fixture. -/
theorem q11694_frontier_canonical :
    ControlledWrapInvariantCanonical hTwo ring4 qFrontier qFrontier
      (0 : Fin 4) 1 2 :=
  ⟨qFrontier_old_invariant,
    q11694_frontier_active_scars_canonical.1,
    q11694_frontier_active_scars_canonical.2⟩

#print axioms BirthB1ControlledWrapCanonical.controlledWrapCanonicalMeasure_step
#print axioms BirthB1ControlledWrapCanonical.destination_after_fields
#print axioms BirthB1ControlledWrapCanonical.controlledWrapCanonicalEchoConsumerStepStatement_false
#print axioms BirthB1ControlledWrapCanonical.q11694_frontier_active_scars_canonical
#print axioms BirthB1ControlledWrapCanonical.q11694_frontier_canonical

end BirthB1ControlledWrapCanonical
