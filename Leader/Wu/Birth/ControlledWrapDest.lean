import Leader.Wu.Birth.ControlledWrapCanonical


namespace BirthB1ControlledWrapDest


open PPLL PPLLDomain
open BirthWaitPassive
open BirthB1ControlledWrap
open BirthB1ControlledWrapCanonical
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


/-- Every protected destination not yet crossed is passive after deleting only
its possible live echo bit.  The old `ProtectedClearedAfterEcho` covers the
strictly crossed suffix. -/
def ProtectedDestinationsCanonical
    (ring : DirectedRing n) (current : FC n psi kappa tau)
    (a : Fin n) (echoPos : Nat) : Prop :=
  ∀ q, q <= echoPos -> q <= 2 ->
    Passive (clearEchoScar
      (raw (current (groupOffset ring a q))))


/-- R6 invariant: maximal reset front, every not-yet-crossed protected
position canonical modulo echo, and the maximal reset scar canonical. -/
def ControlledWrapInvariantDest
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (initial current : FC n psi kappa tau)
    (a : Fin n) (corridorLen echoPos : Nat) : Prop :=
  ControlledWrapInvariant hpsi ring initial current a
      corridorLen echoPos corridorLen ∧
    ProtectedDestinationsCanonical ring current a echoPos ∧
    CanonicalActiveReset ring current a corridorLen


/-- The R6 destination clause subsumes R5 active-echo canonicality. -/
theorem activeEchoCanonical_of_dest
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (initial current : FC n psi kappa tau)
    (a : Fin n) (corridorLen echoPos : Nat)
    (h : ControlledWrapInvariantDest hpsi ring initial current a
      corridorLen echoPos) :
    CanonicalActiveEcho ring current a echoPos := by
  rcases h with ⟨hold, hdest, _⟩
  rcases hold with ⟨_, _, _, _, _, _, _, huniq, _, _⟩
  exact hdest echoPos (Nat.le_refl echoPos) huniq.1


private theorem shield_true_not_passive_after_clearEcho
    (u : AgentState psi) (hs : u.shield = true) :
    ¬ Passive (clearEchoScar u) := by
  intro hp
  unfold BirthWaitPassive.Passive BirthWaitPassive.Metadata at hp
  have h := congrArg (fun v : AgentState psi => v.shield) hp.1
  simp [clearEchoScar, BirthWaitPassive.cell, hs] at h


/-- Any shield on a not-yet-crossed protected destination contradicts R6. -/
theorem protectedDestination_shield_false
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (initial current : FC n psi kappa tau)
    (a : Fin n) (corridorLen echoPos q : Nat)
    (h : ControlledWrapInvariantDest hpsi ring initial current a
      corridorLen echoPos)
    (hq : q <= echoPos) (hq2 : q <= 2)
    (hs : (raw (current (groupOffset ring a q))).shield = true) : False := by
  exact (shield_true_not_passive_after_clearEcho _ hs)
    (h.2.1 q hq hq2)


/-- Exact R6 echo target.  The remaining proof leaf is the full-host
passive-mod-echo row law described in the answer. -/
def ControlledWrapDestEchoConsumerStepStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (initial current : FC n psi kappa tau)
      (a : Fin n) (corridorLen echoPos : Nat),
    ControlledWrapInvariantDest hpsi ring initial current a
      corridorLen echoPos ->
    0 < echoPos ->
    let e := echoTransportEdge ring a echoPos
    PreparedOrdinaryOpen hpsi
        (current e) (current (ring.rightNeighbor e)) ->
    RowPreCap2 hpsi h2 kappa ring current e ->
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring current e
    HasLeader D ∨
      ControlledWrapInvariantDest hpsi ring initial D a
        corridorLen (echoPos - 1)


/-- Exact distance-zero R6 collision target. -/
def ControlledWrapDestCollisionConsumerStepStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (initial current : FC n psi kappa tau)
      (a : Fin n) (corridorLen : Nat),
    ControlledWrapInvariantDest hpsi ring initial current a
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


/-- Producer handoff after the maximal right-drain prefix. -/
def RightDrainControlledWrapDestEntryStatement
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
            ControlledWrapInvariantDest hpsi ring frontier frontier a
              corridorLen 2)))


/-! Closed frontier check. -/


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


private def qSourceRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell (regs 0)
  else if i = 1 then cell (regs 1)
  else if i = 2 then { cell (regs 0) with reset_cmd := true }
  else cell (regs 1)


private theorem qSourceRaw_domain (i : Fin 4) :
    (qSourceRaw i).inProtocolDomain 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [qSourceRaw, regs, AgentState.inProtocolDomain,
      BirthWaitPassive.cell]


private def qSource : C4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain
      (qSourceRaw i) (qSourceRaw_domain i), false⟩, 0⟩


private def qFrontier : C4 :=
  currentRun hTwo hTwoLe ring4 qSource [(2 : Fin 4)]


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


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem qFrontier_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless qFrontier := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;> decide


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
/-- The new R6 clause holds at q = 0,1,2 on the literal frontier. -/
theorem q11694_frontier_destinations :
    ProtectedDestinationsCanonical ring4 qFrontier (0 : Fin 4) 2 := by
  unfold ProtectedDestinationsCanonical
  intro q hq hq2
  have hc : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hc with rfl | rfl | rfl <;>
    unfold clearEchoScar BirthWaitPassive.Passive
      BirthWaitPassive.Metadata BirthWaitPassive.InertWriter <;>
    decide


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem qFrontier_reset_canonical :
    CanonicalActiveReset ring4 qFrontier (0 : Fin 4) 1 := by
  unfold CanonicalActiveReset clearResetScar
  unfold DrainQuiescent BirthWaitPassive.Metadata BirthWaitPassive.InertWriter
  decide


/-- Full R6 frontier check. -/
theorem q11694_frontier_dest :
    ControlledWrapInvariantDest hTwo ring4 qFrontier qFrontier
      (0 : Fin 4) 1 2 :=
  ⟨qFrontier_old_invariant,
    q11694_frontier_destinations,
    qFrontier_reset_canonical⟩


#print axioms BirthB1ControlledWrapDest.activeEchoCanonical_of_dest
#print axioms BirthB1ControlledWrapDest.protectedDestination_shield_false
#print axioms BirthB1ControlledWrapDest.q11694_frontier_destinations
#print axioms BirthB1ControlledWrapDest.q11694_frontier_dest


end BirthB1ControlledWrapDest
