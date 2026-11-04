import Leader.Wu.Splice.PhysicalHoldLeaderDeletionNoGo

set_option autoImplicit false

/-! # Census: certifying physical leader deletions (candidates V10h, V10h2)

Candidate repairs of `B9V10eLeaderPhysicalDeletionNoGo`:
* V10h: whenever the physical row on the served pair would delete the left leader
  (`LeftDeletionCandidate`), perform the certified DELETE write (`deleteWriteV6`: left pending predecessor,
  right reserved front, tickets cleared); otherwise V10g.
* V10h2: the same, except that a left reserved front is never overwritten (it may back a pending
  predecessor on its left); the deletion is held instead.

Census on the physical cores of the no-go fixture (n = 3: site 0 leader label 1, site 1 follower label 0
with bullet 2, site 2 follower label 1) and on the same cores with site 1 also a leader (label 0,
bullet 2): every assignment of 13 controller shapes to each of the three cells (2197 configurations per
core set).  For every `SpliceSafeV7g` start and every served edge: is `SpliceSafeV7g` true after one
service?  Recorded output (#eval, 2026-09-13):

  fixture cores:     756 safe starts x 3 edges; V10g failures 99, V10h failures 9, V10h2 failures 0
  two-leader cores:  756 safe starts x 3 edges; V10g failures 0,  V10h failures 9, V10h2 failures 0

The V10h failures are the DELETE write overwriting a left reserved front that backs a pending predecessor
(first failure: edge 0 with roles front-pending / neutral / predecessor-pending).  V10h2 removes all
failures on both core sets.  Safety only; the hold on a left reserved front needs a liveness check. -/

namespace B9V10hDeletionCensus

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV10b B9SpliceTableV10e B9SpliceTableV10g B9OrphanToFence
open B9V10eLeaderPhysicalDeletionNoGo

instance instDecLeftDeletion (l r : SpliceAgentState 2 1 1) :
    Decidable (LeftDeletionCandidate hTwo hOne hOneTwo l r) := by
  unfold LeftDeletionCandidate; infer_instance

/-- V10h row: certified DELETE on every physical left-leader deletion, else V10g. -/
def rowV10h (l r : R1AgentStateV6 2 1 1) : R1AgentStateV6 2 1 1 × R1AgentStateV6 2 1 1 :=
  if LeftDeletionCandidate hTwo hOne hOneTwo l.carrier.splice r.carrier.splice then
    deleteWriteV6 hTwo hOne hOneTwo l r
  else rowV10g hTwo hOne hOneTwo l r

/-- Refinement: a left reserved front may back a pending predecessor on its left, so it is never
overwritten; the deletion is held instead. -/
def rowV10h2 (l r : R1AgentStateV6 2 1 1) : R1AgentStateV6 2 1 1 × R1AgentStateV6 2 1 1 :=
  if LeftDeletionCandidate hTwo hOne hOneTwo l.carrier.splice r.carrier.splice then
    if ReservedFrontHoldGuard l.carrier then (l, r) else deleteWriteV6 hTwo hOne hOneTwo l r
  else rowV10g hTwo hOne hOneTwo l r

def stepV10h2 (C : R1ConfigV6 3 2 1 1) (e : Fin 3) : R1ConfigV6 3 2 1 1 :=
  if ring3.rightNeighbor e = e then C
  else
    let w := rowV10h2 (C e) (C (ring3.rightNeighbor e))
    fun i => if i = e then w.1 else if i = ring3.rightNeighbor e then w.2 else C i

def stepV10h (C : R1ConfigV6 3 2 1 1) (e : Fin 3) : R1ConfigV6 3 2 1 1 :=
  if ring3.rightNeighbor e = e then C
  else
    let w := rowV10h (C e) (C (ring3.rightNeighbor e))
    fun i => if i = e then w.1 else if i = ring3.rightNeighbor e then w.2 else C i

def leaderView1 : PeaceView 2 :=
  { leader := true, label := 0, shield := false, bullet := 2, signal_B := 0 }
def leaderRaw1 : AgentState 2 := PeaceView.toState leaderView1
theorem leaderDomain1 : leaderRaw1.inProtocolDomain 1 := by
  simp [leaderRaw1, leaderView1, PeaceView.toState, AgentState.inProtocolDomain]

def mk (b : ExpiringAgentState 2 1 1) (r : SpliceRole) (p t : Bool) : R1AgentStateV6 2 1 1 :=
  ⟨{ splice := { base := b, spliceRole := r }, repairPending := p }, t⟩

def shapesOn (b : ExpiringAgentState 2 1 1) : List (R1AgentStateV6 2 1 1) :=
  [mk b .none false false, mk b .none false true, mk b .none true false,
   mk b .front false false, mk b .front true false, mk b .front true true, mk b .front false true,
   mk b .predecessorArmed false false, mk b .predecessorArmed true false, mk b .predecessorArmed true true,
   mk b .victimArmed false false, mk b .victimArmed true false, mk b .victimArmed true true]

def census (b0 b1 b2 : ExpiringAgentState 2 1 1) : String := Id.run do
  let mut safeStarts := 0
  let mut failG := 0
  let mut failH := 0
  let mut failH2 := 0
  let mut firstH : String := ""
  let mut failsH2 : List String := []
  for u in shapesOn b0 do
    for v in shapesOn b1 do
      for w in shapesOn b2 do
        let C : R1ConfigV6 3 2 1 1 := fun i => if i = 0 then u else if i = 1 then v else w
        if decide (SpliceSafeV7g hTwo ring3 C) then
          safeStarts := safeStarts + 1
          for e in List.finRange 3 do
            if !(decide (SpliceSafeV7g hTwo ring3 (stepV10g hTwo hOne hOneTwo ring3 C e))) then
              failG := failG + 1
            if !(decide (SpliceSafeV7g hTwo ring3 (stepV10h2 C e))) then
              failH2 := failH2 + 1
              if failsH2.length < 6 then
                failsH2 := failsH2 ++ [s!"e{e.val}:{repr (role u.carrier)}/{u.carrier.repairPending}/{u.acquireTicket},{repr (role v.carrier)}/{v.carrier.repairPending}/{v.acquireTicket},{repr (role w.carrier)}/{w.carrier.repairPending}/{w.acquireTicket}"]
            if !(decide (SpliceSafeV7g hTwo ring3 (stepV10h C e))) then
              failH := failH + 1
              if firstH == "" then
                firstH := s!"edge {e.val}: roles {repr (role u.carrier)}/{u.carrier.repairPending}/{u.acquireTicket}, {repr (role v.carrier)}/{v.carrier.repairPending}/{v.acquireTicket}, {repr (role w.carrier)}/{w.carrier.repairPending}/{w.acquireTicket}"
  return s!"safeStarts={safeStarts} (x3 edges) V10g failures={failG} V10h failures={failH} V10h2 failures={failH2} first V10h failure: {firstH} | V10h2 failures: {failsH2}"


end B9V10hDeletionCensus
