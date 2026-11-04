import Leader.Wu.Birth.SingleUseReleaseWitnesses

set_option autoImplicit false

namespace BirthOneBitReleaseBoundary

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair PPLLNoCheckBirthOutputLegitimacy
  PPLLWallSweepFinite PPLLWallSweepRepair
  BirthSingleUseReleaseRepair BirthGenerationControlRepair BirthMismatchDisposalProducer
  BirthTossCheckPreservationRepair BirthArrivalCaptureRepair

/-! At psi one, DISAPPEAR's label-zero producer is itself terminal.
The complete single-use host can move its newly produced five before the
terminal application.  The witness starts with no payload or control token;
two initially pending produce states execute real GEN writes.  A normal
less comparison then produces the six, toss, and new five used at the last
edge.  This is an arbitrary-state, small-parameter boundary, not a neutral
WAIT entry or a statement about the final paper parameter domain. -/

theorem onePositive : 1 > 0 := by decide
theorem ringFour : DirectedRing 4 := ⟨by decide⟩

def initialCore (i : Fin 4) : AgentState 1 :=
  { trapCore onePositive i with
    wait := true
    bit := decide (i = 0 ∨ i = 2)
    state := if i = 0 ∨ i = 2 then .produce else .none }

theorem initialCore_domain (i : Fin 4) : (initialCore i).inProtocolDomain 2 := by
  simpa [initialCore, AgentState.inProtocolDomain] using
    (trapCore_domain (κ := 2) onePositive i)

def initial (i : Fin 4) : ExpiringAgentState 1 2 16 :=
  ⟨⟨BoundedAgentState.ofDomain (initialCore i) (initialCore_domain i), false⟩,
    freshStall 16⟩

def schedule : DetSchedule 4 := [3, 0, 0, 1, 1, 0, 2, 2, 1]

def runPrefix (t : Nat) : Fin 4 → ExpiringAgentState 1 2 16 :=
  runLocalSchedule ringFour (singleUseFullTransition onePositive 2 16)
    initial (schedule.take t)

def afterProbe (t : Nat) (e : Fin 4) :
    AuthorizedAgentState 1 × AuthorizedAgentState 1 :=
  authorizedPPsiLeaderResetProbeWall onePositive
    (preparedInput onePositive (runPrefix t e).core.erase)
    (preparedInput onePositive (runPrefix t (ringFour.rightNeighbor e)).core.erase)

def beforeMovement (t : Nat) (e : Fin 4) :
    AuthorizedAgentState 1 × AuthorizedAgentState 1 :=
  generationBeforeMove onePositive 2
    (preparedInput onePositive (runPrefix t e).core.erase)
    (preparedInput onePositive (runPrefix t (ringFour.rightNeighbor e)).core.erase)

def beforeCheck (t : Nat) (e : Fin 4) :
    AuthorizedAgentState 1 × AuthorizedAgentState 1 :=
  singleUseBeforeCheck onePositive 2
    (preparedInput onePositive (runPrefix t e).core.erase)
    (preparedInput onePositive (runPrefix t (ringFour.rightNeighbor e)).core.erase)

def afterCheck (t : Nat) (e : Fin 4) :
    AuthorizedAgentState 1 × AuthorizedAgentState 1 :=
  let q := beforeCheck t e
  preserveTossCheck onePositive q.1 q.2

private theorem get_ofFn {n : Nat} {Q : Type} (C : Fin n → Q) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

private def cachedRun {n : Nat} {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q) :
    DetSchedule n → Vector Q n → Vector Q n
  | [], C => C
  | e :: rest, C => cachedRun ring T rest (Vector.ofFn (localStep ring T C.get e))

private theorem cachedRun_correct {n : Nat} {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) (C : Fin n → Q) (word : DetSchedule n) :
    (cachedRun ring T word (Vector.ofFn C)).get = runLocalSchedule ring T C word := by
  induction word generalizing C with
  | nil => exact get_ofFn C
  | cons e rest ih =>
      simp only [cachedRun, get_ofFn, runLocalSchedule]
      exact ih _

/-- The input contains no preinstalled comparison payload, release token,
authorization or leader.  Its two pending producers are stated explicitly. -/
theorem initial_no_payload_or_release :
    ∀ i : Fin 4,
      (initial i).core.core.path = .bot ∧
        (initial i).core.erase.core.path2 = none ∧
        (initial i).core.path0Crossed = false ∧
        (initial i).core.core.leader = false ∧
        (initial i).core.core.wait = true ∧
        (initial i).core.core.count = 0 ∧
        (initial i).core.core.state = (if i = 0 ∨ i = 2 then .produce else .none) := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Both occupied components are produced by the actual terminal GEN row,
not installed as part of the input.  The later calls perform no GEN writes. -/
theorem two_actual_generation_events :
    (let q := afterProbe 0 3
     generationWrites onePositive 2 q.1.core q.2.core = (false, true)) ∧
      (runPrefix 1 0).core.core.path = .some 0 1 ∧
      (let q := afterProbe 3 1
       generationWrites onePositive 2 q.1.core q.2.core = (false, true)) ∧
      (runPrefix 4 2).core.core.path = .some 0 1 ∧
      (∀ k : Fin 9, k.val ≠ 0 → k.val ≠ 3 →
        let e := schedule[k.val]'(by exact k.isLt)
        let q := afterProbe k.val e
        generationWrites onePositive 2 q.1.core q.2.core = (false, false)) := by
  unfold afterProbe runPrefix
  simp only [← cachedRun_correct]
  decide

/-- The first generated component is captured at one and really compares
against its zero bit.  Its command subsequently reaches toss and the full
DISAPPEAR suffix produces a new five at that same physical site. -/
theorem normal_comparison_produces_terminal_release :
    (runPrefix 3 1).core.core.path = .some 0 1 ∧
      (runPrefix 3 1).core.core.state = .CHECK_ready ∧
      (afterCheck 3 1).1.core.state = .less ∧
      (afterCheck 3 1).1.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      (runPrefix 4 1).core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      (runPrefix 5 1).core.core.state = .toss ∧
      (afterCheck 5 0).2.core.state = .toss ∧
      (runPrefix 6 1).core.core.path = .some 0 1 ∧
      (runPrefix 6 1).core.core.state = .toss_done ∧
      (runPrefix 6 1).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      (runPrefix 6 1).core.core.label = 0 := by
  unfold afterCheck beforeCheck runPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Once the temporary receiving payload leaves, the newly generated five
and its source payload leave an already terminal site in the same SIGMOVE.
Consumption occurs at the next site and leaves depart, so the aligned
freshly received component does not enter CHECK there. -/
theorem genuine_terminal_release_skips_next_arrival :
    (runPrefix 8 1).core.core.path = .some 0 1 ∧
      (runPrefix 8 1).core.core.state = .toss_done ∧
      (runPrefix 8 1).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      (runPrefix 8 2).core.core.path = .bot ∧
      (let q := beforeMovement 8 1
       let p := sigMoveLeaderPreclear onePositive q.1.core q.2.core
       let moved := captureStep1 p.1 p.2
       moved.1.path = .bot ∧ moved.1.path2 = some ⟨0, 0, 0, 5⟩ ∧
         moved.2.path = .some 0 1 ∧ moved.2.state = .CHECK_ready ∧
         moved.2.path2 = none) ∧
      (beforeCheck 8 1).2.core.path = .some 0 1 ∧
      (beforeCheck 8 1).2.core.state = .depart ∧
      (beforeCheck 8 1).2.core.path2 = none ∧
      (afterCheck 8 1).2.core.state = .depart ∧
      (runPrefix 9 2).core.core.path = .some 0 1 ∧
      (runPrefix 9 2).core.core.state = .depart ∧
      (runPrefix 9 2).core.erase.core.path2 = none := by
  unfold beforeMovement afterCheck beforeCheck runPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- No bit or label rewrite, leader creation, or payload expiry explains
the arrival bypass: both real generated components still exist at the end. -/
theorem boundary_keeps_bits_labels_and_components :
    (∀ t : Fin 10, ∀ i : Fin 4,
      (runPrefix t.val i).core.core.label = (initial i).core.core.label ∧
        (runPrefix t.val i).core.core.bit = (initial i).core.core.bit ∧
        (runPrefix t.val i).core.core.leader = false) ∧
      (runPrefix 9 2).core.core.path = .some 0 1 ∧
      (runPrefix 9 3).core.core.path = .some 0 1 := by
  unfold runPrefix
  simp only [← cachedRun_correct]
  decide

#print axioms initial_no_payload_or_release
#print axioms two_actual_generation_events
#print axioms normal_comparison_produces_terminal_release
#print axioms genuine_terminal_release_skips_next_arrival
#print axioms boundary_keeps_bits_labels_and_components

end BirthOneBitReleaseBoundary
