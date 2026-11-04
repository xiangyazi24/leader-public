import Leader.Wu.Birth.MismatchDisposalWitnesses

set_option autoImplicit false

namespace BirthFreshEqualArrivalCounterexample

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLPpsiLeaderCreationRepair PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthOutputLegitimacy PPLLWallSweepFinite
  PPLLWallSweepRepair PPLLWallSweepPreCheckResetRepair
  BirthCheckCongestGuardRepair BirthMismatchDisposalProducer

/-! A newly generated signal can encounter an old equality at an empty
receiver.  This module follows the actual generation and movement stages of
`actionOneFullTransition`; it does not postulate an aligned CHECK snapshot.
Only site seven has a nonneutral comparison state initially.  Every path and
control carrier starts absent.  The sixteen-site ruler is the literal
trailing-zero ruler rooted at fourteen, with group four/five equal to zero
and group six/seven equal to two.  The first terminal arrival accepts the
old equality before the zero component reaches the target group.

This is a counterexample for the named finite legacy host, at psi two,
kappa two and tau sixteen.  It does not identify a final paper parameter
function or imply a lower bound for a different protocol. -/

theorem twoPositive : 2 > 0 := by decide

theorem ringSixteen : DirectedRing 16 := ⟨by decide⟩

abbrev Local := ExpiringAgentState 2 2 16

/-- The ruler ID sequence is 0,1,0,2,0,1,0 after its leader.  An initially
empty terminal receiver alone retains an old equality. -/
def initialCore (i : Fin 16) : AgentState 2 :=
  { trapCore twoPositive i with
    wait := true
    leader := decide (i = 14)
    bit := decide (i = 3 ∨ i = 6 ∨ i = 11)
    state := if i = 7 then .equal else .none }

theorem initialCore_domain (i : Fin 16) :
    (initialCore i).inProtocolDomain 2 := by
  simpa [initialCore, AgentState.inProtocolDomain] using
    (trapCore_domain (κ := 2) twoPositive i)

/-- No physical path, authorization or timer credit is preinstalled. -/
def initial (i : Fin 16) : Local :=
  ⟨⟨BoundedAgentState.ofDomain (initialCore i) (initialCore_domain i), false⟩, 0⟩

theorem initial_erase : eraseExpiringConfig initial = initialCore := by
  funext i
  change (BoundedAgentState.ofDomain (initialCore i) (initialCore_domain i)).erase = initialCore i
  exact BoundedAgentState.erase_ofDomain _ (initialCore_domain i)

private theorem initial_unique : hasUniqueLeader 16 initialCore := by
  unfold hasUniqueLeader
  decide

/-- The comparison garbage does not change any ruler condition. -/
theorem initial_ruler : isStableIDSequence twoPositive ringSixteen initialCore := by
  refine ⟨14, by decide, by decide, ?_, ?_⟩
  · intro k hk
    have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro i hi hb
    have hc : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [groupID, List.range_succ, initialCore, trailingZeros] <;> decide

private theorem initial_no_bad_bullet :
    noNonPeacefulBullet twoPositive ringSixteen initialCore := by
  have h : ∀ i : Fin 16, (initialCore i).bullet ≠ (⟨2, by omega⟩ : Fin 3) := by decide
  intro i hi
  exact False.elim (h i hi)

private theorem initial_no_free_writer :
    noFreeOverwritingSignal twoPositive ringSixteen initialCore := by
  have h : ∀ i : Fin 16, (initialCore i).path3 = none := by decide
  refine ⟨14, by decide, by decide, ?_⟩
  intro i _ _ hf
  obtain ⟨p, hp, _⟩ := hf.1.2 0 (by decide)
  rw [h] at hp
  cases hp

/-- The actual input satisfies all five literal paper safety fields. -/
theorem initial_paperSafe :
    PaperSafeConfig twoPositive ringSixteen (eraseExpiringConfig initial) := by
  rw [initial_erase]
  exact {
    unique_leader := initial_unique
    no_nonpeaceful_bullet := initial_no_bad_bullet
    no_free_barrier := noFreeBarrier_of_stableID _ _ _ initial_ruler
    no_free_overwriting_signal := initial_no_free_writer
    stable_id_sequence := initial_ruler }

/-- All comparison material is empty initially; exactly one old state can
be mistaken for a completed comparison after an actual incoming transfer. -/
theorem initial_empty_comparison :
    (∀ i : Fin 16,
      (initial i).core.core.path = .bot ∧
      (initial i).core.core.path2 = none ∧
      (initial i).core.core.path3 = none ∧
      (initial i).core.path0Crossed = false ∧
      (initial i).core.core.wait = true ∧
      (initial i).core.core.count = 0 ∧
      (initial i).core.core.state = if i = 7 then .equal else .none) ∧
    groupID ringSixteen.hn initialCore 4 = 0 ∧
    groupID ringSixteen.hn initialCore 6 = 2 := by
  decide

/-- Eight WAIT interactions generate one zero word, followed by three
literal transport interactions.  None touches the original leader. -/
def schedule : DetSchedule 16 := List.replicate 8 4 ++ [5, 4, 6]

def arrivalPrefix (t : Nat) : Fin 16 → Local :=
  runLocalSchedule ringSixteen (actionOneFullTransition twoPositive 2 16)
    initial (schedule.take t)

private theorem get_ofFn {Q : Type} (C : Fin 16 → Q) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

private def cachedRun {Q : Type} (T : Q → Q → Q × Q) :
    DetSchedule 16 → Vector Q 16 → Vector Q 16
  | [], C => C
  | e :: rest, C => cachedRun T rest (Vector.ofFn (localStep ringSixteen T C.get e))

private theorem cachedRun_correct {Q : Type} (T : Q → Q → Q × Q)
    (C : Fin 16 → Q) (word : DetSchedule 16) :
    (cachedRun T word (Vector.ofFn C)).get = runLocalSchedule ringSixteen T C word := by
  induction word generalizing C with
  | nil => exact get_ofFn C
  | cons e rest ih =>
      simp only [cachedRun, get_ofFn, runLocalSchedule]
      exact ih _

/-! Named projections of the actual retained prefix expose the causal
producer and its three moves.  Their values are computed from the complete
run at that interaction's input, not supplied by an abstract source mark. -/

def afterProbe (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedPPsiLeaderResetProbeWall twoPositive
    (preparedInput twoPositive (arrivalPrefix t e).core.erase)
    (preparedInput twoPositive (arrivalPrefix t (ringSixteen.rightNeighbor e)).core.erase)

def afterGeneration (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let q := afterProbe t e
  authorizedGenSig twoPositive 2 q.1 q.2

def beforeMovement (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let q := afterGeneration t e
  let q := authorizedCleanSig twoPositive q.1 q.2
  authorizedEliminateSig twoPositive q.1 q.2

def afterMovement (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let q := beforeMovement t e
  authorizedSigMoveLeaderWall twoPositive q.1 q.2

/-- No earlier path exists.  The actual GENSIG call on interaction eight
writes both components; the complete full host retains those exact outputs. -/
theorem actual_fresh_generation :
    (∀ t : Fin 8, ∀ i : Fin 16, (arrivalPrefix t.val i).core.core.path = .bot) ∧
      (arrivalPrefix 7 5).core.core.count = 1 ∧
      (afterProbe 7 4).1.core.path = .bot ∧
      (afterProbe 7 4).2.core.path = .bot ∧
      (afterGeneration 7 4).1.core.path = .some 0 0 ∧
      (afterGeneration 7 4).2.core.path = .some 1 0 ∧
      (arrivalPrefix 8 4).core.core.path = .some 0 0 ∧
      (arrivalPrefix 8 5).core.core.path = .some 1 0 ∧
      (arrivalPrefix 8 5).core.core.count = 2 ∧
      (arrivalPrefix 8 4).core.core.state = .depart ∧
      (arrivalPrefix 8 5).core.core.state = .depart := by
  unfold afterGeneration afterProbe arrivalPrefix
  simp only [← cachedRun_correct]
  decide

/-- The three post-generation edges, in their actual execution order. -/
def moveEdge (k : Fin 3) : Fin 16 := if k = 0 then 5 else if k = 1 then 4 else 6

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Every subsequent path writer before SIGMOVE retains the corresponding
input component.  SIGMOVE then physically transfers that component into an
empty receiver.  This rules out replacement-generation as the cause of the
matching finite values in the transport certificate. -/
theorem actual_fresh_transfers :
    ∀ k : Fin 3,
      let t := 8 + k.val
      let e := moveEdge k
      let b := beforeMovement t e
      let a := afterMovement t e
      b.1.core.path = (arrivalPrefix t e).core.erase.core.path ∧
      b.2.core.path = .bot ∧
      b.1.core.path ≠ .bot ∧
      a.1.core.path = .bot ∧
      a.2.core.path = b.1.core.path ∧
      pathMovedRight b.1.core b.2.core a.1.core a.2.core = true ∧
      (arrivalPrefix (t + 1) (ringSixteen.rightNeighbor e)).core.erase.core.path = a.2.core.path := by
  unfold afterMovement beforeMovement afterGeneration afterProbe arrivalPrefix
  simp only [← cachedRun_correct]
  decide

/-- The last actual sanitized boundary, after the terminal component moves. -/
def lastBeforeCheck : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  actualCheckInput twoPositive 2 (arrivalPrefix 10 6).core.erase (arrivalPrefix 10 7).core.erase

def lastAfterCheck : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  congestGuardCheck twoPositive lastBeforeCheck.1 lastBeforeCheck.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The target's terminal old equality survives real arrival and local
sanitization.  CHECK accepts despite the absent target prefix and despite
both authorization bits being false.  No larger command is produced. -/
theorem actual_stale_terminal_acceptance :
    (arrivalPrefix 10 5).core.core.path = .some 0 0 ∧
      (arrivalPrefix 10 6).core.core.path = .some 1 0 ∧
      (arrivalPrefix 10 7).core.core.path = .bot ∧
      (arrivalPrefix 10 7).core.core.state = .equal ∧
      lastBeforeCheck.1.core.path = .bot ∧
      lastBeforeCheck.1.core.bit = true ∧
      lastBeforeCheck.1.core.state = .none ∧
      lastBeforeCheck.2.core.path = .some 1 0 ∧
      lastBeforeCheck.2.core.bit = false ∧
      lastBeforeCheck.2.core.state = .equal ∧
      lastBeforeCheck.1.path0Crossed = false ∧
      lastBeforeCheck.2.path0Crossed = false ∧
      lastAfterCheck.2.core.leader = true ∧
      lastAfterCheck.1.core.path2 = none ∧
      lastAfterCheck.2.core.path2 = none := by
  unfold lastAfterCheck lastBeforeCheck arrivalPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Through the full suffix, the first birth occurs at interaction eleven:
there are leaders at six and fourteen.  Every preceding prefix retains only
the original leader. -/
theorem actual_fresh_arrival_creates_second_leader :
    (∀ t : Fin 11, ∀ i : Fin 16,
      (arrivalPrefix t.val i).core.core.leader = true ↔ i = 14) ∧
      (∀ i : Fin 16, (arrivalPrefix 11 i).core.core.leader = true ↔ i = 6 ∨ i = 14) := by
  unfold arrivalPrefix
  simp only [← cachedRun_correct]
  decide

/-- Neither bit rewriting nor label corruption contributes to this trace. -/
theorem actual_ruler_fields_preserved :
    ∀ t : Fin 12, ∀ i : Fin 16,
      (arrivalPrefix t.val i).core.core.bit = (initial i).core.core.bit ∧
      (arrivalPrefix t.val i).core.core.label = (initial i).core.core.label := by
  unfold arrivalPrefix
  simp only [← cachedRun_correct]
  decide

end BirthFreshEqualArrivalCounterexample

#print axioms BirthFreshEqualArrivalCounterexample.initial_paperSafe
#print axioms BirthFreshEqualArrivalCounterexample.initial_empty_comparison
#print axioms BirthFreshEqualArrivalCounterexample.actual_fresh_generation
#print axioms BirthFreshEqualArrivalCounterexample.actual_fresh_transfers
#print axioms BirthFreshEqualArrivalCounterexample.actual_stale_terminal_acceptance
#print axioms BirthFreshEqualArrivalCounterexample.actual_fresh_arrival_creates_second_leader
#print axioms BirthFreshEqualArrivalCounterexample.actual_ruler_fields_preserved
