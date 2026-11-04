import Leader.Wu.Birth.ArrivalCaptureWitnesses

set_option autoImplicit false

namespace BirthSourceActionFiveCounterexample

open PPLL PPLLRepair PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite
  BirthFullHostRulerCounterexample BirthCheckParametricWait BirthMismatchDisposalProducer
  BirthArrivalCaptureRepair BirthArrivalCaptureWitnesses

/-! A source-control provenance obstruction in the complete captured-arrival
host.  All receivers initially have neutral comparison state and no control.
One old action five is present at the terminal source before its real GENSIG
emission.  The current GENSIG writers retain it, so the new payload inherits
release permission that did not come from a comparison of this signal.

This is a leaderless finite-host execution with psi = 2, kappa = 2 and
tau = 16.  It does not assert the final paper parameter relation or a global
time lower bound. -/

/-- The terminal writer changes the payload and state but retains every old
control, including an arbitrary initial release token. -/
theorem original_emit_retains_old_control {psi : Nat} (hpsi : psi > 0)
    (l r : AgentState psi) (hl : r.label = ⟨psi - 1, by omega⟩)
    (hs : r.state = .produce) :
    (genSigSaturatedEmit hpsi l r).2.path =
        .some r.label.val (if r.bit then 1 else 0) ∧
      (genSigSaturatedEmit hpsi l r).2.path2 = r.path2 := by
  simp [genSigSaturatedEmit, hl, hs]

/-- The backward writer has the same provenance defect at every nonterminal
source position.  Clearing only the terminal writer would leave this row. -/
theorem original_propagate_retains_old_control {psi : Nat} (hpsi : psi > 0)
    (l r : AgentState psi) (hl : l.label ≠ ⟨psi - 1, by omega⟩)
    (hs : l.state = .produce) (hr : r.state = .done) :
    (genSigSaturatedPropagate hpsi l r).1.path =
        .some l.label.val (if l.bit then 1 else 0) ∧
      (genSigSaturatedPropagate hpsi l r).1.path2 = l.path2 := by
  simp [genSigSaturatedPropagate, hl, hs, hr]

/-- The bounded action index four denotes raw action five.  This is the only
change to the fresh, pathless, all-WAIT two-bit input. -/
def initial (i : Fin 8) : ExpiringAgentState 2 2 16 :=
  let u := familyInitial 16 false false i
  if i = 1 then
    { u with core := { u.core with core :=
        { u.core.core with path2 := some ⟨0, 0, 0, 4⟩ } } }
  else u

def schedule : DetSchedule 8 :=
  List.replicate 8 0 ++ [1, 2, 3, 4, 5, 6, 0, 1] ++ List.replicate 17 1

def sourcePrefix (t : Nat) : Fin 8 → ExpiringAgentState 2 2 16 :=
  runLocalSchedule ringEight (arrivalFullTransition hTwo 2 16)
    initial (schedule.take t)

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

/-- Every initial payload and comparison decision is absent.  The one raw
action-five residue is at the source, not at any receiving site. -/
theorem initial_has_only_source_control :
    (∀ i : Fin 8,
      (initial i).core.core.path = .bot ∧
      (initial i).core.core.state = .none ∧
      (initial i).core.core.wait = true ∧
      (initial i).core.core.leader = false ∧
      (initial i).core.path0Crossed = false ∧
      (initial i).core.core.count = 0 ∧ (initial i).stall.val = 16) ∧
      (initial 1).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      (∀ i : Fin 8, i ≠ 1 → (initial i).core.erase.core.path2 = none) := by
  decide

/-- The exact post-probe pair at an actual prefix of the new complete host. -/
def afterProbe (t : Nat) (e : Fin 8) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedPPsiLeaderResetProbeWall hTwo
    (preparedInput hTwo (sourcePrefix t e).core.erase)
    (preparedInput hTwo (sourcePrefix t (ringEight.rightNeighbor e)).core.erase)

def genStart (t : Nat) (e : Fin 8) : AgentState 2 × AgentState 2 :=
  let p := afterProbe t e
  let w := waitSaturated hTwo 2 p.1.core p.2.core
  genSigSaturatedStart hTwo w.1 w.2

def afterGeneration (t : Nat) (e : Fin 8) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let p := afterProbe t e
  authorizedGenSig hTwo 2 p.1 p.2

/-- The eighth interaction executes both real source writers.  The terminal
is newly emitted while the pre-existing raw action five survives GENSIG and
the entire finite suffix.  No initial comparison payload was reused. -/
theorem actual_generation_inherits_old_release :
    (∀ t : Fin 8, ∀ i : Fin 8, (sourcePrefix t.val i).core.core.path = .bot) ∧
      (genStart 7 0).1.state = .produce ∧
      (genStart 7 0).2.state = .produce ∧
      (genStart 7 0).2.path2 = some ⟨0, 0, 0, 5⟩ ∧
      (afterGeneration 7 0).1.core.path = .some 0 0 ∧
      (afterGeneration 7 0).2.core.path = .some 1 0 ∧
      (afterGeneration 7 0).2.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      (sourcePrefix 8 0).core.core.path = .some 0 0 ∧
      (sourcePrefix 8 1).core.core.path = .some 1 0 ∧
      (sourcePrefix 8 1).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ := by
  unfold genStart afterGeneration afterProbe sourcePrefix
  simp only [← cachedRun_correct]
  decide

/-- The actual prefix through CLEAN and ELIMINATE before captured SIGMOVE. -/
def beforeMovement (t : Nat) (e : Fin 8) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  arrivalBeforeMove hTwo 2
    (preparedInput hTwo (sourcePrefix t e).core.erase)
    (preparedInput hTwo (sourcePrefix t (ringEight.rightNeighbor e)).core.erase)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Each of the six outward interactions transports the same terminal and
source token.  Both GENSIG production guards are false, so no identical
replacement generation explains the successive payload values. -/
theorem actual_source_release_transfers :
    ∀ k : Fin 6,
      let t := 8 + k.val
      let e : Fin 8 := ⟨1 + k.val, by omega⟩
      let b := beforeMovement t e
      let q := authorizedCaptureSigMove hTwo b.1 b.2
      (genStart t e).1.state ≠ .produce ∧
        (genStart t e).2.state ≠ .produce ∧
        b.1.core.path = .some 1 0 ∧ b.2.core.path = .bot ∧
        b.1.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
        b.2.core.path2 = none ∧
        q.1.core.path = .bot ∧ q.2.core.path = .some 1 0 ∧
        q.2.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
        (sourcePrefix (t + 1) (ringEight.rightNeighbor e)).core.core.path = .some 1 0 ∧
        (sourcePrefix (t + 1) (ringEight.rightNeighbor e)).core.erase.core.path2 =
          some ⟨0, 0, 0, 5⟩ := by
  unfold beforeMovement genStart afterProbe sourcePrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Current captured arrival still permits the inherited action five to
release the terminal at its first aligned receiver.  When the predecessor
expires, this same terminal lies five sites ahead, beyond two psi. -/
theorem actual_source_release_exceeds_two_psi :
    schedule.length = 33 ∧
      (sourcePrefix 10 3).core.core.state = .depart ∧
      (sourcePrefix 10 3).core.core.path = .some 1 0 ∧
      (sourcePrefix 10 3).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      (sourcePrefix 14 0).core.core.path = .some 0 0 ∧
      (sourcePrefix 14 7).core.core.path = .some 1 0 ∧
      (sourcePrefix 16 2).core.core.path = .some 0 0 ∧
      (sourcePrefix 16 2).stall.val = 16 ∧
      (sourcePrefix 32 2).core.core.path = .some 0 0 ∧
      (sourcePrefix 32 2).stall.val = 0 ∧
      (sourcePrefix 33 2).core.core.path = .bot ∧
      (∀ t : Fin 20,
        (sourcePrefix (14 + t.val) 7).core.core.path = .some 1 0 ∧
        (sourcePrefix (14 + t.val) 7).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩) ∧
      ((7 + 8 - 2) % 8 : Nat) > 2 * 2 := by
  unfold sourcePrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The failure uses no ruler-bit rewrite, label repair or existing leader. -/
theorem actual_ruler_fields_preserved :
    ∀ t : Fin 34, ∀ i : Fin 8,
      (sourcePrefix t.val i).core.core.label = (initial i).core.core.label ∧
        (sourcePrefix t.val i).core.core.bit = (initial i).core.core.bit ∧
        (sourcePrefix t.val i).core.core.leader = false := by
  unfold sourcePrefix
  simp only [← cachedRun_correct]
  decide

#print axioms original_emit_retains_old_control
#print axioms original_propagate_retains_old_control
#print axioms initial_has_only_source_control
#print axioms actual_generation_inherits_old_release
#print axioms actual_source_release_transfers
#print axioms actual_source_release_exceeds_two_psi
#print axioms actual_ruler_fields_preserved

end BirthSourceActionFiveCounterexample
