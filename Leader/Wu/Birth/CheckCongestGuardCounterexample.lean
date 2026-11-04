import Leader.Wu.Birth.CheckCongestGuardRepair

set_option autoImplicit false

namespace BirthCheckGuardAudit

open PPLLPpsiLeaderCreationRepair PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepPreCheckResetRepair BirthFullHostRulerCounterexample
  BirthFullHostWaitedRulerCounterexample BirthCheckCongestGuardRepair

/-! This certificate starts from the existing clean WAIT-true ruler fixture.
It invokes the entire guarded host at every edge. The fixed parameter point is
eight sites, psi two, kappa two, and tau sixteen; no final-parameter theorem is
asserted. Tabulation below changes evaluation sharing only.

The two components of the single signal generated at zero/one pass through the
unequal group at two/three and reach the equal group at four/five. No expiry or
mixed source is needed. The new congestion guard is clear at every CHECK input.
-/

abbrev Cell := ExpiringAgentState 2 2 16

/-- Eight genuine WAIT interactions followed by eight transfers and two CHECKs. -/
def auditWord : DetSchedule 8 :=
  List.replicate 8 0 ++ [1, 2, 0, 1, 2, 3, 2, 4, 3, 4]

/-- The exact candidate host, including cleanup, suffix, expiry, and birth marking. -/
def auditPrefix (t : Nat) : Fin 8 → Cell :=
  runLocalSchedule ringEight (guardedFullTransition (by omega) 2 16)
    waitedInitial (auditWord.take t)

private theorem get_ofFn {Q : Type} (C : Fin 8 → Q) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

/-- A general evaluation cache that preserves the complete local state. -/
private def vectorRun {Q : Type} (T : Q → Q → Q × Q) :
    DetSchedule 8 → Vector Q 8 → Vector Q 8
  | [], C => C
  | e :: rest, C => vectorRun T rest (Vector.ofFn (localStep ringEight T C.get e))

/-- Tabulation is extensionally the original schedule semantics for every host. -/
private theorem vectorRun_correct {Q : Type} (T : Q → Q → Q × Q)
    (C : Fin 8 → Q) (word : DetSchedule 8) :
    (vectorRun T word (Vector.ofFn C)).get = runLocalSchedule ringEight T C word := by
  induction word generalizing C with
  | nil => exact get_ofFn C
  | cons e rest ih =>
      simp only [vectorRun, get_ofFn, runLocalSchedule]
      exact ih _

/-- The imported fixture is paper-safe, has exactly leader six, and starts with
WAIT true, count zero, no path, no authorization, and neutral comparison state. -/
theorem initial_clean_ruler :
    PaperSafeConfig (by omega) ringEight (eraseExpiringConfig waitedInitial) ∧
      (∀ i : Fin 8, (waitedInitial i).core.core.leader = true ↔ i = 6) ∧
      (∀ i : Fin 8, (waitedInitial i).core.core.wait = true ∧
        (waitedInitial i).core.core.count = 0 ∧
        (waitedInitial i).core.core.path = .bot ∧
        (waitedInitial i).core.path0Crossed = false ∧
        (waitedInitial i).core.core.state = .none ∧
        (waitedInitial i).core.core.path3 = none) :=
  ⟨waitedInitial_paperSafe, by decide, waitedInitial_clean⟩

/-- Actual WAIT reaches kappa before the unique initial pair of paths is born. -/
theorem actual_generation :
    (∀ t : Fin 8, ∀ i : Fin 8, (auditPrefix t.val i).core.core.path = .bot) ∧
      (auditPrefix 7 1).core.core.count = 1 ∧
      (auditPrefix 8 1).core.core.count = 2 ∧
      (auditPrefix 8 0).core.core.path = .some 0 0 ∧
      (auditPrefix 8 1).core.core.path = .some 1 0 ∧
      (auditPrefix 8 0).core.core.state = .depart ∧
      (auditPrefix 8 1).core.core.state = .depart := by
  unfold auditPrefix
  simp only [← vectorRun_correct]
  decide

/-- Sanitation and all preceding physical stages at a named actual boundary. -/
def checkInput (t : Nat) (e : Fin 8) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  wallSweepResetProbePreCheckResetBeforeCheck (by omega) 2
    (normalizeDeletion (auditPrefix t e).core.erase)
    (normalizeDeletion (auditPrefix t (ringEight.rightNeighbor e)).core.erase)

/-- CHECK's own output at the first complete, unequal group comparison. -/
def mismatchOutput : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  congestGuardCheck (by omega) (checkInput 12 2).1 (checkInput 12 2).2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- One complete generated signal arrives with actual crossing authorization.
CHECK correctly detects the unequal terminal bit and installs action four;
the subsequent comparison stage changes action four to three and leaves both
controls congested. -/
theorem mismatch_trace :
    (checkInput 12 2).1.core.path = .some 0 0 ∧
      (checkInput 12 2).2.core.path = .some 1 0 ∧
      (checkInput 12 2).1.core.state = .CHECK_ready ∧
      (checkInput 12 2).2.core.state = .CHECK_ready ∧
      (checkInput 12 2).1.path0Crossed = true ∧
      (checkInput 12 2).2.core.bit = true ∧
      mismatchOutput.1.core.state = .equal ∧
      mismatchOutput.2.core.state = .larger ∧
      mismatchOutput.2.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      (auditPrefix 13 2).core.core.state = .congest ∧
      (auditPrefix 13 3).core.core.state = .congest ∧
      (auditPrefix 13 3).core.erase.core.path2 = some ⟨0, 0, 0, 3⟩ := by
  unfold mismatchOutput checkInput auditPrefix
  simp only [← vectorRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Before the next CHECK, the terminal payload has already moved from three
to four while elimination is attached to the now-empty site three. Both
payloads subsequently reach four/five with genuine new wrap authorization. -/
theorem escaping_payload_trace :
    (checkInput 13 3).1.core.path = .bot ∧
      (checkInput 13 3).1.core.state = .eliminate_signal ∧
      (checkInput 13 3).2.core.path = .some 1 0 ∧
      (checkInput 13 3).2.core.state = .none ∧
      (auditPrefix 14 4).core.core.path = .some 1 0 ∧
      (auditPrefix 15 3).core.core.path = .some 0 0 ∧
      (auditPrefix 16 5).core.core.path = .some 1 0 ∧
      (checkInput 17 4).1.core.path = .some 0 0 ∧
      (checkInput 17 4).2.core.path = .some 1 0 ∧
      (checkInput 17 4).1.core.state = .CHECK_ready ∧
      (checkInput 17 4).2.core.state = .CHECK_ready ∧
      (checkInput 17 4).1.path0Crossed = true := by
  unfold checkInput auditPrefix
  simp only [← vectorRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Every actual CHECK input is clear of congestion. This refutation does not
rely on executing a blocked branch of the candidate guard. -/
theorem guard_never_blocks :
    ∀ t : Fin 18,
      let e := auditWord[t.val]'
        (by simpa only [auditWord, List.length_append, List.length_replicate,
          List.length_cons, List.length_nil] using t.isLt)
      (checkInput t.val e).1.core.state ≠ .congest ∧
      (checkInput t.val e).2.core.state ≠ .congest := by
  unfold checkInput auditPrefix
  simp only [← vectorRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Blocking lock/compare1/compare2 in addition to congestion also leaves this
word unchanged: no active comparison control occurs at any CHECK input. -/
theorem active_controls_absent_at_check :
    ∀ t : Fin 18,
      let e := auditWord[t.val]'
        (by simpa only [auditWord, List.length_append, List.length_replicate,
          List.length_cons, List.length_nil] using t.isLt)
      comparisonActive (checkInput t.val e).1.core.state = false ∧
      comparisonActive (checkInput t.val e).2.core.state = false := by
  unfold checkInput auditPrefix
  simp only [← vectorRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- After the initial generation exactly two live path components remain in
every prefix, including the birth output. No partial-expiry gap is required. -/
theorem two_live_paths :
    ∀ t : Fin 11,
      ((List.finRange 8).filter fun i =>
        decide ((auditPrefix (8 + t.val) i).core.core.path ≠ .bot)).length = 2 := by
  unfold auditPrefix
  simp only [← vectorRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The same word already creates leaders four and six in the unguarded host.
This is an existing lifecycle defect left unrepaired by the new guard. -/
theorem original_host_second_leader :
    (runLocalSchedule ringEight
      (wallSweepBirthSignalZeroPathStallTransition (by omega) 2 16)
      waitedInitial auditWord 4).core.core.leader = true ∧
    (runLocalSchedule ringEight
      (wallSweepBirthSignalZeroPathStallTransition (by omega) 2 16)
      waitedInitial auditWord 6).core.core.leader = true := by
  simp only [← vectorRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The first extra leader is created at four in step eighteen; leader six
remains present and every ruler bit and label survives every prefix. -/
theorem guarded_second_leader :
    auditWord.length = 18 ∧
      (∀ t : Fin 18, ∀ i : Fin 8,
        (auditPrefix t.val i).core.core.leader = true ↔ i = 6) ∧
      (∀ i : Fin 8, (auditPrefix 18 i).core.core.leader = true ↔ i = 4 ∨ i = 6) ∧
      (∀ t : Fin 19, ∀ i : Fin 8,
        (auditPrefix t.val i).core.core.bit = (waitedInitial i).core.core.bit ∧
        (auditPrefix t.val i).core.core.label = (waitedInitial i).core.core.label) := by
  unfold auditPrefix
  simp only [← vectorRun_correct]
  decide

attribute [local irreducible] auditPrefix

/-- At this concrete parameter point the complete guarded host fails to
preserve the real paper predicate from the clean WAIT-true ruler witness. -/
theorem guarded_not_paperSafe :
    ¬ PaperSafeConfig (by omega) ringEight (eraseExpiringConfig (auditPrefix 18)) := by
  intro h
  obtain ⟨i, _, only⟩ := h.unique_leader
  have h4 := only 4 ((guarded_second_leader.2.2.1 4).2 (Or.inl rfl))
  have h6 := only 6 ((guarded_second_leader.2.2.1 6).2 (Or.inr rfl))
  have h46 : (4 : Fin 8) = 6 := h4.trans h6.symm
  have := congrArg Fin.val h46
  omega

end BirthCheckGuardAudit

#print axioms BirthCheckGuardAudit.initial_clean_ruler
#print axioms BirthCheckGuardAudit.actual_generation
#print axioms BirthCheckGuardAudit.mismatch_trace
#print axioms BirthCheckGuardAudit.escaping_payload_trace
#print axioms BirthCheckGuardAudit.guard_never_blocks
#print axioms BirthCheckGuardAudit.active_controls_absent_at_check
#print axioms BirthCheckGuardAudit.two_live_paths
#print axioms BirthCheckGuardAudit.original_host_second_leader
#print axioms BirthCheckGuardAudit.guarded_second_leader
#print axioms BirthCheckGuardAudit.guarded_not_paperSafe
