import Leader.Wu.Birth.ShortDoneTerminalHandoffExpiry
import Leader.Wu.Birth.ShortDoneTerminalConsumer

namespace BirthShortDoneTerminalHandoffExpiryTwoStep

open PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair BirthGenerationDone

open K2BirthDispatcher K2BirthLeaderNormalize
  BirthShortDoneTerminalHost BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalHandoffExpiry

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

private theorem psi_pos : 0 < 3 := by decide
private theorem width_pos : 0 < 2 := by decide
private theorem width_le : 2 ≤ 3 := by decide

/-! ## The same closed local pair -/

private def peace3 (j : Fin 3) : PeaceView 3 :=
  { leader := false
    label := j
    shield := false
    bullet := 0
    signal_B := 0 }

private def rawBase (j : Fin 3) : AgentState 3 :=
  PeaceView.toState (peace3 j)

private def moverRaw : AgentState 3 :=
  { rawBase (1 : Fin 3) with path := .some 1 0 }

private def quietRaw : AgentState 3 :=
  rawBase (0 : Fin 3)

private theorem moverRaw_domain : moverRaw.inProtocolDomain 0 := by
  simp [moverRaw, rawBase, peace3, PeaceView.toState,
    AgentState.inProtocolDomain]

private theorem quietRaw_domain : quietRaw.inProtocolDomain 0 := by
  simp [quietRaw, rawBase, peace3, PeaceView.toState,
    AgentState.inProtocolDomain]

private def mover : ExpiringAgentState 3 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain moverRaw moverRaw_domain, false⟩, 0⟩

private def quiet : ExpiringAgentState 3 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain quietRaw quietRaw_domain, false⟩, 0⟩

private def prepared (u : ExpiringAgentState 3 0 1) : AuthorizedAgentState 3 :=
  normalizeDeletion (prepareExpiringDisposal psi_pos u).core.erase

private def beforeMove (l r : ExpiringAgentState 3 0 1) :
    AuthorizedAgentState 3 × AuthorizedAgentState 3 :=
  generationBeforeMoveEntryWidth psi_pos width_pos width_le 0
    (prepared l) (prepared r)

private def movedCut (l r : ExpiringAgentState 3 0 1) :
    AuthorizedAgentState 3 × AuthorizedAgentState 3 :=
  authorizedDoneMove psi_pos (beforeMove l r).1 (beforeMove l r).2

private def firstPair :
    ExpiringAgentState 3 0 1 × ExpiringAgentState 3 0 1 :=
  row psi_pos width_pos width_le mover quiet

private def secondPair :
    ExpiringAgentState 3 0 1 × ExpiringAgentState 3 0 1 :=
  row psi_pos width_pos width_le firstPair.2 quiet

/-! These are only closed finite discriminators.  In particular the right
path/stall postconditions below are not assumed from these facts: they are
recovered from `row_right_handoff_or_end`. -/

set_option maxRecDepth 32768 in
private theorem first_closed_facts :
    deletionActive (prepared mover) = false ∧
      (prepared quiet).core.path = .bot ∧
      pathMovedRight (beforeMove mover quiet).1.core
        (beforeMove mover quiet).2.core
        (movedCut mover quiet).1.core
        (movedCut mover quiet).2.core = true ∧
      firstPair.2.core.erase.core.path ≠ .bot ∧
      (movedCut mover quiet).2.core.path = .some 1 0 ∧
      firstPair.2.core.erase.core.state = .none ∧
      firstPair.1.core.erase.core.path = .bot ∧
      firstPair.1.stall = freshStall 1 ∧
      firstPair.1.core.core.leader = false ∧
      firstPair.2.core.core.leader = false := by
  decide

set_option maxRecDepth 32768 in
private theorem second_closed_facts :
    deletionActive (prepared firstPair.2) = false ∧
      (prepared quiet).core.path = .bot ∧
      pathMovedRight (beforeMove firstPair.2 quiet).1.core
        (beforeMove firstPair.2 quiet).2.core
        (movedCut firstPair.2 quiet).1.core
        (movedCut firstPair.2 quiet).2.core = true ∧
      secondPair.2.core.erase.core.path ≠ .bot ∧
      (movedCut firstPair.2 quiet).2.core.path =
        firstPair.2.core.erase.core.path ∧
      secondPair.1.core.erase.core.path = .bot ∧
      secondPair.1.stall = freshStall 1 ∧
      secondPair.1.core.core.leader = false ∧
      secondPair.2.core.core.leader = false := by
  decide

private theorem quiet_fields :
    quiet.core.core.leader = false ∧ quiet.stall = 0 := by
  decide

/-- First live residence: the concrete output
is known only to be nonempty, and the public handoff classification supplies
both the retained moved value and the fresh timer. -/
private theorem first_live_handoff :
    firstPair.2.core.erase.core.path = .some 1 0 ∧
      firstPair.2.stall = freshStall 1 := by
  have hf := first_closed_facts
  rcases hf with
    ⟨hL, hR, hmove, hpresent, hmoved, _, _, _, _, _⟩
  have hc := row_right_handoff_or_end
    (κ := 0) (τ := 1) psi_pos width_pos width_le mover quiet
  change deletionActive (prepared mover) = false →
    (prepared quiet).core.path = .bot →
    pathMovedRight (beforeMove mover quiet).1.core
      (beforeMove mover quiet).2.core
      (movedCut mover quiet).1.core
      (movedCut mover quiet).2.core = true →
    (movedCut mover quiet).2.core.path ≠ .bot ∧
      RightHandoffOutcome (movedCut mover quiet).2.core.path firstPair.2 at hc
  obtain ⟨_, ho⟩ := hc hL hR hmove
  unfold RightHandoffOutcome at ho
  rcases ho with hend | hactive | hinactive
  · exact False.elim (hpresent hend)
  · exact ⟨hactive.1.trans hmoved, hactive.2.2⟩
  · exact ⟨hinactive.1.trans hmoved, hinactive.2.2⟩

set_option maxRecDepth 32768 in
/-- The second row contains a second actual movement event.  Its moved value
is finitely checked to equal the *current first-row output path*, not a stored
or assumed ancestor.  The same public classification then gives the second
fresh residence. -/
private theorem second_live_handoff :
    secondPair.2.core.erase.core.path = firstPair.2.core.erase.core.path ∧
      secondPair.2.stall = freshStall 1 := by
  have hs := second_closed_facts
  rcases hs with
    ⟨hL, hR, hmove, hpresent, hmovedSame, _, _, _, _⟩
  have hc := row_right_handoff_or_end
    (κ := 0) (τ := 1) psi_pos width_pos width_le firstPair.2 quiet
  change deletionActive (prepared firstPair.2) = false →
    (prepared quiet).core.path = .bot →
    pathMovedRight (beforeMove firstPair.2 quiet).1.core
      (beforeMove firstPair.2 quiet).2.core
      (movedCut firstPair.2 quiet).1.core
      (movedCut firstPair.2 quiet).2.core = true →
    (movedCut firstPair.2 quiet).2.core.path ≠ .bot ∧
      RightHandoffOutcome (movedCut firstPair.2 quiet).2.core.path secondPair.2 at hc
  obtain ⟨_, ho⟩ := hc hL hR hmove
  unfold RightHandoffOutcome at ho
  rcases ho with hend | hactive | hinactive
  · exact False.elim (hpresent hend)
  · exact ⟨hactive.1.trans hmovedSame, hactive.2.2⟩
  · exact ⟨hinactive.1.trans hmovedSame, hinactive.2.2⟩

/-! ## Embed the local rows in any real ring with n >= 4 -/

private def ring {n : Nat} (h4 : 4 ≤ n) : DirectedRing n :=
  ⟨by omega⟩

private def s0 {n : Nat} (h4 : 4 ≤ n) : Fin n := ⟨0, by omega⟩
private def s1 {n : Nat} (h4 : 4 ≤ n) : Fin n := ⟨1, by omega⟩
private def s2 {n : Nat} (h4 : 4 ≤ n) : Fin n := ⟨2, by omega⟩

private theorem right0 {n : Nat} (h4 : 4 ≤ n) :
    (ring h4).rightNeighbor (s0 h4) = s1 h4 := by
  apply Fin.ext
  change (0 + 1) % n = 1
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem right1 {n : Nat} (h4 : 4 ≤ n) :
    (ring h4).rightNeighbor (s1 h4) = s2 h4 := by
  apply Fin.ext
  change (1 + 1) % n = 2
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem s01 {n : Nat} (h4 : 4 ≤ n) : s0 h4 ≠ s1 h4 := by
  intro h
  have hv : (0 : Nat) = 1 := by
    simpa [s0, s1] using congrArg Fin.val h
  omega

private theorem s02 {n : Nat} (h4 : 4 ≤ n) : s0 h4 ≠ s2 h4 := by
  intro h
  have hv : (0 : Nat) = 2 := by
    simpa [s0, s2] using congrArg Fin.val h
  omega

private theorem s12 {n : Nat} (h4 : 4 ≤ n) : s1 h4 ≠ s2 h4 := by
  intro h
  have hv : (1 : Nat) = 2 := by
    simpa [s1, s2] using congrArg Fin.val h
  omega

/-- Site zero contains the mover.  Every other site is the same quiet,
empty bounded state, so in particular sites one and two are free responders. -/
private def initial {n : Nat} (h4 : 4 ≤ n) :
    Fin n → ExpiringAgentState 3 0 1 := fun i =>
  if i = s0 h4 then mover else quiet

/-- Exact deterministic two-edge word: first `0 -> 1`, then the new carrier's
next outgoing edge `1 -> 2`. -/
def edgeWord {n : Nat} (h4 : 4 ≤ n) : DetSchedule n :=
  [s0 h4, s1 h4]

/-- We use the explicit local-step semantics so the finite word has no hidden
scheduler object.  `first_is_protocol_step` and `second_is_protocol_step` below
identify both calls with the supplied actual terminal protocol. -/
private def after1 {n : Nat} (h4 : 4 ≤ n) :
    Fin n → ExpiringAgentState 3 0 1 :=
  localStep (ring h4)
    (row psi_pos width_pos width_le) (initial h4) (s0 h4)

private def after2 {n : Nat} (h4 : 4 ≤ n) :
    Fin n → ExpiringAgentState 3 0 1 :=
  localStep (ring h4)
    (row psi_pos width_pos width_le) (after1 h4) (s1 h4)

/-- The literal list execution is exactly the two named full configurations. -/
def wordRun {n : Nat} (h4 : 4 ≤ n) :
    Fin n → ExpiringAgentState 3 0 1 :=
  runLocalSchedule (ring h4)
    (row psi_pos width_pos width_le) (initial h4) (edgeWord h4)

 theorem wordRun_eq_after2 {n : Nat} (h4 : 4 ≤ n) :
    wordRun h4 = after2 h4 := by
  rfl

/-- First list step is definitionally the actual `PopulationProtocol.step`
consumer supplied with the terminal host. -/
theorem first_is_protocol_step {n : Nat} (h4 : 4 ≤ n) :
    after1 h4 =
      BirthShortDoneTerminalConsumer.step
        psi_pos width_pos width_le (ring h4) (initial h4) (s0 h4) := by
  unfold after1 BirthShortDoneTerminalConsumer.step
  simpa [BirthShortDoneTerminalConsumer.protocol] using
    (localStep_eq_protocol_step
      (BirthShortDoneTerminalConsumer.protocol
        psi_pos width_pos width_le 0 1)
      (ring h4) (initial h4) (s0 h4))

/-- Likewise the second list step is the actual protocol step from the first
complete physical output configuration. -/
theorem second_is_protocol_step {n : Nat} (h4 : 4 ≤ n) :
    after2 h4 =
      BirthShortDoneTerminalConsumer.step
        psi_pos width_pos width_le (ring h4) (after1 h4) (s1 h4) := by
  unfold after2 BirthShortDoneTerminalConsumer.step
  simpa [BirthShortDoneTerminalConsumer.protocol] using
    (localStep_eq_protocol_step
      (BirthShortDoneTerminalConsumer.protocol
        psi_pos width_pos width_le 0 1)
      (ring h4) (after1 h4) (s1 h4))

/-- Exact full-state first prefix: the row outputs occupy sites zero/one and
all other sites retain their entire original bounded records. -/
theorem first_step_full_state {n : Nat} (h4 : 4 ≤ n) :
    after1 h4 (s0 h4) = firstPair.1 ∧
      after1 h4 (s1 h4) = firstPair.2 ∧
      (∀ i : Fin n, i ≠ s0 h4 → i ≠ s1 h4 → after1 h4 i = quiet) := by
  have h01 := s01 h4
  constructor
  · simp [after1, localStep, initial, firstPair, right0 h4,
      h01, h01.symm]
  · constructor
    · simp [after1, localStep, initial, firstPair, right0 h4,
        h01, h01.symm]
    · intro i hi0 hi1
      simp [after1, localStep, initial, right0 h4, hi0, hi1]

/-- Exact full-state second prefix.  Site zero keeps its first-row full record;
site one gets the second row's initiator record; site two gets the second row's
responder record; every other site is byte-for-byte the original quiet state. -/
theorem second_step_full_state {n : Nat} (h4 : 4 ≤ n) :
    after2 h4 (s0 h4) = firstPair.1 ∧
      after2 h4 (s1 h4) = secondPair.1 ∧
      after2 h4 (s2 h4) = secondPair.2 ∧
      (∀ i : Fin n, i ≠ s0 h4 → i ≠ s1 h4 → i ≠ s2 h4 →
        after2 h4 i = quiet) := by
  have h01 := s01 h4
  have h02 := s02 h4
  have h12 := s12 h4
  have hfirst := first_step_full_state h4
  rcases hfirst with ⟨h0, h1, hother⟩
  have h2 : after1 h4 (s2 h4) = quiet :=
    hother (s2 h4) h02.symm h12.symm
  constructor
  · simp [after2, localStep, right1 h4,
      h01, h01.symm, h02, h02.symm, h12, h12.symm, h0]
  · constructor
    · simp [after2, localStep, secondPair, right1 h4,
        h01, h01.symm, h02, h02.symm, h12, h12.symm, h1, h2]
    · constructor
      · simp [after2, localStep, secondPair, right1 h4,
          h01, h01.symm, h02, h02.symm, h12, h12.symm, h1, h2]
      · intro i hi0 hi1 hi2
        have hp := hother i hi0 hi1
        simp [after2, localStep, right1 h4, hi1, hi2, hp]

/-- Main moving-carrier observation.  The second row does not merely end with
the same numeral by coincidence: `second_live_handoff` joins a second concrete
movement event to the first row's *current* physical path. -/
theorem same_path_advances_two_edges {n : Nat} (h4 : 4 ≤ n) :
    (after1 h4 (s0 h4)).core.erase.core.path = .bot ∧
      (after1 h4 (s0 h4)).stall = freshStall 1 ∧
      (after1 h4 (s1 h4)).core.erase.core.path = .some 1 0 ∧
      (after1 h4 (s1 h4)).core.erase.core.state = .none ∧
      (after1 h4 (s1 h4)).stall = freshStall 1 ∧
      after2 h4 (s0 h4) = after1 h4 (s0 h4) ∧
      (after2 h4 (s1 h4)).core.erase.core.path = .bot ∧
      (after2 h4 (s1 h4)).stall = freshStall 1 ∧
      (after2 h4 (s2 h4)).core.erase.core.path =
        (after1 h4 (s1 h4)).core.erase.core.path ∧
      (after2 h4 (s2 h4)).core.erase.core.path = .some 1 0 ∧
      (after2 h4 (s2 h4)).stall = freshStall 1 := by
  have hf := first_closed_facts
  rcases hf with
    ⟨_, _, _, _, _, hstate1, hleftPath1, hleftStall1, _, _⟩
  have hs := second_closed_facts
  rcases hs with
    ⟨_, _, _, _, _, hleftPath2, hleftStall2, _, _⟩
  have hLive1 := first_live_handoff
  have hLive2 := second_live_handoff
  have hFull1 := first_step_full_state h4
  rcases hFull1 with ⟨h10, h11, _⟩
  have hFull2 := second_step_full_state h4
  rcases hFull2 with ⟨h20, h21, h22, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h10]
    exact hleftPath1
  · rw [h10]
    exact hleftStall1
  · rw [h11]
    exact hLive1.1
  · rw [h11]
    exact hstate1
  · rw [h11]
    exact hLive1.2
  · exact h20.trans h10.symm
  · rw [h21]
    exact hleftPath2
  · rw [h21]
    exact hleftStall2
  · rw [h22, h11]
    exact hLive2.1
  · rw [h22]
    exact hLive2.1.trans hLive1.1
  · rw [h22]
    exact hLive2.2

/-- No leader is created at either finite prefix.  This is a complete output
check on the actual ring configuration, not an assumed no-birth invariant. -/
theorem no_leader_after_either_step {n : Nat} (h4 : 4 ≤ n) :
    (∀ i : Fin n, (after1 h4 i).core.core.leader = false) ∧
      (∀ i : Fin n, (after2 h4 i).core.core.leader = false) := by
  have hf := first_closed_facts
  rcases hf with
    ⟨_, _, _, _, _, _, _, _, hFirstL, hFirstR⟩
  have hs := second_closed_facts
  rcases hs with
    ⟨_, _, _, _, _, _, _, hSecondL, hSecondR⟩
  have hq := quiet_fields
  have hFull1 := first_step_full_state h4
  rcases hFull1 with ⟨h10, h11, h1other⟩
  have hFull2 := second_step_full_state h4
  rcases hFull2 with ⟨h20, h21, h22, h2other⟩
  constructor
  · intro i
    by_cases hi0 : i = s0 h4
    · subst i
      rw [h10]
      exact hFirstL
    · by_cases hi1 : i = s1 h4
      · subst i
        rw [h11]
        exact hFirstR
      · rw [h1other i hi0 hi1]
        exact hq.1
  · intro i
    by_cases hi0 : i = s0 h4
    · subst i
      rw [h20]
      exact hFirstL
    · by_cases hi1 : i = s1 h4
      · subst i
        rw [h21]
        exact hSecondL
      · by_cases hi2 : i = s2 h4
        · subst i
          rw [h22]
          exact hSecondR
        · rw [h2other i hi0 hi1 hi2]
          exact hq.1

/-- Timer profile after the two-edge word: all three touched sites are fresh;
untouched sites remain at the literal initial zero timer. -/
theorem timers_after_two_edges {n : Nat} (h4 : 4 ≤ n) :
    (after2 h4 (s0 h4)).stall = freshStall 1 ∧
      (after2 h4 (s1 h4)).stall = freshStall 1 ∧
      (after2 h4 (s2 h4)).stall = freshStall 1 ∧
      (∀ i : Fin n, i ≠ s0 h4 → i ≠ s1 h4 → i ≠ s2 h4 →
        (after2 h4 i).stall = 0) := by
  have hf := first_closed_facts
  rcases hf with ⟨_, _, _, _, _, _, _, hFirstStall, _, _⟩
  have hs := second_closed_facts
  rcases hs with ⟨_, _, _, _, _, _, hSecondStall, _, _⟩
  have hLive2 := second_live_handoff
  have hq := quiet_fields
  have hFull2 := second_step_full_state h4
  rcases hFull2 with ⟨h20, h21, h22, hother⟩
  exact ⟨by rw [h20]; exact hFirstStall,
    by rw [h21]; exact hSecondStall,
    by rw [h22]; exact hLive2.2,
    fun i hi0 hi1 hi2 => by rw [hother i hi0 hi1 hi2]; exact hq.2⟩

#print axioms BirthShortDoneTerminalHandoffExpiryTwoStep.wordRun_eq_after2
#print axioms BirthShortDoneTerminalHandoffExpiryTwoStep.first_is_protocol_step
#print axioms BirthShortDoneTerminalHandoffExpiryTwoStep.second_is_protocol_step
#print axioms BirthShortDoneTerminalHandoffExpiryTwoStep.first_step_full_state
#print axioms BirthShortDoneTerminalHandoffExpiryTwoStep.second_step_full_state
#print axioms BirthShortDoneTerminalHandoffExpiryTwoStep.same_path_advances_two_edges
#print axioms BirthShortDoneTerminalHandoffExpiryTwoStep.no_leader_after_either_step
#print axioms BirthShortDoneTerminalHandoffExpiryTwoStep.timers_after_two_edges

end BirthShortDoneTerminalHandoffExpiryTwoStep
