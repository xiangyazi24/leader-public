import Leader.Wu.Splice.BirthCohortNotPreserved


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace Q11541PPrimeReachability


open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open BirthPhaseCohortDesign
open Q11536B9CohortRefutation
open Q11531PPrimeRebirth


private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hSix : 0 < 6 := by decide


abbrev E := ExpiringAgentState 2 1 1


def ring6 : DirectedRing 6 := ⟨hSix⟩
def s0 : Fin 6 := 0
def s1 : Fin 6 := 1
def s2 : Fin 6 := 2
def s3 : Fin 6 := 3
def s4 : Fin 6 := 4
def s5 : Fin 6 := 5


def clean : E := BirthShortDoneTerminalPositiveWitness.endpoint false


def C0 : Fin 6 -> E := fun _ => clean


def C1 : Fin 6 -> E :=
  BirthShortDoneTerminalConsumer.step hTwo hTwo hTwoLe ring6 C0 s1


def C2 : Fin 6 -> E :=
  BirthShortDoneTerminalConsumer.step hTwo hTwo hTwoLe ring6 C1 s0


def C3 : Fin 6 -> E :=
  BirthShortDoneTerminalConsumer.step hTwo hTwo hTwoLe ring6 C2 s4


def C4 : Fin 6 -> E :=
  BirthShortDoneTerminalConsumer.step hTwo hTwo hTwoLe ring6 C3 s3


theorem initial_leaderless :
    forall i, (C0 i).core.core.leader = false := by
  intro i
  rfl


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- First scheduled row 1->2 is the re-arm, not a birth. -/
theorem first_row_no_birth :
    BirthShortDoneTerminalObserver.birthEvent hTwo hTwo hTwoLe
      (C0 s1) (C0 (ring6.rightNeighbor s1)) = false := by
  decide


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- Therefore the next row 0->1 is the first positive birthEvent. -/
theorem second_row_birth :
    BirthShortDoneTerminalObserver.birthEvent hTwo hTwo hTwoLe
      (C1 s0) (C1 (ring6.rightNeighbor s0)) = true := by
  decide


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- The first birth leaves a surviving leader and a literally untouched
three-follower re-arm gadget at sites 3,4,5. -/
theorem after_first_birth_shape :
    (C2 s1).core.core.leader = true /\
      C2 s3 = clean /\ C2 s4 = clean /\ C2 s5 = clean := by
  decide


theorem after_first_birth_not_strong :
    ¬ (NoResetFreeFollowerBarrierAt hTwo ring6 C2 s3) := by
  intro h
  unfold NoResetFreeFollowerBarrierAt at h
  dsimp only at h
  have hright : ring6.rightNeighbor s3 = s4 := by decide
  rw [hright, after_first_birth_shape.2.1,
    after_first_birth_shape.2.2.1] at h
  apply h
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · unfold isBarrier
    decide


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- Re-arm the untouched triple on 4->5, then 3->4 is another current
positive P-prime birth. -/
theorem appended_second_birth :
    BirthShortDoneTerminalObserver.birthEvent hTwo hTwo hTwoLe
      (C3 s3) (C3 (ring6.rightNeighbor s3)) = true := by
  decide


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- The original first leader is untouched by [4,3], and the second leader
appears at site 4. -/
theorem two_leaders_after_word :
    (C4 s1).core.core.leader = true /\
      (C4 s4).core.core.leader = true /\ s1 != s4 := by
  decide


/-! A separate three-site full-row counterexample to one-row closure of the
strengthened predicate. -/


def echo0Raw : AgentState 2 :=
  { BirthShortDoneTerminalPositiveWitness.raw false with echo := true }


def label1Raw : AgentState 2 :=
  { BirthShortDoneTerminalPositiveWitness.raw false with label := (1 : Fin 2) }


private theorem echo0_domain : echo0Raw.inProtocolDomain 1 := by
  simp [echo0Raw, BirthShortDoneTerminalPositiveWitness.raw,
    AgentState.inProtocolDomain]


private theorem label1_domain : label1Raw.inProtocolDomain 1 := by
  simp [label1Raw, BirthShortDoneTerminalPositiveWitness.raw,
    AgentState.inProtocolDomain]


def echo0 : E :=
  ⟨⟨BoundedAgentState.ofDomain echo0Raw echo0_domain, false⟩, 0⟩


def label1 : E :=
  ⟨⟨BoundedAgentState.ofDomain label1Raw label1_domain, false⟩, 0⟩


def ring3 : DirectedRing 3 := ⟨hThree⟩


def strongStart : Fin 3 -> E := fun i =>
  if i = 0 then leaderEndpoint
  else if i = 1 then echo0
  else label1


theorem strongStart_all_edges :
    NoResetFreeFollowerBarrierAt hTwo ring3 strongStart 0 /\
      NoResetFreeFollowerBarrierAt hTwo ring3 strongStart 1 /\
      NoResetFreeFollowerBarrierAt hTwo ring3 strongStart 2 := by
  constructor
  · unfold NoResetFreeFollowerBarrierAt
    dsimp only
    unfold isBarrier
    decide
  · constructor
    · unfold NoResetFreeFollowerBarrierAt
      dsimp only
      unfold isBarrier
      decide
    · unfold NoResetFreeFollowerBarrierAt
      dsimp only
      unfold isBarrier
      decide


def strongAfter : Fin 3 -> E :=
  BirthShortDoneTerminalConsumer.step hTwo hTwo hTwoLe
    ring3 strongStart 0


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
theorem current_row_breaks_strong :
    (strongAfter 0).core.core.leader = true /\
      ¬ (NoResetFreeFollowerBarrierAt hTwo ring3 strongAfter 1) := by
  constructor
  · decide
  · intro h
    unfold NoResetFreeFollowerBarrierAt at h
    dsimp only at h
    apply h
    refine ⟨?_, ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
    · unfold isBarrier
      decide


end Q11541PPrimeReachability
