import Leader.Wu.Safety.NoCheckBirthConditionTwoProtocol

/-!
# Singleton post-kill repair is insufficient

After deleting the middle of three separated leaders, repairing only the edge
entering the victim moves the free barrier to the next follower edge.  The
complete merged follower segment must be swept.
-/

namespace PPLLQ4775Counterexample

open PPLL PPLLResearchFormulation
open PPLLNoCheckBirthConditionTwoPhysical
open PPLLNoCheckBirthConditionTwoProtocol

private theorem hThree : 3 > 0 := by omega

private theorem ring6 : DirectedRing 6 := ⟨by omega⟩

private def parityView
    (leaders : Fin 6 → Bool) (i : Fin 6) : PeaceView 3 :=
  { leader := leaders i
    label := ⟨i.val % 2, by omega⟩
    shield := leaders i
    bullet := 0
    signal_B := 0 }

private def threeLeaders (i : Fin 6) : Bool :=
  decide (i.val = 0 ∨ i.val = 2 ∨ i.val = 4)

private def survivingLeaders (i : Fin 6) : Bool :=
  decide (i.val = 0 ∨ i.val = 4)

private def beforeKill (i : Fin 6) : AgentState 3 :=
  PeaceView.toState (parityView threeLeaders i)

private def afterKill (i : Fin 6) : AgentState 3 :=
  PeaceView.toState (parityView survivingLeaders i)

private def afterSingletonRepairView (i : Fin 6) : PeaceView 3 :=
  { leader := survivingLeaders i
    label :=
      if i.val = 2 then ⟨2, by omega⟩
      else ⟨i.val % 2, by omega⟩
    shield := survivingLeaders i
    bullet := 0
    signal_B := 0 }

private def afterSingletonRepair (i : Fin 6) : AgentState 3 :=
  PeaceView.toState (afterSingletonRepairView i)

private def afterSegmentRepairView (i : Fin 6) : PeaceView 3 :=
  { leader := survivingLeaders i
    label :=
      if i.val = 2 then ⟨2, by omega⟩
      else if i.val = 3 then ⟨0, by omega⟩
      else ⟨i.val % 2, by omega⟩
    shield := survivingLeaders i
    bullet := 0
    signal_B := 0 }

private def afterSegmentRepair (i : Fin 6) : AgentState 3 :=
  PeaceView.toState (afterSegmentRepairView i)

private theorem fin6_cases (i : Fin 6) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  omega

@[simp] private theorem ring6_right_zero :
    ring6.rightNeighbor (0 : Fin 6) = 1 := by rfl

@[simp] private theorem ring6_right_one :
    ring6.rightNeighbor (1 : Fin 6) = 2 := by rfl

@[simp] private theorem ring6_right_two :
    ring6.rightNeighbor (2 : Fin 6) = 3 := by rfl

@[simp] private theorem ring6_right_three :
    ring6.rightNeighbor (3 : Fin 6) = 4 := by rfl

@[simp] private theorem ring6_right_four :
    ring6.rightNeighbor (4 : Fin 6) = 5 := by rfl

@[simp] private theorem ring6_right_five :
    ring6.rightNeighbor (5 : Fin 6) = 0 := by rfl

@[simp] private theorem fin6_zero_val : (0 : Fin 6).val = 0 := by rfl
@[simp] private theorem fin6_one_val : (1 : Fin 6).val = 1 := by rfl
@[simp] private theorem fin6_two_val : (2 : Fin 6).val = 2 := by rfl
@[simp] private theorem fin6_three_val : (3 : Fin 6).val = 3 := by rfl
@[simp] private theorem fin6_four_val : (4 : Fin 6).val = 4 := by rfl
@[simp] private theorem fin6_five_val : (5 : Fin 6).val = 5 := by rfl

theorem beforeKill_noFreeBarrier :
    noFreeBarrier hThree ring6 beforeKill := by
  intro i
  rcases fin6_cases i with h | h | h | h | h | h <;> subst i <;>
    simp [isBarrier, beforeKill, parityView, threeLeaders,
      PeaceView.toState, AgentState.isLeader]

theorem afterKill_hasFreeBarrier :
    ¬ noFreeBarrier hThree ring6 afterKill := by
  intro h
  have hbad := h (1 : Fin 6)
  simp [isBarrier, afterKill, parityView,
    survivingLeaders, PeaceView.toState, AgentState.isLeader] at hbad

theorem singletonPredIncoming_still_hasFreeBarrier :
    ¬ noFreeBarrier hThree ring6 afterSingletonRepair := by
  intro h
  have hbad := h (2 : Fin 6)
  simp [isBarrier, afterSingletonRepair,
    afterSingletonRepairView, survivingLeaders, PeaceView.toState,
    AgentState.isLeader] at hbad

theorem segmentRepair_noFreeBarrier :
    noFreeBarrier hThree ring6 afterSegmentRepair := by
  intro i
  rcases fin6_cases i with h | h | h | h | h | h <;> subst i <;>
    simp [isBarrier, afterSegmentRepair,
      afterSegmentRepairView, survivingLeaders, PeaceView.toState,
      AgentState.isLeader]

theorem afterKill_hasLeader :
    hasLeader 6 afterKill := by
  refine ⟨0, ?_⟩
  decide

end PPLLQ4775Counterexample
