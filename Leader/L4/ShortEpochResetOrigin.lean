import Leader.L4.ShortEpochFirstHit

namespace L4.ShortEpochResetOrigin
open PhysicalCustody ShortResetMIS1Ring ShortResetCycle ShortObservedResetRelease
open SequentialMarkClock (ClearBefore)

/-- From the actual first-hit history, recover the literal own-door
mark that sets the issue observer from false to true. -/
theorem true_goal_has_launch {s n : Nat} {h : Fin n→Bool}
    (C : Chart h) (x : Raw s n) (w : List (Fin n))
    (F : BeforeGoal C (x,false) w)
    (G : ShortActualIssueClock.Goal C (ShortObservedResetRelease.run C (x,false) w)) :
    ∃ lead tail : List (Fin n),
      w=lead++RearTrace.predecessor C.root::tail ∧
      ShortActualIssueClock.Issuable C (rawRun x lead) ∧
      BeforeGoal C (rawNext s (rawRun x lead) (RearTrace.predecessor C.root),true) tail ∧
      ShortActualIssueClock.Goal C (ShortObservedResetRelease.run C
        (rawNext s (rawRun x lead) (RearTrace.predecessor C.root),true) tail) := by
  induction w generalizing x with
  | nil => exact False.elim (Bool.noConfusion G.1)
  | cons e w IH =>
    change ¬ShortActualIssueClock.Goal C (x,false) ∧
      BeforeGoal C (ShortActualIssueClock.step C (x,false) e) w at F
    change ShortActualIssueClock.Goal C (ShortObservedResetRelease.run C
      (ShortActualIssueClock.step C (x,false) e) w) at G
    by_cases Q : ShortActualIssueClock.Issuable C x ∧ e=RearTrace.predecessor C.root
    · have S : ShortActualIssueClock.step C (x,false) e=(rawNext s x e,true) := by
        simp only [ShortActualIssueClock.step,Bool.false_or,decide_eq_true Q]
      rw [S] at F G
      rw [Q.2] at F G
      exact ⟨[],w,by simp [Q.2],Q.1,F.2,G⟩
    · have S : ShortActualIssueClock.step C (x,false) e=(rawNext s x e,false) := by
        simp only [ShortActualIssueClock.step,Bool.false_or,decide_eq_false_iff_not.mpr Q]
      rw [S] at F G
      obtain ⟨a,b,W,A,B,D⟩ := IH _ F.2 G
      exact ⟨e::a,b,congrArg (e::·) W,A,B,D⟩

private theorem lower_run {s n : Nat} {h : Fin n→Bool} (N : 5≤n)
    (x : Raw s n) (H : H2Ready x) (heads : ∀ q,header x q=h q)
    (w : List (Fin n)) : H2Ready (rawRun x w) ∧ ∀ q,header (rawRun x w) q=h q := by
  induction w generalizing x with
  | nil => exact ⟨H,heads⟩
  | cons e w IH =>
    exact IH _ (h2_ready_closed N x e H)
      (fun q => (H1.raw_h1_selected_frozen N x e q H.1).trans (heads q))

/-- Corrected E4 seed carries both genuine origin and a genuinely
grant-free Parked endpoint. A fabricated Parked snapshot cannot supply
the old ISSUABLE door on its actual prefix. -/
theorem genuine_reset_seed {s n : Nat} {h : Fin n→Bool} (N : 5≤n)
    (C : Chart h) (x : Raw s n) (H : H2Ready x) (heads : ∀ q,header x q=h q)
    (w : List (Fin n)) (F : BeforeGoal C (x,false) w)
    (G : ShortActualIssueClock.Goal C (ShortObservedResetRelease.run C (x,false) w)) :
    ShortResetHelloSplice.Parked C (rawRun x w) ∧
    ∃ lead tail : List (Fin n), w=lead++RearTrace.predecessor C.root::tail ∧
      ShortActualIssueClock.Issuable C (rawRun x lead) ∧
      Active C (rawNext s (rawRun x lead) (RearTrace.predecessor C.root)) (.fwd 0) ∧
      BeforeGoal C (rawNext s (rawRun x lead) (RearTrace.predecessor C.root),true) tail ∧
      ShortActualIssueClock.Goal C (ShortObservedResetRelease.run C
        (rawNext s (rawRun x lead) (RearTrace.predecessor C.root),true) tail) := by
  obtain ⟨a,b,W,A,B,D⟩ := true_goal_has_launch C x w F G
  refine ⟨observed_first_goal_parked C N w x H heads F G,a,b,W,A,?_,B,D⟩
  exact (ShortActualIssueClock.actual_issue C N _ (lower_run N x H heads a).2 A).2

#print axioms true_goal_has_launch
#print axioms genuine_reset_seed
end L4.ShortEpochResetOrigin
