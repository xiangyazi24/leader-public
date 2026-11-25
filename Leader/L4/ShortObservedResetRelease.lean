import Leader.L4.ShortResetHelloSplice
import Leader.L4.ShortAllOwnerClock

namespace L4.ShortObservedResetRelease
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetCycle
open ShortResetReleased

def run {s n : Nat} {h : Fin n → Bool} (C : Chart h) :
    (Raw s n × Bool) → List (Fin n) → Raw s n × Bool :=
  SequentialMarkClock.run (ShortActualIssueClock.step C)

/-- No proper prefix (including the empty prefix) of this segment has
already hit its phase's real observer target. The empty segment has
no proper prefixes. -/
abbrev BeforeGoal {s n : Nat} {h : Fin n → Bool} (C : Chart h) :=
  SequentialMarkClock.ClearBefore (ShortActualIssueClock.step (s:=s) C)
    (ShortActualIssueClock.Goal (s:=s) C)

private theorem phase_wait_or_done {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (st : Stage) (A : Active C x st) : st=.done ∨ Wait0 x C.root := by
  cases st
  · exact .inr A.2.1
  · exact .inr A.2.1
  · exact .inl rfl

private theorem active_of_observed_completion {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (x : Raw s n) (st : Stage) (A : Active C x st)
    (G : ShortActualIssueClock.Goal C (x,true)) : st=.done := by
  obtain E|W := phase_wait_or_done C x st A
  · exact E
  · exact False.elim (by have bad := W.1.symm.trans G.2.2.1; contradiction)

private theorem observed_from_active {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (N : 5≤n) (w : List (Fin n)) (x : Raw s n)
    (H : H2Ready x) (heads : ∀ j,header x j=h j)
    (st : Stage) (A : Active C x st) (R : Released C x st)
    (first : BeforeGoal C (x,true) w)
    (G : ShortActualIssueClock.Goal C (run C (x,true) w)) :
    Released C (run C (x,true) w).1 .done := by
  induction w generalizing x st with
  | nil =>
    have E := active_of_observed_completion C x st A G
    subst st
    exact R
  | cons e w ih =>
    change ¬ShortActualIssueClock.Goal C (x,true) ∧
      BeforeGoal C (ShortActualIssueClock.step C (x,true) e) w at first
    have prev : st≠.done := by
      intro D
      subst st
      exact first.1 ⟨rfl,A⟩
    have S : ShortActualIssueClock.step C (x,true) e=(rawNext s x e,true) := rfl
    rw [S] at first
    change ShortActualIssueClock.Goal C (run C (ShortActualIssueClock.step C (x,true) e) w) at G
    rw [S] at G
    change Released C (run C (ShortActualIssueClock.step C (x,true) e) w).1 .done
    rw [S]
    exact ih (rawNext s x e) (h2_ready_closed N x e H)
      (fun j=>(H1.raw_h1_selected_frozen N x e j H.1).trans (heads j))
      (nextStage C e st) (active_step C x e (by omega) heads st prev A)
      (step_released C x e (by omega) heads st prev A R) first.2 G

/-- The first paid observer goal has a real RESET0 origin and has
released each of that chart's owned grants. An arbitrary late snapshot
with the sticky issue bit is not credited by this lemma. -/
theorem observed_reset_goal_has_released {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (N : 5≤n) (w : List (Fin n)) (x : Raw s n)
    (H : H2Ready x) (heads : ∀ j, header x j=h j)
    (first : BeforeGoal C (x,false) w)
    (G : ShortActualIssueClock.Goal C (run C (x,false) w)) :
    Released C (run C (x,false) w).1 .done := by
  induction w generalizing x with
  | nil =>
    have E : false=true := G.1
    contradiction
  | cons e w ih =>
    change ¬ShortActualIssueClock.Goal C (x,false) ∧
      BeforeGoal C (ShortActualIssueClock.step C (x,false) e) w at first
    change ShortActualIssueClock.Goal C (run C (ShortActualIssueClock.step C (x,false) e) w) at G
    change Released C (run C (ShortActualIssueClock.step C (x,false) e) w).1 .done
    have Y := h2_ready_closed N x e H
    have HH (j : Fin n) := (H1.raw_h1_selected_frozen N x e j H.1).trans (heads j)
    by_cases Q : ShortActualIssueClock.Issuable C x ∧ e=RearTrace.predecessor C.root
    · have S : ShortActualIssueClock.step C (x,false) e=(rawNext s x e,true) := by
        simp only [ShortActualIssueClock.step,Bool.false_or,decide_eq_true Q]
      rw [S] at first G ⊢
      have A : Active C (rawNext s x e) (.fwd 0) := by
        rw [Q.2]
        exact (ShortActualIssueClock.actual_issue C N x heads Q.1).2
      exact observed_from_active C N w _ Y HH (.fwd 0) A (released_at_issue C _) first.2 G
    · have S : ShortActualIssueClock.step C (x,false) e=(rawNext s x e,false) := by
        simp only [ShortActualIssueClock.step,Bool.false_or,decide_eq_false_iff_not.mpr Q]
      rw [S] at first G ⊢
      exact ih _ Y HH first.2 G

theorem observed_endpoint_is_literal {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (z : Raw s n × Bool) (w : List (Fin n)) :
    (run C z w).1 = rawRun z.1 w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih => exact ih (ShortActualIssueClock.step C z e)

/-- The start of an owner's next clean epoch is a specific physical
cut, not the eventual endpoint of all-owner cleanup. -/
theorem observed_first_goal_parked {s n : Nat} {h : Fin n → Bool}
    (C : Chart h) (N : 5≤n) (w : List (Fin n)) (x : Raw s n)
    (H : H2Ready x) (heads : ∀ j,header x j=h j)
    (first : BeforeGoal C (x,false) w)
    (G : ShortActualIssueClock.Goal C (run C (x,false) w)) :
    ShortResetHelloSplice.Parked C (rawRun x w) := by
  rw [←observed_endpoint_is_literal C (x,false) w]
  exact ShortResetHelloSplice.parked_after_consume C _ G.2
    (observed_reset_goal_has_released C N w x H heads first G)

open ShortSequentialClean in
/-- On this very word, every listed owner has a real, grant-free
ISSUE1 receipt at its own chronological reset cut. -/
def ReleasedReceipts {s n : Nat} {h : Fin n → Bool} :
    List (Certified s n h) → Raw s n → List (Fin n) → Prop
  | [], _, _ => True
  | c::cs, x, w => ∃ u v, w=u++v ∧ u≠[] ∧
      BeforeGoal c.chart (x,false) u ∧
      ShortResetHelloSplice.Parked c.chart (rawRun x u) ∧
      ReleasedReceipts cs (rawRun x u) v

open ShortSequentialClean in
private theorem fiber_run {s n : Nat} {h : Fin n → Bool} (N : 5≤n)
    (x : Raw s n) (w : List (Fin n)) (H : Fiber h x) :
    Fiber h (rawRun x w) := by
  induction w generalizing x with
  | nil => exact H
  | cons e w ih =>
    exact ih _ ⟨h2_ready_closed N x e H.1,
      fun j=>(H1.raw_h1_selected_frozen N x e j H.1.1).trans (H.2 j)⟩

open ShortSequentialClean in
theorem released_of_first_hits {s n : Nat} {h : Fin n → Bool} (N : 5≤n)
    (cs : List (Certified s n h)) (x : Raw s n) (w : List (Fin n))
    (H : Fiber h x)
    (R : SequentialMarkClock.FirstHitReceipts phase goal false cs (x,false) w) :
    ReleasedReceipts cs x w := by
  induction cs generalizing x w with
  | nil => trivial
  | cons c cs ih =>
    obtain ⟨u,v,E,ne,F,G,T⟩ := R
    have same : (run c.chart (x,false) u).1=rawRun x u := observed_endpoint_is_literal _ _ _
    change SequentialMarkClock.FirstHitReceipts phase goal false cs ((run c.chart (x,false) u).1,false) v at T
    rw [same] at T
    exact ⟨u,v,E,ne,F,observed_first_goal_parked c.chart N u x H.1 H.2 F G,
      ih _ _ (fiber_run N x u H) T⟩

open ShortSequentialClean in
theorem all_owner_released_receipts {s n : Nat} {h : Fin n → Bool} (N : 5≤n)
    (x : Raw s n) (cs : List (Certified s n h)) (w : List (Fin n))
    (H : Fiber h x) (E : cs.map (fun c=>c.chart.root)=ShortAllOwnerClock.roots h)
    (D : SequentialMarkClock.finished
      (SequentialMarkClock.run next (SequentialMarkClock.start false cs x) w)) :
    (∀ r : Fin n, h r=true ↔ ∃ c∈cs,c.chart.root=r) ∧ ReleasedReceipts cs x w := by
  obtain ⟨U,R⟩ := ShortAllOwnerClock.all_owner_first_hit_receipts x cs w E D
  exact ⟨U,released_of_first_hits N cs x w H R⟩

end L4.ShortObservedResetRelease
