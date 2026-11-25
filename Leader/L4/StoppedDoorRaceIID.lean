import Leader.L4.PhysicalRacePrefixes
import Leader.L4.ResetReturnIID

namespace L4.StoppedDoorRaceIID
open PhysicalCustody PhysicalDoorRace PhysicalRacePrefixes ProjectedDoor

inductive Decision where
  | live (left : Nat)
  | accept
  | reject
  deriving DecidableEq

def target : Decision→Prop
  | .live _ => False
  | .accept | .reject => True

def next {n : Nat} (d : Fin n) : Decision→Fin n→Decision
  | .accept,_ => .accept
  | .reject,_ => .reject
  | .live 0,_ => .accept
  | .live (k+1),e =>
      if DisjointMarks d e then .live (k+1)
      else if e=d then if k=0 then .accept else .live k
      else .reject

/-- The raced word monitor stops at the first wrong incident or at
the k-th correct incident. Its clock never waits for retry inside a
single race. Counting only one guaranteed paying label is enough for
the k*n upper bound; failures may stop sooner. -/
theorem race_expected {n : Nat} (d : Fin n) (k : Nat) (K : 0<k) :
    Height.IIDExpectedHittingTimeAtMost (next d) target (.live k) (n*k) := by
  let Live := fun q r=> q=Decision.live r ∧ 0<r
  apply ResetReturnIID.iid_of_relational_rank (next d) target Live (fun _ _ R=>R.2) ?_ _ k
    (.inr ⟨rfl,K⟩)
  intro q r L
  obtain ⟨rfl,R⟩ := L
  refine ⟨d,fun e=>?_⟩
  cases r with
  | zero => exact (Nat.not_lt_zero _ R).elim
  | succ j =>
    by_cases D : DisjointMarks d e
    · right
      have N : e≠d := fun eq=>D.1 eq.symm
      exact ⟨j+1,⟨by simp [next,D],R⟩,Nat.le_refl _,fun E=>(N E).elim⟩
    · by_cases E : e=d
      · subst e
        by_cases J : j=0
        · exact .inl (by simp [next,D,J,target])
        · exact .inr ⟨j,⟨by simp [next,D,J],Nat.pos_of_ne_zero J⟩,Nat.le_succ _,fun _=>Nat.lt_succ_self _⟩
      · exact .inl (by simp [next,D,E,target])

/-- This monitor's absorbing acceptance is exactly the counted
successful-event predicate at every finite sampled horizon. -/
theorem reaches_accept_iff {n : Nat} (d : Fin n) (k : Nat) (K : 0<k)
    (w : List (Fin n)) :
    BStarResetSchedule.run (next d) (.live k) w=.accept ↔ accepted d k w=1 := by
  have stayA (w : List (Fin n)) : BStarResetSchedule.run (next d) .accept w=.accept := by
    induction w with
    | nil => rfl
    | cons _ _ ih => exact ih
  have stayR (w : List (Fin n)) : BStarResetSchedule.run (next d) .reject w=.reject := by
    induction w with
    | nil => rfl
    | cons _ _ ih => exact ih
  have acc₀ (w : List (Fin n)) : accepted d 0 w=1 := by cases w <;> rfl
  induction w generalizing k with
  | nil =>
    cases k with
    | zero => exact (Nat.not_lt_zero _ K).elim
    | succ j => simp [BStarResetSchedule.run,accepted]
  | cons e w ih =>
    cases k with
    | zero => exact (Nat.not_lt_zero _ K).elim
    | succ j =>
      simp only [BStarResetSchedule.run,next,accepted]
      by_cases D : DisjointMarks d e
      · simp only [if_pos D]
        exact ih _ K
      · simp only [if_neg D]
        by_cases E : e=d
        · simp only [if_pos E]
          by_cases J : j=0
          · subst j; simp [stayA,acc₀]
          · rw [if_neg J]; exact ih _ (Nat.pos_of_ne_zero J)
        · simp [E,stayR]

/-- The full attempt still owes `later` successes outside this race.
A successful local stop retains exactly the credit earned to date. -/
def score (later : Nat) : Decision→Nat
  | .live k => AdaptiveDoorCredit.score (.live (later+k))
  | .accept => AdaptiveDoorCredit.score (.live later)
  | .reject => 0

/-- On an actual active race, the winning door multiplies accumulated
credit by three; either neighboring incident label loses, and any
truly disjoint mark maintains the current credit. -/
theorem active_race_credit {n : Nat} (hn : 4≤n) (d : Fin n) (later k : Nat)
    (K : 0<k) (cap : later+k≤6) :
    AdaptiveDoorCredit.LocalLaw (next d) (score later) (.live k) := by
  apply literal_door_local_law hn (next d) (score later) (.live k) d
  · cases k with
    | zero => exact (Nat.not_lt_zero _ K).elim
    | succ j =>
      have D : ¬ DisjointMarks d d := fun b=>b.1 rfl
      have M : (later+(j+1))-1=later+j := by omega
      have V := AdaptiveDoorCredit.pay_one (by omega : 0<later+(j+1)) cap
      rw [M] at V
      by_cases E : j=0
      · subst j
        simp only [next,if_neg D,score]
        exact Nat.le_of_eq V.symm
      · simp only [next,if_neg D,if_neg E,score]
        exact Nat.le_of_eq V.symm
  · intro e E
    cases k with
    | zero => exact (Nat.not_lt_zero _ K).elim
    | succ j =>
      have D := disjoint_symm E
      simp only [next,if_pos D,Nat.le_refl]

#print axioms active_race_credit

#print axioms race_expected
#print axioms reaches_accept_iff
end L4.StoppedDoorRaceIID
