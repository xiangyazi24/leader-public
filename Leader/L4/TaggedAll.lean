import Leader.L4.TaggedTrace
import Leader.L4.TaggedTail

namespace L4.TaggedTrace

abbrev AllObs (p c1 n : Nat) := Fin n → Obs p c1 n

def allInit {p c1 n : Nat} (x : Config p c1 n) : AllObs p c1 n :=
  fun i => init x i

def allAdvance {p c1 n : Nat} (x : AllObs p c1 n) (e : Fin n) : AllObs p c1 n :=
  fun i => advance (x i) e

def allEnded {p c1 n : Nat} (s : AllObs p c1 n) : Prop :=
  ¬ ∃ i : Fin n, ¬ ended (s i)

theorem allSurvival_proj {p c1 n : Nat} (x : AllObs p c1 n) (i : Fin n)
    (t : Nat) :
    TaggedTail.survival allAdvance (fun y => ¬ ended (y i)) t x =
    TaggedTail.survival advance (fun y => ¬ ended y) t (x i) := by
  classical
  unfold TaggedTail.survival
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases h : ¬ ended (x i)
    · simp only [TaggedTail.weightedSurvival, h]
      apply congrArg TaggedTail.sumEdge
      funext e
      exact ih (allAdvance x e)
    · simp [TaggedTail.weightedSurvival, h]

/-- Remaining probabilistic instantiation in the actual tape model:
derive these one-tag finite-word bounds from predictable drift and the
concrete live debt cap. The upper bound has no extra factor n per tag. -/
def ConcreteTagTail : Prop :=
  ∀ {p c1 n : Nat} (x : Config p c1 n) (i : Fin n) (t : Nat),
    2 ≤ p → 12 ≤ c1 → 4 ≤ n → (¬ p ∣ n) → MCOV x → COV x →
    6^t * TaggedTail.survival advance (fun y => ¬ ended y) (144*n^2+t) (init x i) ≤
      n^(144*n^2) * (6*n-1)^t

/-- This is the actual maximum (all initial tags under common physical
marks). If the concrete per-tag tail is discharged, its IID expected time
is bounded by 150n², sufficient for the entrance proof. -/
theorem concreteAllTags_mean_of_tail (htail : ConcreteTagTail)
    {p c1 n : Nat} (x : Config p c1 n)
    (hp : 2 ≤ p) (hcal : 12 ≤ c1) (hn : 4 ≤ n) (hnd : ¬ p ∣ n)
    (hm : MCOV x) (hc : COV x) :
    IIDExpectedHittingTimeAtMost allAdvance allEnded (allInit x) (150*n^2) := by
  apply TaggedTail.allTags_expected_of_tail allAdvance
    (fun (s : Fin n) y => ¬ ended (y s)) (allInit x) (by omega) (Nat.le_refl n)
  · intro i y e h he
    exact h (ended_step he e)
  · intro i t
    rw [allSurvival_proj]
    exact htail x i t hp hcal hn hnd hm hc

end L4.TaggedTrace

#print axioms L4.TaggedTrace.allSurvival_proj
#print axioms L4.TaggedTrace.concreteAllTags_mean_of_tail
