import Leader.L4.PhysicalCustody
import Leader.L4.Statement

namespace L4.PhysicalShortSheet
open AllSizeProtocol AllSizeS1Geometry PhysicalCustody

inductive Sheet where
  | mis1 | mis2 | mis3

def bytes {a : LargeParams} : Sheet → LargeSite a → BitVec 96
  | .mis1 => LargeSite.mis1
  | .mis2 => LargeSite.mis2
  | .mis3 => LargeSite.mis3

def eligible : Sheet → Headers → Bool
  | .mis1 => Headers.h1
  | .mis2 => Headers.h2
  | .mis3 => Headers.h3

def pairStep {a : LargeParams} (b : LargeRows a) (h : Pair Bool)
    (x : Pair (BitVec 96)) : Pair (BitVec 96) :=
  patchPair (ShortGeo.mis.patches 3 h x (b.mis h x)) x

/-- Unified literal old-pair projection, including the cache patch. No
restriction on raw slice bytes or compatibility of the other layers. -/
theorem exact_pair {a : LargeParams} (b : LargeRows a) (j : Sheet)
    (x : Pair (LargeSite a)) :
    Pair.map (bytes j) (largePair b x) =
      pairStep b (Pair.map (fun y=>eligible j (oldHeaders b y)) x) (Pair.map (bytes j) x) := by
  cases j <;> rfl

def sliceStep {a : LargeParams} {n : Nat} (b : LargeRows a) (h : Fin n → Bool)
    (x : Fin n → BitVec 96) (e : Fin n) : Fin n → BitVec 96 :=
  let r := rightNeighbor e
  let p := pairStep b (h e,h r) (x e,x r)
  fun i=>if i=e then p.1 else if i=r then p.2 else x i

def mask {s n : Nat} (j : Sheet) (x : Raw s n) (i : Fin n) : Bool :=
  eligible j (oldHeaders (rows s) (x i))

theorem exact_raw_step {s n : Nat} (j : Sheet) (x : Raw s n) (e : Fin n) :
    (fun i=>bytes j (rawNext s x e i)) =
      sliceStep (rows s) (mask j x) (fun i=>bytes j (x i)) e := by
  have P := exact_pair (rows s) j (x e,x (rightNeighbor e))
  funext i
  unfold rawNext AllSizeS1Geometry.step sliceStep
  dsimp only
  by_cases E : i=e
  · simp only [E]
    exact congrArg Prod.fst P
  · rw [if_neg E,if_neg E]
    by_cases F : i=rightNeighbor e
    · rw [if_pos F,if_pos F]
      exact congrArg Prod.snd P
    · rw [if_neg F,if_neg F]

/-- Iterate the very same raw labels, not a thinned or resampled tape.
The frozen-mask field is explicit and must be proved independently. -/
theorem exact_fixed_run {s n : Nat} (j : Sheet) (h : Fin n → Bool)
    (Q : Raw s n → Prop) (frozen : ∀ x, Q x → mask j x=h)
    (closed : ∀ x e, Q x → Q (rawNext s x e)) (w : List (Fin n)) (x : Raw s n) (X : Q x) :
    (fun i=>bytes j (rawRun x w i)) =
      BStarResetSchedule.run (sliceStep (rows s) h) (fun i=>bytes j (x i)) w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    change (fun i=>bytes j (rawRun (rawNext s x e) w i)) =
      BStarResetSchedule.run (sliceStep (rows s) h)
        (sliceStep (rows s) h (fun i=>bytes j (x i)) e) w
    rw [ih _ (closed x e X),exact_raw_step,frozen x X]

/-- Lift an IID hitting-time bound for the sheet on the original physical
alphabet. This applies only to a target detected from the sheet itself. -/
theorem exact_fixed_cost {s n : Nat} (j : Sheet) (h : Fin n → Bool)
    (Q : Raw s n → Prop) (frozen : ∀ x, Q x → mask j x=h)
    (closed : ∀ x e, Q x → Q (rawNext s x e))
    (T : (Fin n → BitVec 96) → Prop) (t : Nat) (x : Raw s n) (X : Q x) :
    iidHitCost (rawNext s) (fun y=>T (fun i=>bytes j (y i))) t x =
      iidHitCost (sliceStep (rows s) h) T t (fun i=>bytes j (x i)) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases H : T (fun i=>bytes j (x i))
    · simp [iidHitCost,H]
    · simp only [iidHitCost,if_neg H]
      congr 2
      apply congrArg List.ofFn
      funext e
      rw [ih _ (closed x e X),exact_raw_step,frozen x X]

theorem expected_of_slice {s n K : Nat} (j : Sheet) (h : Fin n → Bool)
    (Q : Raw s n → Prop) (frozen : ∀ x, Q x → mask j x=h)
    (closed : ∀ x e, Q x → Q (rawNext s x e))
    (T : (Fin n → BitVec 96) → Prop) (x : Raw s n) (X : Q x)
    (E : IIDExpectedHittingTimeAtMost (sliceStep (rows s) h) T
      (fun i=>bytes j (x i)) K) :
    IIDExpectedHittingTimeAtMost (rawNext s) (fun y=>T (fun i=>bytes j (y i))) x K := by
  intro t
  rw [exact_fixed_cost j h Q frozen closed T t x X]
  exact E t

#print axioms exact_fixed_cost
#print axioms expected_of_slice
#print axioms exact_pair
#print axioms exact_raw_step
#print axioms exact_fixed_run
end L4.PhysicalShortSheet
