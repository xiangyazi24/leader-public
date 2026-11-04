import Leader.AAFJ.MultiBarrier.GlobalCountDropAssembly

set_option autoImplicit false

namespace AAFJPK.NoHighClosedClass

open BarrierAlgebra
open OriginalNonbarrierWord
open GlobalBarrierCountDropAssembly

/-- A set of configurations closed under every literal scheduler action. -/
def RawStepForwardClosed {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (S : (Fin n → State k) → Prop) : Prop :=
  ∀ ⦃C : Fin n → State k⦄, S C → ∀ e : Fin n,
    S ((protocol k hk).step ring C e)

/-- Every two members are connected by a literal scheduler word. -/
def RawCommunicating {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (S : (Fin n → State k) → Prop) : Prop :=
  ∀ ⦃C D : Fin n → State k⦄, S C → S D →
    ∃ w : List (Fin n), rawRun hk ring C w = D

/-- One-step closure iterates along the actual raw scheduler semantics. -/
theorem rawRun_mem_of_step_closed
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (S : (Fin n → State k) → Prop)
    (hclosed : RawStepForwardClosed hk ring S)
    {C : Fin n → State k} (hC : S C) :
    ∀ w : List (Fin n), S (rawRun hk ring C w) := by
  intro w
  induction w generalizing C with
  | nil => simpa [rawRun] using hC
  | cons e es ih =>
      simp only [rawRun]
      exact ih (hclosed hC e)

/-- Barrier count is nonincreasing along every literal scheduler word. -/
theorem rawRun_barrierCount_le
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) :
    ∀ w : List (Fin n),
      barrierCount hk ring (labelsOf (rawRun hk ring C w)) ≤
        barrierCount hk ring (labelsOf C) := by
  intro w
  induction w generalizing C with
  | nil => simp [rawRun]
  | cons e es ih =>
      have hstep := protocol_step_barrierCount_le hk ring hn2 C e
      have htail := ih ((protocol k hk).step ring C e)
      exact Nat.le_trans (by simpa [rawRun] using htail) hstep

/-- Any forward-closed set containing a multi-barrier configuration also
contains the literal endpoint of a scheduler word with strictly lower barrier
count.  This is the deterministic core of the closed-class argument. -/
theorem forward_closed_contains_strict_lower
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (S : (Fin n → State k) → Prop)
    (hclosed : RawStepForwardClosed hk ring S)
    (C : Fin n → State k) (hC : S C)
    (hcount : 1 < barrierCount hk ring (labelsOf C)) :
    ∃ D : Fin n → State k,
      S D ∧
      barrierCount hk ring (labelsOf D) <
        barrierCount hk ring (labelsOf C) := by
  obtain ⟨w, _hwlen, hdrop⟩ :=
    barrierCount_gt_one_strict_drop_word hk ring hn3 C hcount
  exact ⟨rawRun hk ring C w,
    rawRun_mem_of_step_closed hk ring S hclosed hC w, hdrop⟩

/-- No raw-step closed communicating set can contain a configuration with more
than one barrier.  A strict-drop word remains in the set, while communication
back to the root contradicts pathwise barrier-count monotonicity. -/
theorem no_closed_communicating_class_contains_count_gt_one
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (S : (Fin n → State k) → Prop)
    (hclosed : RawStepForwardClosed hk ring S)
    (hcomm : RawCommunicating hk ring S) :
    ¬ ∃ C : Fin n → State k,
      S C ∧ 1 < barrierCount hk ring (labelsOf C) := by
  rintro ⟨C, hC, hcount⟩
  obtain ⟨D, hD, hDC⟩ :=
    forward_closed_contains_strict_lower hk ring hn3 S hclosed C hC hcount
  obtain ⟨back, hback⟩ := hcomm hD hC
  have hmono := rawRun_barrierCount_le hk ring (by omega) D back
  rw [hback] at hmono
  omega

#print axioms rawRun_mem_of_step_closed
#print axioms rawRun_barrierCount_le
#print axioms forward_closed_contains_strict_lower
#print axioms no_closed_communicating_class_contains_count_gt_one

end AAFJPK.NoHighClosedClass
