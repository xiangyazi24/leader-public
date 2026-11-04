import Leader.AAFJ.BarrierAlgebra

set_option autoImplicit false

namespace AAFJPK.OriginalNonbarrierWord

open BarrierAlgebra

/-- Literal execution of a finite word of physical directed-ring interactions. -/
def rawRun {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) :
    (Fin n → State k) → List (Fin n) → Fin n → State k
  | C, [] => C
  | C, e :: es =>
      rawRun hk ring ((AAFJPK.protocol k hk).step ring C e) es

/-- Every selected edge is nonbarrier in its actual current prestate.

The recursive state argument is the prefix state after all earlier interactions,
so this is stronger than checking the whole word against the initial state. -/
def CurrentNonbarrierWord {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) :
    (Fin n → State k) → List (Fin n) → Prop
  | _, [] => True
  | C, e :: es =>
      ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) ∧
      CurrentNonbarrierWord hk ring
        ((AAFJPK.protocol k hk).step ring C e) es

/-- A current nonbarrier interaction cannot satisfy the original AAFJ
label-advance gate. -/
theorem not_advanceReady_of_nonbarrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n)
    (hnb : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    ¬ AdvanceReady hk ring C e := by
  intro hready
  rcases hready with ⟨hbar, _, _⟩
  exact hnb hbar

/-- A finite word that is nonbarrier at every current prefix preserves the
entire label configuration. -/
theorem labelsOf_rawRun_eq
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    {C : Fin n → State k} {word : List (Fin n)}
    (hword : CurrentNonbarrierWord hk ring C word) :
    labelsOf (rawRun hk ring C word) = labelsOf C := by
  induction word generalizing C with
  | nil =>
      rfl
  | cons e es ih =>
      rcases hword with ⟨hnb, htail⟩
      have hnot : ¬ AdvanceReady hk ring C e :=
        not_advanceReady_of_nonbarrier hk ring C e hnb
      change
        labelsOf
            (rawRun hk ring
              ((AAFJPK.protocol k hk).step ring C e) es) =
          labelsOf C
      calc
        labelsOf
            (rawRun hk ring
              ((AAFJPK.protocol k hk).step ring C e) es) =
            labelsOf ((AAFJPK.protocol k hk).step ring C e) :=
          ih htail
        _ = labelsOf C :=
          labelsOf_step_eq_self_of_not_ready hk ring C e hnot

/-- Barrier status of every physical edge is unchanged after the word. -/
theorem barrierAt_rawRun_iff
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    {C : Fin n → State k} {word : List (Fin n)}
    (hword : CurrentNonbarrierWord hk ring C word)
    (e : Fin n) :
    BarrierAt hk ring (labelsOf (rawRun hk ring C word)) e ↔
      BarrierAt hk ring (labelsOf C) e := by
  rw [labelsOf_rawRun_eq hk ring hword]

/-- Consequently the charged-barrier count is exactly invariant. -/
theorem barrierCount_rawRun_eq
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    {C : Fin n → State k} {word : List (Fin n)}
    (hword : CurrentNonbarrierWord hk ring C word) :
    barrierCount hk ring (labelsOf (rawRun hk ring C word)) =
      barrierCount hk ring (labelsOf C) := by
  rw [labelsOf_rawRun_eq hk ring hword]

/-- Exact support on two distinct physical edges. -/
def ExactTwoBarrierSupport
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (a b : Fin n) : Prop :=
  a ≠ b ∧
    ∀ e : Fin n,
      BarrierAt hk ring (labelsOf C) e ↔ e = a ∨ e = b

/-- Exact two-edge support is transported unchanged across every finite word
whose selected edge is nonbarrier in its current prestate. -/
theorem exactTwoBarrierSupport_rawRun
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    {C : Fin n → State k} {word : List (Fin n)}
    {a b : Fin n}
    (hword : CurrentNonbarrierWord hk ring C word)
    (hsupport : ExactTwoBarrierSupport hk ring C a b) :
    ExactTwoBarrierSupport hk ring (rawRun hk ring C word) a b := by
  rcases hsupport with ⟨hab, hs⟩
  refine ⟨hab, ?_⟩
  intro e
  rw [barrierAt_rawRun_iff hk ring hword e]
  exact hs e

#print axioms labelsOf_rawRun_eq
#print axioms barrierCount_rawRun_eq
#print axioms exactTwoBarrierSupport_rawRun

end AAFJPK.OriginalNonbarrierWord
