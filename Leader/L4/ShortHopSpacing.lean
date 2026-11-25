import Leader.L4.ShortLayerGeometry

/-! Static quotient-to-physical transfer for selected headers. A hop is
a counter on a frozen header mask, not a new mark in the raw scheduler. -/
namespace L4.ShortHopSpacing

open ShortResetChart ShortLayerGeometry

def hop {n : Nat} (f : Fin n → Nat) (r : Fin n) : Nat → Fin n
  | 0 => r
  | j+1 => hop f (nextAt r (f r)) j

def span {n : Nat} (f : Fin n → Nat) (r : Fin n) : Nat → Nat
  | 0 => 0
  | j+1 => f r + span f (nextAt r (f r)) j

theorem hop_eq_nextAt_span {n : Nat} (f : Fin n → Nat) (r : Fin n) (j : Nat) :
    hop f r j = nextAt r (span f r j) := by
  induction j generalizing r with
  | zero => rfl
  | succ j ih =>
    change hop f (nextAt r (f r)) j = nextAt r (f r + span f (nextAt r (f r)) j)
    rw [ih, nextAt_add]

theorem hop_add {n : Nat} (f : Fin n → Nat) (r : Fin n) (i j : Nat) :
    hop f r (i+j) = hop f (hop f r i) j := by
  induction i generalizing r with
  | zero => simp [hop]
  | succ i ih =>
    rw [show i+1+j=i+j+1 by omega]
    exact ih (nextAt r (f r))

/-- Every positive count below this hit contains only rejected headers. -/
structure HopGap {n : Nat} (f : Fin n → Nat) (sel : Fin n → Bool)
    (r : Fin n) (j : Nat) : Prop where
  positive : 0<j
  atEnd : sel (hop f r j)=true
  interior : ∀ i, 0<i → i<j → sel (hop f r i)=false

abbrev GapBounds {n : Nat} (h : Fin n → Bool) (L U : Nat) : Prop :=
  ∀ q, h q=true → ∃ d, L≤d ∧ d≤U ∧ Gap h q d

abbrev HopBounds {n : Nat} (f : Fin n → Nat) (sel : Fin n → Bool) (a b : Nat) : Prop :=
  ∀ q, sel q=true → ∃ j, a≤j ∧ j≤b ∧ HopGap f sel q j

theorem physical_gap_of_hop_gap {n L U : Nat} {h sel : Fin n → Bool}
    {f : Fin n → Nat}
    (f_ok : ∀ q, h q=true → L≤f q ∧ f q≤U ∧ Gap h q (f q))
    (sub : ∀ q, sel q=true → h q=true) {r : Fin n} (root : h r=true)
    {j : Nat} (H : HopGap f sel r j) :
    L*j≤span f r j ∧ span f r j≤U*j ∧ Gap sel r (span f r j) := by
  induction j generalizing r with
  | zero => exact False.elim (Nat.not_lt_zero 0 H.positive)
  | succ j ih =>
    obtain ⟨A,B,G⟩ := f_ok r root
    by_cases J : j=0
    · subst j
      have R : sel (nextAt r (f r))=true := H.atEnd
      simpa [span] using And.intro A (And.intro B (gap_to_submask sub G R))
    · have skip : sel (nextAt r (f r))=false := H.interior 1 (by decide) (by omega)
      have K : HopGap f sel (nextAt r (f r)) j := by
        refine ⟨by omega,H.atEnd,?_⟩
        intro i I P
        exact H.interior (i+1) (by omega) (by omega)
      obtain ⟨a,b,g⟩ := ih G.atEnd K
      exact ⟨by simp only [Nat.mul_succ, span]; omega,
        by simp only [Nat.mul_succ, span]; omega, join_rejected sub G skip g⟩

theorem spacing_transfer {n L U a b : Nat} {h sel : Fin n → Bool}
    {f : Fin n → Nat}
    (f_ok : ∀ q, h q=true → L≤f q ∧ f q≤U ∧ Gap h q (f q))
    (sub : ∀ q, sel q=true → h q=true) (H : HopBounds f sel a b) :
    GapBounds sel (L*a) (U*b) := by
  intro r R
  obtain ⟨j,A,B,G⟩ := H r R
  obtain ⟨C,D,F⟩ := physical_gap_of_hop_gap f_ok sub (sub r R) G
  exact ⟨span f r j,Nat.le_trans (Nat.mul_le_mul_left _ A) C,
    Nat.le_trans D (Nat.mul_le_mul_left _ B),F⟩

/-- Eliminates a need to expose the original successor width implementation.
The distant choices at sites that are not headers are never used on a
chain starting at a header. -/
noncomputable def successorWidth {n L U : Nat} {h : Fin n → Bool}
    (H : GapBounds h L U) (q : Fin n) : Nat :=
  if Q : h q=true then Classical.choose (H q Q) else 0

theorem successorWidth_spec {n L U : Nat} {h : Fin n → Bool}
    (H : GapBounds h L U) (q : Fin n) (Q : h q=true) :
    L≤successorWidth H q ∧ successorWidth H q≤U ∧ Gap h q (successorWidth H q) := by
  simpa only [successorWidth,dif_pos Q] using Classical.choose_spec (H q Q)

theorem spacing_transfer_chosen {n L U a b : Nat} {h sel : Fin n → Bool}
    (base : GapBounds h L U) (sub : ∀ q, sel q=true → h q=true)
    (H : HopBounds (successorWidth base) sel a b) :
    GapBounds sel (L*a) (U*b) :=
  spacing_transfer (successorWidth_spec base) sub H

end L4.ShortHopSpacing
