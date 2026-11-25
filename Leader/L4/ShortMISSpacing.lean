import Leader.L4.ShortHopSpacing

/-! The static maximal-independent-mask spacing fact on a cyclic
header subring. No time or convergence claim is made. -/
namespace L4.ShortMISSpacing

variable {V : Type}

/-- Adjacent vertices cannot both be selected. The requirement is written
only forward; a predecessor is not needed for independence. -/
def Independent (next : V → V) (sel : V → Bool) : Prop :=
  ∀ r, sel r=true → sel (next r)=false

/-- A rejected vertex has a selected predecessor or successor. -/
def Dominating (next prev : V → V) (sel : V → Bool) : Prop :=
  ∀ r, sel r=false → sel (prev r)=true ∨ sel (next r)=true

def advance (next : V → V) (r : V) : Nat → V
  | 0 => r
  | i+1 => advance next (next r) i

structure SelectedGap (next : V → V) (sel : V → Bool) (r : V) (j : Nat) : Prop where
  positive : 0<j
  atEnd : sel (advance next r j)=true
  interior : ∀ i, 0<i → i<j → sel (advance next r i)=false

/-- Starting at a selected vertex, independence rejects the first
neighbor. If the second neighbor is rejected too, domination cannot
point back and hence selects the third neighbor. -/
theorem next_selected {next prev : V → V} {sel : V → Bool}
    (inv : ∀ r, prev (next r)=r)
    (I : Independent next sel) (D : Dominating next prev sel)
    (r : V) (R : sel r=true) :
    ∃ j, 2≤j ∧ j≤3 ∧ SelectedGap next sel r j := by
  let a := next r
  let b := next a
  have A : sel a=false := I r R
  by_cases B : sel b=true
  · refine ⟨2,by decide,by decide,⟨by decide,B,?_⟩⟩
    intro i Z K
    have : i=1 := by omega
    exact this ▸ A
  · have B' : sel b=false := Bool.eq_false_iff.mpr B
    have C : sel (next b)=true := by
      rcases D b B' with Q|Q
      · have E : prev b=a := inv a
        rw [E,A] at Q
        contradiction
      · exact Q
    refine ⟨3,by decide,by decide,⟨by decide,C,?_⟩⟩
    intro i Z K
    have E : i=1 ∨ i=2 := by omega
    rcases E with E|E
    · exact E ▸ A
    · exact E ▸ B'

theorem selected_nonempty {next prev : V → V} {sel : V → Bool}
    (D : Dominating next prev sel) (r : V) : ∃ q, sel q=true := by
  cases H : sel r
  · rcases D r H with H|H
    · exact ⟨prev r,H⟩
    · exact ⟨next r,H⟩
  · exact ⟨r,H⟩

section Physical
open ShortHopSpacing ShortResetChart ShortLayerGeometry

abbrev physicalNext {n : Nat} (f : Fin n → Nat) (r : Fin n) : Fin n :=
  nextAt r (f r)

theorem advance_eq_hop {n : Nat} (f : Fin n → Nat) (r : Fin n) (i : Nat) :
    advance (physicalNext f) r i = hop f r i := by
  induction i generalizing r with
  | zero => rfl
  | succ i ih => exact ih (physicalNext f r)

/-- The same spacing proof on the whole physical ring without requiring
the compressed predecessor to be inverse on non-headers. -/
theorem hopBounds {n : Nat} {base sel : Fin n → Bool} {f : Fin n → Nat}
    {prev : Fin n → Fin n}
    (good : ∀ q, base q=true → Gap base q (f q))
    (inv : ∀ r, base r=true → prev (physicalNext f r)=r)
    (sub : ∀ q, sel q=true → base q=true)
    (I : ∀ r, sel r=true → sel (physicalNext f r)=false)
    (D : ∀ r, base r=true → sel r=false →
         sel (prev r)=true ∨ sel (physicalNext f r)=true) :
    HopBounds f sel 2 3 := by
  intro r R
  let a := physicalNext f r
  let b := physicalNext f a
  have A : sel a=false := I r R
  have ha : base a=true := (good r (sub r R)).atEnd
  by_cases B : sel b=true
  · refine ⟨2,by decide,by decide,⟨by decide,B,?_⟩⟩
    intro i Z K
    have : i=1 := by omega
    exact this ▸ A
  · have B' : sel b=false := Bool.eq_false_iff.mpr B
    have C : sel (physicalNext f b)=true := by
      have hb : base b=true := (good a ha).atEnd
      rcases D b hb B' with Q|Q
      · have E : prev b=a := inv a ha
        rw [E,A] at Q
        contradiction
      · exact Q
    refine ⟨3,by decide,by decide,⟨by decide,C,?_⟩⟩
    intro i Z K
    have E : i=1 ∨ i=2 := by omega
    rcases E with E|E
    · exact E ▸ A
    · exact E ▸ B'

theorem nonempty_of_base {n : Nat} {base sel : Fin n → Bool}
    {f : Fin n → Nat} {prev : Fin n → Fin n}
    (H : ∃ r, base r=true)
    (D : ∀ r, base r=true → sel r=false →
         sel (prev r)=true ∨ sel (physicalNext f r)=true) :
    ∃ r, sel r=true := by
  obtain ⟨r,R⟩ := H
  cases K : sel r
  · rcases D r R K with K|K
    · exact ⟨prev r,K⟩
    · exact ⟨physicalNext f r,K⟩
  · exact ⟨r,K⟩

theorem physical_gap_bounds {n L U : Nat} {base sel : Fin n → Bool}
    {f : Fin n → Nat} {prev : Fin n → Fin n}
    (good : ∀ q, base q=true → L≤f q ∧ f q≤U ∧ Gap base q (f q))
    (inv : ∀ r, base r=true → prev (physicalNext f r)=r)
    (sub : ∀ q, sel q=true → base q=true)
    (I : ∀ r, sel r=true → sel (physicalNext f r)=false)
    (D : ∀ r, base r=true → sel r=false →
         sel (prev r)=true ∨ sel (physicalNext f r)=true) :
    GapBounds sel (2*L) (3*U) := by
  have H := spacing_transfer good sub
    (hopBounds (fun r R=>(good r R).2.2) inv sub I D)
  simpa only [Nat.mul_comm L 2,Nat.mul_comm U 3] using H

end Physical
#print axioms next_selected
#print axioms selected_nonempty
#print axioms advance_eq_hop
#print axioms hopBounds
#print axioms nonempty_of_base
#print axioms physical_gap_bounds
end L4.ShortMISSpacing
