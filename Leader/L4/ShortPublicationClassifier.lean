import Leader.L4.ShortSelectorChange
import Leader.L4.ShortSelectorFlip
import Leader.L4.ShortPublicationOwner

namespace L4.ShortPublicationClassifier
open AllSizeProtocol PhysicalCustody ShortResetMIS1Ring ShortResetRow

/-- Count publication by the selected BANK'S INDEX, not its data bit.
A real COMMIT preserves this event even when the new Boolean equals
the old one. The eligibility test is on the actual old H1 responder. -/
def classify {s n : Nat} (x : Raw s n) (e : Fin n) : Option (Fin n) :=
  let i := rightNeighbor e
  if header x i=true ∧ (rawNext s x e i).mis1.getLsbD 92≠(x i).mis1.getLsbD 92 then
    some i else none

theorem classify_some {s n : Nat} (x : Raw s n) (e i : Fin n) :
    classify x e=some i ↔ rightNeighbor e=i ∧ header x i=true ∧
      (rawNext s x e i).mis1.getLsbD 92≠(x i).mis1.getLsbD 92 := by
  unfold classify
  dsimp only
  split
  · rename_i H
    constructor
    · intro E
      have D := Option.some.inj E
      exact ⟨D,D ▸ H⟩
    · exact fun P=>congrArg some P.1
  · rename_i H
    constructor
    · intro P
      cases P
    · intro ⟨P,A,B⟩
      rw [←P] at A B
      exact False.elim (H ⟨A,B⟩)

theorem recorded_guard {s n : Nat} (x : Raw s n) (e i : Fin n) (E : classify x e=some i) :
    rightNeighbor e=i ∧ header x i=true ∧
      selectorGuard (header x e) (x e).mis1 (x i).mis1 := by
  obtain ⟨R,H,D⟩ := (classify_some x e i).mp E
  exact ⟨R,H,(ShortSelectorChange.selector_change_incoming_guard x e i D).2⟩

/-- On a selected old header not recorded by the classifier, the
selector did not change, including nonincident and initiating marks. -/
theorem unrecorded_selector_stutters {s n : Nat} (x : Raw s n) (e i : Fin n)
    (H : header x i=true) (none : classify x e≠some i) :
    (rawNext s x e i).mis1.getLsbD 92=(x i).mis1.getLsbD 92 := by
  by_cases D : (rawNext s x e i).mis1.getLsbD 92≠(x i).mis1.getLsbD 92
  · have R := (ShortSelectorChange.selector_change_incoming_guard x e i D).1
    exact False.elim (none ((classify_some x e i).mpr ⟨R,H,D⟩))
  · exact Classical.not_not.mp D

/-- Lift the controller's literal NOR payload to the chosen publisher's
fresh verified two-reader witness. This contract is intentionally
conditional on the provenance of the two stored witness bits. -/
def FromProtectedBits (l r : Bool) (d : Nat) : Prop :=
  ∃ raw : BitVec 96, raw.getLsbD 74=l ∧ raw.getLsbD 72=r ∧
    MISByteCodec.issuedDescriptor raw=d

#print axioms classify_some
#print axioms recorded_guard
#print axioms unrecorded_selector_stutters

/-- Every eligible guarded COMMIT is counted, including identity writes
to the public Boolean, because it takes the complementary selector. -/
theorem guard_recorded {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (G : selectorGuard (header x e) (x e).mis1 (x (rightNeighbor e)).mis1) :
    classify x e=some (rightNeighbor e) := by
  apply (classify_some _ _ _).mpr
  refine ⟨rfl,head,?_⟩
  rw [ShortSelectorFlip.guarded_commit_flips x e sep head G]
  cases (x (rightNeighbor e)).mis1.getLsbD 92 <;> decide

#print axioms guard_recorded
end L4.ShortPublicationClassifier
