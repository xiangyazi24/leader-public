import Leader.L3.Top.StrongClasses

/-!
# Q7: repaired cut classes

`topClockStrongClasses` adds permanent purity (`MarkedDown`).  This module adds the
clause of paper (P.5) that the coloured cut had lost: every pending target input has a
post-anchor audit atom, that is, it is the operand of an export recorded after the
genuine first-tail export (the anchor).  The anchor's own packet is accepted at the
anchor time, not after it, so it must have left the window as well.

* `topClockPostAnchor` : an atom is the operand of an export after time `τ`;
* `topClockNoOldPending` : every pending target input has a post-anchor atom;
* `topClockRepairedClasses` : the record, all `TopClockCutClasses` specs proved.

The settled-empty class also carries the barrier and the carry gap: the clearing
argument of (P.11) needs them at the settled-empty cut.

Consumer: `TopClockPhaseBundle.cuts` (TopClockAssembly), for every phase from P.4--P.5 on.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The audit atom `a` is the operand of an export recorded after time `τ`.

Consumer: `topClockNoOldPending`. -/
def topClockPostAnchor {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (τ : Nat)
    (a : Option (DigitAtom n)) : Prop :=
  ∃ ex ∈ topClockConcreteExportsAfter s Z τ, ex.operand = a

/-- Every pending target input is post-anchor: accepted strictly after time `τ`.

Consumer: `topClockHasNoOld`. -/
def topClockNoOldPending {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (τ : Nat) : Prop :=
  ∀ j : Fin (topClockSpan n), (topClockConcreteInputAt s Z j).isP = true →
    topClockPostAnchor s Z τ (topClockConcreteInputAtom s Z j)

/-- The state has a tail anchor after which no pending input is older.

Consumer: `topClockRepairedClasses`. -/
def topClockHasNoOld {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  ∃ anchor : DigitExport (compileAdvice (ceilLogTwo n)) n,
    topClockConcreteTailAnchor s Z anchor ∧ topClockNoOldPending s Z anchor.time

/-- **The repaired cut classes.**  Coloured and unfavourable cuts have no old pending
input; settled-empty cuts have none and also the barrier and the carry gap.

Consumer: `TopClockPhaseBundle.cuts`. -/
noncomputable def topClockRepairedClasses {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) : TopClockCutClasses ring C s :=
  { topClockStrongClasses ring C s with
    coloured := fun Z =>
      MarkedDown ring C s Z ∧ topClockConcreteColoured ring C s Z ∧ topClockHasNoOld s Z
    settledEmpty := fun Z =>
      MarkedDown ring C s Z ∧ topClockConcreteSettledEmpty ring C s Z ∧
        topClockHasNoOld s Z ∧ topClockConcreteMovingBarrier s Z ∧
        topClockConcreteGeneratedCarryGap s Z
    unfavourable := fun Z =>
      MarkedDown ring C s Z ∧ topClockConcreteUnfavourable ring C s Z ∧ topClockHasNoOld s Z
    colouredSpec := by
      intro Z h
      obtain ⟨hr, _, hb, hgap, hf, hn⟩ := h.2.1
      exact ⟨hr, h.1, hb, hgap, hf, hn⟩
    settledSpec := by
      intro Z h
      exact ⟨h.2.1.1, h.1, h.2.1.2.2⟩
    unfavourableSpec := by
      intro Z h
      exact ⟨h.1, h.2.1.1, h.2.2⟩ }

/-- The repaired record keeps the first-tail class and the strong pending-only class.

Consumer: `topClockRepairedClasses`. -/
theorem topClockRepaired_firstTail {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) (Z : TopFixedTraceState n) :
    (topClockRepairedClasses ring C s).firstTail Z ↔ topFreshTailPermanentCut ring C s Z :=
  Iff.rfl

end MarkedCells
end L3

#print axioms L3.MarkedCells.topClockRepairedClasses
