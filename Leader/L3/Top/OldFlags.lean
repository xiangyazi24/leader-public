import Leader.L3.Top.OldGhost
import Leader.L3.Top.MarkedDebtRows
import Leader.L3.Top.RepairedClasses

/-!
# Q7: the old-pending flags of the fixed trace

`oldFlag s Z τ j` : target register `j` holds a pending input whose audit atom is not the
operand of an export recorded after time `τ`.  Along an edge the flags are carried by
the pending inputs: a flag is created nowhere, because an accepted packet's atom is the
operand of the export recorded in the same step, and the set of recorded exports only grows.

Consumer: `Leader/L3/Top/OldMarkStep.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false

/-- Filtering the reversed exports of a longer frame list.

Consumer: `exportsAfter_next`. -/
theorem exports_cons {α β : Type} (L : List α) (F : α) (g : α → Option β) (φ : β → Bool) :
    ((F :: L).reverse.filterMap g).filter φ =
      ((L.reverse.filterMap g).filter φ) ++ ((g F).toList.filter φ) := by
  rcases hg : g F with _ | b <;>
    simp [List.reverse_cons, List.filterMap_append, List.filter_append, hg]

/-- The exports after time `τ` only grow along the trace.

Consumer: `post_next`. -/
theorem exportsAfter_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat) :
    ∃ extra, topClockConcreteExportsAfter s (topFixedTraceNext ring C Z e) τ =
      topClockConcreteExportsAfter s Z τ ++ extra ∧
    ∀ ex, ex ∈ extra ↔
      ((digitLaneReplay .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
          (Z.1.1 (ring.rightNeighbor e)).beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).exported = some ex ∧
        τ < ex.time ∧ ex.source = certSite s (topClockSpan n - 1) ∧
        ex.destination = certSite s (topClockSpan n)) := by
  obtain ⟨F, hF1, hF2⟩ : ∃ F : DigitFrame (compileAdvice (ceilLogTwo n)) n,
      (topFixedTraceNext ring C Z e).1.2.frames = F :: Z.1.2.frames ∧
      (digitReceiptLane .comparison F.receipt).exported =
        (digitLaneReplay .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
          (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
          (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
            (Z.1.1 (ring.rightNeighbor e)).beta)
          (Z.1.2.current e).comparison
          (Z.1.2.current (ring.rightNeighbor e)).comparison).exported := ⟨_, rfl, rfl⟩
  refine ⟨((digitReceiptLane .comparison F.receipt).exported.toList).filter
      (fun ex => if τ < ex.time ∧ ex.source = certSite s (topClockSpan n - 1) ∧
          ex.destination = certSite s (topClockSpan n) then true else false), ?_, ?_⟩
  · unfold topClockConcreteExportsAfter
    rw [hF1]
    exact exports_cons Z.1.2.frames F _ _
  · intro ex
    rw [← hF2]
    simp [List.mem_filter, Option.mem_toList]

/-- A post-anchor atom stays post-anchor.

Consumer: `old_away`. -/
theorem post_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat)
    (a : Option (DigitAtom n)) (h : topClockPostAnchor s Z τ a) :
    topClockPostAnchor s (topFixedTraceNext ring C Z e) τ a := by
  obtain ⟨ex, hex, hop⟩ := h
  obtain ⟨extra, hl, _⟩ := exportsAfter_next ring C s Z e τ
  exact ⟨ex, by rw [hl]; exact List.mem_append_left _ hex, hop⟩

/-- The exported operand of an accepting edge is post-anchor.

Consumer: `old_responder`. -/
theorem post_accept {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (τ : Nat) (hτ : τ ≤ Z.1.2.clock)
    (he : e = certSite s (topClockSpan n - 1))
    (hy : ring.rightNeighbor e = certSite s (topClockSpan n))
    (ex : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hR : (digitLaneReplay .comparison (Z.1.2.clock + 1) e (ring.rightNeighbor e)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
        (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
          (Z.1.1 (ring.rightNeighbor e)).beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).exported = some ex)
    (htime : ex.time = Z.1.2.clock + 1) (hsrc : ex.source = e) (hdst : ex.destination = ring.rightNeighbor e) :
    topClockPostAnchor s (topFixedTraceNext ring C Z e) τ ex.operand := by
  obtain ⟨extra, hl, hex⟩ := exportsAfter_next ring C s Z e τ
  refine ⟨ex, ?_, rfl⟩
  rw [hl]
  apply List.mem_append_right
  rw [hex]
  exact ⟨hR, by omega, by rw [hsrc, he], by rw [hdst, hy]⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.post_next
#print axioms L3.MarkedCells.post_accept
