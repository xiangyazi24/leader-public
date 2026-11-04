import Leader.L3.Top.FinalMobileSuffix
import Leader.L3.Top.FinalMobileLink
import Leader.L3.Top.RepairedClasses

/-!
# Q7: the audit window as a labelled window

For a fixed-trace state `Y` and an anchor time `τ`, the target registers carry:

* the queue `paQ`: the exports recorded after `τ` through the port, each with its operand and
  the pending token it makes;
* the flag `paFlag`: the register holds a pending input whose audit atom is the operand of one
  of these exports;
* the label `paLab`: the audit atom and the physical input of the register.

`consecutivePendingSuffix_of_inv` reads the pending-suffix cut clause off the labelled window
invariant `LInv`, given that every pending input is flagged (no old pending input) and that the
operands of the exports are distinct.

Consumer: `Leader/L3/TopFinalMobilePhase.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false

/-- The label of a target register: its audit atom and its physical input.

Consumer: `paLab`. -/
abbrev PaLabel (n : Nat) : Type :=
  Option (DigitAtom n) × InTok (compileAdvice (ceilLogTwo n)).topA

/-- The queue of accepted packets after `τ`.

Consumer: `LInv` for the fixed trace. -/
noncomputable def paQ {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (τ : Nat) :
    List (PaLabel n) :=
  (topClockConcreteExportsAfter s Y τ).map
    (fun ex => (ex.operand, InTok.P ex.value ex.tail))

/-- The label of window register `j`.

Consumer: `LInv` for the fixed trace. -/
def paLab {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (j : Nat) : PaLabel n :=
  ((Y.1.2.current (winSite s j)).comparison.input, (Y.1.1 (winSite s j)).qIn)

/-- Window register `j` holds a pending input whose atom is the operand of an export after `τ`.

Consumer: `LInv` for the fixed trace. -/
noncomputable def paFlag {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (τ : Nat)
    (j : Nat) : Bool :=
  decide (j < topClockSpan n ∧ (Y.1.1 (winSite s j)).qIn.isP = true ∧
    topClockPostAnchor s Y τ ((Y.1.2.current (winSite s j)).comparison.input))

/-- A flagged register is in the window, pending, and post-anchor.

Consumer: `consecutivePendingSuffix_of_inv`. -/
theorem paFlag_iff {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (τ : Nat) (j : Nat) :
    paFlag s Y τ j = true ↔ j < topClockSpan n ∧ (Y.1.1 (winSite s j)).qIn.isP = true ∧
      topClockPostAnchor s Y τ ((Y.1.2.current (winSite s j)).comparison.input) := by
  unfold paFlag
  simp

/-- **The pending suffix, read off the labelled window.**  If the labelled window invariant
holds, no pending input is old, and the operands of the exports after the anchor are distinct,
then the pending inputs are exactly the export operands from some index on, with matching
tokens, and distinct pending registers carry distinct atoms.

Consumer: `Leader/L3/TopFinalMobilePhase.lean`. -/
theorem consecutivePendingSuffix_of_inv {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hanchor : topClockConcreteTailAnchor s Y anchor)
    (hpure : topClockConcretePureStream s Y anchor)
    (hinv : LInv (topClockSpan n) (paQ s Y anchor.time) (cellOf s Y)
      (paFlag s Y anchor.time) (paLab s Y))
    (hold : topClockNoOldPending s Y anchor.time)
    (hnd : ((topClockConcreteExportsAfter s Y anchor.time).map (fun ex => ex.operand)).Nodup) :
    topClockConcreteConsecutivePendingSuffix s Y := by
  obtain ⟨_, _, k, hk, hlist⟩ := hinv
  refine ⟨anchor, hanchor, hpure, k, ?_, ?_, ?_, ?_⟩
  · simpa [paQ] using hk
  · intro j hjP
    have hflag : paFlag s Y anchor.time j.val = true := by
      rw [paFlag_iff]
      exact ⟨j.isLt, hjP, hold j hjP⟩
    obtain ⟨i, hi, hki, hl⟩ := (extract_suffix _ _ _ (topClockConcreteExportsAfter s Y anchor.time)
      (fun ex => (ex.operand, InTok.P ex.value ex.tail)) k hlist).1 j.val j.isLt hflag
    refine ⟨⟨i, hi⟩, hki, ?_, ?_⟩
    · have := congrArg Prod.fst hl
      exact this
    · refine ⟨(topClockConcreteExportsAfter s Y anchor.time)[i].value,
        (topClockConcreteExportsAfter s Y anchor.time)[i].tail, ?_, rfl, rfl⟩
      have := congrArg Prod.snd hl
      exact this
  · intro i hki
    obtain ⟨j, hj, hflag, hl⟩ := (extract_suffix _ _ _
      (topClockConcreteExportsAfter s Y anchor.time)
      (fun ex => (ex.operand, InTok.P ex.value ex.tail)) k hlist).2 i.val i.isLt hki
    obtain ⟨_, hP, _⟩ := (paFlag_iff s Y anchor.time j).1 hflag
    refine ⟨⟨j, hj⟩, hP, ?_⟩
    exact congrArg Prod.fst hl
  · intro i j hi hj hij
    have hfi : paFlag s Y anchor.time i.val = true := by
      rw [paFlag_iff]; exact ⟨i.isLt, hi, hold i hi⟩
    have hfj : paFlag s Y anchor.time j.val = true := by
      rw [paFlag_iff]; exact ⟨j.isLt, hj, hold j hj⟩
    exact Fin.ext (extract_suffix_inj _ _ _ (topClockConcreteExportsAfter s Y anchor.time)
      (fun ex => (ex.operand, InTok.P ex.value ex.tail)) Prod.fst k hlist hnd
      i.val j.val i.isLt j.isLt hfi hfj hij)

end MarkedCells
end L3

#print axioms L3.MarkedCells.consecutivePendingSuffix_of_inv
