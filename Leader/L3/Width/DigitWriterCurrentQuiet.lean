import Leader.L3.Width.DigitWriterCurrentCells
import Leader.L3.Width.DigitWriterCurrentValue

/-!
# Writer currentness: the physical value step of a completion, from the quiet intervals

`writerBlockValueQuiet`: on the audit fold of a drained start, for a writer completion of a complete
pair after `cut`, if

* every source cell `source + j` of the pair is quiet from `cut` on, and
* every target cell is written by its use with a clean cell that does not carry the base label
  `ZERO`, and is quiet from the time of its use on,

then the physical digits at the end of the word satisfy
`valueBlockID target = (valueBlockID source + 1) % topA ^ digitSpan`.

The two hypotheses are exactly the stability facts (c) of the task, written on the time-indexed
digits (`digitAt`); they are not derived from the cut.  Everything else (the ledger is a carry
chain, the uses have their frames, the frames are the letters) is proved.

Consumer: the assembly of `DigitValuesCorrect` at the writer comparison cut.
-/

namespace L3

open L3.WidthDigit
open L3.AcceptedReceipts
open L3.WriterCurrent

set_option autoImplicit false

section Quiet

variable {c : Compiled} {n : Nat}

/-- The uses of a completion's ledger are aligned with the target cells.

Consumer: `writerBlockValueQuiet`. -/
theorem usesTarget_of_completion (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (cut : Nat) (terminal : DigitTerminal c n)
    (h : DigitCompletion ring A root source target lane cut terminal) :
    ∃ L : DigitCarryGhost c n, terminal.ledger = some L ∧
      ∀ j : Nat, j < digitSpan c →
        ∃ u : DigitUse c n, L.uses[j]? = some u ∧ u.target = digitSite ring root (target + j) := by
  obtain ⟨-, -, -, -, -, -, pos, ledger, samples, exports, uses, h1, h2, h3, hj, -, -⟩ := h
  refine ⟨ledger, h1, fun j hjlt => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, u1, u2, -, -, -, -, -, -⟩ := hj ⟨j, hjlt⟩
  exact ⟨uses ⟨j, hjlt⟩, u1, u2⟩

/-- Consumer: `writerBlockValueQuiet`. -/
theorem ledgerOut_of_get (us : List (DigitUse c n)) (j : Nat) (u : DigitUse c n)
    (h : us[j]? = some u) :
    ledgerOut us j = (u.value.val + (if u.carryIn then 1 else 0)) % c.topA := by
  unfold ledgerOut
  rw [h]
  rfl

end Quiet

section Value

variable {n : Nat} {ring : DirectedRing n}

/-- **The physical value step of a writer completion on the audit fold, from the quiet
intervals.**

Consumer: the assembly of `DigitValuesCorrect` at the writer comparison cut; `hsrc` and `htgt` are
the stability facts (c). -/
theorem writerBlockValueQuiet (ref : WidthDigitReference ring) (hn2 : 2 ≤ n) (start : ref.State)
    (hd : ref.drained start) (w : List (Fin n)) (root : Fin n) (source target cut : Nat)
    (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hcomp : DigitCompletion ring
      (w.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2
      root source target DigitLane.writer cut T)
    (hsrc : ∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) →
      ∀ k, cut ≤ k → k < w.length →
        digitAt ref start w (k + 1) (digitSite ring root (source + j)) =
          digitAt ref start w k (digitSite ring root (source + j)))
    (htgt : ∀ L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n, T.ledger = some L →
      ∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) →
      ∀ u : DigitUse (compileAdvice (ceilLogTwo n)) n, L.uses[j]? = some u →
        ((piD (ref.phys (stateAt ref start w (u.time - 1)).1)) u.target).top.topDirty = false ∧
        ((piD (ref.phys (stateAt ref start w (u.time - 1)).1)) u.target).top.wBase ≠ .ZERO ∧
        ∀ k, u.time ≤ k → k < w.length →
          digitAt ref start w (k + 1) u.target = digitAt ref start w k u.target) :
    valueBlockID ring root
        (digitValueView (piD (ref.phys (w.foldl (widthDigitAuditNext ref)
          (start, digitAuditInitial (piD (ref.phys start)))).1))) target =
      (valueBlockID ring root
        (digitValueView (piD (ref.phys (w.foldl (widthDigitAuditNext ref)
          (start, digitAuditInitial (piD (ref.phys start)))).1))) source + 1) %
        (compileAdvice (ceilLogTwo n)).topA ^ digitSpan (compileAdvice (ceilLogTwo n)) := by
  obtain ⟨L, hL, hinh, hlen, hsamp⟩ := ledgerIn_of_completion ring _ root source target
    DigitLane.writer cut T hcomp
  obtain ⟨L', hL', huse⟩ := usesTarget_of_completion ring _ root source target
    DigitLane.writer cut T hcomp
  have hLL : L' = L := by
    have := hL.symm.trans hL'
    exact (Option.some.inj this).symm
  subst hLL
  have hinv := (auditCarryInv_fold ref w (start, digitAuditInitial (piD (ref.phys start))) hd
    (auditCarryInv_initial ring _)).2
  have hch := writerTerminalChain hinv T hcomp.2.1 hcomp.2.2.1 L' hL hinh
  have hframed := terminalUsesFramed ref hn2 start hd w T hcomp.2.1 hcomp.2.2.1 L' hL
  have hend : ∀ i, (digitValueView (piD (ref.phys (w.foldl (widthDigitAuditNext ref)
      (start, digitAuditInitial (piD (ref.phys start)))).1)) i).2 =
      digitAt ref start w w.length i := by
    intro i
    simp [digitValueView, digitAt, stateAt, List.take_length]
  refine blockValue_succ_of_cells _ source target hch hlen ?_ ?_
  · intro j hj
    obtain ⟨f, hf, hfe, hfc, hfv⟩ := hsamp j hj
    obtain ⟨h1, h2, h3, h4⟩ := frameLink ref start w hd f hf
    rw [hend]
    have hold : ledgerIn L'.uses j = (digitAt ref start w (f.time - 1) (f.edge)).val := by
      rw [hfv, hfe, h3]
      rfl
    rw [hold, hfe]
    have hq := digitAt_quiet ref start w (digitSite ring root (source + j)) (f.time - 1)
      (by omega) (fun k hk hk2 => hsrc j hj k (by omega) hk2)
    rw [hq]
  · intro j hj
    obtain ⟨u, hu, hut⟩ := huse j hj
    have hmem : u ∈ L'.uses := List.mem_iff_getElem?.mpr ⟨j, hu⟩
    obtain ⟨f, hf, hft, hcase⟩ := hframed u hmem
    obtain ⟨h1, h2, h3, h4⟩ := frameLink ref start w hd f hf
    obtain ⟨hcl, hnz, hqu⟩ := htgt L' hL j hj u hu
    rw [hend, ledgerOut_of_get _ j u hu, ← hut]
    have hdig : digitAt ref start w u.time u.target =
        (phiD ring f.old f.edge u.target).top.d := by
      rw [← hft]
      unfold digitAt
      rw [h4]
    have hdirt : ¬ ((f.old u.target).top.topDirty = true) := by
      rw [h3, hft]
      intro h
      rw [h] at hcl
      exact absurd hcl (by simp)
    have hzero : ¬ ((f.old u.target).top.wBase = .ZERO) := by
      intro h
      rw [h3, hft] at h
      exact hnz h
    have hval : digitAt ref start w u.time u.target =
        (compileAdvice (ceilLogTwo n)).digitMod
          (u.value.val + (if u.carryIn then 1 else 0)) := by
      rw [hdig]
      rcases hcase with hc | hc | hc
      · exact hc
      · exact absurd hc hdirt
      · exact absurd hc hzero
    have hq := digitAt_quiet ref start w u.target u.time (by omega)
      (fun k hk hk2 => hqu k hk hk2)
    rw [hq, hval]
    rfl

end Value

end L3

#print axioms L3.writerBlockValueQuiet
