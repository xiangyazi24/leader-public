import Leader.L3.Width.DigitComparisonValuesRow
import Leader.L3.Target

/-!
# R10c digit values: the digit-write rows of one step of the digit projection

Item (a) of the task.  One step `phiD ring S e` of the digit projection writes the digit of the
edge endpoints through `liveTopPair`.  The rows below state what a writer step stores:

* advance: the right endpoint stores `digitMod (v + carry)` for the settled input `v` it holds;
* launch: a delimiter source holding a settled input `v` stores `digitMod (v + 1)`;
* base: a source with base label `ZERO` stores `zeroDigit`;

each unless the written cell is dirty, in which case the digit is kept (and the dirty cell is
rejected at its next service).  The stored digit is therefore a function of the *sampled* input,
not of the final value of the source block: items (b) and (c) need the sampled input to be settled
and the cell to be clean, which are not consequences of the cut (see
`research/lean-l3/ledgers/R10c-digit-values-notes.md`).

Consumer: `Leader/L3/Width/DigitComparisonValuesLedger.lean` pairs these rows with the ghost uses;
the notes list the remaining freshness facts.
-/

namespace L3

set_option autoImplicit false

section Write

variable {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c) (e : Fin n)

/-- **Advance write.**  The right endpoint of the edge `e` stores the settled input plus the
carry.

Consumer: the writer value step of a completion (ledger use `h`, `targetDigit` and `carryIn`). -/
theorem writerAdvanceWrite (hne : ring.rightNeighbor e ≠ e) (cc : Bool) (v : Fin c.topA) (T : Bool)
    (hxl : (S e).word.native.l = false) (hyl : (S (ring.rightNeighbor e)).word.native.l = false)
    (hbY : (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta = false)
    (hw : (S e).top.wCarry = .W cc) (hoff : (S (ring.rightNeighbor e)).top.wCarry = .OFF)
    (hs : (S (ring.rightNeighbor e)).top.wIn = .S v T) :
    (phiD ring S e (ring.rightNeighbor e)).top.d =
      (if (S (ring.rightNeighbor e)).top.topDirty = true then (S (ring.rightNeighbor e)).top.d
       else c.digitMod (v.val + (if cc then 1 else 0))) := by
  have h := liveTop_advance_d c (S e).lift (S (ring.rightNeighbor e)).lift
    (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
    (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta cc v T hxl hyl hbY hw hoff hs
  have hp : (phiD ring S e (ring.rightNeighbor e)).top.d =
      (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift
        (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
        (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta).y.d := by
    simp [phiD, projectedEdge, hne, pairD, topD]
  rw [hp]
  exact h

/-- **Launch write.**  A delimiter source holding a settled input stores the input plus one.

Consumer: the writer value step of a completion (first use of the ledger). -/
theorem writerLaunchWrite (v : Fin c.topA) (T : Bool)
    (hxl : (S e).word.native.l = false) (hyl : (S (ring.rightNeighbor e)).word.native.l = false)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = true)
    (hbase : (S e).top.wBase ≠ .ZERO) (hw : (S e).top.wCarry = .OFF)
    (hs : (S e).top.wIn = .S v T) :
    (phiD ring S e e).top.d =
      (if (S e).top.topDirty = true then (S e).top.d else c.digitMod (v.val + 1)) := by
  have h := liveTop_launch_d c (S e).lift (S (ring.rightNeighbor e)).lift
    (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
    (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta v T hxl hyl hbX hbase hw hs
  have hp : (phiD ring S e e).top.d =
      (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift
        (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
        (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta).x.d := by
    simp [phiD, projectedEdge, pairD, topD]
  rw [hp]
  exact h

/-- **Base write.**  A source with base label `ZERO` stores the digit zero.

Consumer: the base value cut (first segment of `DigitValuesCorrect`). -/
theorem writerBaseWrite
    (hxl : (S e).word.native.l = false) (hyl : (S (ring.rightNeighbor e)).word.native.l = false)
    (hb : (S e).top.wBase = .ZERO) :
    (phiD ring S e e).top.d =
      (if (S e).top.topDirty = true then (S e).top.d else c.zeroDigit) := by
  have h := liveTop_base_d c (S e).lift (S (ring.rightNeighbor e)).lift
    (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
    (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta hxl hyl hb
  have hp : (phiD ring S e e).top.d =
      (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift
        (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
        (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta).x.d := by
    simp [phiD, projectedEdge, pairD, topD]
  rw [hp]
  exact h

end Write

end L3

#print axioms L3.writerAdvanceWrite
#print axioms L3.writerLaunchWrite
#print axioms L3.writerBaseWrite
