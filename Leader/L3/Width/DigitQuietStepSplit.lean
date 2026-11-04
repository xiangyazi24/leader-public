import Leader.L3.Width.DigitQuietStepRow
import Leader.L3.Width.DigitQuietStepReplace

/-!
# The quiet class split into the pair clause and the rest

* `QuietNoPairs`: every field of `WidthDigitQuiet` except `pairs`;
* `quiet_of_parts`, `QuietNoPairs.of_quiet`: the two views of the class;
* `PQ`: the pair predicate in block-relative form (`vs` the source block's views, `vt` the target
  block's, `Dp` the source digits), with `pairQuiet_eq_PQ`.

Consumer: the region closure (`WidthDigitQuietStepRegions`), the pair closure and the assembly of
`QuietStepLaw`.
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled} {n : Nat}

/-- The class without its `pairs` field.  Consumer: `quiet_of_parts`, `WidthDigitQuietStepRegions`. -/
structure QuietNoPairs (ring : DirectedRing n) (root : Fin n) (first : Nat)
    (S : Fin n → ProjD c) : Prop where
  rootFixed : ∀ i : Fin n, (S i).word.native.l = true ↔ i = root
  layout : 2 ≤ first ∧ first < n ∧
    ∀ k : Nat, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔
        first ≤ k ∧ (k - first) % digitSpan c = 0)
  values : DigitValuesCorrect ring root (digitValueView S)
  base : ∀ k : Nat, 0 < k → k < n →
    ((S (digitSite ring root k)).top.wBase = .SEEK → k < first) ∧
    ((S (digitSite ring root k)).top.wBase = .ZERO → first ≤ k ∧ k < first + digitSpan c)
  leading : ∀ (lane : DigitLane) (k : Nat), 0 < k → k < first →
    (view ring root S lane k).out = .E ∧ DigitLeadingInput (view ring root S lane k).input ∧
    (view ring root S lane k).carryLive = false
  firstSegment : ∀ (lane : DigitLane) (k : Nat), first ≤ k → k < first + digitSpan c → k < n →
    (k + 1 = n ∧ (view ring root S lane k).carryLive = true) ∨
      ((view ring root S lane k).carryLive = false ∧
        (if k = first then (view ring root S lane k).input = .E
          else DigitLeadingInput (view ring root S lane k).input))
  fragment : first + digitSpan c < n →
    ∀ (lane : DigitLane) (k : Nat), lastDelimiter first (digitSpan c) n ≤ k → k < n →
      ∀ (val : Fin c.topA) (tail : Bool), (view ring root S lane k).input ≠ .S val tail ∨
        (k + 1 = n ∧ (view ring root S lane k).carryLive = true)

/-- The pairs clause of the class.  Consumer: `quiet_of_parts`. -/
def QuietPairs (ring : DirectedRing n) (root : Fin n) (first : Nat) (S : Fin n → ProjD c) : Prop :=
  ∀ (lane : DigitLane) (j : Nat), first + (j + 2) * digitSpan c < n →
    PairQuiet ring root S lane (first + j * digitSpan c) (first + (j + 1) * digitSpan c)

/-- The class from its two parts.  Consumer: the assembly of `QuietStepLaw`. -/
theorem quiet_of_parts {ring : DirectedRing n} {root : Fin n} {first : Nat} {S : Fin n → ProjD c}
    (h : QuietNoPairs ring root first S) (hp : QuietPairs ring root first S) :
    WidthDigitQuiet ring root first S :=
  { rootFixed := h.rootFixed, layout := h.layout, values := h.values, base := h.base,
    leading := h.leading, firstSegment := h.firstSegment, pairs := hp, fragment := h.fragment }

/-- The parts of the class.  Consumer: the region closure. -/
theorem quiet_parts {ring : DirectedRing n} {root : Fin n} {first : Nat} {S : Fin n → ProjD c}
    (h : WidthDigitQuiet ring root first S) :
    QuietNoPairs ring root first S ∧ QuietPairs ring root first S :=
  ⟨{ rootFixed := h.rootFixed, layout := h.layout, values := h.values, base := h.base,
     leading := h.leading, firstSegment := h.firstSegment, fragment := h.fragment }, h.pairs⟩

/-- The pair predicate in block-relative form: `vs` the views of the source block, `vt` those of the
target block, `Dp` the digits of the source block.  Consumer: the window lemmas of the pair closure. -/
def PQ (R : Nat) (vs vt : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA) : Prop :=
  ScanTarget R vt Dp (ScanSource vs Dp R) R (R - 1) false false

/-- `PairQuiet` is `PQ` of the views of the two blocks.  Consumer: the pair closure. -/
theorem pairQuiet_eq_PQ (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c)
    (lane : DigitLane) (a b : Nat) :
    PairQuiet ring root S lane a b =
      PQ (digitSpan c) (fun h => view ring root S lane (a + h))
        (fun h => view ring root S lane (b + h))
        (fun h => (S (digitSite ring root (a + h))).top.d) := rfl

end L3.DigitQuiet
