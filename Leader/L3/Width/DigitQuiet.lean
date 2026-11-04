import Leader.L3.Target

/-!
# The quiet class of the digit machine

`WidthDigitQuiet ring root first S`: the closed invariant of the top machine (`liveTopPair`,
CertRows.lean 605-758) under which no letter changes a digit and no letter reports `topReject`
except by clearing an OLD dirty bit.  `AcceptedReceipts.QDigit` is this class with every dirty bit
false (WidthDigitQuietSafe); the class itself tolerates dirty bits, which is what lets the dirty
drain of `widthWriterDirtyRank` (WidthDigitWriterCore) run on it.

Paper proof and data: research/lean-l3/ledgers/R10c-qdigit-notes.md; the invariant is the
predicate `quiet` of research/lean-l3/wip/r10c-qdigit/quiet.py, checked inductive on the literal
transcription of `liveTopPair` (every letter from random states of the class) and sound along runs
(13 layouts, R = 3 and 7, topA = 2, 3, 4).

Geometry (layout of the clean word, `widthCleanBoundaryDelimiters`): root at position `0`,
delimiters at `first + j R` (`R = digitSpan c`), the complete blocks `[first + jR, first + (j+1)R)`
with `first + (j+1) R < n`, the final fragment `[last, n)` after the last delimiter.

The pipeline of a pair (source block, next block), one lane: reading the target in-lane from the
far end down to its delimiter and then the source out-lane from its far end down to its delimiter
walks the tokens in flight from the oldest to the youngest.  `nxt` is the source offset of the
next token to be met (the position where it will settle): it starts at `R - 1`; a settled input
at position `k` is the token of offset `k`; a live carry at position `k` (the write of offset `k`
done) resets the count to `R - 1`; an in-flight input at the target or a packet at the source
takes the offset `nxt`; an unread marker `U` at source position `k` is the pending packet of
offset `k`; a tail packet (the delimiter's own, offset `0`) passing source position `k` leaves the
offsets `k - 1, …, 1` still to be emitted behind it.  The one exception is the straggling tail
packet: the topmost token of a target whose cells are all empty travels to the far end and is
dropped there without settling.
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled} {n : Nat}

/-- The carry into source offset `h`: every source digit below `h` is the top digit.  Consumer:
`ScanTarget` (the carry bit of a live carry at target position `h - 1`). -/
def carryInto (Dp : Nat → Fin c.topA) : Nat → Bool
  | 0 => true
  | h + 1 => carryInto Dp h && decide ((Dp h).val + 1 = c.topA)

/-- The source out-lane scan over the positions `k - 1, …, 0` with the expected offset `nxt`.
Consumer: `PairQuiet`. -/
def ScanSource (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA) : Nat → Nat → Prop
  | 0, _ => True
  | k + 1, nxt =>
      match (v k).out with
      | .E => (if k = 0 then nxt = 0 else nxt < k) ∧ ScanSource v Dp k nxt
      | .U => nxt = k ∧ ScanSource v Dp k (k - 1)
      | .D val tail =>
          nxt ≤ k ∧ val = Dp nxt ∧ tail = decide (nxt = 0) ∧
            ScanSource v Dp k (if nxt = 0 then k - 1 else nxt - 1)

/-- The target in-lane scan over the positions `k - 1, …, 0` with the expected offset `nxt`,
`sawP` (an in-flight input was met: no live carry and no settled input may follow, since the launch
turns a settled tail into a live carry) and `seen` (any token was met: no
straggling tail packet may follow); at position `0` it continues into `src nxt`.  Consumer:
`PairQuiet`. -/
def ScanTarget (R : Nat) (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (src : Nat → Prop) : Nat → Nat → Bool → Bool → Prop
  | 0, nxt, _, _ => src nxt
  | k + 1, nxt, sawP, seen =>
      if (v k).carryLive = true then
        nxt = k ∧ sawP = false ∧ (v k).input = .E ∧
          (v k).carryBit = carryInto Dp (k + 1) ∧ (v k).carryError = false ∧
          ScanTarget R v Dp src k (R - 1) sawP true
      else
        match (v k).input with
        | .E => ScanTarget R v Dp src k nxt sawP seen
        | .X => False
        | .S val tail =>
            sawP = false ∧ nxt = k ∧ val = Dp k ∧ tail = decide (k = 0) ∧
              ScanTarget R v Dp src k (if k = 0 then R - 1 else k - 1) sawP true
        | .P val tail =>
            (tail = true ∧ nxt ≠ 0 ∧ seen = false ∧ val = Dp 0 ∧
              ScanTarget R v Dp src k nxt true true) ∨
            (k ≤ nxt ∧ val = Dp nxt ∧ tail = decide (nxt = 0) ∧
              ScanTarget R v Dp src k (if nxt = 0 then R - 1 else nxt - 1) true true)

/-- The lane view at position `k` from the root.  Consumer: the clauses of `WidthDigitQuiet`. -/
def view (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c) (lane : DigitLane)
    (k : Nat) : DigitLaneView c :=
  digitEndpointView lane S (digitSite ring root k)

/-- The pipeline of the pair (`source`, `target`) in one lane: the target in-lane and the source
out-lane hold a factor of the periodic token stream aligned with the source digits.  Consumer:
`WidthDigitQuiet.pairs`. -/
def PairQuiet (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c) (lane : DigitLane)
    (source target : Nat) : Prop :=
  ScanTarget (digitSpan c) (fun h => view ring root S lane (target + h))
    (fun h => (S (digitSite ring root (source + h))).top.d)
    (ScanSource (fun h => view ring root S lane (source + h))
      (fun h => (S (digitSite ring root (source + h))).top.d) (digitSpan c))
    (digitSpan c) (digitSpan c - 1) false false

/-- The last delimiter of the layout.  Consumer: `WidthDigitQuiet.fragment`. -/
def lastDelimiter (first R n : Nat) : Nat :=
  first + R * ((n - 1 - first) / R)

/-- The quiet class at the layout with first delimiter `first`.  Consumer:
`L3.DigitQuiet.QuietStepLaw`, `WidthDigitQuietSafe`. -/
structure WidthDigitQuiet (ring : DirectedRing n) (root : Fin n) (first : Nat)
    (S : Fin n → ProjD c) : Prop where
  /-- The root is the unique leader. -/
  rootFixed : ∀ i : Fin n, (S i).word.native.l = true ↔ i = root
  /-- The delimiters are at `first + j R`, `first ≥ 2` (`widthCleanBoundaryDelimiters`). -/
  layout : 2 ≤ first ∧ first < n ∧
    ∀ k : Nat, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔
        first ≤ k ∧ (k - first) % digitSpan c = 0)
  /-- The digit values: first block zero, successive blocks successors. -/
  values : DigitValuesCorrect ring root (digitValueView S)
  /-- Base labels: `SEEK` only before the first delimiter, `ZERO` only in the first segment. -/
  base : ∀ k : Nat, 0 < k → k < n →
    ((S (digitSite ring root k)).top.wBase = .SEEK → k < first) ∧
    ((S (digitSite ring root k)).top.wBase = .ZERO → first ≤ k ∧ k < first + digitSpan c)
  /-- The leading segment carries nothing but settled non-tail inputs. -/
  leading : ∀ (lane : DigitLane) (k : Nat), 0 < k → k < first →
    (view ring root S lane k).out = .E ∧ DigitLeadingInput (view ring root S lane k).input ∧
    (view ring root S lane k).carryLive = false
  /-- The first segment: no live carry, an empty input at its delimiter and settled non-tail inputs
  elsewhere; except an inert live carry at the last site, whose input is free (`DigitLeadingBoundary`
  allows it, at a truncated layout with `first = n - 1` too). -/
  firstSegment : ∀ (lane : DigitLane) (k : Nat), first ≤ k → k < first + digitSpan c → k < n →
    (k + 1 = n ∧ (view ring root S lane k).carryLive = true) ∨
      ((view ring root S lane k).carryLive = false ∧
        (if k = first then (view ring root S lane k).input = .E
         else DigitLeadingInput (view ring root S lane k).input))
  /-- Every pair of complete blocks is a quiet pipeline in both lanes. -/
  pairs : ∀ (lane : DigitLane) (j : Nat), first + (j + 2) * digitSpan c < n →
    PairQuiet ring root S lane (first + j * digitSpan c) (first + (j + 1) * digitSpan c)
  /-- The final fragment settles nothing (its inputs are erased at the root edge), except an inert
  input under a live carry at the last site, which `DigitFinalBoundary` allows at a reached cut. -/
  fragment : first + digitSpan c < n →
    ∀ (lane : DigitLane) (k : Nat), lastDelimiter first (digitSpan c) n ≤ k → k < n →
      ∀ (val : Fin c.topA) (tail : Bool), (view ring root S lane k).input ≠ .S val tail ∨
        (k + 1 = n ∧ (view ring root S lane k).carryLive = true)

/-- No dirty bit.  Consumer: `WidthDigitQuietSafe` (`QDigit` is the quiet class without dirty
bits). -/
def NoDirty (S : Fin n → ProjD c) : Prop :=
  ∀ i : Fin n, (S i).top.topDirty = false

/-- The one-letter law of the quiet class: it is closed under every projected letter at a fixed
visible word, every digit is kept, and a report is the clearing of an OLD dirty endpoint.
`WFixedRoot` is what keeps the leader flag: `QWord` fixes only the visible `(u, beta)`, and every
consumer holds `CleanWordAtRoot`, which contains both.
Consumer: `L3.DigitQuiet.qdigitOfQuiet` (WidthDigitQuietSafe); producer: the step modules
`WidthDigitQuietStep*` (open). -/
def QuietStepLaw (ring : DirectedRing n) (root : Fin n) (first : Nat) : Prop :=
  ∀ (S : Fin n → ProjD c) (e : Fin n),
    WidthDigitQuiet ring root first S →
    WFixedRoot ring root (wordProjection S) →
    QWord ring (wordProjection S) →
    WidthDigitQuiet ring root first (phiD ring S e) ∧
    (∀ i : Fin n, ((phiD ring S e) i).top.d = (S i).top.d) ∧
    ((topD (S e) (S (ring.rightNeighbor e))).topReject = true →
      (S e).top.topDirty = true ∨ (S (ring.rightNeighbor e)).top.topDirty = true)

end L3.DigitQuiet
