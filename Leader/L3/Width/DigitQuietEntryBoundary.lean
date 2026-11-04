import Leader.L3.Width.DigitQuietEntry

/-!
# The entrance into the quiet class: first segment and final fragment

From the delimiter layout and the boundary receipt at the cut:

* `firstSegmentOfReceipt`: every site of the first segment `[first, min (first + R) n)` is the
  inert last site or has no live carry and the input the `firstSegment` clause asks for; the
  receipt's `stop` is `min (first + R) n`;
* `firstSegmentFieldOfLong`: the field `WidthDigitQuiet.firstSegment` itself when `first + R < n`;
* `fragmentOfReceipt`: the field `WidthDigitQuiet.fragment`;
* `quietReceiptOfCut`: the boundary receipt at the fixed root of a writer comparison cut.

A truncated first segment (`n ≤ first + R`, only `n ≤ 7` in the band) can hold the inert live
carry of `DigitLastCarryInert` at site `n - 1` with an arbitrary input, which the literal field
`firstSegment` forbids: research/lean-l3/ledgers/R10c-qdigit-notes.md section 8.
-/

namespace L3.DigitQuiet

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WriterValueCuts
open L3.AcceptedReceipts
open L3.WriterCertificate

set_option autoImplicit false

section Layout

variable {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c)
  (first : Nat)

/-- The delimiter layout at the first delimiter `first`.  Consumer: the entrance lemmas of this
module and of `WidthDigitQuietEntryBase`. -/
def QuietLayout : Prop :=
  ∀ k : Nat, 0 < k → k < n →
    ((S (digitSite ring root k)).word.beta = true ↔
      first ≤ k ∧ (k - first) % digitSpan c = 0)

variable {ring root S first}

/-- A delimiter of the layout.  Consumer: `layoutNonroot`. -/
theorem layoutBetaAt (hb : QuietLayout ring root S first) (h0 : 0 < first) (q : Nat)
    (hlt : first + digitSpan c * q < n) :
    (S (digitSite ring root (first + digitSpan c * q))).word.beta = true :=
  (hb _ (by omega) hlt).2 ⟨by omega, by rw [Nat.add_sub_cancel_left, Nat.mul_mod_right]⟩

/-- Strictly between two consecutive delimiters there is none.  Consumer: `layoutNext`,
`fragmentOfReceipt`, `layoutStop`. -/
theorem layoutBetaBetween (hb : QuietLayout ring root S first) (q k : Nat)
    (h1 : first + digitSpan c * q < k) (h2 : k < first + digitSpan c * q + digitSpan c)
    (hk : k < n) : (S (digitSite ring root k)).word.beta = false := by
  cases hbt : (S (digitSite ring root k)).word.beta with
  | false => rfl
  | true =>
      exfalso
      have hmod := ((hb k (by omega) hk).1 hbt).2
      have heq : k - first = digitSpan c * q + (k - (first + digitSpan c * q)) := by omega
      rw [heq, Nat.mul_add_mod,
        Nat.mod_eq_of_lt (show k - (first + digitSpan c * q) < digitSpan c by omega)] at hmod
      omega

/-- A non-root delimiter of the layout.  Consumer: `layoutNext`, `fragmentOfReceipt`. -/
theorem layoutNonroot (hb : QuietLayout ring root S first) (h0 : 0 < first) (q : Nat)
    (hlt : first + digitSpan c * q < n) :
    DigitNonrootDelimiter ring root S (first + digitSpan c * q) :=
  ⟨by omega, hlt, layoutBetaAt hb h0 q hlt⟩

/-- Every block of the layout ending before the root is complete.  Consumer:
`fragmentOfReceipt`. -/
theorem layoutCompleteBlock (hb : QuietLayout ring root S first) (h0 : 0 < first)
    (hR : 0 < digitSpan c) (q : Nat) (hlt : first + digitSpan c * q + digitSpan c < n) :
    DigitCompleteBlock ring root S (first + digitSpan c * q) := by
  refine ⟨⟨layoutNonroot hb h0 q (by omega), by omega, by omega, fun _ => ?_, fun k h1 h2 => ?_⟩,
    hlt⟩
  · have := layoutBetaAt hb h0 (q + 1) (by rw [Nat.mul_succ]; omega)
    rw [Nat.mul_succ] at this
    rw [← Nat.add_assoc] at this
    exact this
  · exact layoutBetaBetween hb q k h1 h2 (by omega)

/-- The first delimiter of the receipt is the first delimiter of the layout.  Consumer:
`firstSegmentOfReceipt`, `L3.DigitQuiet.quietBaseOfCut`. -/
theorem layoutFirstEq (hb : QuietLayout ring root S first) (h0 : 0 < first) (hfn : first < n)
    (f : Nat) (hf : DigitFirstDelimiter ring root S f) : f = first := by
  obtain ⟨⟨hf0, hfn', hfb⟩, hmin⟩ := hf
  have h1 := ((hb f hf0 hfn').1 hfb).1
  rcases Nat.lt_or_ge first f with h | h
  · have hfalse := hmin first h0 h
    have htrue := (hb first h0 hfn).2 ⟨Nat.le_refl _, by rw [Nat.sub_self, Nat.zero_mod]⟩
    rw [hfalse] at htrue
    cases htrue
  · omega

/-- The stop of the first segment of the receipt is `min (first + R) n`.  Consumer:
`firstSegmentOfReceipt`. -/
theorem layoutStop (hb : QuietLayout ring root S first) (stop : Nat)
    (h : DigitNextDelimiterOrRoot ring root S first stop) (k : Nat)
    (hk1 : k < first + digitSpan c) (hk2 : k < n) : k < stop := by
  obtain ⟨-, hlt, -, hbeta, -⟩ := h
  rcases Nat.lt_or_ge k stop with h' | h'
  · exact h'
  · exfalso
    have hs := hbeta (by omega)
    have := layoutBetaBetween hb 0 stop (by rw [Nat.mul_zero]; omega)
      (by rw [Nat.mul_zero]; omega) (by omega)
    rw [hs] at this
    cases this

/-- **The first segment from the boundary receipt.**  On `[first, min (first + R) n)` a site is
the inert last site (`DigitLastCarryInert`) or has no live carry, an empty input at the delimiter
and a settled non-tail or empty input elsewhere.  Consumer: `firstSegmentFieldOfLong` and the
entrance `WidthWriterQuietAtCut`. -/
theorem firstSegmentOfReceipt (hlead : DigitLeadingBoundary ring root S)
    (hb : QuietLayout ring root S first) (h0 : 0 < first) (hfn : first < n)
    (lane : DigitLane) (k : Nat) (h1 : first ≤ k) (h2 : k < first + digitSpan c) (h3 : k < n) :
    (k + 1 = n ∧ (view ring root S lane k).carryLive = true) ∨
      ((view ring root S lane k).carryLive = false ∧
        (if k = first then (view ring root S lane k).input = .E
         else DigitLeadingInput (view ring root S lane k).input)) := by
  obtain ⟨first', stop, ⟨hd, hnext⟩, -, hseg⟩ := hlead
  have hf := layoutFirstEq hb h0 hfn first' hd
  subst hf
  rcases hseg lane k h1 (layoutStop hb stop hnext k h2 h3) with ⟨h, hc⟩ | ⟨hc, hi⟩
  · exact Or.inl ⟨h, hc⟩
  · exact Or.inr ⟨hc, hi⟩

/-- **The field `firstSegment` when the first segment is not truncated**: `first + R < n` rules out
the inert last site.  Consumer: the entrance `WidthWriterQuietAtCut`. -/
theorem firstSegmentFieldOfLong (hlead : DigitLeadingBoundary ring root S)
    (hb : QuietLayout ring root S first) (h0 : 0 < first) (hfn : first < n)
    (hlong : first + digitSpan c < n)
    (lane : DigitLane) (k : Nat) (h1 : first ≤ k) (h2 : k < first + digitSpan c) (h3 : k < n) :
    (if k = first then (view ring root S lane k).input = .E
      else DigitLeadingInput (view ring root S lane k).input) ∧
    (k + 1 < n → (view ring root S lane k).carryLive = false) := by
  rcases firstSegmentOfReceipt hlead hb h0 hfn lane k h1 h2 h3 with ⟨h, -⟩ | ⟨hc, hi⟩
  · omega
  · exact ⟨hi, fun _ => hc⟩

/-- **The field `fragment` from the final boundary receipt.**  Every delimiter of the layout gives
the last complete block and the final fragment `[last, n)` of `DigitFinalBoundary`, whose inputs
are empty or in flight, except at the inert last site.  Consumer: the entrance
`WidthWriterQuietAtCut`. -/
theorem fragmentOfReceipt (hfinal : DigitFinalBoundary ring root S)
    (hb : QuietLayout ring root S first) (h0 : 0 < first) (hR : 0 < digitSpan c)
    (hlong : first + digitSpan c < n)
    (lane : DigitLane) (k : Nat) (h1 : lastDelimiter first (digitSpan c) n ≤ k) (h3 : k < n)
    (val : Fin c.topA) (tail : Bool) :
    (view ring root S lane k).input ≠ .S val tail ∨
      (k + 1 = n ∧ (view ring root S lane k).carryLive = true) := by
  unfold lastDelimiter at h1
  have hqpos : 0 < (n - 1 - first) / digitSpan c :=
    Nat.div_pos (by omega) hR
  obtain ⟨q, hq⟩ : ∃ q, (n - 1 - first) / digitSpan c = q + 1 :=
    ⟨(n - 1 - first) / digitSpan c - 1, by omega⟩
  have hdm := Nat.div_add_mod (n - 1 - first) (digitSpan c)
  have hml := Nat.mod_lt (n - 1 - first) hR
  rw [hq] at h1 hdm
  rw [Nat.mul_succ] at h1 hdm
  have hblock := layoutCompleteBlock hb h0 hR q (by omega)
  have hnext : DigitNextDelimiterOrRoot ring root S (first + digitSpan c * q + digitSpan c) n := by
    refine ⟨?_, by omega, Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _), fun j hj1 hj2 => ?_⟩
    · have := layoutNonroot hb h0 (q + 1) (by rw [Nat.mul_succ]; omega)
      rw [Nat.mul_succ, ← Nat.add_assoc] at this
      exact this
    · have := layoutBetaBetween hb (q + 1) j (by rw [Nat.mul_succ]; omega)
        (by rw [Nat.mul_succ]; omega) hj2
      exact this
  rcases hfinal _ _ hblock rfl hnext lane k (by omega) h3 with ⟨h, hc⟩ | ⟨-, hi⟩
  · exact Or.inr ⟨h, hc⟩
  · refine Or.inl fun hs => ?_
    have hs' : (digitEndpointView lane S (digitSite ring root k)).input = .S val tail := hs
    rcases hi with h | ⟨v, t, h⟩ <;> rw [hs'] at h <;> cases h

end Layout

/-- **Two blocks fit in every ring with `n ≥ 8`**: `t + 2 R ≤ n`.  So a first segment is truncated
(`n ≤ first + R`, with `first < t + R`) only at `n ≤ 7`.  Consumer: `firstSegmentFieldOfBig`. -/
theorem widthTwoBlocks {n : Nat} (hn : 8 ≤ n) :
    (compileAdvice (ceilLogTwo n)).t + 2 * digitSpan (compileAdvice (ceilLogTwo n)) ≤ n := by
  have hn5 : 5 ≤ n := by omega
  cases hh : (compileAdvice (ceilLogTwo n)).useSmall with
  | true =>
    obtain ⟨hlo, hhi⟩ := L3.SmallFinishClean.smallDigitSliceBounds hn5 hh
    have hpop := (ceilLogTwo_spec n (by omega : 2 ≤ n)).1
    unfold digitSpan
    generalize ceilLogTwo n = q at hlo hhi hpop ⊢
    by_cases h32 : q ≤ 32
    · rw [compileAdvice_t_finite q hlo h32]
      unfold finiteCertWidth
      by_cases h4 : q ≤ 4
      · rw [if_pos h4]
        have e2 : (2 : Nat) ^ 2 = 4 := by decide
        omega
      · rw [if_neg h4]
        have h5 : 2 ^ 4 ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have e4 : (2 : Nat) ^ 4 = 16 := by decide
        by_cases h16 : q ≤ 16
        · rw [if_pos h16]
          have e3 : (2 : Nat) ^ 3 = 8 := by decide
          omega
        · rw [if_neg h16]
          have h17' : 2 ^ 16 ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
          have e5 : (2 : Nat) ^ 5 = 32 := by decide
          have e16 : (2 : Nat) ^ 16 = 65536 := by decide
          omega
    · rw [compileAdvice_t_large q (by omega)]
      have hc := ceilLogTwo_spec q (by omega)
      have e7 : (2 : Nat) ^ 7 = 128 := by decide
      have hc7 : ceilLogTwo q ≤ 7 := by
        by_cases h : ceilLogTwo q ≤ 7
        · exact h
        · have : 2 ^ 7 ≤ 2 ^ (ceilLogTwo q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
      have hp : 2 ^ ceilLogTwo q ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) hc7
      have h32' : 2 ^ 32 ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have e32 : (2 : Nat) ^ 32 = 4294967296 := by decide
      omega
  | false =>
    have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hh
    have ht : (compileAdvice (ceilLogTwo n)).t = ceilLogTwo (ceilLogTwo n) :=
      compileAdvice_t_large _ (by omega)
    have hs : 7 ≤ ceilLogTwo (ceilLogTwo n) := bankRepairDigitWidthBank hh
    have hpop := bankRepairDigitPopulationLower hn5 hh
    unfold digitSpan
    rw [ht]
    unfold bankRepairDigitExponent at hpop
    generalize ceilLogTwo (ceilLogTwo n) = s at hs hpop ⊢
    have h2s : 2 ^ s = 2 * 2 ^ (s - 1) := by
      have := Nat.pow_add 2 (s - 1) 1
      rw [show s - 1 + 1 = s by omega, Nat.pow_one] at this
      omega
    have hE := bankRepairDigitPowLower (s - 1)
    generalize 2 ^ (s - 1) = E at h2s hpop hE
    have hE3 := bankRepairDigitPowLower (E - 3)
    have h8 : 2 ^ E = 2 ^ (E - 3) * 8 := by
      have := Nat.pow_add 2 (E - 3) 3
      rw [show E - 3 + 3 = E by omega] at this
      rw [this]
    omega

/-- **The field `firstSegment` at the cut for `n ≥ 8`**: the first delimiter of the clean word is
below `t + R`, so `first + R < n` by `widthTwoBlocks`.  Consumer: the entrance
`WidthWriterQuietAtCut`. -/
theorem firstSegmentFieldOfBig {n : Nat} {ring : DirectedRing n} {root : Fin n}
    {S : Fin n → ProjD (compileAdvice (ceilLogTwo n))} {first : Nat} (hn : 8 ≤ n)
    (hlead : DigitLeadingBoundary ring root S)
    (hb : QuietLayout ring root S first) (h0 : 0 < first) (hfn : first < n)
    (hft : first < (compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)))
    (lane : DigitLane) (k : Nat) (h1 : first ≤ k)
    (h2 : k < first + digitSpan (compileAdvice (ceilLogTwo n))) (h3 : k < n) :
    (if k = first then (view ring root S lane k).input = .E
      else DigitLeadingInput (view ring root S lane k).input) ∧
    (k + 1 < n → (view ring root S lane k).carryLive = false) :=
  firstSegmentFieldOfLong hlead hb h0 hfn (by have := widthTwoBlocks hn; omega) lane k h1 h2 h3

section Cut

variable {n : Nat} {ring : DirectedRing n}

/-- The boundary receipt at the fixed root of a writer comparison cut.  Consumer: the entrance
`WidthWriterQuietAtCut`, `L3.DigitQuiet.quietPartsOfCut`. -/
theorem quietReceiptOfCut (ref : WidthDigitReference ring) (z : ref.State)
    (hcut : WidthWriterComparisonCut ref z) (root : Fin n)
    (hfixed : WFixedRoot ring root (piW (ref.phys z))) :
    DigitBoundaryReceipt ring root (piD (ref.phys z)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, root'', hfixed'', hrec⟩ := hcut
  have hr : root'' = root := hfixed.2.1 root'' hfixed''.1
  subst hr
  exact hrec

end Cut

end L3.DigitQuiet

#print axioms L3.DigitQuiet.firstSegmentOfReceipt
#print axioms L3.DigitQuiet.firstSegmentFieldOfLong
#print axioms L3.DigitQuiet.fragmentOfReceipt
#print axioms L3.DigitQuiet.widthTwoBlocks
#print axioms L3.DigitQuiet.firstSegmentFieldOfBig
#print axioms L3.DigitQuiet.quietReceiptOfCut
