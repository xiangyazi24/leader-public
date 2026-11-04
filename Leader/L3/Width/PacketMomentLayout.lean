import Leader.L3.Width.PacketMomentPhases
import Leader.L3.Width.DigitBoundary
import Leader.L3.Width.DigitFirstZero

/-!
# Lemma e-packet at a boundary reference: every interior pair is in the layout class

`L3.RenewalReferenceClock.bankCleanBoundaryCohortLayout` (BankRepairDigitBoundaryClean) puts every
interior pair `(first + iR, first + (i+1)R)` (`R = digitSpan`) of a continuation of a clean BANK
entrance into `CohortLayout`, the class on which the e-packet chain runs. Its BANK facts are the
clean root, the layout-values class along words and the delimiters; all three have generic forms
at a `WidthBoundaryReference` (`widthCleanBoundaryRoot`, `widthBoundaryDigitLayoutValuesWord`,
`widthCleanBoundaryDelimiters`). Here:

* `widthCleanBoundaryCohortLayout`: the generic statement, from a clean start `ref.start z`;
* `widthAuditFoldFst`: the coupled chain moves its reference component by `ref.next`;
* `widthCleanBoundaryCohortLayoutCoupled`: the same along every word of the coupled chain;
* `smallCleanBoundaryCohortLayoutCoupled`: the SMALL instance at
  `smallWidthBoundaryReference ring hn hs`;
* `bankCleanBoundaryCohortLayoutCheck`: the BANK instance against the BANK statement.
-/

namespace L3.WidthPacketMoment

set_option autoImplicit false

open L3
open L3.WidthDigit
open L3.CohortSites
open L3.RenewalReferenceClock

/-- **Every interior pair is in the layout class** along every continuation of a clean start of
a boundary reference (generic `bankCleanBoundaryCohortLayout`): with the fixed root and the first
delimiter `first`, the pair `(first + iR, first + (i+1)R)` has its delimiters at `src`, `src + R`,
`src + 2R` and none in between. Consumer: `widthCleanBoundaryCohortLayoutCoupled`. -/
theorem widthCleanBoundaryCohortLayout {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (z : ref.State) (hz : ref.start z)
    (word : List (Fin n)) :
    ∃ (root : Fin n) (first : Nat), (compileAdvice (ceilLogTwo n)).t ≤ first ∧
      ∀ i, 2 ≤ first + i * digitSpan (compileAdvice (ceilLogTwo n)) →
        first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
          2 * digitSpan (compileAdvice (ceilLogTwo n)) < n →
        WidthCohortLayout ref.toWidthDigitReference root
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (digitSpan (compileAdvice (ceilLogTwo n)))
          (word.foldl ref.next z) := by
  obtain ⟨root, -, hL⟩ := widthCleanBoundaryRoot ref z hz
  have hL' := widthBoundaryDigitLayoutValuesWord ref root word z hL
  obtain ⟨first, ht, -, hb⟩ := widthCleanBoundaryDelimiters ref hn root _ hL'
  refine ⟨root, first, ht, fun i h2 hend => ?_⟩
  generalize digitSpan (compileAdvice (ceilLogTwo n)) = R at h2 hend hb ⊢
  generalize hm : i * R = m at h2 hend
  have hmR : m % R = 0 := by rw [← hm]; exact Nat.mul_mod_left i R
  have hm1 : (m + R) % R = 0 := by
    rw [← hm, show i * R + R = (i + 1) * R by rw [Nat.succ_mul]]
    exact Nat.mul_mod_left _ R
  have hm2 : (m + 2 * R) % R = 0 := by
    rw [← hm, show i * R + 2 * R = (i + 2) * R by rw [Nat.add_mul]]
    exact Nat.mul_mod_left _ R
  refine ⟨hL'.1, ?_, ?_, ?_, fun k hk0 hk2 hkR => ?_⟩
  · exact (hb _ (by omega) (by omega)).2
      ⟨by omega, by rw [show first + m - first = m by omega]; exact hmR⟩
  · exact (hb _ (by omega) (by omega)).2
      ⟨by omega, by rw [show first + m + R - first = m + R by omega]; exact hm1⟩
  · exact (hb _ (by omega) (by omega)).2
      ⟨by omega, by rw [show first + m + 2 * R - first = m + 2 * R by omega]; exact hm2⟩
  · cases hbeta : (piD (ref.phys (word.foldl ref.next z))
        (digitSite ring root (first + m + k))).word.beta with
    | false => rfl
    | true =>
      exfalso
      have h := ((hb _ (by omega) (by omega)).1 hbeta).2
      rw [show first + m + k - first = m + k by omega, ← hm, Nat.mul_add_mod' i R k] at h
      by_cases hk : k < R
      · rw [Nat.mod_eq_of_lt hk] at h
        omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
        omega

/-- The coupled chain moves its reference component by the reference successor. Consumer:
`widthCleanBoundaryCohortLayoutCoupled`. -/
theorem widthAuditFoldFst {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (word : List (Fin n)) :
    ∀ x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      (word.foldl (widthDigitAuditNext ref) x).1 = word.foldl ref.next x.1 := by
  induction word with
  | nil => intro x; rfl
  | cons e rest ih => intro x; exact ih _

/-- **The layout class on the coupled chain**: from a coupled state whose reference component is
a clean start, every interior pair is in the layout class along every coupled word. Consumer: the
per-pair moment at the band reference (the start class of `widthRaceAlignPend`,
`widthPrepMoment`), `smallCleanBoundaryCohortLayoutCoupled`. -/
theorem widthCleanBoundaryCohortLayoutCoupled {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (hx : ref.start x.1)
    (word : List (Fin n)) :
    ∃ (root : Fin n) (first : Nat), (compileAdvice (ceilLogTwo n)).t ≤ first ∧
      ∀ i, 2 ≤ first + i * digitSpan (compileAdvice (ceilLogTwo n)) →
        first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
          2 * digitSpan (compileAdvice (ceilLogTwo n)) < n →
        WidthCohortLayout ref.toWidthDigitReference root
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (digitSpan (compileAdvice (ceilLogTwo n)))
          (word.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).1 := by
  rw [widthAuditFoldFst]
  exact widthCleanBoundaryCohortLayout ref hn x.1 hx word

/-- **The SMALL pair layout**: at the SMALL boundary reference every interior pair is in the
layout class along every coupled word from a clean start. Consumer: the SMALL per-pair moment
(`hcmpMomentSmall` / `hwriterSmall` of the headline) through WidthPacketMomentPhases. -/
theorem smallCleanBoundaryCohortLayoutCoupled {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hs : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (x : (smallWidthBoundaryReference ring hn hs).State ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : (smallWidthBoundaryReference ring hn hs).start x.1) (word : List (Fin n)) :
    ∃ (root : Fin n) (first : Nat), (compileAdvice (ceilLogTwo n)).t ≤ first ∧
      ∀ i, 2 ≤ first + i * digitSpan (compileAdvice (ceilLogTwo n)) →
        first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
          2 * digitSpan (compileAdvice (ceilLogTwo n)) < n →
        WidthCohortLayout (smallWidthBoundaryReference ring hn hs).toWidthDigitReference root
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (digitSpan (compileAdvice (ceilLogTwo n)))
          (word.foldl (widthDigitAuditNext
            (smallWidthBoundaryReference ring hn hs).toWidthDigitReference) x).1 :=
  widthCleanBoundaryCohortLayoutCoupled (smallWidthBoundaryReference ring hn hs) hn x hx word

/-- **Port check**: at the BANK boundary reference the generic statement is
`bankCleanBoundaryCohortLayout` (the BANK clean start is the drained class with the clean fold).
Consumer: none in the chain; it checks the port. -/
theorem bankCleanBoundaryCohortLayoutCheck {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z) (hC : BankCleanRFold ring hbank z)
    (word : List (Fin n)) :
    ∃ (root : Fin n) (first : Nat), (compileAdvice (ceilLogTwo n)).t ≤ first ∧
      ∀ i, 2 ≤ first + i * digitSpan (compileAdvice (ceilLogTwo n)) →
        first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
          2 * digitSpan (compileAdvice (ceilLogTwo n)) < n →
        L3.CohortSites.CohortLayout ring hbank root
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (digitSpan (compileAdvice (ceilLogTwo n)))
          (word.foldl (bankRepairNext ring hbank) z) :=
  widthCleanBoundaryCohortLayout (bankWidthBoundaryReference ring hn hbank) hn z ⟨hD, hC⟩ word

end L3.WidthPacketMoment

#print axioms L3.WidthPacketMoment.widthCleanBoundaryCohortLayout
#print axioms L3.WidthPacketMoment.widthAuditFoldFst
#print axioms L3.WidthPacketMoment.widthCleanBoundaryCohortLayoutCoupled
#print axioms L3.WidthPacketMoment.smallCleanBoundaryCohortLayoutCoupled
#print axioms L3.WidthPacketMoment.bankCleanBoundaryCohortLayoutCheck
