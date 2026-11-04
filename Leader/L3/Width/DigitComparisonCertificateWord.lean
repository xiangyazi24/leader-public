import Leader.L3.Width.DigitWriterCore

/-!
# R10c: the word part of the comparison-entry certificate

The word conjunct of `WidthWriterComparisonCertificate` is carried by the cut itself: the clean
start of a boundary reference carries `CleanWord`, every drained step keeps the clean-word class at
its root (`cleanWordRootPhiStep`), and the fixed root of the cut is that root (a fixed root is the
unique native leader).

* `widthCutWordRun`: the clean-word class at a root persists along a drained word;
* `cleanWordOfWriterComparisonCut`: at a writer comparison cut the word is clean at the root of the
  cut;
* `WidthWriterQuietAtCut`, `writerCertificateOfQuiet`: the certificate reduces to the quiet class at
  the cut, at the fixed root of the cut.

Consumer: the producer of the certificate premise of `l3HeadlineOfCleanBranches`.
-/

namespace L3.WriterCertificate

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WriterValueCuts

set_option autoImplicit false

variable {n : Nat} {ring : DirectedRing n}

/-- The state component of an audited word is the reference run.  Consumer:
`cleanWordOfWriterComparisonCut`. -/
theorem widthAuditFoldFst (ref : WidthDigitReference ring) (word : List (Fin n))
    (s : ref.State) (a : DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    (word.foldl (widthDigitAuditNext ref) (s, a)).1 = word.foldl ref.next s := by
  induction word generalizing s a with
  | nil => rfl
  | cons e rest ih => exact ih (ref.next s e) _

/-- The clean-word class at a root persists along a drained word.  Consumer:
`cleanWordOfWriterComparisonCut`. -/
theorem widthCutWordRun (ref : WidthDigitReference ring) (hn : 5 ≤ n) (root : Fin n)
    (word : List (Fin n)) :
    ∀ z : ref.State, ref.drained z → CleanWordAtRoot ring root (piW (ref.phys z)) →
      CleanWordAtRoot ring root (piW (ref.phys (word.foldl ref.next z))) := by
  induction word with
  | nil => intro z _ h; exact h
  | cons e rest ih =>
      intro z hD hW
      have hW' : CleanWordAtRoot ring root (piW (ref.phys (ref.next z e))) := by
        rw [ref.wordStep z hD e]
        exact cleanWordRootPhiStep (by omega : 3 ≤ n) ring root (piW (ref.phys z)) e hW
      exact ih (ref.next z e) (ref.drainedClosed z hD e) hW'

/-- The drain of the start persists along every word.  Consumer:
`cleanWordOfWriterComparisonCut`. -/
theorem widthCutDrainRun (ref : WidthDigitReference ring) (word : List (Fin n)) :
    ∀ z : ref.State, ref.drained z → ref.drained (word.foldl ref.next z) := by
  induction word with
  | nil => intro z h; exact h
  | cons e rest ih => intro z h; exact ih _ (ref.drainedClosed z h e)

/-- **The word part of the certificate**: at a writer comparison cut of a boundary reference the
word is clean at the fixed root of the cut.  Consumer: `writerCertificateOfQuiet`. -/
theorem cleanWordOfWriterComparisonCut (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (z : ref.State) (hcut : WidthWriterComparisonCut ref.toWidthDigitReference z) :
    ∃ root : Fin n, WFixedRoot ring root (piW (ref.phys z)) ∧
      CleanWordAtRoot ring root (piW (ref.phys z)) := by
  obtain ⟨start, word, root, audit, retired, restart, cmp, hstart, hrun, hfixed, _⟩ := hcut
  have hz : z = word.foldl ref.next start := by
    have := widthAuditFoldFst ref.toWidthDigitReference word start
      (digitAuditInitial (piD (ref.phys start)))
    rw [hrun] at this
    exact this
  obtain ⟨root', hroot'⟩ := ref.startClean start hstart
  have hD := ref.startDrained start hstart
  have hW := widthCutWordRun ref.toWidthDigitReference hn root' word start hD hroot'
  have hroot : root = root' := by
    have h1 := hW.1.2.1 root (by
      have := hfixed.1
      rw [hz] at this
      exact this)
    exact h1
  subst hroot
  refine ⟨root, hfixed, ?_⟩
  rw [hz]
  exact hW

/-- The content of the certificate beyond the word: at a drained writer comparison cut, the digit
machine is in the quiet class at the fixed root of the cut, for some first delimiter.  Consumer:
`writerCertificateOfQuiet`. -/
def WidthWriterQuietAtCut (ref : WidthDigitReference ring) : Prop :=
  ∀ start : ref.State, ref.drained start → WidthWriterComparisonCut ref start →
    ∀ root : Fin n, WFixedRoot ring root (piW (ref.phys start)) →
      ∃ first : Nat, L3.DigitQuiet.WidthDigitQuiet ring root first (piD (ref.phys start))

/-- **The certificate from the quiet class at the cut**: the word conjunct is
`cleanWordOfWriterComparisonCut`.  Consumer: the producer of the certificate premise of
`l3HeadlineOfCleanBranches`. -/
theorem writerCertificateOfQuiet (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hq : WidthWriterQuietAtCut ref.toWidthDigitReference) :
    WidthWriterComparisonCertificate ref.toWidthDigitReference := by
  intro start hD hC
  obtain ⟨root, hfixed, hW⟩ := cleanWordOfWriterComparisonCut ref hn start hC
  obtain ⟨first, hQ⟩ := hq start hD hC root hfixed
  exact ⟨root, first, hW, hQ⟩

end L3.WriterCertificate

#print axioms L3.WriterCertificate.widthAuditFoldFst
#print axioms L3.WriterCertificate.widthCutWordRun
#print axioms L3.WriterCertificate.cleanWordOfWriterComparisonCut
#print axioms L3.WriterCertificate.writerCertificateOfQuiet
