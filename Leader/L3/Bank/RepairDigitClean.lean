import Leader.L3.Bank.FinishCleanWord
import Leader.L3.Bank.RepairDigit

/-!
Clean-origin BANK digit producer, conditional on one origin-free
causal clock/row certificate.  Nothing here asserts the R10c
certificate, and no old accepted-word observer is used as a
replacement for a clean observer.

The only timing consumer below assumes t <= 17.
The successor is always the installed masked BANK successor.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Clean R-fold provides the two old T7 word facts directly,
without constructing an AcceptedWord history.  Consumer:
bankCleanDigitLayoutValuesOfSingleton and a future clean
single-label task producer. -/
theorem bankCleanDigitRFoldCarriesWordFacts {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankCleanRFold ring hbank z) :
    AcceptedReceipts.QWord ring (piW z.val.1) ∧
      BankRepairDigitRootWordValues ring hbank z := by
  have hw : CleanWord ring (piW z.val.1) := hz.1.2
  constructor
  · exact bankCleanWordQWord ring (piW z.val.1) hw
  · obtain ⟨root, hfixed, hvalues, _hquiet⟩ := hw
    intro site hs
    have heq : site = root := hfixed.2.1 site hs
    rw [heq]
    exact hvalues

/-- Reuse the existing BANK layout/value class at the clean W
root.  This is the old digit geometry's actual QWord and
CleanWorkerWordValues content, not its monitor provenance.
Consumer: bankCleanDigitLayoutValuesOnWord. -/
theorem bankCleanDigitLayoutValuesOfSingleton {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (z : BankReferenceState ring hbank)
    (hsingle : BankPostInheritedSingleton ring hbank root z)
    (hword : BankCleanWord ring hbank z) :
    BankRepairDigitLayoutValues ring hbank root z := by
  have hw : CleanWord ring (piW z.val.1) := hword
  obtain ⟨r, hfixed, hvalues, hquiet⟩ := hw
  have heq : root = r := hfixed.2.1 root hsingle.2.1
  refine ⟨⟨hsingle, hquiet⟩, ?_⟩
  rw [heq]
  exact hvalues

/-- The clean W root's layout and word equations remain true
through every actual masked BANK continuation.  Consumer:
clean-origin boundary/delimiter clocks. -/
theorem bankCleanDigitLayoutValuesOnWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (z : BankReferenceState ring hbank)
    (word : List (Fin n))
    (hsingle : BankPostInheritedSingleton ring hbank root z)
    (hword : BankCleanWord ring hbank z) :
    BankRepairDigitLayoutValues ring hbank root
      (word.foldl (bankRepairNext ring hbank) z) :=
  bankRepairDigitLayoutValuesWord ring hn hbank root word z
    (bankCleanDigitLayoutValuesOfSingleton
      ring hbank root z hsingle hword)

/-- A genuine boundary receipt survives an arbitrary BANK suffix
from the clean W root.  Consumer: clean-origin boundary flush
and first-zero receipt transport.  This does not create the
boundary receipt at entry. -/
theorem bankCleanDigitBoundaryReceiptOnWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (z : BankReferenceState ring hbank)
    (word : List (Fin n))
    (hsingle : BankPostInheritedSingleton ring hbank root z)
    (hword : BankCleanWord ring hbank z)
    (hreceipt : DigitBoundaryReceipt ring root (piD z.val.1)) :
    DigitBoundaryReceipt ring root
      (piD (word.foldl (bankRepairNext ring hbank) z).val.1) := by
  have hlayout := bankCleanDigitLayoutValuesOfSingleton
    ring hbank root z hsingle hword
  exact bankRepairDigitReceiptBankWord
    ring hn hbank root word z hlayout.1 hreceipt

/-! The remaining clock/row interface is origin-free: it
quantifies over arbitrary entrance and terminal predicates on the
SAME BANK reference, rather than a monitored word origin.
The fine boundary/first-zero/value/pair charges are preserved
before a single rounding to 201 half-units. -/

/-- R10c causal input, parametrized by arbitrary BANK entrance
and terminal predicates.  The four first-hit clocks, invariant
closure and nominated-edge dirty rank are substantive premises;
neither zero dirty nor an old digit receipt is silently identified
with clean generated digit acceptance.  Consumer:
bankDigitHalfOfCausalCore. -/
def BankDigitCausalCore {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (entrance preDrain terminal : BankReferenceState ring hbank → Prop)
    (cuts : BankRepairDigitPreDrainCuts ring hbank) : Prop :=
  BankRepairDigitChargedStage (bankRepairNext ring hbank)
    entrance cuts.boundaryRetired
    (bankRepairDigitBoundaryMicroCharge n) ∧
  BankRepairDigitChargedStage (bankRepairNext ring hbank)
    cuts.boundaryRetired cuts.firstBlockZero
    (bankRepairDigitFirstZeroMicroCharge n) ∧
  BankRepairDigitChargedStage (bankRepairNext ring hbank)
    cuts.firstBlockZero cuts.successorValuesStable
    (bankRepairDigitValueWaveMicroCharge n) ∧
  BankRepairDigitChargedStage (bankRepairNext ring hbank)
    cuts.successorValuesStable preDrain
    (bankRepairDigitComparisonMicroCharge n) ∧
  BankRepairDigitPreDrainClosed ring hbank preDrain ∧
  ∃ (rank : BankReferenceState ring hbank → Nat)
    (chosen : BankReferenceState ring hbank → Fin n),
    (∀ z, preDrain z → rank z ≤ n) ∧
    (∀ z, preDrain z → rank z = 0 → terminal z) ∧
    (∀ z, preDrain z → ¬ terminal z →
      rank (bankRepairNext ring hbank z (chosen z)) + 1 ≤ rank z) ∧
    (∀ z, preDrain z → ¬ terminal z →
      ∀ e : Fin n,
        rank (bankRepairNext ring hbank z e) ≤ rank z)

/-- A forward-closed pre-drain class cannot be escaped along
any scheduler word.  Hence adjoining its complement to the
terminal does not change first-hit cost at entry.  Consumer:
bankDigitDirtyHalfOfCausalRank. -/
private theorem bankDigitCostOnForwardClosed {S : Type} {n : Nat}
    (next : S → Fin n → S) (A terminal : S → Prop)
    (hclosed : ∀ z, A z → ∀ e : Fin n, A (next z e)) :
    ∀ z, A z → ∀ T,
      costNumerator next terminal z T =
        costNumerator next (fun y => ¬ A y ∨ terminal y) z T := by
  classical
  intro z hz T
  induction T generalizing z with
  | zero =>
      simp only [costNumerator_zero]
  | succ T ih =>
      by_cases ht : terminal z
      · rw [costNumerator_terminal next terminal z ht (T + 1),
          costNumerator_terminal next (fun y => ¬ A y ∨ terminal y)
            z (Or.inr ht) (T + 1)]
      · have hu : ¬ (¬ A z ∨ terminal z) := by
          intro h
          rcases h with hna | ht'
          · exact hna hz
          · exact ht ht'
        rw [costNumerator_succ next terminal z ht T,
          costNumerator_succ next (fun y => ¬ A y ∨ terminal y)
            z hu T]
        have hsum := ofFn_sum_eq
          (fun e : Fin n => costNumerator next terminal (next z e) T)
          (fun e : Fin n =>
            costNumerator next (fun y => ¬ A y ∨ terminal y)
              (next z e) T)
          (fun e => ih (next z e) (hclosed z hz e))
        rw [hsum]

/-- The two-half-unit final dirty drain for ANY terminal
predicate, via the installed nominated-edge Bellman inequality
on the same BANK scheduler.  Consumer: bankDigitHalfOfCausalCore.
The zero-rank acceptance clause is not derived from bit clearing. -/
theorem bankDigitDirtyHalfOfCausalRank {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (preDrain terminal : BankReferenceState ring hbank → Prop)
    (hclosed : BankRepairDigitPreDrainClosed ring hbank preDrain)
    (rank : BankReferenceState ring hbank → Nat)
    (chosen : BankReferenceState ring hbank → Fin n)
    (hcap : ∀ z, preDrain z → rank z ≤ n)
    (_hzero : ∀ z, preDrain z → rank z = 0 → terminal z)
    (hdrop : ∀ z, preDrain z → ¬ terminal z →
      rank (bankRepairNext ring hbank z (chosen z)) + 1 ≤ rank z)
    (hnoninc : ∀ z, preDrain z → ¬ terminal z →
      ∀ e : Fin n,
        rank (bankRepairNext ring hbank z e) ≤ rank z) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      preDrain terminal 2 := by
  classical
  have hglobal :
      ∀ z T,
        costNumerator (bankRepairNext ring hbank)
          (fun y => ¬ preDrain y ∨ terminal y) z T ≤
          n ^ T * (n * (if preDrain z then rank z else 0)) :=
    Prob.costNumerator_le_of_nominated_edge
      (bankRepairNext ring hbank)
      (fun y => ¬ preDrain y ∨ terminal y)
      (fun y => if preDrain y then rank y else 0)
      chosen
      (fun y hnot => by
        have hy : preDrain y := by
          by_cases hp : preDrain y
          · exact hp
          · exact False.elim (hnot (Or.inl hp))
        have hnotTerminal : ¬ terminal y := by
          intro ht
          exact hnot (Or.inr ht)
        have hnext := hclosed y hy (chosen y)
        simpa only [if_pos hy, if_pos hnext] using
          hdrop y hy hnotTerminal)
      (fun y hnot e => by
        have hy : preDrain y := by
          by_cases hp : preDrain y
          · exact hp
          · exact False.elim (hnot (Or.inl hp))
        have hnotTerminal : ¬ terminal y := by
          intro ht
          exact hnot (Or.inr ht)
        have hnext := hclosed y hy e
        simpa only [if_pos hy, if_pos hnext] using
          hnoninc y hy hnotTerminal e)
  intro z hz T
  have heq := bankDigitCostOnForwardClosed
    (bankRepairNext ring hbank)
    preDrain terminal
    (fun y hy e => hclosed y hy e) z hz T
  have hle := hglobal z T
  rw [← heq] at hle
  simp only [if_pos hz] at hle
  have hcapz : n * rank z ≤ n * n :=
    Nat.mul_le_mul_left n (hcap z hz)
  calc
    2 * costNumerator (bankRepairNext ring hbank)
        terminal z T ≤
      2 * (n ^ T * (n * rank z)) :=
      Nat.mul_le_mul_left 2 hle
    _ ≤ 2 * (n ^ T * (n * n)) :=
      Nat.mul_le_mul_left 2
        (Nat.mul_le_mul_left (n ^ T) hcapz)
    _ = n ^ T * (2 * n ^ 2) := by
      simp only [Nat.pow_two]
      ac_rfl

/-- The origin-free 201 + 2 causal producer.  The first
stage invokes the existing generic four-clock micro-ledger;
the second uses the generic nominated dirty rank; the final
composition uses the installed half-stage reserve theorem.
Consumer: bankCleanDigitHalfOnDrainOfCausalCore. -/
theorem bankDigitHalfOfCausalCore {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (entrance preDrain terminal : BankReferenceState ring hbank → Prop)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (hcore : BankDigitCausalCore ring hbank
      entrance preDrain terminal cuts) :
    BankRepairHalfStage (bankRepairNext ring hbank)
      entrance terminal 203 := by
  obtain ⟨hboundary, hzero, hwave, hpair, hclosed,
    rank, chosen, hcap, hrankzero, hdrop, hnoninc⟩ := hcore
  have hpre : BankRepairHalfStage (bankRepairNext ring hbank)
      entrance preDrain 201 :=
    bankRepairDigitPreDrain201OfEntranceClocks
      ring hn hbank entrance cuts preDrain
      hboundary hzero hwave hpair
  have hdirty : BankRepairHalfStage (bankRepairNext ring hbank)
      preDrain terminal 2 :=
    bankDigitDirtyHalfOfCausalRank ring hbank preDrain terminal
      hclosed rank chosen hcap hrankzero hdrop hnoninc
  have hcombined := bankRepairCloseHalfCompose
    (bankRepairNext ring hbank)
    entrance preDrain terminal 201 2 hpre hdirty
  have hsum : (201 : Nat) + 2 = 203 := by omega
  rw [hsum] at hcombined
  exact hcombined

/-- The clean-origin R10c conclusion consumed by
bankCleanFinishMaskedBound and bankCleanFinishReference.
This is conditional on ONE origin-free causal input; it is NOT
an assertion that an old AcceptedWord-based digit clock reaches
the clean barred digit class.  Scope: t <= 17. -/
theorem bankCleanDigitHalfOnDrainOfCausalCore {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (preDrain : BankReferenceState ring hbank → Prop)
    (hcore : BankDigitCausalCore ring hbank
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankCleanRFold ring hbank z)
      preDrain (BankCleanDigit ring hbank) cuts) :
    BankCleanDigitHalfOnDrain ring hbank := by
  exact bankDigitHalfOfCausalCore ring hn hbank
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankCleanRFold ring hbank z)
    preDrain (BankCleanDigit ring hbank) cuts hcore

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankCleanDigitRFoldCarriesWordFacts
#print axioms L3.RenewalReferenceClock.bankCleanDigitLayoutValuesOfSingleton
#print axioms L3.RenewalReferenceClock.bankCleanDigitLayoutValuesOnWord
#print axioms L3.RenewalReferenceClock.bankCleanDigitBoundaryReceiptOnWord
#print axioms L3.RenewalReferenceClock.bankDigitDirtyHalfOfCausalRank
#print axioms L3.RenewalReferenceClock.bankDigitHalfOfCausalCore
#print axioms L3.RenewalReferenceClock.bankCleanDigitHalfOnDrainOfCausalCore
