import Leader.L3.Width.DigitQuietStepDigitsRows
import Leader.L3.Width.DigitQuietStepDigitsLocal
import Leader.L3.Width.DigitQuietStepReport
import Leader.L3.Bank.RepairDigitValueWaveClose

/-!
# No letter changes a digit on the quiet class

`digits_kept_of_span`: for any compiled `c` with `0 < digitSpan c`, the digit of every site is kept
by every projected letter, on the quiet class under `QWord`.  The three writes of the top machine
(BASE, LAUNCH, ADVANCE, `WidthDigitQuietStepDigitsRows`) each store the digit already there
(`WidthDigitQuietStepDigitsLocal`); a dirty side drops its write.  `digits_kept` is the instance of
the value wave `compileAdvice (ceilLogTwo n)` at `5 ≤ n`.

Consumer: `QuietStepLaw` (WidthDigitQuiet), digit clause.
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled} {n : Nat}

/-- Two non-leader consecutive sites are the sites `k` and `k + 1` from the root with `0 < k`.
Consumer: `digits_kept_of_span`. -/
theorem digits_sites (ring : DirectedRing n) (root : Fin n) (first : Nat) (S : Fin n → ProjD c)
    (hQ : WidthDigitQuiet ring root first S) (e : Fin n)
    (hx : (S e).word.native.l = false) (hy : (S (ring.rightNeighbor e)).word.native.l = false) :
    ∃ k, 0 < k ∧ k + 1 < n ∧ e = digitSite ring root k ∧
      ring.rightNeighbor e = digitSite ring root (k + 1) := by
  obtain ⟨k, hk, rfl⟩ := RenewalReferenceClock.bankRepairDigitSiteSurj ring root e
  have hroot := hQ.rootFixed
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      have := (hroot (digitSite ring root 0)).mpr rfl
      rw [hx] at this
      exact absurd this Bool.false_ne_true
    · exact h0
  have hY : ring.rightNeighbor (digitSite ring root k) = digitSite ring root (k + 1) :=
    (CloseReceipt.digitSiteSucc ring root k).symm
  have hk1 : k + 1 < n := by
    by_cases hkn : k + 1 = n
    · exfalso
      rw [hY, hkn, digitSite_n] at hy
      have := (hroot root).mpr rfl
      rw [hy] at this
      exact absurd this Bool.false_ne_true
    · omega
  exact ⟨k, hk0, hk1, rfl, hY⟩

/-- **No letter changes a digit on the quiet class** (any compiled data with a nonempty block).
Consumer: `digits_kept`. -/
theorem digits_kept_of_span (hR : 0 < digitSpan c) (hn : 2 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (first : Nat) (S : Fin n → ProjD c)
    (hQ : WidthDigitQuiet ring root first S) (hW : QWord ring (wordProjection S)) (e : Fin n) :
    ∀ i : Fin n, ((phiD ring S e) i).top.d = (S i).top.d := by
  have hne := rightNeighbor_ne ring hn e
  intro i
  by_cases hie : i = e
  · rw [hie]
    rw [digits_phi_left ring S hW e hne]
    by_cases hd : (S e).top.topDirty = true
    · rw [if_pos hd]
    rw [if_neg hd]
    by_cases hbase : (S e).word.native.l = false ∧ (S (ring.rightNeighbor e)).word.native.l = false ∧
        (S e).top.wBase = .ZERO
    · rw [if_pos hbase]
      obtain ⟨k, hk0, hk1, hek, -⟩ := digits_sites ring root first S hQ e hbase.1 hbase.2.1
      subst hek
      exact (digits_base_value hR ring root first S hQ k hk0 hk1 hbase.2.2).symm
    rw [if_neg hbase]
    by_cases hl : (S e).word.native.l = false ∧ (S (ring.rightNeighbor e)).word.native.l = false ∧
        (S e).word.beta = true ∧ (S e).top.wCarry = .OFF ∧ (S e).top.wIn.isS = true
    · rw [if_pos hl]
      obtain ⟨k, hk0, hk1, hek, -⟩ := digits_sites ring root first S hQ e hl.1 hl.2.1
      obtain ⟨-, -, hb, hcar, hs⟩ := hl
      subst hek
      cases hin : (S (digitSite ring root k)).top.wIn with
      | E => rw [hin] at hs; simp [InTok.isS] at hs
      | X => rw [hin] at hs; simp [InTok.isS] at hs
      | P v t => rw [hin] at hs; simp [InTok.isS] at hs
      | S v t =>
        have := digits_launch_value hR ring root first S hQ k hk0 hk1 hb hcar v t hin
        rw [this]
        try rfl
    · rw [if_neg hl]
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij]
      rw [digits_phi_right ring S hW e hne]
      by_cases hd : (S (ring.rightNeighbor e)).top.topDirty = true
      · rw [if_pos hd]
      rw [if_neg hd]
      by_cases hadv : (S e).word.native.l = false ∧
          (S (ring.rightNeighbor e)).word.native.l = false ∧ (S e).top.wCarry.isW = true ∧
          (S (ring.rightNeighbor e)).word.beta = false ∧
          (S (ring.rightNeighbor e)).top.wCarry = .OFF ∧
          (S (ring.rightNeighbor e)).top.wIn.isS = true
      · rw [if_pos hadv]
        obtain ⟨k, hk0, hk1, hek, hrk⟩ := digits_sites ring root first S hQ e hadv.1 hadv.2.1
        obtain ⟨-, -, hw, hb, hcy, hs⟩ := hadv
        rw [hrk] at hb hcy hs ⊢
        rw [hek] at hw
        cases hcx : (S (digitSite ring root k)).top.wCarry with
        | OFF => rw [hcx] at hw; cases hw
        | W cc =>
          rw [hek, hcx]
          cases hin : (S (digitSite ring root (k + 1))).top.wIn with
          | E => rw [hin] at hs; simp [InTok.isS] at hs
          | X => rw [hin] at hs; simp [InTok.isS] at hs
          | P v t => rw [hin] at hs; simp [InTok.isS] at hs
          | S v t =>
            have := digits_advance_value hR ring root first S hQ k hk0 hk1 hb cc hcx hcy v t hin
            rw [this]
            try rfl
      · rw [if_neg hadv]
    · rw [phiD_at_other ring S e i hie hij]

set_option linter.unusedVariables false in
/-- **No letter changes a digit on the quiet class**: the digit clause of `QuietStepLaw`, for the
value wave `compileAdvice (ceilLogTwo n)`.  Consumer: `QuietStepLaw` (WidthDigitQuiet), assembled
with the pair closure. -/
theorem digits_kept {n : Nat} (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n) (first : Nat)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (hQ : WidthDigitQuiet ring root first S) (hF : WFixedRoot ring root (wordProjection S))
    (hW : QWord ring (wordProjection S)) (e : Fin n) :
    ∀ i : Fin n, ((phiD ring S e) i).top.d = (S i).top.d := by
  have hR : 0 < digitSpan (compileAdvice (ceilLogTwo n)) := by
    have := L3.ValueWaveClose.valueSpanTwo hn
    unfold L3.ValueWaveClose.valueSpan at this
    omega
  exact digits_kept_of_span hR (by omega) ring root first S hQ hW e

end L3.DigitQuiet

#print axioms L3.DigitQuiet.digits_kept_of_span
#print axioms L3.DigitQuiet.digits_kept
