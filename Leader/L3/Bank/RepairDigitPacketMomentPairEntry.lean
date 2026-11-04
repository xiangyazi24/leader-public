import Leader.L3.Bank.RepairDigitPacketMomentPairDone
import Leader.L3.Bank.RepairDigitPairsClean

/-!
# Lemma e-packet at BANK: the entry at the mobile-free cut and the per-pair moment

The attempt loop (`L3.PacketMomentAttempt.attemptMomentBank`) runs from the attempt class
`AttemptInv`. This module supplies its entry and composes it with the pre-attempt stages.

* `MobileFree R s`: no target cell of the pair is carry-live, every target input is empty or
  settled (the mobile-free cut of repair.tex, Lemma e-packet).
* `LaneCut`: the labelled aligned source (`SrcLabAt`: `SrcLab` with `LabelOk`) at a mobile-free
  lane. `RunInv`: the audit invariants of the pair (`PairInv` with the inherited atoms as base) and
  the complete pair at the audit start.
* `attemptOfCut`: `RunInv` and `LaneCut` give `AttemptInv` (`winAlignedOfMobileFree`,
  `winLabOfMobileFree`, `packetQueueMobileFree`).
* `cleanRunStart`, `runInvFold`: on every continuation of a clean start, every interior pair of the
  first delimiter of the audit start has `RunInv` (`pairInvInitial` on the clean layout,
  `pairInOfDelims`, `pairInvStep`); `zeroRunInv` at a `WidthZeroRun` state.
* `pairMomentOfStage`: a stage bound `a/b` to `PairDone ∨ LaneCut`, kept with `RunInv`, composed at
  the first hit with the attempt loop (`E[z^τ] ≤ 6`): `E[z^τ] ≤ 6a/b` to `PairDone`.
* `BankPairStage a b`: the pre-attempt stage obligation (from every `WidthZeroRun` state of an
  interior pair not yet complete, `E[z^τ] ≤ a/b` to `PairDone ∨ LaneCut`).
* `pairOfFirstMoment`: `BankPairStage a b` with `3a ≤ 20b` gives the per-pair moment
  `E[z^τ] ≤ 40` to `PairOfFirst` (the body of `WidthPairDone`) at `N = n (2 C_r + 1)`;
  `stagePow`: a stage bound `w^B`, `B ≤ 3 C_r`, has `3 w^B ≤ 20`.
-/

namespace L3.PacketMomentPairEntry

set_option autoImplicit false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
open L3.WidthDigit
open L3.DigitPacketTransport
open L3.DigitPacketQueue
open L3.PacketMomentPrep
open L3.PacketMomentCells
open L3.PacketMomentTrialLabels
open L3.PacketMomentGroupLabels
open L3.PacketMomentGroupCompletion
open L3.PacketMomentAttempt
open L3.PacketMomentPairDone
open L3.DigitPairsClean

/-! ### The mobile-free cut -/

/-- **The mobile-free target half**: no target cell is carry-live and every target input is
empty or settled. Consumer: `LaneCut`, `attemptOfCut`. -/
def MobileFree (R : Nat) (s : CohortLane) : Prop :=
  ∀ q, R ≤ q → q < 2 * R → s.live q = false ∧ (s.inp q = .E ∨ ∃ T, s.inp q = .S T)

/-- A moment bound at a state of the target. Consumer: `pairMomentOfStage` (the `PairDone`
alternative of the stage target). -/
theorem momentDone {S : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop) (N a b : Nat)
    (x : S) (hba : b ≤ a) (hx : P x) : MomentBoundQ next P N a b x := fun T => by
  rw [momentNumeratorTerminal next P N x hx T]
  exact Nat.mul_le_mul_right _ hba

/-- **The BANK span is at least `7`** (`t = ⌈log₂ q⌉ ≥ 6` for `q ≥ 80`). Consumer:
`pairOfFirstMoment` (the `R ≥ 7` premise of `attemptMomentBank`). -/
theorem spanSeven {n : Nat} (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    7 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := by
  have hq := bankRepairBankBand hbank
  have ht := compileAdvice_t_large (ceilLogTwo n) (by omega)
  have h6 := ceilLogTwo_ge_six (ceilLogTwo n) (by omega)
  unfold digitSpan
  rw [ht]
  have h1 : 2 ^ 6 ≤ 2 ^ ceilLogTwo (ceilLogTwo n) := Nat.pow_le_pow_right (by omega) h6
  have h2 : (2 : Nat) ^ 6 = 64 := by decide
  omega

/-- **A stage of at most `3 C` letters has factor at most `20/3`** at width `N ≥ n (2C + 1)`,
`C ≥ 4000` (`widePow` cubed: `1.67³ < 20/3`). Consumer: `pairOfFirstMomentPow`. -/
theorem stagePow (N n C B : Nat) (hn : 1 ≤ n) (hC : 4000 ≤ C) (hN : n * (2 * C + 1) ≤ N)
    (hB : B ≤ 3 * C) : 3 * N ^ B ≤ 20 * (N - n) ^ B := by
  have hnN : n < N := by
    have : n * 2 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  have hw := L3.PacketMomentWide.widePow N n C C hn hC hN (Nat.le_refl _)
  have h3 : (100 * N ^ C) ^ 3 ≤ (167 * (N - n) ^ C) ^ 3 := Nat.pow_le_pow_left hw 3
  rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at h3
  have hnum : 3 * 167 ^ 3 ≤ 20 * 100 ^ 3 := by decide
  have hm : 3 * N ^ (C * 3) ≤ 20 * (N - n) ^ (C * 3) := by
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 100 ^ 3 by decide)
    calc 100 ^ 3 * (3 * N ^ (C * 3)) = 3 * (100 ^ 3 * N ^ (C * 3)) := Nat.mul_left_comm _ _ _
      _ ≤ 3 * (167 ^ 3 * (N - n) ^ (C * 3)) := Nat.mul_le_mul_left _ h3
      _ = (3 * 167 ^ 3) * (N - n) ^ (C * 3) := by rw [Nat.mul_assoc]
      _ ≤ (20 * 100 ^ 3) * (N - n) ^ (C * 3) := Nat.mul_le_mul_right _ hnum
      _ = 100 ^ 3 * (20 * (N - n) ^ (C * 3)) := by
          rw [Nat.mul_comm 20, Nat.mul_assoc]
  exact L3.PacketMomentWide.ratioMono N n B (C * 3) 3 20 hnN (by omega) hm

section Coupled

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat)

/-- **The lane part of the mobile-free cut**: the labelled aligned source (the distinguished tail
exported, with labels that are the audit's samples) at a mobile-free target half. Consumer:
`attemptOfCut`, `BankPairStage`. -/
def LaneCut (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  SrcLabAt ring hbank root lane src R x ∧ MobileFree R (laneOfState ring hbank root lane src R x)

/-- **The run invariant of the pair**: the audit invariants with the inherited atoms as base and
the complete pair at the audit start. Consumer: `attemptOfCut`, `pairMomentOfStage`. -/
def RunInv (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  PairInv ring hbank root lane src R (InheritedOk lane) x ∧
    DigitCompletePair ring root x.2.start src (src + R)

/-- Every coupled letter keeps the run invariant. Consumer: `runInvFold`, `pairMomentOfStage`. -/
theorem runInvStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : RunInv ring hbank root lane src R x) (e : Fin n) :
    RunInv ring hbank root lane src R (nxt ring hn hbank x e) :=
  ⟨pairInvStep ring hn hbank root lane src R hR hsrc hend _ x h.1 e, h.2⟩

/-- **The entry at the mobile-free cut**: the run invariant and the lane cut give the attempt
class. Consumer: `pairMomentOfStage`. -/
theorem attemptOfCut
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hI : RunInv ring hbank root lane src R x) (hc : LaneCut ring hbank root lane src R x) :
    AttemptInv ring hbank root lane src R (InheritedOk lane) x := by
  obtain ⟨⟨σ, hL, hs⟩, hm⟩ := hc
  obtain ⟨a, hA, -⟩ := id hs
  exact ⟨hI.1, winAlignedOfMobileFree R _ ⟨a, hA⟩ hm, ⟨σ, hL, winLabOfMobileFree R _ σ hs hm⟩,
    packetQueueMobileFree ring root lane src R (piD x.1.val.1) x.2
      (fun _ => ⟨0, lane, root, root, none, ⟨0, compileAdvice_topA_pos _⟩, false⟩) hm, hI.2⟩

/-- The run invariant along every word. Consumer: `zeroRunInv`. -/
theorem runInvFold (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) :
    ∀ (w : List (Fin n)) (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      RunInv ring hbank root lane src R q →
      RunInv ring hbank root lane src R (w.foldl (nxt ring hn hbank) q) := by
  intro w
  induction w with
  | nil => intro q h; exact h
  | cons e rest ih =>
    intro q h
    exact ih _ (runInvStep ring hn hbank root lane src R hR hsrc hend q h e)

/-- The audit start along every word. Consumer: `zeroRunInv`. -/
theorem foldStart : ∀ (w : List (Fin n))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    (w.foldl (nxt ring hn hbank) q).2.start = q.2.start := by
  intro w
  induction w with
  | nil => intro q; rfl
  | cons e rest ih => intro q; exact ih _

/-- The reference component along every word. Consumer: `zeroRunInv`. -/
theorem foldFst : ∀ (w : List (Fin n))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    (w.foldl (nxt ring hn hbank) q).1 = w.foldl (bankRepairNext ring hbank) q.1 := by
  intro w
  induction w with
  | nil => intro q; rfl
  | cons e rest ih => intro q; exact ih _

include hn in
/-- **The run invariant at a clean start**: for the W fixed root of a continuation and the first
delimiter of the start, every interior pair has the audit invariants at the audit start
(`pairInvInitial` on the clean layout) and is complete there (`pairInOfDelims`). Consumer:
`zeroRunInv`. -/
theorem cleanRunStart
    (start : BankReferenceState ring hbank) (hD : BankPostInheritedGrantDrain ring hbank start)
    (hC : BankCleanRFold ring hbank start) (word0 : List (Fin n))
    (hW : WFixedRoot ring root (piW (word0.foldl (bankRepairNext ring hbank) start).val.1))
    (first : Nat) (hf : DigitFirstDelimiter ring root (piD start.val.1) first) (i : Nat)
    (hend : first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
      2 * digitSpan (compileAdvice (ceilLogTwo n)) < n) :
    2 ≤ first + i * digitSpan (compileAdvice (ceilLogTwo n)) ∧
      RunInv ring hbank root lane (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (digitSpan (compileAdvice (ceilLogTwo n))) (start, digitAuditInitial (piD start.val.1)) := by
  obtain ⟨root0, hs, hV⟩ := bankCleanBoundaryRoot ring hbank start hD hC
  have hsz := bankRepairDigitSingletonWordFold ring hn hbank root0 word0 start hs
  have hr : root = root0 := hsz.2.2.1 root hW.1
  subst hr
  obtain ⟨first0, ht, -, hb⟩ := bankCleanBoundaryDelimiters ring hbank hn root start hV
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hfe := firstDelimEq ring root (piD start.val.1) first0 hb (by omega)
    (by have := hf.1.2.1; have := (hb _ hf.1.1 hf.1.2.1).1 hf.1.2.2; omega) first hf
  subst hfe
  have hR := bankRepairDigitLeadSpanTwo hbank
  have hlay : CohortLayout ring hbank root (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
      (digitSpan (compileAdvice (ceilLogTwo n))) start := by
    generalize digitSpan (compileAdvice (ceilLogTwo n)) = R at hend hb hR ⊢
    generalize hm : i * R = m at hend
    have hmR : m % R = 0 := by rw [← hm]; exact Nat.mul_mod_left i R
    have hm1 : (m + R) % R = 0 := by
      rw [← hm, show i * R + R = (i + 1) * R by rw [Nat.succ_mul]]
      exact Nat.mul_mod_left _ R
    have hm2 : (m + 2 * R) % R = 0 := by
      rw [← hm, show i * R + 2 * R = (i + 2) * R by rw [Nat.add_mul]]
      exact Nat.mul_mod_left _ R
    refine ⟨hV.1, ?_, ?_, ?_, fun k hk0 hk2 hkR => ?_⟩
    · exact (hb _ (by omega) (by omega)).2
        ⟨by omega, by rw [show first + m - first = m by omega]; exact hmR⟩
    · exact (hb _ (by omega) (by omega)).2
        ⟨by omega, by rw [show first + m + R - first = m + R by omega]; exact hm1⟩
    · exact (hb _ (by omega) (by omega)).2
        ⟨by omega, by rw [show first + m + 2 * R - first = m + 2 * R by omega]; exact hm2⟩
    · cases hbeta : (piD start.val.1 (digitSite ring root (first + m + k))).word.beta with
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
  refine ⟨by omega, pairInvInitial ring hbank root lane _ _ start hlay, ?_⟩
  exact pairInOfDelims ring root (piD start.val.1) first hb
    (i * digitSpan (compileAdvice (ceilLogTwo n))) (Nat.mul_mod_left i _) (by omega) hend
    (by omega)

include hn in
/-- **The run invariant at a `WidthZeroRun` state**: for the first delimiter of the audit start,
every interior pair has the run invariant. Consumer: `pairOfFirstMoment`. -/
theorem zeroRunInv
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthZeroRun (bankWidthDigitReference ring hn hbank) root x) (first : Nat)
    (hf : DigitFirstDelimiter ring root x.2.start first) (i : Nat)
    (hend : first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
      2 * digitSpan (compileAdvice (ceilLogTwo n)) < n) :
    2 ≤ first + i * digitSpan (compileAdvice (ceilLogTwo n)) ∧
      RunInv ring hbank root lane (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (digitSpan (compileAdvice (ceilLogTwo n))) x := by
  obtain ⟨start, word0, word, y, _, hs, hy, hW, -, -, -, hxw⟩ := hx
  have hy' : word0.foldl (nxt ring hn hbank) (start, digitAuditInitial (piD start.val.1)) = y := hy
  have hxw' : word.foldl (nxt ring hn hbank) y = x := hxw
  have hst : x.2.start = piD start.val.1 := by
    rw [← hxw', foldStart ring hn hbank word y, ← hy', foldStart ring hn hbank word0]
    rfl
  have hW' : WFixedRoot ring root (piW (word0.foldl (bankRepairNext ring hbank) start).val.1) := by
    have h1 := foldFst ring hn hbank word0 (start, digitAuditInitial (piD start.val.1))
    rw [hy'] at h1
    rw [← h1]
    exact hW
  rw [hst] at hf
  obtain ⟨h2, hI⟩ := cleanRunStart ring hn hbank root lane start hs.1 hs.2 word0 hW' first hf i
    hend
  refine ⟨h2, ?_⟩
  rw [← hxw', ← hy']
  have hR := bankRepairDigitLeadSpanTwo hbank
  exact runInvFold ring hn hbank root lane _ _ (by omega) h2 hend word _
    (runInvFold ring hn hbank root lane _ _ (by omega) h2 hend word0 _ hI)

/-! ### The composition -/

/-- **The stage, then the attempt loop**: a stage bound `a/b` from a run-invariant state to
`PairDone ∨ LaneCut`, kept with the run invariant, composed at the first hit with the attempt
loop (`attemptMomentBank`, `E[z^τ] ≤ 6`): `E[z^τ] ≤ 6 a / b` to `PairDone`. Consumer:
`pairOfFirstMoment`. -/
theorem pairMomentOfStage (hR : 7 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hI : RunInv ring hbank root lane src R x) (a b : Nat)
    (hstage : MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => PairDone ring hbank root lane src R y ∨ LaneCut ring hbank root lane src R y)
      (n * (2 * bankRepairDigitPairClock R + 1)) a b x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (PairDone ring hbank root lane src R) (n * (2 * bankRepairDigitPairClock R + 1))
      (a * (6 * (n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R))
      (b * (n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R) x := by
  have hk := momentKeep (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) _
    (RunInv ring hbank root lane src R) _ a b
    (fun y e hy => runInvStep ring hn hbank root lane src R (by omega) hsrc hend y hy e) x hI hstage
  refine momentSeq _ _ _ _ a b _ _ x (Nat.le_mul_of_pos_left _ (by decide)) (fun y hy => ?_) hk
  obtain ⟨hd | hc, hy⟩ := hy
  · exact momentDone _ _ _ _ _ y (Nat.le_mul_of_pos_left _ (by decide)) hd
  · exact attemptMomentBank ring hn hbank root lane src R hR hsrc hend (InheritedOk lane) y
      (attemptOfCut ring hbank root lane src R y hy hc)

end Coupled

section Stage

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- **The pre-attempt stage obligation at BANK**: from every `WidthZeroRun` state, for every
interior pair `(first + i r, first + (i+1) r)` of the first delimiter of the audit start
(`r = digitSpan`) not yet complete, the first hit of its completion or of the mobile-free cut
(`LaneCut`) has `E[z^τ] ≤ a/b`, `z = N/(N-1)`, `N = n (2 C_r + 1)`. These are the phases before the
first attempt (inherited mobile work, the distinguished tail with its labels, the mobile-free
cut). Consumer: `pairOfFirstMoment`. -/
def BankPairStage (a b : Nat) : Prop :=
  ∀ (root : Fin n) (i : Nat) (lane : DigitLane) (first : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthZeroRun (bankWidthDigitReference ring hn hbank) root x →
    DigitFirstDelimiter ring root x.2.start first →
    first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
      2 * digitSpan (compileAdvice (ceilLogTwo n)) < n →
    ¬ PairDone ring hbank root lane (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
      (digitSpan (compileAdvice (ceilLogTwo n))) x →
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => PairDone ring hbank root lane (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (digitSpan (compileAdvice (ceilLogTwo n))) y ∨
        LaneCut ring hbank root lane (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (digitSpan (compileAdvice (ceilLogTwo n))) y)
      (n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) a b x

/-- **The per-pair moment at BANK from the stage obligation**: with `3a ≤ 20b`, from every
`WidthZeroRun` state with pair `i` not complete, the first completion of pair `i` (`PairOfFirst`,
the body of `WidthPairDone`) has `E[z^τ] ≤ 40` at `N = n (2 C_r + 1)`. Consumer:
`pairOfFirstMomentPow`, `L3.PacketMomentPairBank.bankStrictPairMomentOfStage`. -/
theorem pairOfFirstMoment (a b : Nat) (hb : 0 < b)
    (hab : 3 * a ≤ 20 * b) (hst : BankPairStage ring hn hbank a b) (root : Fin n) (i : Nat)
    (lane : DigitLane)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthZeroRun (bankWidthDigitReference ring hn hbank) root x)
    (hnd : ¬ PairOfFirst (ring := ring) (hbank := hbank) root i lane x) :
    L3.PairMoment.MomentBound (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (PairOfFirst (ring := ring) (hbank := hbank) root i lane)
      (n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) 40 x := by
  obtain ⟨first, hf, hend, hno⟩ : ∃ first, DigitFirstDelimiter ring root x.2.start first ∧
      first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
        2 * digitSpan (compileAdvice (ceilLogTwo n)) < n ∧
      ¬ PairDone ring hbank root lane (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (digitSpan (compileAdvice (ceilLogTwo n))) x := by
    refine Classical.byContradiction fun hcon => hnd ?_
    intro first hf hend
    exact Classical.byContradiction fun hno => hcon ⟨first, hf, hend, hno⟩
  obtain ⟨h2, hI⟩ := zeroRunInv ring hn hbank root lane x hx first hf i hend
  have h7 := spanSeven hbank
  have hq := pairMomentOfStage ring hn hbank root lane _ _ h7 h2 hend x hI a b
    (hst root i lane first x hx hf hend hno)
  have hw := pairMomentWidth ring hn hbank root lane _ _ i first _ _ _ x hf rfl rfl hq
  have hC := L3.PacketMomentWide.pairClockLarge _ h7
  generalize bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) = C at hw hC ⊢
  have hNn : 0 < n * (2 * C + 1) - n := by
    have : n * 2 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  refine momentBoundOfQ _ _ _ _ _ 40 x (Nat.mul_pos hb (Nat.pow_pos hNn)) ?_ hw
  generalize (n * (2 * C + 1) - n) ^ C = p
  have h6 : 6 * a ≤ 40 * b := by omega
  have e1 : a * (6 * p) = 6 * a * p := by ac_rfl
  have e2 : 40 * (b * p) = 40 * b * p := by ac_rfl
  rw [e1, e2]
  exact Nat.mul_le_mul_right p h6

/-- **The per-pair moment from a stage of at most `3 C_r` letters' worth**: a stage bound
`w^B = N^B / (N-n)^B` with `B ≤ 3 C_r` (`stagePow`). Consumer:
`L3.PacketMomentPairBank.bankStrictPairMomentOfStage`. -/
theorem pairOfFirstMomentPow (B : Nat)
    (hB : B ≤ 3 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))))
    (hst : BankPairStage ring hn hbank
      ((n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) ^ B)
      ((n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1) - n) ^ B))
    (root : Fin n) (i : Nat) (lane : DigitLane)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthZeroRun (bankWidthDigitReference ring hn hbank) root x)
    (hnd : ¬ PairOfFirst (ring := ring) (hbank := hbank) root i lane x) :
    L3.PairMoment.MomentBound (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (PairOfFirst (ring := ring) (hbank := hbank) root i lane)
      (n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) 40 x := by
  have hC := L3.PacketMomentWide.pairClockLarge _ (spanSeven hbank)
  have hNn : 0 < n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1)
      - n := by
    have : n * 2 ≤ n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n)))
      + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  exact pairOfFirstMoment ring hn hbank _ _ (Nat.pow_pos hNn)
    (stagePow _ n _ B (by omega) hC (Nat.le_refl _) hB) hst root i lane x hx hnd

end Stage

end L3.PacketMomentPairEntry

#print axioms L3.PacketMomentPairEntry.momentDone
#print axioms L3.PacketMomentPairEntry.spanSeven
#print axioms L3.PacketMomentPairEntry.stagePow
#print axioms L3.PacketMomentPairEntry.runInvStep
#print axioms L3.PacketMomentPairEntry.attemptOfCut
#print axioms L3.PacketMomentPairEntry.runInvFold
#print axioms L3.PacketMomentPairEntry.foldStart
#print axioms L3.PacketMomentPairEntry.foldFst
#print axioms L3.PacketMomentPairEntry.cleanRunStart
#print axioms L3.PacketMomentPairEntry.zeroRunInv
#print axioms L3.PacketMomentPairEntry.pairMomentOfStage
#print axioms L3.PacketMomentPairEntry.pairOfFirstMoment
#print axioms L3.PacketMomentPairEntry.pairOfFirstMomentPow
