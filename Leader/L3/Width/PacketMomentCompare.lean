import Leader.L3.Bank.RepairDigitPacketMomentCompareBank
import Leader.L3.Width.PacketMomentCutEntry
import Leader.L3.Width.PacketMomentLayout
import Leader.L3.Width.PacketMomentLoop

/-!
# The comparison-lane per-pair moment at a boundary reference (`hcmpMomentSmall`)

Generic form of `L3.PacketMomentCompareBank` (BankRepairDigitPacketMomentCompareBank) at an
arbitrary `WidthBoundaryReference`, and its SMALL instance:

* `widthCleanRunStart`, `widthStableRunInv`: on a values-stable state (`WidthStableRun`), every
  interior pair of the first delimiter has the run invariant (`WidthRunInv`) on the comparison
  lane.
* `WidthCmpPairStage a b`, `WidthCmpPairStageW`: the pre-attempt stage obligation on the
  comparison lane after the restart (to the completion after `restart` or to the attempt cut
  `WidthLaneCutC` with labels stamped after `restart`), at a factor `w^B`, `B ≤ 3 C_r`.
* `bernoulliPow`, `stageFactor`: a stage of at most `3 C` letters has factor at most `20/3` at
  width `N ≥ n (2C + 1)` for every `C ≥ 20` (blocks of `⌊C/3⌋` letters, factor `6/5` each, ten
  blocks; the BANK `stagePow` needs `C ≥ 4000`, the SMALL clock is `C_3 = 442`).
* `widthComparePairMoment`: `WidthComparePairMoment` at the reference from `WidthCmpPairStageW`
  (`widthPairMomentOfStageC` with the cut `restart`, every `r ≥ 3`).
* `smallComparePairMoment`: the headline premise `hcmpMomentSmall` from the stage obligation at
  `smallWidthBoundaryReference`.
-/

namespace L3.WidthPacketMomentCompare

set_option autoImplicit false
set_option linter.unusedSectionVars false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.CohortSites
open L3.PacketMomentPrep
open L3.PacketMomentCells
open L3.PacketMomentGroupLabels
open L3.PacketMomentPairEntry
open L3.DigitPairsClean
open L3.CompareStage
open L3.WriterValueCuts
open L3.PairMomentPremise
open L3.WidthPacketMoment
open L3.WidthPacketMomentAudit
open L3.WidthPacketMomentGroupCompletion
open L3.WidthPacketMomentCutAttempt
open L3.WidthPacketMomentCutEntry

/-! ### The stage factor at every clock `C ≥ 20` -/

/-- **Bernoulli's inequality in `Nat`**: `(M + n)^k (M - k n) ≤ M^(k+1)`. Consumer:
`stageFactor`. -/
theorem bernoulliPow (M n : Nat) : ∀ k, (M + n) ^ k * (M - k * n) ≤ M ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    rw [Nat.pow_zero, Nat.one_mul, Nat.zero_mul, Nat.sub_zero, Nat.pow_one]
    exact Nat.le_refl _
  | succ k ih =>
    rw [Nat.add_mul, Nat.one_mul]
    by_cases h : k * n + n ≤ M
    · generalize hp : k * n = p at ih h
      obtain ⟨a, ha⟩ : ∃ a, M = a + p + n := ⟨M - (p + n), by omega⟩
      have e1 : M - (p + n) = a := by omega
      have e2 : M - p = a + n := by omega
      rw [e1]
      rw [e2] at ih
      have key : (M + n) * a ≤ M * (a + n) := by
        have e3 : (a + p + n + n) * a + (p + n) * n = (a + p + n) * (a + n) := by grind
        rw [ha]
        omega
      calc (M + n) ^ (k + 1) * a = (M + n) ^ k * ((M + n) * a) := by
            rw [Nat.pow_succ, Nat.mul_assoc]
        _ ≤ (M + n) ^ k * (M * (a + n)) := Nat.mul_le_mul_left _ key
        _ = (M + n) ^ k * (a + n) * M := by rw [Nat.mul_comm M, Nat.mul_assoc]
        _ ≤ M ^ (k + 1) * M := Nat.mul_le_mul_right _ ih
        _ = M ^ (k + 1 + 1) := (Nat.pow_succ _ _).symm
    · have : M - (k * n + n) = 0 := by omega
      rw [this, Nat.mul_zero]
      exact Nat.zero_le _

/-- **A stage of at most `3 C` letters has factor at most `20/3`** at width `N ≥ n (2C + 1)`,
every `C ≥ 20` (ten blocks of `⌊C/3⌋` letters, `(6/5)^10 < 20/3`). Consumer:
`widthComparePairMoment` (the SMALL clock `C_3 = 442` is below `stagePow`'s `C ≥ 4000`). -/
theorem stageFactor (N n C B : Nat) (hn : 1 ≤ n) (hC : 20 ≤ C) (hN : n * (2 * C + 1) ≤ N)
    (hB : B ≤ 3 * C) : 3 * N ^ B ≤ 20 * (N - n) ^ B := by
  have e : n * (2 * C + 1) = 2 * C * n + n := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm n]
  rw [e] at hN
  obtain ⟨M, rfl⟩ : ∃ M, N = M + n := ⟨N - n, by omega⟩
  have hMn : M + n - n = M := by omega
  rw [hMn]
  have hk6 : 6 * (C / 3 * n) ≤ M := by
    have h1 : 6 * (C / 3) * n ≤ 2 * C * n := Nat.mul_le_mul_right n (by omega)
    rw [Nat.mul_assoc] at h1
    omega
  have hMpos : 0 < M := by
    have : 1 ≤ 2 * C * n := Nat.mul_pos (by omega) hn
    omega
  have h56 : 5 * (M + n) ^ (C / 3) ≤ 6 * M ^ (C / 3) := by
    have a1 : 5 * M ≤ 6 * (M - C / 3 * n) := by omega
    have a2 := bernoulliPow M n (C / 3)
    have a3 : 5 * (M + n) ^ (C / 3) * M ≤ 6 * M ^ (C / 3) * M := by
      calc 5 * (M + n) ^ (C / 3) * M = (M + n) ^ (C / 3) * (5 * M) := by
            rw [Nat.mul_comm 5, Nat.mul_assoc]
        _ ≤ (M + n) ^ (C / 3) * (6 * (M - C / 3 * n)) := Nat.mul_le_mul_left _ a1
        _ = 6 * ((M + n) ^ (C / 3) * (M - C / 3 * n)) := Nat.mul_left_comm _ _ _
        _ ≤ 6 * M ^ (C / 3 + 1) := Nat.mul_le_mul_left _ a2
        _ = 6 * M ^ (C / 3) * M := by rw [Nat.pow_succ, Nat.mul_assoc]
    exact Nat.le_of_mul_le_mul_right a3 hMpos
  have h10 : (5 * (M + n) ^ (C / 3)) ^ 10 ≤ (6 * M ^ (C / 3)) ^ 10 := Nat.pow_le_pow_left h56 10
  rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at h10
  have hm : B ≤ C / 3 * 10 := by omega
  have hr := L3.PacketMomentWide.ratioMono (M + n) n B (C / 3 * 10) (5 ^ 10) (6 ^ 10)
    (by omega) hm (by rw [hMn]; exact h10)
  rw [hMn] at hr
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 5 ^ 10 by decide)
  calc 5 ^ 10 * (3 * (M + n) ^ B) = 3 * (5 ^ 10 * (M + n) ^ B) := Nat.mul_left_comm _ _ _
    _ ≤ 3 * (6 ^ 10 * M ^ B) := Nat.mul_le_mul_left _ hr
    _ = (3 * 6 ^ 10) * M ^ B := by rw [Nat.mul_assoc]
    _ ≤ (20 * 5 ^ 10) * M ^ B := Nat.mul_le_mul_right _ (by decide)
    _ = 5 ^ 10 * (20 * M ^ B) := by rw [Nat.mul_comm 20, Nat.mul_assoc]

/-- The span is at least `3` (`r = 2^t - 1`, `t ≥ 2`). Consumer: `widthComparePairMoment`
(the `R ≥ 3` premise of `widthPairMomentOfStageC`). -/
theorem widthSpanThree {n : Nat} (hn : 5 ≤ n) : 3 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := by
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two _ (ringQ_facts n hn).1
  unfold digitSpan
  have h : 2 ^ 2 ≤ 2 ^ (compileAdvice (ceilLogTwo n)).t := Nat.pow_le_pow_right (by omega) ht2
  have h4 : (2 : Nat) ^ 2 = 4 := by decide
  omega

section Coupled

variable {n : Nat} (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)

/-- The audit start along every coupled word. Consumer: `widthStableRunInv`. -/
theorem widthFoldStart : ∀ (w : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) q).2.start = q.2.start := by
  intro w
  induction w with
  | nil => intro q; rfl
  | cons e rest ih => intro q; exact ih _

/-- The singleton class along every reference word. Consumer: `widthCleanRunStart`. -/
theorem widthSingletonFold (root : Fin n) : ∀ (w : List (Fin n)) (z : ref.State),
    ref.singleton root z → ref.singleton root (w.foldl ref.next z) := by
  intro w
  induction w with
  | nil => intro z hz; exact hz
  | cons e rest ih => intro z hz; exact ih _ (ref.singletonClosed root z hz e)

include hn in
/-- The run invariant along every coupled word. Consumer: `widthStableRunInv`. -/
theorem widthRunInvFold (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n) :
    ∀ (w : List (Fin n)) (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      WidthRunInv ring ref root lane src R q →
      WidthRunInv ring ref root lane src R
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) q) := by
  intro w
  induction w with
  | nil => intro q h; exact h
  | cons e rest ih =>
    intro q h
    exact ih _ (widthRunInvStep ring ref hn root lane src R hR hsrc hend q h e)

include hn in
/-- **The run invariant at a clean start** at a boundary reference: for the W fixed root of a
continuation and the first delimiter of the start, every interior pair has the audit invariants at
the audit start (`widthPairInvInitial` on the clean layout) and is complete there
(`pairInOfDelims`). Consumer: `widthStableRunInv`. -/
theorem widthCleanRunStart (root : Fin n)
    (lane : DigitLane) (start : ref.State) (hstart : ref.start start) (word0 : List (Fin n))
    (hW : WFixedRoot ring root (piW (ref.phys (word0.foldl ref.next start))))
    (first : Nat) (hf : DigitFirstDelimiter ring root (piD (ref.phys start)) first) (i : Nat)
    (hend : first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
      2 * digitSpan (compileAdvice (ceilLogTwo n)) < n) :
    2 ≤ first + i * digitSpan (compileAdvice (ceilLogTwo n)) ∧
      WidthRunInv ring ref root lane (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (digitSpan (compileAdvice (ceilLogTwo n)))
        (start, digitAuditInitial (piD (ref.phys start))) := by
  obtain ⟨root0, hs, hL⟩ := widthCleanBoundaryRoot ref start hstart
  have hsw := widthSingletonFold ring ref root0 word0 start hs
  have hfix := ref.singletonFixed root0 _ hsw
  have hr : root = root0 := hfix.2.1 root hW.1
  subst hr
  obtain ⟨first0, ht, -, hb⟩ := widthCleanBoundaryDelimiters ref hn root start hL
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hfe := firstDelimEq ring root (piD (ref.phys start)) first0 hb (by omega)
    (by have := hf.1.2.1; have := (hb _ hf.1.1 hf.1.2.1).1 hf.1.2.2; omega) first hf
  subst hfe
  have hR := widthBoundaryDigitSpanTwo hn
  have hlay : WidthCohortLayout ref.toWidthDigitReference root
      (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
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
    refine ⟨hL.1, ?_, ?_, ?_, fun k hk0 hk2 hkR => ?_⟩
    · exact (hb _ (by omega) (by omega)).2
        ⟨by omega, by rw [show first + m - first = m by omega]; exact hmR⟩
    · exact (hb _ (by omega) (by omega)).2
        ⟨by omega, by rw [show first + m + R - first = m + R by omega]; exact hm1⟩
    · exact (hb _ (by omega) (by omega)).2
        ⟨by omega, by rw [show first + m + 2 * R - first = m + 2 * R by omega]; exact hm2⟩
    · cases hbeta : (piD (ref.phys start) (digitSite ring root (first + m + k))).word.beta with
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
  refine ⟨by omega, widthPairInvInitial ring ref hn root lane _ _ start hlay, ?_⟩
  exact pairInOfDelims ring root (piD (ref.phys start)) first hb
    (i * digitSpan (compileAdvice (ceilLogTwo n))) (Nat.mul_mod_left i _) (by omega) hend
    (by omega)

include hn in
/-- **The run invariant at a values-stable state** on the comparison lane, at a boundary
reference. Consumer: `widthComparePairMoment`. -/
theorem widthStableRunInv (root : Fin n)
    (restart : Nat) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthStableRun ref.toWidthDigitReference root restart x) (first : Nat)
    (hf : DigitFirstDelimiter ring root x.2.start first) (i : Nat)
    (hend : first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
      2 * digitSpan (compileAdvice (ceilLogTwo n)) < n) :
    2 ≤ first + i * digitSpan (compileAdvice (ceilLogTwo n)) ∧
      WidthRunInv ring ref root DigitLane.comparison
        (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (digitSpan (compileAdvice (ceilLogTwo n))) x := by
  obtain ⟨start, word, _, hs, hfold, hW, -, -⟩ := hx
  have hst : x.2.start = piD (ref.phys start) := by
    rw [← hfold, widthFoldStart ring ref word]
    rfl
  have hW' : WFixedRoot ring root (piW (ref.phys (word.foldl ref.next start))) := by
    have h1 := widthAuditFoldFst ref.toWidthDigitReference word
      (start, digitAuditInitial (piD (ref.phys start)))
    rw [hfold] at h1
    rw [← h1]
    exact hW
  rw [hst] at hf
  obtain ⟨h2, hI⟩ := widthCleanRunStart ring ref hn root DigitLane.comparison start hs word
    hW' first hf i hend
  refine ⟨h2, ?_⟩
  rw [← hfold]
  have hR := widthBoundaryDigitSpanTwo hn
  exact widthRunInvFold ring ref hn root _ _ _ (by omega) h2 hend word _ hI

/-- **The comparison-lane stage obligation after the restart** at a boundary reference.
Consumer: `WidthCmpPairStageW`, `widthComparePairMoment`. -/
def WidthCmpPairStage (a b : Nat) : Prop :=
  ∀ (root : Fin n) (restart i first : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthStableRun ref.toWidthDigitReference root restart x →
    DigitFirstDelimiter ring root x.2.start first →
    first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
      2 * digitSpan (compileAdvice (ceilLogTwo n)) < n →
    ¬ WidthPairDoneC ring ref root DigitLane.comparison
      (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
      (digitSpan (compileAdvice (ceilLogTwo n))) restart x →
    MomentBoundQ (widthDigitAuditNext ref.toWidthDigitReference)
      (fun y => WidthPairDoneC ring ref root DigitLane.comparison
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (digitSpan (compileAdvice (ceilLogTwo n))) restart y ∨
        WidthLaneCutC ring ref root DigitLane.comparison
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (digitSpan (compileAdvice (ceilLogTwo n))) restart y)
      (n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) a b x

/-- **The comparison-lane stage obligation at a factor `w^B`, `B ≤ 3 C_r`**, at a boundary
reference. Consumer: `widthComparePairMoment`, `smallComparePairMoment`. -/
def WidthCmpPairStageW : Prop :=
  ∃ B, B ≤ 3 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) ∧
    WidthCmpPairStage ring ref
      ((n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) ^ B)
      ((n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1) - n) ^ B)

/-- A completion of the pair of the first delimiter after `restart` is `WidthComparePairDone`
(the first delimiter is unique). Consumer: `widthComparePairMoment`. -/
theorem widthCompareDoneOf (root : Fin n) (restart i first : Nat)
    (x y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hf : DigitFirstDelimiter ring root x.2.start first) (hy : y.2.start = x.2.start)
    (h : WidthPairDoneC ring ref root DigitLane.comparison
      (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
      (digitSpan (compileAdvice (ceilLogTwo n))) restart y) :
    WidthComparePairDone ref.toWidthDigitReference root restart i y := by
  intro f hf' _
  have he := L3.PacketMomentPairDone.firstDelimUnique ring root _ f first hf'
    (by rw [hy]; exact hf)
  subst he
  exact h

include hn in
/-- **`WidthComparePairMoment` at a boundary reference** (`N = widthPairMomentWidth n`) from the
comparison-lane stage obligation. Consumer: `smallComparePairMoment`. -/
theorem widthComparePairMoment
    (hst : WidthCmpPairStageW ring ref) :
    WidthComparePairMoment ref.toWidthDigitReference (widthPairMomentWidth n) := by
  obtain ⟨B, hB, hs⟩ := hst
  intro root restart i x hx hnd
  obtain ⟨first, hf, hend, hno⟩ : ∃ first, DigitFirstDelimiter ring root x.2.start first ∧
      first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
        2 * digitSpan (compileAdvice (ceilLogTwo n)) < n ∧
      ¬ WidthPairDoneC ring ref root DigitLane.comparison
        (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (digitSpan (compileAdvice (ceilLogTwo n))) restart x := by
    refine Classical.byContradiction fun hcon => hnd ?_
    intro first hf hend
    exact Classical.byContradiction fun hno => hcon ⟨first, hf, hend, hno⟩
  obtain ⟨h2, hI⟩ := widthStableRunInv ring ref hn root restart x hx first hf i hend
  have h3 := widthSpanThree hn
  have hq := widthPairMomentOfStageC ring ref hn root DigitLane.comparison _ _ h3 h2 hend restart
    x hI _ _ (hs root restart i first x hx hf hend hno)
  have hk := momentKeep (widthDigitAuditNext ref.toWidthDigitReference) _
    (fun y => y.2.start = x.2.start) _ _ _ (fun y e hy => hy) x rfl hq
  have hw := momentWeaken _ _ (WidthComparePairDone ref.toWidthDigitReference root restart i)
    _ _ _ (fun y hy => widthCompareDoneOf ring ref root restart i first x y hf hy.2 hy.1) x hk
  have hC : 20 ≤ bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) :=
    Nat.le_trans (by decide) (pairClockMid _ (by omega))
  show L3.PairMoment.MomentBound _ _
    (n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) 40 x
  have hab := stageFactor (n * (2 * bankRepairDigitPairClock
    (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) n _ B (by omega) hC (Nat.le_refl _) hB
  generalize bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) = C at hw hC hab ⊢
  have hNn : 0 < n * (2 * C + 1) - n := by
    have : n * 2 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  refine momentBoundOfQ _ _ _ _ _ 40 x (Nat.mul_pos (Nat.pow_pos hNn) (Nat.pow_pos hNn)) ?_ hw
  generalize (n * (2 * C + 1)) ^ B = a at hab ⊢
  generalize (n * (2 * C + 1) - n) ^ B = b at hab ⊢
  generalize (n * (2 * C + 1) - n) ^ C = p
  have h6 : 6 * a ≤ 40 * b := by omega
  have e1 : a * (6 * p) = 6 * a * p := by ac_rfl
  have e2 : 40 * (b * p) = 40 * b * p := by ac_rfl
  rw [e1, e2]
  exact Nat.mul_le_mul_right p h6

end Coupled

/-- **The headline premise `hcmpMomentSmall`** from the comparison-lane stage obligation at the
SMALL boundary reference. Consumer: `hcmpMomentSmall` of `l3HeadlineOfCleanBranches`
(HeadlineCleanAssembly). -/
theorem smallComparePairMoment {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hs : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hst : WidthCmpPairStageW ring (smallWidthBoundaryReference ring hn hs)) :
    WidthComparePairMoment (bandWidthDigitReference ring hn) (widthPairMomentWidth n) := by
  rw [bandWidthDigitReferenceSmall ring hn hs]
  exact widthComparePairMoment ring (smallWidthBoundaryReference ring hn hs) hn hst

end L3.WidthPacketMomentCompare

#print axioms L3.WidthPacketMomentCompare.bernoulliPow
#print axioms L3.WidthPacketMomentCompare.stageFactor
#print axioms L3.WidthPacketMomentCompare.widthSpanThree
#print axioms L3.WidthPacketMomentCompare.widthCleanRunStart
#print axioms L3.WidthPacketMomentCompare.widthStableRunInv
#print axioms L3.WidthPacketMomentCompare.widthCompareDoneOf
#print axioms L3.WidthPacketMomentCompare.widthComparePairMoment
#print axioms L3.WidthPacketMomentCompare.smallComparePairMoment
