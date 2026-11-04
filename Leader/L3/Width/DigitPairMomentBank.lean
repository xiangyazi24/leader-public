import Leader.L3.Width.DigitPairMomentPremise
import Leader.L3.Bank.RepairDigitStructuralFit

/-!
# BANK: the structural clock from per-pair exponential moments, and its 201 fit

`widthStructuralClockOfMoments` is `widthStructuralClockOfPairs` with Lemma e-max done as in
the paper: the `2 n` (pair, lane) obligations each have `E[z^T] ≤ 40`
(`WidthStrictPairMoment`, `z = N / (N-1)`, `N = widthPairMomentWidth n = n (2 C_r + 1)`), the
union bound and the discrete Jensen inequality of `L3.PairMoment.simultaneousOfMomentBlocks`
give all of them at expected cost `N (L + 6)` (`L = ceilLogTwo n`; `80 n 2^{L+6} ≤ 5^{L+6}`,
`pairMomentCount`), so the structural stage is charged `2 N (L + 6)` (doubled units).

`momentLedgerFit` (replaces `structuralLedgerFit` on this route): the six BANK charges with
this structural charge total at most `201 n^2`.  Since `2 C_r + 1 ≤ h(r)` and
`L + 6 ≤ 3 (L + 3)`, the new structural charge is at most the old one
(`momentStructuralChargeLe`), and the old total fits by `structuralLedgerFit`.
-/

namespace L3.PairMomentBank

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open LeaderCountDyadicTail
open L3.CohortTail
open L3.CohortSites
open L3.FiveTransfer
open L3.ValueWaveClose
open L3.WidthDigit
open L3.DigitPairsClean
open L3.DigitStructuralClean
open L3.DigitCohortScratch
open L3.PairMomentPremise

set_option autoImplicit false

/-- `2 n · 40 · 2^{L+6} ≤ 5^{L+6}` for `L = ceilLogTwo n`: the block horizon of the `2 n`
obligations. Consumer: `widthStructuralClockOfMoments`. -/
theorem pairMomentCount {n : Nat} (hn : 5 ≤ n) :
    2 * n * 40 * 2 ^ (ceilLogTwo n + 6) ≤ 5 ^ (ceilLogTwo n + 6) := by
  have hL := (ceilLogTwo_spec n (by omega)).2
  generalize ceilLogTwo n = L at hL
  have h4 : 4 ^ L ≤ 5 ^ L := Nat.pow_le_pow_left (by omega) L
  have h22 : 2 ^ L * 2 ^ L = 4 ^ L := by
    rw [← Nat.mul_pow]
  have e1 : 2 * n * 40 * 2 ^ (L + 6) = 5120 * (n * 2 ^ L) := by
    rw [Nat.pow_add]; grind
  have e2 : 5 ^ (L + 6) = 15625 * 5 ^ L := by
    rw [Nat.pow_add]; grind
  have h1 : n * 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul_right _ hL
  rw [e1, e2]
  omega

section Bank

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- **The structural clock on BANK from per-pair exponential moments** (Lemma e-max as
in repair.tex 1421-1465): if every interior pair on both lanes has `E[z^T] ≤ 40` from every
first-zero continuation of the clean audit (`WidthStrictPairMoment` at
`N = widthPairMomentWidth n`), the first hit of the clean structural cut from the clean
first-zero cut costs at most `2 N (ceilLogTwo n + 6)` (doubled units).  Consumer:
`L3.WriterCore.bankWriterValueWaveOfMoments`. -/
theorem widthStructuralClockOfMoments
    (hmom : WidthStrictPairMoment (bankWidthDigitReference ring hn hbank)
      (widthPairMomentWidth n)) :
    WidthDigitStructuralClock (bankWidthDigitReference ring hn hbank)
      (2 * (widthPairMomentWidth n * (ceilLogTwo n + 6))) := by
  intro z hz T
  obtain ⟨start, word, root, audit, retired, ⟨hD, hC⟩, hfold, hW, hDA, hcov, hBd, -⟩ := hz
  have hfold' : word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) := hfold
  have hP0 : scratchClass ring hn hbank root (z, audit) (z, audit) := ⟨⟨start, word, [], (z, audit), retired, ⟨hD, hC⟩, hfold, hW, hDA,
    hcov, hBd, rfl⟩, [], rfl⟩
  have hcl : ∀ x e, scratchClass ring hn hbank root (z, audit) x →
      scratchClass ring hn hbank root (z, audit) (bankRepairDigitBoundaryAuditNext ring hbank x e) := by
    rintro x e ⟨hx, w, rfl⟩
    exact ⟨widthZeroRunStep (bankWidthDigitReference ring hn hbank) root _ hx e, w ++ [e],
      by rw [List.foldl_append]; rfl⟩
  have hsim : 2 * costNumerator (bankRepairDigitBoundaryAuditNext ring hbank)
      (fun y => ∀ d, scratchGood ring hn hbank root d y) (z, audit) T ≤
      n ^ T * (2 * (widthPairMomentWidth n * (ceilLogTwo n + 6))) := by
    have h := L3.PairMoment.simultaneousOfMomentBlocks (bankRepairDigitBoundaryAuditNext ring hbank)
      (scratchGood ring hn hbank root) (widthPairMomentWidth n) 40 (ceilLogTwo n + 6)
      (widthPairMomentWidthTwo (by omega))
      (fun d x e h => widthPairDoneStep (bankWidthDigitReference ring hn hbank) root _ _ x e h)
      (z, audit) (fun d hng => hmom root _ _ (z, audit) hP0.1 hng) (pairMomentCount hn) T
    rw [Nat.mul_left_comm]
    exact Nat.mul_le_mul_left 2 h
  -- the singleton root and the delimiter layout of the start
  obtain ⟨root0, hs, hV⟩ := bankCleanBoundaryRoot ring hbank start hD hC
  have hsz := bankRepairDigitSingletonWordFold ring hn hbank root0 word start hs
  have hz1 : z = word.foldl (bankRepairNext ring hbank) start := by
    have := bankRepairDigitBoundaryAuditFirst ring hbank start
      (digitAuditInitial (piD start.val.1)) word
    rw [hfold'] at this
    exact this
  have hW' : WFixedRoot ring root (piW (word.foldl (bankRepairNext ring hbank) start).val.1) := by
    rw [← hz1]; exact hW
  have hr : root = root0 := hsz.2.2.1 root hW'.1
  subst hr
  obtain ⟨first0, ht, -, hb⟩ := bankCleanBoundaryDelimiters ring hbank hn root start hV
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hR := valueSpanTwo hn
  -- the all-done coupled states are structural cuts
  have hB : ∀ x, (scratchClass ring hn hbank root (z, audit) x ∧
      ∀ d, scratchGood ring hn hbank root d x) →
      WidthDigitStructuralCut (bankWidthDigitReference ring hn hbank) x.1 := by
    rintro x ⟨⟨-, w, hw⟩, hgood⟩
    have hxfold : (word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1)) = x := by
      rw [List.foldl_append, hfold']
      exact hw.symm
    have hx1 : x.1 = (word ++ w).foldl (bankRepairNext ring hbank) start := by
      rw [← hxfold]
      exact bankRepairDigitBoundaryAuditFirst ring hbank start _ (word ++ w)
    have hinv := bankRepairDigitBoundaryAuditInvariantRun ring hn hbank root start hs (word ++ w)
    rw [hxfold] at hinv
    have hstartx : x.2.start = piD start.val.1 := by
      rw [← hxfold]
      exact bankAuditStart ring hbank (word ++ w) _
    have hsubf : ∀ f, f ∈ audit.frames → f ∈ x.2.frames := by
      intro f hf
      rw [hw]
      exact bankRepairDigitZeroFramesWord ring hbank w (z, audit) f hf
    have hclk : audit.clock ≤ x.2.clock := by
      rw [hw, bankRepairDigitZeroClockWord ring hbank w]
      exact Nat.le_add_right _ _
    have haudst : audit.start = piD start.val.1 := by
      have := bankAuditStart ring hbank word (start, digitAuditInitial (piD start.val.1))
      rw [hfold'] at this
      exact this
    -- the structural predicate at the current clock
    have hSA : DigitStructuralAt ring root x.2 x.2.clock := by
      refine ⟨Nat.le_refl _, fun source target lane hpair => ?_⟩
      rw [hstartx] at hpair
      obtain ⟨⟨⟨hs0, hsn, hsb⟩, -, -, -, -⟩, -⟩ := hpair.1
      obtain ⟨hfs, hmod⟩ := (hb source hs0 hsn).1 hsb
      have htg := hpair.2.1
      have hend2 := hpair.2.2.2
      generalize hRv : valueSpan n = R at hR
      have hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R := hRv
      rw [hRd] at hmod htg hend2
      have hsrc : source = first0 + (source - first0) / R * R := by
        have := Nat.div_add_mod (source - first0) R
        rw [hmod, Nat.add_zero, Nat.mul_comm] at this
        omega
      generalize (source - first0) / R = i at hsrc
      have hiR : i ≤ i * R := Nat.le_mul_of_pos_right i (by omega)
      have hin : i < n := by omega
      obtain ⟨hdiv, hlane⟩ := laneDecode i lane
      have hidx : 2 * i + laneCode lane < 2 * n := by
        cases lane
        · show 2 * i + 0 < 2 * n
          omega
        · show 2 * i + 1 < 2 * n
          omega
      have hg' : WidthPairDone (bankWidthDigitReference ring hn hbank) root i lane x := by
        have h1 : WidthPairDone (bankWidthDigitReference ring hn hbank) root
            ((2 * i + laneCode lane) / 2) (laneOf (2 * i + laneCode lane)) x :=
          hgood ⟨2 * i + laneCode lane, hidx⟩
        rw [hdiv, hlane] at h1
        exact h1
      have hfd : DigitFirstDelimiter ring root x.2.start first0 := by
        rw [hstartx]
        exact firstDelimOf ring root (piD start.val.1) first0 hb (by omega)
          (by omega)
      have hc := hg' first0 hfd (by rw [hRv]; omega)
      rw [hRv, ← hsrc] at hc
      rw [htg]
      obtain ⟨tm, htm⟩ := firstStrictOfCompletion ring x.2 root source (source + R) lane 0 hc
      exact ⟨tm, htm, htm.1.2.2.2.2.2.1⟩
    obtain ⟨structural, hst, hmin⟩ := existsFirst (DigitStructuralAt ring root x.2) ⟨_, hSA⟩
    refine ⟨start, word ++ w, root, x.2, retired, audit.clock, structural, ⟨hD, hC⟩, hxfold, ?_,
      hinv.2.1, ?_, digitBoundaryAtMono ring root audit x.2 (by rw [hstartx, haudst]) hsubf retired hBd,
      ⟨hst, hmin⟩⟩
    · show WFixedRoot ring root (piW x.1.val.1)
      rw [hx1]
      exact bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root start hs (word ++ w)
    · exact coversExtend ring root audit x.2 (by rw [hstartx, haudst]) hsubf hclk 0 retired
        audit.clock hcov
  have hstop := costNumeratorTargetOnClosed (bankRepairDigitBoundaryAuditNext ring hbank)
    (scratchClass ring hn hbank root (z, audit))
    (fun x => scratchClass ring hn hbank root (z, audit) x ∧ ∀ d, scratchGood ring hn hbank root d x)
    (fun y => ∀ d, scratchGood ring hn hbank root d y) (fun x hx e => hcl x e hx)
    (fun x hx hq => ⟨hx, hq⟩) T (z, audit) hP0
  have hproj := L3.Projection.costProjectLe (bankRepairNext ring hbank)
    (bankRepairDigitBoundaryAuditNext ring hbank) Prod.fst (fun _ _ => rfl)
    (WidthDigitStructuralCut (bankWidthDigitReference ring hn hbank))
    (fun x => scratchClass ring hn hbank root (z, audit) x ∧ ∀ d, scratchGood ring hn hbank root d x)
    hB (z, audit) T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.le_trans hproj hstop)) hsim

end Bank

/-- The moment structural charge is at most the first-moment one:
`2 N (L + 6) ≤ 3 ((L + 3) (2 n h(r))) + 2`, from `2 C_r + 1 ≤ h(r)` and `L + 6 ≤ 3 (L + 3)`.
Consumer: `momentLedgerFit`. -/
theorem momentStructuralChargeLe {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 * (widthPairMomentWidth n * (ceilLogTwo n + 6)) ≤
      3 * ((ceilLogTwo n + 3) * (2 * (n * bankRepairDigitPairEnvelope
        (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)))))) + 2 := by
  have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
  have ht : (compileAdvice (ceilLogTwo n)).t = ceilLogTwo (ceilLogTwo n) :=
    compileAdvice_t_large _ (by omega)
  unfold widthPairMomentWidth
  rw [ht]
  generalize bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)) = r
  generalize ceilLogTwo n = L
  have hCh : 2 * bankRepairDigitPairClock r + 1 ≤ bankRepairDigitPairEnvelope r := by
    unfold bankRepairDigitPairClock bankRepairDigitPairEnvelope
    omega
  have h1 : n * (2 * bankRepairDigitPairClock r + 1) ≤ n * bankRepairDigitPairEnvelope r :=
    Nat.mul_le_mul_left n hCh
  have h2 : n * (2 * bankRepairDigitPairClock r + 1) * (L + 6) ≤
      n * bankRepairDigitPairEnvelope r * (3 * (L + 3)) :=
    Nat.mul_le_mul h1 (by omega)
  have e : 3 * ((L + 3) * (2 * (n * bankRepairDigitPairEnvelope r))) =
      2 * (n * bankRepairDigitPairEnvelope r * (3 * (L + 3))) := by grind
  rw [e]
  omega

/-- **The BANK ledger with the moment structural clock fits 201**: boundary, first zero, the
structural charge `2 N (L + 6)` of `widthStructuralClockOfMoments`, the entry charge
`6 n (5 R + 2 + L)`, the `200 n^2` wave and the comparison stage total at most `201 n^2`.
Replaces `structuralLedgerFit` on the moment route.  Consumer:
`L3.WriterCore.bankWriterDigitHalfOfMoment`. -/
theorem momentLedgerFit {n : Nat} (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n +
        2 * (widthPairMomentWidth n * (ceilLogTwo n + 6)) +
        6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) +
        bankRepairDigitValueWaveMicroCharge n + bankRepairDigitComparisonMicroCharge n ≤
      201 * n ^ 2 := by
  have h := L3.DigitStructuralFit.structuralLedgerFit hn hbank
  have hle := momentStructuralChargeLe hbank
  omega

end L3.PairMomentBank

#print axioms L3.PairMomentBank.pairMomentCount
#print axioms L3.PairMomentBank.widthStructuralClockOfMoments
#print axioms L3.PairMomentBank.momentStructuralChargeLe
#print axioms L3.PairMomentBank.momentLedgerFit
