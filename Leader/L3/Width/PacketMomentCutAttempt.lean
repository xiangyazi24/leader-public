import Leader.L3.Bank.RepairDigitPacketMomentCutAttempt
import Leader.L3.Width.PacketMomentCutCompletion
import Leader.L3.Width.PacketMomentAttempt

/-!
# Lemma e-packet with a cut at a boundary reference: the attempt loop of one pair

Generic form of the coupled part of `L3.PacketMomentCutAttempt` (BankRepairDigitPacketMomentCutAttempt)
at an arbitrary `WidthBoundaryReference` (`WidthAttemptInvC`, `widthAttemptInvStepC`, the entries,
`widthTrialRunMomentC`, `widthSuccessMomentC`, `widthRaceMomentC`, `widthPrepAttemptMomentC`,
`widthAttemptMomentC` with `attemptLoopWide`), and `widthAttemptMomentPairC`: the attempt loop at
`C = C_R` for every `R ≥ 3` through `L3.WidthPacketMoment.attemptLoopPair` (the SMALL slice `r = 3`).
Consumer: the SMALL comparison lane (`hcmpMomentSmall`).
-/

namespace L3.WidthPacketMomentCutAttempt

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortIdentity
open L3.CohortLedger
open L3.CohortSites
open L3.CohortWindow
open L3.Correspondence
open L3.DigitPacketQueue
open L3.DigitPacketQueueExport
open L3.DigitPacketTransport
open L3.GhostBridge
open L3.HClose
open L3.ValueLedger
open L3.WidthDigit
open L3.PacketMomentAfter
open L3.PacketMomentCarry
open L3.PacketMomentCells
open L3.PacketMomentFinish
open L3.PacketMomentGroupLabels
open L3.PacketMomentHeldQueue
open L3.PacketMomentLabels
open L3.PacketMomentPending
open L3.PacketMomentPrep
open L3.PacketMomentQueueLabels
open L3.PacketMomentTrialEnd
open L3.PacketMomentTrialLabels
open L3.PacketMomentU
open L3.PacketMomentV
open L3.PacketMomentVSerial
open L3.PacketMomentGroupCompletion
open L3.PacketMomentAttempt
open L3.PacketMomentCutLabels
open L3.PacketMomentCutCompletion
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentAudit
open L3.WidthPacketMomentCarry
open L3.WidthPacketMomentHeldQueue
open L3.WidthPacketMomentGroupCompletion
open L3.WidthPacketMomentQueue
open L3.WidthPacketMomentCutLabels
open L3.WidthPacketMomentCutCompletion
open L3.WidthPacketMomentAttempt

section Ported

variable {n : Nat} (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat)

include hn

/-- **The attempt class**: the audit invariants, the aligned queue with the window invariants,
the labelled queue, the reached-state queue invariant and the complete pair at the audit start.
Consumer: `attemptMoment` (the class `A` of `attemptLoopWide`). -/
def WidthAttemptInvC (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthPairInv ring ref root lane src R Base x ∧
    WinAligned R (widthLaneOfState ref.toWidthDigitReference root lane src R x) ∧
    WidthWinLabAtC ring ref root lane src R cut x ∧
    PacketQueue ring root lane src R (piD (ref.phys x.1)) x.2 ∧
    DigitCompletePair ring root x.2.start src (src + R)

/-- **Every coupled letter keeps the attempt class.** Consumer: every phase below and the failure
clause of `attemptMoment`. -/
theorem widthAttemptInvStepC (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInvC ring ref root lane src R Base cut x) (e : Fin n) :
    WidthAttemptInvC ring ref root lane src R Base cut (widthNxt ring ref x e) := by
  obtain ⟨hP, hw, hl, hq, hp⟩ := h
  have h1 := widthWinLabCoupledC ring ref hn root lane src R hR hsrc hend cut x e ⟨hP.1, hw, hl⟩
  have h2 := widthPacketQueueStep ring ref hn root lane src R hR hsrc hend x hP.1 hP.2.1 hq e
  exact ⟨widthPairInvStep ring ref hn root lane src R hR hsrc hend Base x hP e, h1.2.1, h1.2.2,
    h2.2.2, hp⟩

/-! ### Entering the labelled trial -/

/-- The labelled trial at index `m` with the held clause. Consumer: `trialRunMoment`. -/
def WidthTrialStartC (cut m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  VIAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) ∧
    (∃ χ, WidthHeldAt ring ref root lane src R x χ) ∧
    ∃ σ, LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
      LabelCut ring root lane src R cut (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
      LabTrial R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ

/-- **Entry into the labelled trial**: at a state of the attempt class without settled target
cells, aligned at index `a`, the labelled trial of index `vIdx R a 0` with the held clause.
Consumer: `trialStartOfPacketOnly`, `trialStartOfCleared`. -/
theorem widthTrialStartOfC (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInvC ring ref root lane src R Base cut x) (a : Nat)
    (hS : VShape R 0 (widthLaneOfState ref.toWidthDigitReference root lane src R x))
    (hA : AlignExt R a (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :
    WidthTrialStartC ring ref root lane src R cut (vIdx R a 0) x := by
  obtain ⟨σ, hL, hC, a', -, hL'⟩ := h.2.2.1
  have ha := extIdx R a a' _ σ hA hL'
  rw [← ha] at hL'
  have hrun : LabRun R (vIdx R a 0) (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ := by
    intro q hq1 hq2 hSq
    exfalso
    rcases (hS.2 q hq1 hq2).2.2 (by omega) with he | hp
    · rw [he] at hSq; cases hSq
    · revert hSq hp; cases (widthLaneOfState ref.toWidthDigitReference root lane src R x).inp q <;> simp [isSI, isPI]
  have hai : 0 + a + 1 ≤ R := by have := hA.2.1; omega
  exact ⟨⟨a, 0, hai, hA, hS, rfl⟩, widthHeldOfPacketQueue ring ref hn root lane src R x hS h.2.2.2.1,
    σ, hL, hC, a, 0, hai, hA, hS, rfl, hL', hrun⟩

/-- **Entry at the packet-only cut**, at an index `m ≥ 1`. Consumer: `prepAttemptMoment`. -/
theorem widthTrialStartOfPacketOnlyC (hR : 2 ≤ R) (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInvC ring ref root lane src R Base cut x)
    (hP : L3.PacketMomentRetire.PacketOnly R (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :
    ∃ m, 1 ≤ m ∧ WidthTrialStartC ring ref root lane src R cut m x := by
  obtain ⟨⟨a, hA⟩, -, -⟩ := h.2.1
  refine ⟨vIdx R a 0, by unfold vIdx; split <;> omega, ?_⟩
  exact widthTrialStartOfC ring ref hn root lane src R Base cut x h a (shapeOfPacketOnly R (by omega) _ hP) hA

/-- **Entry at the cleared window** after the front (`DoneW R (R - 1)`), at index `R - 1`.
Consumer: `raceMoment`. -/
theorem widthTrialStartOfClearedC (hR : 2 ≤ R) (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInvC ring ref root lane src R Base cut x)
    (hd : DoneW R (R - 1) (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :
    WidthTrialStartC ring ref root lane src R cut (R - 1) x := by
  have hS : VShape R 0 (widthLaneOfState ref.toWidthDigitReference root lane src R x) :=
    ⟨by omega, fun q h1 h2 => ⟨(hd.1 q h1 h2).1, fun hq => absurd hq (by omega),
      fun _ => (hd.1 q h1 h2).2⟩⟩
  have ht := widthTrialStartOfC ring ref hn root lane src R Base cut x h (R - 1) hS hd.2.1
  have e : vIdx R (R - 1) 0 = R - 1 := by unfold vIdx; split <;> omega
  rw [e] at ht
  exact ht

/-! ### The trial and the two outcomes -/

/-- The trial at index `m` (or its outcome) with the held clause, the labels and the attempt
class. Consumer: `trialRunMoment`, `successMoment`, `prepAttemptMoment`. -/
def WidthTrialRunC (Base : Bool → DigitAtom n → Prop) (cut : Nat) (m : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthHeldTrial ring ref root lane src R m y ∧
    (WidthCohortLayout ref.toWidthDigitReference root src R y.1 ∧ WidthTrialLabAtC ring ref root lane src R cut m y) ∧
    WidthAttemptInvC ring ref root lane src R Base cut y

/-- **The labelled trial with the held clause reaches its outcome** `VTA R m` with all the
invariants, with the bound of `vAlignAtCoupled`. Consumer: `prepAttemptMoment`. -/
theorem widthTrialRunMomentC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop) (cut : Nat) (m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInvC ring ref root lane src R Base cut x)
    (ht : WidthTrialStartC ring ref root lane src R cut m x) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (fun y => VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
        WidthTrialRunC ring ref root lane src R Base cut m y) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x := by
  obtain ⟨hs, ⟨χ, hq⟩, σ, hL, hC, hlt⟩ := ht
  exact momentKeepUntil (widthDigitAuditNext (ref.toWidthDigitReference))
    (fun y => VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y))
    (WidthTrialRunC ring ref root lane src R Base cut m) N _ _
    (fun y e hy hnt => by
      have hvi : VIAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) := by
        rcases hy.1.2.2.1 with hv | hv
        · exact hv
        · exact absurd hv hnt
      exact ⟨widthHeldTrialStep ring ref hn root lane src R hR hsrc hend m y e hy.1 hnt,
        widthTrialLabCoupledC ring ref hn root lane src R hR hsrc hend cut m y e hy.2.1
          (viNotVtAt R m _ hvi),
        widthAttemptInvStepC ring ref hn root lane src R (by omega) hsrc hend Base cut y hy.2.2 e⟩) x
    ⟨⟨h.1.1, h.1.2.1, Or.inl hs, χ, hq⟩, ⟨h.1.1, σ, hL, hC, labTrialRun hlt, Or.inl hlt⟩, h⟩
    (widthVAlignAt ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend N hN hR m x h.1.1 hs)

/-- The first `DigitCompletion` of the pair `(src, src + R)` with cut `0`. Consumer:
`attemptMoment` (the target `P`). -/
def WidthPairDoneC (cut : Nat) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  ∃ U, DigitCompletion ring x.2 root src (src + R) lane cut U

/-- **The aligned outcome is finished**: `E[z^T] ≤ w^{R+1}`. Consumer: the second alternative
of `attemptMoment`'s outcome clause. -/
theorem widthSuccessMomentC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hv : VTA R (R - 1) (widthLaneOfState ref.toWidthDigitReference root lane src R y))
    (h : WidthTrialRunC ring ref root lane src R Base cut (R - 1) y) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (WidthPairDoneC ring ref root lane src R cut) N (N ^ (R + 1)) ((N - n) ^ (R + 1)) y := by
  obtain ⟨⟨-, -, -, χ, hq⟩, ⟨-, hlab⟩, hA⟩ := h
  exact widthGroupDoneMomentC ring ref hn root lane src R (by omega) cut hsrc hend N hN Base y hA.1 hv.1 χ
    hq hlab hA.2.2.2.2

/-- **The outgoing race edge to the completion**: from a misaligned outcome `VTA R m`
(`1 ≤ m ≤ R - 2`) in the attempt class, after the outgoing race edge the front clears the window
(`w^R`), the cleared window is the labelled trial of index `R - 1` with the held clause, which
ends aligned and is finished (`alignedMoment`): `E[z^T] ≤ w^{R + ((R+2)(2R+2) + (R+1))}`.
Consumer: the race alternative of `attemptMoment`'s outcome clause (`F_a`). -/
theorem widthRaceMomentC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (m : Nat)
    (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R) (N : Nat) (hN : n < N) (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hv : VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R x))
    (h : WidthAttemptInvC ring ref root lane src R Base cut x) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (WidthPairDoneC ring ref root lane src R cut) N
      (N ^ R * (N ^ ((R + 2) * vK R) * N ^ (R + 1)))
      ((N - n) ^ R * ((N - n) ^ ((R + 2) * vK R) * (N - n) ^ (R + 1)))
      (widthNxt ring ref x (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))) := by
  obtain ⟨hl0, hfi⟩ := widthFrontOfRace ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend (R - 1) m hR
    hm1 hm2 x h.1.1 hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  have hF := momentKeep (widthDigitAuditNext (ref.toWidthDigitReference)) _
    (WidthAttemptInvC ring ref root lane src R Base cut) N _ _
    (fun y e hy => widthAttemptInvStepC ring ref hn root lane src R (by omega) hsrc hend Base cut y hy e) _
    (widthAttemptInvStepC ring ref hn root lane src R (by omega) hsrc hend Base cut x h _)
    (widthFrontMoment ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend N hN (R - 1) (by omega) _ hl0 hfi)
  refine momentSeq _ _ _ N _ _ _ _ _ (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.sub_le N n) _)
    (Nat.pow_le_pow_left (Nat.sub_le N n) _)) (fun y hy => ?_) hF
  obtain ⟨hd, hy'⟩ := hy
  obtain ⟨hs, ⟨χ, hq⟩, σ, hL, hC, ht⟩ :=
    widthTrialStartOfClearedC ring ref hn root lane src R (by omega) Base cut y hy' hd
  exact widthAlignedMomentC ring ref hn root lane src R hR cut hsrc hend N hN Base y hy'.1 hy'.2.2.2.2 hs χ
    hq σ hL hC ht

/-- **The preparation of one attempt**: from the attempt class, phases U and retirement reach the
packet-only cut (`prepCutCoupled`), whose trial with the held clause and the labels ends at an
outcome `VTA R m`, `m ≥ 1`, with all the invariants:
`E[z^T] ≤ w^{uBudget R + 2R + (R+2)(2R+2)}`. Consumer: `attemptMoment` (`hprep`). -/
theorem widthPrepAttemptMomentC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInvC ring ref root lane src R Base cut x) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (fun y => ∃ m, 1 ≤ m ∧ VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
        WidthTrialRunC ring ref root lane src R Base cut m y) N
      (N ^ uBudget R * N ^ (2 * R) * N ^ ((R + 2) * vK R))
      ((N - n) ^ uBudget R * (N - n) ^ (2 * R) * (N - n) ^ ((R + 2) * vK R)) x := by
  have hcut := momentKeep (widthDigitAuditNext (ref.toWidthDigitReference)) _
    (WidthAttemptInvC ring ref root lane src R Base cut) N _ _
    (fun y e hy => widthAttemptInvStepC ring ref hn root lane src R (by omega) hsrc hend Base cut y hy e) x
    h (widthPrepCut ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend N hN hR x h.1.1 h.2.1)
  refine momentSeq _ _ _ N _ _ _ _ x (Nat.pow_le_pow_left (Nat.sub_le N n) _)
    (fun y hy => ?_) hcut
  obtain ⟨⟨hP, -⟩, hy⟩ := hy
  obtain ⟨m, hm, hts⟩ := widthTrialStartOfPacketOnlyC ring ref hn root lane src R (by omega) Base cut y hy hP
  exact momentWeaken _ _ _ N _ _ (fun z hz => ⟨m, hm, hz⟩) y
    (widthTrialRunMomentC ring ref hn root lane src R hR hsrc hend N hN Base cut m y hy hts)

/-! ### The attempt loop -/

/-- **The attempt loop of one pair.** At a width `N ≥ n (2C + 1)` with `C ≥ 4000` and the three
budgets inside `C` (`B_p ≤ C`, `R + 1 ≤ C`, `11 B_a ≤ 2C + 1`), from every state of the attempt
class the first `DigitCompletion` of the pair `(src, src + R)` with cut `0` has `E[z^τ] ≤ 6`,
`z = N / (N - n)`. Inputs of `attemptLoopWide`: preparation `prepAttemptMoment`; at an outcome
`VTA R m`: `m = R - 1` is finished (`successMoment`), `1 ≤ m ≤ R - 2` races, with
`Pend = VTA R m ∧ AttemptInv` kept off the race edges (`raceAlignStep`, `attemptInvStep`), the
outgoing edge to the completion (`raceMoment`) and the incoming edge back in the attempt class
(`attemptInvStep`). Consumer: the per-pair moment (`WidthStrictPairMoment` at BANK). -/
theorem widthAttemptMomentC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N C : Nat)
    (hC : 4000 ≤ C) (hNC : n * (2 * C + 1) ≤ N) (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (hBp : uBudget R + 2 * R + (R + 2) * vK R ≤ C) (hBs : R + 1 ≤ C)
    (hBa : 11 * (R + ((R + 2) * vK R + (R + 1))) ≤ 2 * C + 1) :
    ∀ x, WidthAttemptInvC ring ref root lane src R Base cut x →
      MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
        (WidthPairDoneC ring ref root lane src R cut) N (6 * (N - n) ^ C) ((N - n) ^ C) x := by
  have hN : n < N := by
    have : n * 2 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  refine L3.PacketMomentWide.attemptLoopWide (widthDigitAuditNext (ref.toWidthDigitReference))
    (WidthPairDoneC ring ref root lane src R cut) (WidthAttemptInvC ring ref root lane src R Base cut)
    (fun y => ∃ m, 1 ≤ m ∧ VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
      WidthTrialRunC ring ref root lane src R Base cut m y)
    N C (uBudget R + 2 * R + (R + 2) * vK R) (R + 1) (R + ((R + 2) * vK R + (R + 1)))
    (by omega) hC hNC hBp hBs hBa
    (fun x hx => powSplitL _ _ N _ _ _ x
      (widthPrepAttemptMomentC ring ref hn root lane src R hR hsrc hend N hN Base cut x hx)) ?_
  intro y hy
  obtain ⟨m, hm, hv, hr⟩ := hy
  by_cases hmR : m = R - 1
  · rw [hmR] at hv hr
    exact Or.inr (Or.inl (widthSuccessMomentC ring ref hn root lane src R hR hsrc hend N hN Base cut y hv hr))
  · have hm2 : m + 2 ≤ R := by have := hv.1.1; omega
    refine Or.inr (Or.inr ⟨fun z => VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R z) ∧
        WidthAttemptInvC ring ref root lane src R Base cut z,
      L3.DigitPacketRace.raceOut ring root src R (R - 1 - m),
      L3.DigitPacketRace.raceIn ring root src R (R - 1 - m), ⟨hv, hr.2.2⟩,
      fun he => L3.DigitPacketRace.raceInNe ring root src R (R - 1 - m) (by omega) (by omega)
        he.symm, ?_, ?_, ?_⟩)
    · intro z hz _ e ha hb
      exact ⟨(widthRaceAlignStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend m hR hm hm2 z hz.2.1.1 hz.1 e
        hb ha).2, widthAttemptInvStepC ring ref hn root lane src R (by omega) hsrc hend Base cut z hz.2 e⟩
    · intro z hz _
      exact powSplitR _ _ N _ _ _ _
        (widthRaceMomentC ring ref hn root lane src R hR hsrc hend m hm hm2 N hN Base cut z hz.1 hz.2)
    · intro z hz _
      exact widthAttemptInvStepC ring ref hn root lane src R (by omega) hsrc hend Base cut z hz.2 _

/-- **The attempt loop of one pair at the pair clock**, every `R ≥ 3`: `C = C_R`,
`N ≥ n (2 C_R + 1)`, through `L3.WidthPacketMoment.attemptLoopPair` (the block form of the
attempt loop; covers the SMALL slice `r = 3` that `attemptLoopWide`, `C ≥ 4000`, does not). From
every state of the attempt class the first `DigitCompletion` of the pair `(src, src + R)` with cut
`cut` has `E[z^τ] ≤ 6`. Consumer: the per-pair moment of the comparison lane at a boundary reference (SMALL,
`hcmpMomentSmall`). -/
theorem widthAttemptMomentPairC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hNC : n * (2 * bankRepairDigitPairClock R + 1) ≤ N) (Base : Bool → DigitAtom n → Prop) (cut : Nat) :
    ∀ x, WidthAttemptInvC ring ref root lane src R Base cut x →
      MomentBoundQ (widthDigitAuditNext ref.toWidthDigitReference)
        (WidthPairDoneC ring ref root lane src R cut) N
        (6 * (N - n) ^ bankRepairDigitPairClock R) ((N - n) ^ bankRepairDigitPairClock R) x := by
  have hC : 1 ≤ bankRepairDigitPairClock R := Nat.le_trans (by omega) (successBudgetLe R)
  have hN : n < N := by
    have : n * 2 ≤ n * (2 * bankRepairDigitPairClock R + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  have hBa : afterBudget R + (R + 1) = R + ((R + 2) * vK R + (R + 1)) := by
    unfold afterBudget; omega
  refine attemptLoopPair (widthDigitAuditNext ref.toWidthDigitReference)
    (WidthPairDoneC ring ref root lane src R cut) (WidthAttemptInvC ring ref root lane src R Base cut)
    (fun y => ∃ m, 1 ≤ m ∧ VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
      WidthTrialRunC ring ref root lane src R Base cut m y)
    N R (by omega) hR hNC
    (fun x hx => powSplitL _ _ N _ _ _ x
      (widthPrepAttemptMomentC ring ref hn root lane src R hR hsrc hend N hN Base cut x hx)) ?_
  intro y hy
  obtain ⟨m, hm, hv, hr⟩ := hy
  by_cases hmR : m = R - 1
  · rw [hmR] at hv hr
    exact Or.inr (Or.inl (widthSuccessMomentC ring ref hn root lane src R hR hsrc hend N hN Base cut y hv hr))
  · have hm2 : m + 2 ≤ R := by have := hv.1.1; omega
    refine Or.inr (Or.inr ⟨fun z => VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R z) ∧
        WidthAttemptInvC ring ref root lane src R Base cut z,
      L3.DigitPacketRace.raceOut ring root src R (R - 1 - m),
      L3.DigitPacketRace.raceIn ring root src R (R - 1 - m), ⟨hv, hr.2.2⟩,
      fun he => L3.DigitPacketRace.raceInNe ring root src R (R - 1 - m) (by omega) (by omega)
        he.symm, ?_, ?_, ?_⟩)
    · intro z hz _ e ha hb
      exact ⟨(widthRaceAlignStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc
        hend m hR hm hm2 z hz.2.1.1 hz.1 e hb ha).2,
        widthAttemptInvStepC ring ref hn root lane src R (by omega) hsrc hend Base cut z hz.2 e⟩
    · intro z hz _
      rw [hBa]
      exact powSplitR _ _ N _ _ _ _
        (widthRaceMomentC ring ref hn root lane src R hR hsrc hend m hm hm2 N hN Base cut z hz.1 hz.2)
    · intro z hz _
      exact widthAttemptInvStepC ring ref hn root lane src R (by omega) hsrc hend Base cut z hz.2 _

end Ported

end L3.WidthPacketMomentCutAttempt

#print axioms L3.WidthPacketMomentCutAttempt.widthAttemptInvStepC
#print axioms L3.WidthPacketMomentCutAttempt.widthTrialStartOfC
#print axioms L3.WidthPacketMomentCutAttempt.widthTrialStartOfPacketOnlyC
#print axioms L3.WidthPacketMomentCutAttempt.widthTrialStartOfClearedC
#print axioms L3.WidthPacketMomentCutAttempt.widthTrialRunMomentC
#print axioms L3.WidthPacketMomentCutAttempt.widthSuccessMomentC
#print axioms L3.WidthPacketMomentCutAttempt.widthRaceMomentC
#print axioms L3.WidthPacketMomentCutAttempt.widthPrepAttemptMomentC
#print axioms L3.WidthPacketMomentCutAttempt.widthAttemptMomentC
#print axioms L3.WidthPacketMomentCutAttempt.widthAttemptMomentPairC
