import Leader.L3.Bank.RepairDigitPacketMomentAttempt
import Leader.L3.Width.PacketMomentGroupCompletion
import Leader.L3.Width.PacketMomentQueue
import Leader.L3.Width.PacketMomentPairLoop

/-!
# Lemma e-packet at a boundary reference: the attempt loop of one pair

Generic form of the coupled part of `L3.PacketMomentAttempt` (BankRepairDigitPacketMomentAttempt)
at an arbitrary `WidthBoundaryReference`: the attempt class `WidthAttemptInv` (kept by every letter,
`widthAttemptInvStep`, with `L3.WidthPacketMomentQueue.widthPacketQueueStep`), the entries into the
labelled trial, `widthTrialRunMoment`, `widthSuccessMoment`, `widthRaceMoment`,
`widthPrepAttemptMoment`, `widthAttemptMoment` (`attemptLoopWide`, `C ≥ 4000`), and
`widthAttemptMomentPair` (`attemptLoopPair` at `C = C_R`, every `R ≥ 3`; the SMALL slice `r = 3`).
The phases are `L3.WidthPacketMoment.widthVAlignAt`, `widthFrontOfRace`, `widthFrontMoment`,
`widthPrepCut`, `widthRaceAlignStep`. `powSplitL`, `powSplitR` are used as they are.
-/

namespace L3.WidthPacketMomentAttempt

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

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
open L3.PacketMomentU
open L3.PacketMomentRetire
open L3.PacketMomentV
open L3.PacketMomentVSerial
open L3.PacketMomentFinish
open L3.PacketMomentAfter
open L3.PacketMomentPending
open L3.PacketMomentCells
open L3.PacketMomentLabels
open L3.PacketMomentQueueLabels
open L3.DigitPacketQueueExport
open L3.PacketMomentTrialLabels
open L3.PacketMomentGroupLabels
open L3.PacketMomentTrialEnd
open L3.PacketMomentHeldQueue
open L3.PacketMomentGroupCompletion
open L3.PacketMomentAttempt
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentAudit
open L3.WidthPacketMomentHeldQueue
open L3.WidthPacketMomentGroupCompletion
open L3.WidthPacketMomentQueue

section Ported

variable {n : Nat} (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat)

include hn

/-! ### The attempt class -/

/-- **The attempt class**: the audit invariants, the aligned queue with the window invariants,
the labelled queue, the reached-state queue invariant and the complete pair at the audit start.
Consumer: `widthAttemptMoment` (the class `A` of `attemptLoopWide`). -/
def WidthAttemptInv (Base : Bool → DigitAtom n → Prop)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthPairInv ring ref root lane src R Base x ∧
    WinAligned R (widthLaneOfState ref.toWidthDigitReference root lane src R x) ∧
    WidthWinLabAt ring ref root lane src R x ∧
    PacketQueue ring root lane src R (piD (ref.phys x.1)) x.2 ∧
    DigitCompletePair ring root x.2.start src (src + R)

/-- **Every coupled letter keeps the attempt class.** Consumer: every phase below and the failure
clause of `widthAttemptMoment`. -/
theorem widthAttemptInvStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (Base : Bool → DigitAtom n → Prop)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInv ring ref root lane src R Base x) (e : Fin n) :
    WidthAttemptInv ring ref root lane src R Base (widthNxt ring ref x e) := by
  obtain ⟨hP, hw, hl, hq, hp⟩ := h
  have h1 := widthWinLabCoupled ring ref hn root lane src R hR hsrc hend x e ⟨hP.1, hw, hl⟩
  have h2 := widthPacketQueueStep ring ref hn root lane src R hR hsrc hend x hP.1 hP.2.1 hq e
  exact ⟨widthPairInvStep ring ref hn root lane src R hR hsrc hend Base x hP e, h1.2.1, h1.2.2,
    h2.2.2, hp⟩

/-! ### Entering the labelled trial -/

/-- The labelled trial at index `m` with the held clause. Consumer: `widthTrialRunMoment`. -/
def WidthTrialStart (m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  VIAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) ∧
    (∃ χ, WidthHeldAt ring ref root lane src R x χ) ∧
    ∃ σ, LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
      LabTrial R m (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ

/-- **Entry into the labelled trial**: at a state of the attempt class without settled target
cells, aligned at index `a`, the labelled trial of index `vIdx R a 0` with the held clause.
Consumer: `widthTrialStartOfPacketOnly`, `widthTrialStartOfCleared`. -/
theorem widthTrialStartOf (Base : Bool → DigitAtom n → Prop)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInv ring ref root lane src R Base x) (a : Nat)
    (hS : VShape R 0 (widthLaneOfState ref.toWidthDigitReference root lane src R x))
    (hA : AlignExt R a (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :
    WidthTrialStart ring ref root lane src R (vIdx R a 0) x := by
  obtain ⟨σ, hL, a', -, hL'⟩ := h.2.2.1
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
    σ, hL, a, 0, hai, hA, hS, rfl, hL', hrun⟩

/-- **Entry at the packet-only cut**, at an index `m ≥ 1`. Consumer: `widthPrepAttemptMoment`. -/
theorem widthTrialStartOfPacketOnly (hR : 2 ≤ R) (Base : Bool → DigitAtom n → Prop)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInv ring ref root lane src R Base x)
    (hP : L3.PacketMomentRetire.PacketOnly R (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :
    ∃ m, 1 ≤ m ∧ WidthTrialStart ring ref root lane src R m x := by
  obtain ⟨⟨a, hA⟩, -, -⟩ := h.2.1
  refine ⟨vIdx R a 0, by unfold vIdx; split <;> omega, ?_⟩
  exact widthTrialStartOf ring ref hn root lane src R Base x h a (shapeOfPacketOnly R (by omega) _ hP) hA

/-- **Entry at the cleared window** after the front (`DoneW R (R - 1)`), at index `R - 1`.
Consumer: `widthRaceMoment`. -/
theorem widthTrialStartOfCleared (hR : 2 ≤ R) (Base : Bool → DigitAtom n → Prop)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInv ring ref root lane src R Base x)
    (hd : DoneW R (R - 1) (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :
    WidthTrialStart ring ref root lane src R (R - 1) x := by
  have hS : VShape R 0 (widthLaneOfState ref.toWidthDigitReference root lane src R x) :=
    ⟨by omega, fun q h1 h2 => ⟨(hd.1 q h1 h2).1, fun hq => absurd hq (by omega),
      fun _ => (hd.1 q h1 h2).2⟩⟩
  have ht := widthTrialStartOf ring ref hn root lane src R Base x h (R - 1) hS hd.2.1
  have e : vIdx R (R - 1) 0 = R - 1 := by unfold vIdx; split <;> omega
  rw [e] at ht
  exact ht

/-! ### The trial and the two outcomes -/

/-- The trial at index `m` (or its outcome) with the held clause, the labels and the attempt
class. Consumer: `widthTrialRunMoment`, `widthSuccessMoment`, `widthPrepAttemptMoment`. -/
def WidthTrialRun (Base : Bool → DigitAtom n → Prop) (m : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthHeldTrial ring ref root lane src R m y ∧
    (WidthCohortLayout ref.toWidthDigitReference root src R y.1 ∧ WidthTrialLabAt ring ref root lane src R m y) ∧
    WidthAttemptInv ring ref root lane src R Base y

/-- **The labelled trial with the held clause reaches its outcome** `VTA R m` with all the
invariants, with the bound of `vAlignAtCoupled`. Consumer: `widthPrepAttemptMoment`. -/
theorem widthTrialRunMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop) (m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInv ring ref root lane src R Base x)
    (ht : WidthTrialStart ring ref root lane src R m x) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (fun y => VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
        WidthTrialRun ring ref root lane src R Base m y) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x := by
  obtain ⟨hs, ⟨χ, hq⟩, σ, hL, hlt⟩ := ht
  exact momentKeepUntil (widthDigitAuditNext (ref.toWidthDigitReference))
    (fun y => VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y))
    (WidthTrialRun ring ref root lane src R Base m) N _ _
    (fun y e hy hnt => by
      have hvi : VIAt R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) := by
        rcases hy.1.2.2.1 with hv | hv
        · exact hv
        · exact absurd hv hnt
      exact ⟨widthHeldTrialStep ring ref hn root lane src R hR hsrc hend m y e hy.1 hnt,
        widthTrialLabCoupled ring ref hn root lane src R hR hsrc hend m y e hy.2.1
          (viNotVtAt R m _ hvi),
        widthAttemptInvStep ring ref hn root lane src R (by omega) hsrc hend Base y hy.2.2 e⟩) x
    ⟨⟨h.1.1, h.1.2.1, Or.inl hs, χ, hq⟩, ⟨h.1.1, σ, hL, labTrialRun hlt, Or.inl hlt⟩, h⟩
    (widthVAlignAt ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend N hN hR m x h.1.1 hs)

/-- The first `DigitCompletion` of the pair `(src, src + R)` with cut `0`. Consumer:
`widthAttemptMoment` (the target `P`). -/
def WidthPairDone (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  ∃ U, DigitCompletion ring x.2 root src (src + R) lane 0 U

/-- **The aligned outcome is finished**: `E[z^T] ≤ w^{R+1}`. Consumer: the second alternative
of `widthAttemptMoment`'s outcome clause. -/
theorem widthSuccessMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hv : VTA R (R - 1) (widthLaneOfState ref.toWidthDigitReference root lane src R y))
    (h : WidthTrialRun ring ref root lane src R Base (R - 1) y) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (WidthPairDone ring ref root lane src R) N (N ^ (R + 1)) ((N - n) ^ (R + 1)) y := by
  obtain ⟨⟨-, -, -, χ, hq⟩, ⟨-, hlab⟩, hA⟩ := h
  exact widthGroupDoneMoment ring ref hn root lane src R (by omega) hsrc hend N hN Base y hA.1 hv.1 χ
    hq hlab hA.2.2.2.2

/-- **The outgoing race edge to the completion**: from a misaligned outcome `VTA R m`
(`1 ≤ m ≤ R - 2`) in the attempt class, after the outgoing race edge the front clears the window
(`w^R`), the cleared window is the labelled trial of index `R - 1` with the held clause, which
ends aligned and is finished (`widthAlignedMoment`): `E[z^T] ≤ w^{R + ((R+2)(2R+2) + (R+1))}`.
Consumer: the race alternative of `widthAttemptMoment`'s outcome clause (`F_a`). -/
theorem widthRaceMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (m : Nat)
    (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R) (N : Nat) (hN : n < N) (Base : Bool → DigitAtom n → Prop)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hv : VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R x))
    (h : WidthAttemptInv ring ref root lane src R Base x) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (WidthPairDone ring ref root lane src R) N
      (N ^ R * (N ^ ((R + 2) * vK R) * N ^ (R + 1)))
      ((N - n) ^ R * ((N - n) ^ ((R + 2) * vK R) * (N - n) ^ (R + 1)))
      (widthNxt ring ref x (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))) := by
  obtain ⟨hl0, hfi⟩ := widthFrontOfRace ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend (R - 1) m hR
    hm1 hm2 x h.1.1 hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  have hF := momentKeep (widthDigitAuditNext (ref.toWidthDigitReference)) _
    (WidthAttemptInv ring ref root lane src R Base) N _ _
    (fun y e hy => widthAttemptInvStep ring ref hn root lane src R (by omega) hsrc hend Base y hy e) _
    (widthAttemptInvStep ring ref hn root lane src R (by omega) hsrc hend Base x h _)
    (widthFrontMoment ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend N hN (R - 1) (by omega) _ hl0 hfi)
  refine momentSeq _ _ _ N _ _ _ _ _ (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.sub_le N n) _)
    (Nat.pow_le_pow_left (Nat.sub_le N n) _)) (fun y hy => ?_) hF
  obtain ⟨hd, hy'⟩ := hy
  obtain ⟨hs, ⟨χ, hq⟩, σ, hL, ht⟩ :=
    widthTrialStartOfCleared ring ref hn root lane src R (by omega) Base y hy' hd
  exact widthAlignedMoment ring ref hn root lane src R hR hsrc hend N hN Base y hy'.1 hy'.2.2.2.2 hs χ
    hq σ hL ht

/-- **The preparation of one attempt**: from the attempt class, phases U and retirement reach the
packet-only cut (`prepCutCoupled`), whose trial with the held clause and the labels ends at an
outcome `VTA R m`, `m ≥ 1`, with all the invariants:
`E[z^T] ≤ w^{uBudget R + 2R + (R+2)(2R+2)}`. Consumer: `widthAttemptMoment` (`hprep`). -/
theorem widthPrepAttemptMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInv ring ref root lane src R Base x) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (fun y => ∃ m, 1 ≤ m ∧ VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
        WidthTrialRun ring ref root lane src R Base m y) N
      (N ^ uBudget R * N ^ (2 * R) * N ^ ((R + 2) * vK R))
      ((N - n) ^ uBudget R * (N - n) ^ (2 * R) * (N - n) ^ ((R + 2) * vK R)) x := by
  have hcut := momentKeep (widthDigitAuditNext (ref.toWidthDigitReference)) _
    (WidthAttemptInv ring ref root lane src R Base) N _ _
    (fun y e hy => widthAttemptInvStep ring ref hn root lane src R (by omega) hsrc hend Base y hy e) x
    h (widthPrepCut ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend N hN hR x h.1.1 h.2.1)
  refine momentSeq _ _ _ N _ _ _ _ x (Nat.pow_le_pow_left (Nat.sub_le N n) _)
    (fun y hy => ?_) hcut
  obtain ⟨⟨hP, -⟩, hy⟩ := hy
  obtain ⟨m, hm, hts⟩ := widthTrialStartOfPacketOnly ring ref hn root lane src R (by omega) Base y hy hP
  exact momentWeaken _ _ _ N _ _ (fun z hz => ⟨m, hm, hz⟩) y
    (widthTrialRunMoment ring ref hn root lane src R hR hsrc hend N hN Base m y hy hts)

/-! ### The attempt loop -/

/-- **The attempt loop of one pair.** At a width `N ≥ n (2C + 1)` with `C ≥ 4000` and the three
budgets inside `C` (`B_p ≤ C`, `R + 1 ≤ C`, `11 B_a ≤ 2C + 1`), from every state of the attempt
class the first `DigitCompletion` of the pair `(src, src + R)` with cut `0` has `E[z^τ] ≤ 6`,
`z = N / (N - n)`. Inputs of `attemptLoopWide`: preparation `widthPrepAttemptMoment`; at an outcome
`VTA R m`: `m = R - 1` is finished (`widthSuccessMoment`), `1 ≤ m ≤ R - 2` races, with
`Pend = VTA R m ∧ WidthAttemptInv` kept off the race edges (`raceAlignStep`, `widthAttemptInvStep`), the
outgoing edge to the completion (`widthRaceMoment`) and the incoming edge back in the attempt class
(`widthAttemptInvStep`). Consumer: the per-pair moment (`WidthStrictPairMoment` at BANK). -/
theorem widthAttemptMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N C : Nat)
    (hC : 4000 ≤ C) (hNC : n * (2 * C + 1) ≤ N) (Base : Bool → DigitAtom n → Prop)
    (hBp : uBudget R + 2 * R + (R + 2) * vK R ≤ C) (hBs : R + 1 ≤ C)
    (hBa : 11 * (R + ((R + 2) * vK R + (R + 1))) ≤ 2 * C + 1) :
    ∀ x, WidthAttemptInv ring ref root lane src R Base x →
      MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
        (WidthPairDone ring ref root lane src R) N (6 * (N - n) ^ C) ((N - n) ^ C) x := by
  have hN : n < N := by
    have : n * 2 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  refine L3.PacketMomentWide.attemptLoopWide (widthDigitAuditNext (ref.toWidthDigitReference))
    (WidthPairDone ring ref root lane src R) (WidthAttemptInv ring ref root lane src R Base)
    (fun y => ∃ m, 1 ≤ m ∧ VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
      WidthTrialRun ring ref root lane src R Base m y)
    N C (uBudget R + 2 * R + (R + 2) * vK R) (R + 1) (R + ((R + 2) * vK R + (R + 1)))
    (by omega) hC hNC hBp hBs hBa
    (fun x hx => powSplitL _ _ N _ _ _ x
      (widthPrepAttemptMoment ring ref hn root lane src R hR hsrc hend N hN Base x hx)) ?_
  intro y hy
  obtain ⟨m, hm, hv, hr⟩ := hy
  by_cases hmR : m = R - 1
  · rw [hmR] at hv hr
    exact Or.inr (Or.inl (widthSuccessMoment ring ref hn root lane src R hR hsrc hend N hN Base y hv hr))
  · have hm2 : m + 2 ≤ R := by have := hv.1.1; omega
    refine Or.inr (Or.inr ⟨fun z => VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R z) ∧
        WidthAttemptInv ring ref root lane src R Base z,
      L3.DigitPacketRace.raceOut ring root src R (R - 1 - m),
      L3.DigitPacketRace.raceIn ring root src R (R - 1 - m), ⟨hv, hr.2.2⟩,
      fun he => L3.DigitPacketRace.raceInNe ring root src R (R - 1 - m) (by omega) (by omega)
        he.symm, ?_, ?_, ?_⟩)
    · intro z hz _ e ha hb
      exact ⟨(widthRaceAlignStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend m hR hm hm2 z hz.2.1.1 hz.1 e
        hb ha).2, widthAttemptInvStep ring ref hn root lane src R (by omega) hsrc hend Base z hz.2 e⟩
    · intro z hz _
      exact powSplitR _ _ N _ _ _ _
        (widthRaceMoment ring ref hn root lane src R hR hsrc hend m hm hm2 N hN Base z hz.1 hz.2)
    · intro z hz _
      exact widthAttemptInvStep ring ref hn root lane src R (by omega) hsrc hend Base z hz.2 _

/-- **The attempt loop of one pair at the pair clock**, every `R ≥ 3`: `C = C_R`,
`N ≥ n (2 C_R + 1)`, through `L3.WidthPacketMoment.attemptLoopPair` (the block form of the
attempt loop; covers the SMALL slice `r = 3` that `attemptLoopWide`, `C ≥ 4000`, does not). From
every state of the attempt class the first `DigitCompletion` of the pair `(src, src + R)` with cut
`0` has `E[z^τ] ≤ 6`. Consumer: the per-pair moment at a boundary reference (SMALL). -/
theorem widthAttemptMomentPair (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hNC : n * (2 * bankRepairDigitPairClock R + 1) ≤ N) (Base : Bool → DigitAtom n → Prop) :
    ∀ x, WidthAttemptInv ring ref root lane src R Base x →
      MomentBoundQ (widthDigitAuditNext ref.toWidthDigitReference)
        (WidthPairDone ring ref root lane src R) N
        (6 * (N - n) ^ bankRepairDigitPairClock R) ((N - n) ^ bankRepairDigitPairClock R) x := by
  have hC : 1 ≤ bankRepairDigitPairClock R := Nat.le_trans (by omega) (successBudgetLe R)
  have hN : n < N := by
    have : n * 2 ≤ n * (2 * bankRepairDigitPairClock R + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  have hBa : afterBudget R + (R + 1) = R + ((R + 2) * vK R + (R + 1)) := by
    unfold afterBudget; omega
  refine attemptLoopPair (widthDigitAuditNext ref.toWidthDigitReference)
    (WidthPairDone ring ref root lane src R) (WidthAttemptInv ring ref root lane src R Base)
    (fun y => ∃ m, 1 ≤ m ∧ VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
      WidthTrialRun ring ref root lane src R Base m y)
    N R (by omega) hR hNC
    (fun x hx => powSplitL _ _ N _ _ _ x
      (widthPrepAttemptMoment ring ref hn root lane src R hR hsrc hend N hN Base x hx)) ?_
  intro y hy
  obtain ⟨m, hm, hv, hr⟩ := hy
  by_cases hmR : m = R - 1
  · rw [hmR] at hv hr
    exact Or.inr (Or.inl (widthSuccessMoment ring ref hn root lane src R hR hsrc hend N hN Base y hv hr))
  · have hm2 : m + 2 ≤ R := by have := hv.1.1; omega
    refine Or.inr (Or.inr ⟨fun z => VTA R m (widthLaneOfState ref.toWidthDigitReference root lane src R z) ∧
        WidthAttemptInv ring ref root lane src R Base z,
      L3.DigitPacketRace.raceOut ring root src R (R - 1 - m),
      L3.DigitPacketRace.raceIn ring root src R (R - 1 - m), ⟨hv, hr.2.2⟩,
      fun he => L3.DigitPacketRace.raceInNe ring root src R (R - 1 - m) (by omega) (by omega)
        he.symm, ?_, ?_, ?_⟩)
    · intro z hz _ e ha hb
      exact ⟨(widthRaceAlignStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc
        hend m hR hm hm2 z hz.2.1.1 hz.1 e hb ha).2,
        widthAttemptInvStep ring ref hn root lane src R (by omega) hsrc hend Base z hz.2 e⟩
    · intro z hz _
      rw [hBa]
      exact powSplitR _ _ N _ _ _ _
        (widthRaceMoment ring ref hn root lane src R hR hsrc hend m hm hm2 N hN Base z hz.1 hz.2)
    · intro z hz _
      exact widthAttemptInvStep ring ref hn root lane src R (by omega) hsrc hend Base z hz.2 _

end Ported

end L3.WidthPacketMomentAttempt

#print axioms L3.WidthPacketMomentAttempt.widthAttemptInvStep
#print axioms L3.WidthPacketMomentAttempt.widthTrialStartOf
#print axioms L3.WidthPacketMomentAttempt.widthTrialStartOfPacketOnly
#print axioms L3.WidthPacketMomentAttempt.widthTrialStartOfCleared
#print axioms L3.WidthPacketMomentAttempt.widthTrialRunMoment
#print axioms L3.WidthPacketMomentAttempt.widthSuccessMoment
#print axioms L3.WidthPacketMomentAttempt.widthRaceMoment
#print axioms L3.WidthPacketMomentAttempt.widthPrepAttemptMoment
#print axioms L3.WidthPacketMomentAttempt.widthAttemptMoment
#print axioms L3.WidthPacketMomentAttempt.widthAttemptMomentPair
