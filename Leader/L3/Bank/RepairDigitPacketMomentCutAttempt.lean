import Leader.L3.Bank.RepairDigitPacketMomentAttempt
import Leader.L3.Bank.RepairDigitPacketMomentCutCompletion

/-!
# Lemma e-packet with a cut: the attempt loop to a `DigitCompletion` with cut `c`

`L3.PacketMomentAttempt` with the cut of the completion as a parameter. The attempt class carries
the labelled queue with labels stamped after `c` (`WinLabAtC`, `L3.PacketMomentCutLabels`); every
letter keeps it (`attemptInvStepC`), the trial and the two outcomes reach the completion with cut
`c` (`successMomentC`, `raceMomentC`, through `L3.PacketMomentCutCompletion.alignedMomentC`), with
the same bounds: `attemptMomentC` (`E[z^τ] ≤ 6` to `PairDoneC c`), `attemptMomentBankC` at
`C = C_R`. At `c = 0` these are the uncut statements.
-/

namespace L3.PacketMomentCutAttempt

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
open L3.WidthDigit
open L3.DigitPacketTransport
open L3.DigitPacketQueue
open L3.DigitPacketQueueExport
open L3.PacketMomentPrep
open L3.PacketMomentPending
open L3.PacketMomentU
open L3.PacketMomentV
open L3.PacketMomentVSerial
open L3.PacketMomentFinish
open L3.PacketMomentCells
open L3.PacketMomentLabels
open L3.PacketMomentQueueLabels
open L3.PacketMomentTrialLabels
open L3.PacketMomentGroupLabels
open L3.PacketMomentAfter
open L3.PacketMomentTrialEnd
open L3.PacketMomentHeldQueue
open L3.PacketMomentGroupCompletion
open L3.PacketMomentAttempt
open L3.PacketMomentCutLabels
open L3.PacketMomentCutCompletion

section Coupled

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat)

/-! ### The attempt class -/

/-- **The attempt class**: the audit invariants, the aligned queue with the window invariants,
the labelled queue, the reached-state queue invariant and the complete pair at the audit start.
Consumer: `attemptMoment` (the class `A` of `attemptLoopWide`). -/
def AttemptInvC (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  PairInv ring hbank root lane src R Base x ∧
    WinAligned R (laneOfState ring hbank root lane src R x) ∧
    WinLabAtC ring hbank root lane src R cut x ∧
    PacketQueue ring root lane src R (piD x.1.val.1) x.2 ∧
    DigitCompletePair ring root x.2.start src (src + R)

/-- **Every coupled letter keeps the attempt class.** Consumer: every phase below and the failure
clause of `attemptMoment`. -/
theorem attemptInvStepC (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInvC ring hbank root lane src R Base cut x) (e : Fin n) :
    AttemptInvC ring hbank root lane src R Base cut (nxt ring hn hbank x e) := by
  obtain ⟨hP, hw, hl, hq, hp⟩ := h
  have h1 := winLabCoupledC ring hn hbank root lane src R hR hsrc hend cut x e ⟨hP.1, hw, hl⟩
  have h2 := packetQueueStep ring hn hbank root lane src R hR hsrc hend x hP.1 hP.2.1 hq e
  exact ⟨pairInvStep ring hn hbank root lane src R hR hsrc hend Base x hP e, h1.2.1, h1.2.2,
    h2.2.2, hp⟩

/-! ### Entering the labelled trial -/

/-- The labelled trial at index `m` with the held clause. Consumer: `trialRunMoment`. -/
def TrialStartC (cut m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  VIAt R m (laneOfState ring hbank root lane src R x) ∧
    (∃ χ, HeldAt ring hbank root lane src R x χ) ∧
    ∃ σ, LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2 ∧
      LabelCut ring root lane src R cut (laneOfState ring hbank root lane src R x) σ x.2 ∧
      LabTrial R m (laneOfState ring hbank root lane src R x) σ

/-- **Entry into the labelled trial**: at a state of the attempt class without settled target
cells, aligned at index `a`, the labelled trial of index `vIdx R a 0` with the held clause.
Consumer: `trialStartOfPacketOnly`, `trialStartOfCleared`. -/
theorem trialStartOfC (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInvC ring hbank root lane src R Base cut x) (a : Nat)
    (hS : VShape R 0 (laneOfState ring hbank root lane src R x))
    (hA : AlignExt R a (laneOfState ring hbank root lane src R x)) :
    TrialStartC ring hbank root lane src R cut (vIdx R a 0) x := by
  obtain ⟨σ, hL, hC, a', -, hL'⟩ := h.2.2.1
  have ha := extIdx R a a' _ σ hA hL'
  rw [← ha] at hL'
  have hrun : LabRun R (vIdx R a 0) (laneOfState ring hbank root lane src R x) σ := by
    intro q hq1 hq2 hSq
    exfalso
    rcases (hS.2 q hq1 hq2).2.2 (by omega) with he | hp
    · rw [he] at hSq; cases hSq
    · revert hSq hp; cases (laneOfState ring hbank root lane src R x).inp q <;> simp [isSI, isPI]
  have hai : 0 + a + 1 ≤ R := by have := hA.2.1; omega
  exact ⟨⟨a, 0, hai, hA, hS, rfl⟩, heldOfPacketQueue ring hbank root lane src R x hS h.2.2.2.1,
    σ, hL, hC, a, 0, hai, hA, hS, rfl, hL', hrun⟩

/-- **Entry at the packet-only cut**, at an index `m ≥ 1`. Consumer: `prepAttemptMoment`. -/
theorem trialStartOfPacketOnlyC (hR : 2 ≤ R) (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInvC ring hbank root lane src R Base cut x)
    (hP : L3.PacketMomentRetire.PacketOnly R (laneOfState ring hbank root lane src R x)) :
    ∃ m, 1 ≤ m ∧ TrialStartC ring hbank root lane src R cut m x := by
  obtain ⟨⟨a, hA⟩, -, -⟩ := h.2.1
  refine ⟨vIdx R a 0, by unfold vIdx; split <;> omega, ?_⟩
  exact trialStartOfC ring hbank root lane src R Base cut x h a (shapeOfPacketOnly R (by omega) _ hP) hA

/-- **Entry at the cleared window** after the front (`DoneW R (R - 1)`), at index `R - 1`.
Consumer: `raceMoment`. -/
theorem trialStartOfClearedC (hR : 2 ≤ R) (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInvC ring hbank root lane src R Base cut x)
    (hd : DoneW R (R - 1) (laneOfState ring hbank root lane src R x)) :
    TrialStartC ring hbank root lane src R cut (R - 1) x := by
  have hS : VShape R 0 (laneOfState ring hbank root lane src R x) :=
    ⟨by omega, fun q h1 h2 => ⟨(hd.1 q h1 h2).1, fun hq => absurd hq (by omega),
      fun _ => (hd.1 q h1 h2).2⟩⟩
  have ht := trialStartOfC ring hbank root lane src R Base cut x h (R - 1) hS hd.2.1
  have e : vIdx R (R - 1) 0 = R - 1 := by unfold vIdx; split <;> omega
  rw [e] at ht
  exact ht

/-! ### The trial and the two outcomes -/

/-- The trial at index `m` (or its outcome) with the held clause, the labels and the attempt
class. Consumer: `trialRunMoment`, `successMoment`, `prepAttemptMoment`. -/
def TrialRunC (Base : Bool → DigitAtom n → Prop) (cut : Nat) (m : Nat)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  HeldTrial ring hbank root lane src R m y ∧
    (CohortLayout ring hbank root src R y.1 ∧ TrialLabAtC ring hbank root lane src R cut m y) ∧
    AttemptInvC ring hbank root lane src R Base cut y

/-- **The labelled trial with the held clause reaches its outcome** `VTA R m` with all the
invariants, with the bound of `vAlignAtCoupled`. Consumer: `prepAttemptMoment`. -/
theorem trialRunMomentC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop) (cut : Nat) (m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInvC ring hbank root lane src R Base cut x)
    (ht : TrialStartC ring hbank root lane src R cut m x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => VTA R m (laneOfState ring hbank root lane src R y) ∧
        TrialRunC ring hbank root lane src R Base cut m y) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x := by
  obtain ⟨hs, ⟨χ, hq⟩, σ, hL, hC, hlt⟩ := ht
  exact momentKeepUntil (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (fun y => VTA R m (laneOfState ring hbank root lane src R y))
    (TrialRunC ring hbank root lane src R Base cut m) N _ _
    (fun y e hy hnt => by
      have hvi : VIAt R m (laneOfState ring hbank root lane src R y) := by
        rcases hy.1.2.2.1 with hv | hv
        · exact hv
        · exact absurd hv hnt
      exact ⟨heldTrialStep ring hn hbank root lane src R hR hsrc hend m y e hy.1 hnt,
        trialLabCoupledC ring hn hbank root lane src R hR hsrc hend cut m y e hy.2.1
          (viNotVtAt R m _ hvi),
        attemptInvStepC ring hn hbank root lane src R (by omega) hsrc hend Base cut y hy.2.2 e⟩) x
    ⟨⟨h.1.1, h.1.2.1, Or.inl hs, χ, hq⟩, ⟨h.1.1, σ, hL, hC, labTrialRun hlt, Or.inl hlt⟩, h⟩
    (vAlignAtCoupled ring hn hbank root lane src R hR hsrc hend N hN m x h.1.1 hs)

/-- The first `DigitCompletion` of the pair `(src, src + R)` with cut `0`. Consumer:
`attemptMoment` (the target `P`). -/
def PairDoneC (cut : Nat) (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  ∃ U, DigitCompletion ring x.2 root src (src + R) lane cut U

/-- **The aligned outcome is finished**: `E[z^T] ≤ w^{R+1}`. Consumer: the second alternative
of `attemptMoment`'s outcome clause. -/
theorem successMomentC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hv : VTA R (R - 1) (laneOfState ring hbank root lane src R y))
    (h : TrialRunC ring hbank root lane src R Base cut (R - 1) y) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (PairDoneC ring hbank root lane src R cut) N (N ^ (R + 1)) ((N - n) ^ (R + 1)) y := by
  obtain ⟨⟨-, -, -, χ, hq⟩, ⟨-, hlab⟩, hA⟩ := h
  exact groupDoneMomentC ring hn hbank root lane src R (by omega) cut hsrc hend N hN Base y hA.1 hv.1 χ
    hq hlab hA.2.2.2.2

/-- **The outgoing race edge to the completion**: from a misaligned outcome `VTA R m`
(`1 ≤ m ≤ R - 2`) in the attempt class, after the outgoing race edge the front clears the window
(`w^R`), the cleared window is the labelled trial of index `R - 1` with the held clause, which
ends aligned and is finished (`alignedMoment`): `E[z^T] ≤ w^{R + ((R+2)(2R+2) + (R+1))}`.
Consumer: the race alternative of `attemptMoment`'s outcome clause (`F_a`). -/
theorem raceMomentC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (m : Nat)
    (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R) (N : Nat) (hN : n < N) (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hv : VTA R m (laneOfState ring hbank root lane src R x))
    (h : AttemptInvC ring hbank root lane src R Base cut x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (PairDoneC ring hbank root lane src R cut) N
      (N ^ R * (N ^ ((R + 2) * vK R) * N ^ (R + 1)))
      ((N - n) ^ R * ((N - n) ^ ((R + 2) * vK R) * (N - n) ^ (R + 1)))
      (nxt ring hn hbank x (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))) := by
  obtain ⟨hl0, hfi⟩ := frontOfRaceCoupled ring hn hbank root lane src R (R - 1) m hR hsrc hend
    hm1 hm2 x h.1.1 hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  have hF := momentKeep (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) _
    (AttemptInvC ring hbank root lane src R Base cut) N _ _
    (fun y e hy => attemptInvStepC ring hn hbank root lane src R (by omega) hsrc hend Base cut y hy e) _
    (attemptInvStepC ring hn hbank root lane src R (by omega) hsrc hend Base cut x h _)
    (frontMomentCoupled ring hn hbank root lane src R (R - 1) (by omega) hsrc hend N hN _ hl0 hfi)
  refine momentSeq _ _ _ N _ _ _ _ _ (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.sub_le N n) _)
    (Nat.pow_le_pow_left (Nat.sub_le N n) _)) (fun y hy => ?_) hF
  obtain ⟨hd, hy'⟩ := hy
  obtain ⟨hs, ⟨χ, hq⟩, σ, hL, hC, ht⟩ :=
    trialStartOfClearedC ring hbank root lane src R (by omega) Base cut y hy' hd
  exact alignedMomentC ring hn hbank root lane src R hR cut hsrc hend N hN Base y hy'.1 hy'.2.2.2.2 hs χ
    hq σ hL hC ht

/-- **The preparation of one attempt**: from the attempt class, phases U and retirement reach the
packet-only cut (`prepCutCoupled`), whose trial with the held clause and the labels ends at an
outcome `VTA R m`, `m ≥ 1`, with all the invariants:
`E[z^T] ≤ w^{uBudget R + 2R + (R+2)(2R+2)}`. Consumer: `attemptMoment` (`hprep`). -/
theorem prepAttemptMomentC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInvC ring hbank root lane src R Base cut x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => ∃ m, 1 ≤ m ∧ VTA R m (laneOfState ring hbank root lane src R y) ∧
        TrialRunC ring hbank root lane src R Base cut m y) N
      (N ^ uBudget R * N ^ (2 * R) * N ^ ((R + 2) * vK R))
      ((N - n) ^ uBudget R * (N - n) ^ (2 * R) * (N - n) ^ ((R + 2) * vK R)) x := by
  have hcut := momentKeep (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) _
    (AttemptInvC ring hbank root lane src R Base cut) N _ _
    (fun y e hy => attemptInvStepC ring hn hbank root lane src R (by omega) hsrc hend Base cut y hy e) x
    h (prepCutCoupled ring hn hbank root lane src R hR hsrc hend N hN x h.1.1 h.2.1)
  refine momentSeq _ _ _ N _ _ _ _ x (Nat.pow_le_pow_left (Nat.sub_le N n) _)
    (fun y hy => ?_) hcut
  obtain ⟨⟨hP, -⟩, hy⟩ := hy
  obtain ⟨m, hm, hts⟩ := trialStartOfPacketOnlyC ring hbank root lane src R (by omega) Base cut y hy hP
  exact momentWeaken _ _ _ N _ _ (fun z hz => ⟨m, hm, hz⟩) y
    (trialRunMomentC ring hn hbank root lane src R hR hsrc hend N hN Base cut m y hy hts)

/-! ### The attempt loop -/

/-- **The attempt loop of one pair.** At a width `N ≥ n (2C + 1)` with `C ≥ 4000` and the three
budgets inside `C` (`B_p ≤ C`, `R + 1 ≤ C`, `11 B_a ≤ 2C + 1`), from every state of the attempt
class the first `DigitCompletion` of the pair `(src, src + R)` with cut `0` has `E[z^τ] ≤ 6`,
`z = N / (N - n)`. Inputs of `attemptLoopWide`: preparation `prepAttemptMoment`; at an outcome
`VTA R m`: `m = R - 1` is finished (`successMoment`), `1 ≤ m ≤ R - 2` races, with
`Pend = VTA R m ∧ AttemptInv` kept off the race edges (`raceAlignStep`, `attemptInvStep`), the
outgoing edge to the completion (`raceMoment`) and the incoming edge back in the attempt class
(`attemptInvStep`). Consumer: the per-pair moment (`WidthStrictPairMoment` at BANK). -/
theorem attemptMomentC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N C : Nat)
    (hC : 4000 ≤ C) (hNC : n * (2 * C + 1) ≤ N) (Base : Bool → DigitAtom n → Prop) (cut : Nat)
    (hBp : uBudget R + 2 * R + (R + 2) * vK R ≤ C) (hBs : R + 1 ≤ C)
    (hBa : 11 * (R + ((R + 2) * vK R + (R + 1))) ≤ 2 * C + 1) :
    ∀ x, AttemptInvC ring hbank root lane src R Base cut x →
      MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
        (PairDoneC ring hbank root lane src R cut) N (6 * (N - n) ^ C) ((N - n) ^ C) x := by
  have hN : n < N := by
    have : n * 2 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  refine L3.PacketMomentWide.attemptLoopWide (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (PairDoneC ring hbank root lane src R cut) (AttemptInvC ring hbank root lane src R Base cut)
    (fun y => ∃ m, 1 ≤ m ∧ VTA R m (laneOfState ring hbank root lane src R y) ∧
      TrialRunC ring hbank root lane src R Base cut m y)
    N C (uBudget R + 2 * R + (R + 2) * vK R) (R + 1) (R + ((R + 2) * vK R + (R + 1)))
    (by omega) hC hNC hBp hBs hBa
    (fun x hx => powSplitL _ _ N _ _ _ x
      (prepAttemptMomentC ring hn hbank root lane src R hR hsrc hend N hN Base cut x hx)) ?_
  intro y hy
  obtain ⟨m, hm, hv, hr⟩ := hy
  by_cases hmR : m = R - 1
  · rw [hmR] at hv hr
    exact Or.inr (Or.inl (successMomentC ring hn hbank root lane src R hR hsrc hend N hN Base cut y hv hr))
  · have hm2 : m + 2 ≤ R := by have := hv.1.1; omega
    refine Or.inr (Or.inr ⟨fun z => VTA R m (laneOfState ring hbank root lane src R z) ∧
        AttemptInvC ring hbank root lane src R Base cut z,
      L3.DigitPacketRace.raceOut ring root src R (R - 1 - m),
      L3.DigitPacketRace.raceIn ring root src R (R - 1 - m), ⟨hv, hr.2.2⟩,
      fun he => L3.DigitPacketRace.raceInNe ring root src R (R - 1 - m) (by omega) (by omega)
        he.symm, ?_, ?_, ?_⟩)
    · intro z hz _ e ha hb
      exact ⟨(raceAlignStep ring hn hbank root lane src R m hR hsrc hend hm hm2 z hz.2.1.1 hz.1 e
        hb ha).2, attemptInvStepC ring hn hbank root lane src R (by omega) hsrc hend Base cut z hz.2 e⟩
    · intro z hz _
      exact powSplitR _ _ N _ _ _ _
        (raceMomentC ring hn hbank root lane src R hR hsrc hend m hm hm2 N hN Base cut z hz.1 hz.2)
    · intro z hz _
      exact attemptInvStepC ring hn hbank root lane src R (by omega) hsrc hend Base cut z hz.2 _

/-- **The attempt loop at the BANK width**: `C = C_R`, `N = n (2 C_R + 1)`, `R ≥ 7`; the budgets
are `prepBudgetLe`, `C_R ≥ 4000` (`pairClockLarge`) and `afterBudgetShort`. Consumer: the
per-pair moment at BANK (`R = r = digitSpan ≥ 127`). -/
theorem attemptMomentBankC (hR : 7 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (Base : Bool → DigitAtom n → Prop) (cut : Nat) :
    ∀ x, AttemptInvC ring hbank root lane src R Base cut x →
      MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
        (PairDoneC ring hbank root lane src R cut) (n * (2 * bankRepairDigitPairClock R + 1))
        (6 * (n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R)
        ((n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R) x := by
  have hBp := L3.PacketMomentWide.prepBudgetLe R (by omega)
  have hBa := afterBudgetShort R (by omega)
  have hC := L3.PacketMomentWide.pairClockLarge R hR
  unfold afterBudget at hBa
  refine attemptMomentC ring hn hbank root lane src R (by omega) hsrc hend _
    (bankRepairDigitPairClock R) hC (Nat.le_refl _) Base cut hBp (by omega) ?_
  generalize (R + 2) * vK R = V at hBa ⊢
  omega

end Coupled

end L3.PacketMomentCutAttempt



#print axioms L3.PacketMomentCutAttempt.attemptInvStepC
#print axioms L3.PacketMomentCutAttempt.trialStartOfC
#print axioms L3.PacketMomentCutAttempt.trialStartOfPacketOnlyC
#print axioms L3.PacketMomentCutAttempt.trialStartOfClearedC
#print axioms L3.PacketMomentCutAttempt.trialRunMomentC
#print axioms L3.PacketMomentCutAttempt.successMomentC
#print axioms L3.PacketMomentCutAttempt.raceMomentC
#print axioms L3.PacketMomentCutAttempt.prepAttemptMomentC
#print axioms L3.PacketMomentCutAttempt.attemptMomentC
#print axioms L3.PacketMomentCutAttempt.attemptMomentBankC
