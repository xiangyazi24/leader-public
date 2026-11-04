import Leader.L3.Bank.RepairDigitPacketMomentGroupCompletion
import Leader.L3.Bank.RepairDigitPacketMomentWide

/-!
# Lemma e-packet: the attempt loop of one pair to its `DigitCompletion`

repair.tex, Lemma e-packet: from the mobile-free cut each attempt prepares the aligned queue
(phases U, retirement, the renewal trial) and ends at a trial outcome; the aligned outcome is
finished by its carry; a misaligned outcome races its incoming edge against its outgoing edge,
the outgoing edge clears the window and a fresh trial ends aligned, the incoming edge returns to
the attempt class.

* `AttemptInv Base x`: the audit invariants (`PairInv`), the aligned queue with the window
  invariants (`WinAligned`), the labelled queue (`WinLabAt`), the reached-state queue invariant
  (`PacketQueue`) and the complete pair at the audit start. **Every coupled letter keeps it**
  (`attemptInvStep`), so the failure clause of the attempt loop is free.
* `trialStartOf`: at a trial state without settled cells (the packet-only cut, the cleared window)
  the attempt invariant gives the labelled trial with the held clause (`TrialStart`).
* `trialRunMoment`: the trial ends at its outcome `VTA R m` with all the invariants;
  `prepAttemptMoment`: from the attempt class the outcome is reached within `w^{B_p}`,
  `B_p = uBudget R + 2R + (R+2)(2R+2)`.
* `successMoment` (aligned outcome, `w^{R+1}`), `raceMoment` (outgoing race edge, front, cleared
  window, aligned trial, finish: `w^{R + ((R+2)(2R+2) + (R+1))}`).
* `attemptMoment`: `L3.PacketMomentWide.attemptLoopWide` with these inputs: from the attempt
  class, `E[z^τ] ≤ 6` for the first `DigitCompletion` of the pair `(src, src + R)` with cut `0`;
  `attemptMomentBank`: the budgets checked at `C = C_R`, `R ≥ 7`.
-/

namespace L3.PacketMomentAttempt

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

/-! ### Splitting powers in a moment bound -/

/-- Consumer: `attemptMoment`. -/
theorem powSplitL {S : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop) (N a b c : Nat)
    (x : S) (h : MomentBoundQ next P N (N ^ a * N ^ b * N ^ c)
      ((N - n) ^ a * (N - n) ^ b * (N - n) ^ c) x) :
    MomentBoundQ next P N (N ^ (a + b + c)) ((N - n) ^ (a + b + c)) x := by
  rw [Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
  exact h

/-- Consumer: `attemptMoment`. -/
theorem powSplitR {S : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop) (N a b c : Nat)
    (x : S) (h : MomentBoundQ next P N (N ^ a * (N ^ b * N ^ c))
      ((N - n) ^ a * ((N - n) ^ b * (N - n) ^ c)) x) :
    MomentBoundQ next P N (N ^ (a + (b + c))) ((N - n) ^ (a + (b + c))) x := by
  rw [Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add]
  exact h

section Coupled

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat)

/-! ### The attempt class -/

/-- **The attempt class**: the audit invariants, the aligned queue with the window invariants,
the labelled queue, the reached-state queue invariant and the complete pair at the audit start.
Consumer: `attemptMoment` (the class `A` of `attemptLoopWide`). -/
def AttemptInv (Base : Bool → DigitAtom n → Prop)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  PairInv ring hbank root lane src R Base x ∧
    WinAligned R (laneOfState ring hbank root lane src R x) ∧
    WinLabAt ring hbank root lane src R x ∧
    PacketQueue ring root lane src R (piD x.1.val.1) x.2 ∧
    DigitCompletePair ring root x.2.start src (src + R)

/-- **Every coupled letter keeps the attempt class.** Consumer: every phase below and the failure
clause of `attemptMoment`. -/
theorem attemptInvStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (Base : Bool → DigitAtom n → Prop)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInv ring hbank root lane src R Base x) (e : Fin n) :
    AttemptInv ring hbank root lane src R Base (nxt ring hn hbank x e) := by
  obtain ⟨hP, hw, hl, hq, hp⟩ := h
  have h1 := winLabCoupled ring hn hbank root lane src R hR hsrc hend x e ⟨hP.1, hw, hl⟩
  have h2 := packetQueueStep ring hn hbank root lane src R hR hsrc hend x hP.1 hP.2.1 hq e
  exact ⟨pairInvStep ring hn hbank root lane src R hR hsrc hend Base x hP e, h1.2.1, h1.2.2,
    h2.2.2, hp⟩

/-! ### Entering the labelled trial -/

/-- The labelled trial at index `m` with the held clause. Consumer: `trialRunMoment`. -/
def TrialStart (m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  VIAt R m (laneOfState ring hbank root lane src R x) ∧
    (∃ χ, HeldAt ring hbank root lane src R x χ) ∧
    ∃ σ, LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2 ∧
      LabTrial R m (laneOfState ring hbank root lane src R x) σ

/-- **Entry into the labelled trial**: at a state of the attempt class without settled target
cells, aligned at index `a`, the labelled trial of index `vIdx R a 0` with the held clause.
Consumer: `trialStartOfPacketOnly`, `trialStartOfCleared`. -/
theorem trialStartOf (Base : Bool → DigitAtom n → Prop)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInv ring hbank root lane src R Base x) (a : Nat)
    (hS : VShape R 0 (laneOfState ring hbank root lane src R x))
    (hA : AlignExt R a (laneOfState ring hbank root lane src R x)) :
    TrialStart ring hbank root lane src R (vIdx R a 0) x := by
  obtain ⟨σ, hL, a', -, hL'⟩ := h.2.2.1
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
    σ, hL, a, 0, hai, hA, hS, rfl, hL', hrun⟩

/-- **Entry at the packet-only cut**, at an index `m ≥ 1`. Consumer: `prepAttemptMoment`. -/
theorem trialStartOfPacketOnly (hR : 2 ≤ R) (Base : Bool → DigitAtom n → Prop)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInv ring hbank root lane src R Base x)
    (hP : L3.PacketMomentRetire.PacketOnly R (laneOfState ring hbank root lane src R x)) :
    ∃ m, 1 ≤ m ∧ TrialStart ring hbank root lane src R m x := by
  obtain ⟨⟨a, hA⟩, -, -⟩ := h.2.1
  refine ⟨vIdx R a 0, by unfold vIdx; split <;> omega, ?_⟩
  exact trialStartOf ring hbank root lane src R Base x h a (shapeOfPacketOnly R (by omega) _ hP) hA

/-- **Entry at the cleared window** after the front (`DoneW R (R - 1)`), at index `R - 1`.
Consumer: `raceMoment`. -/
theorem trialStartOfCleared (hR : 2 ≤ R) (Base : Bool → DigitAtom n → Prop)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInv ring hbank root lane src R Base x)
    (hd : DoneW R (R - 1) (laneOfState ring hbank root lane src R x)) :
    TrialStart ring hbank root lane src R (R - 1) x := by
  have hS : VShape R 0 (laneOfState ring hbank root lane src R x) :=
    ⟨by omega, fun q h1 h2 => ⟨(hd.1 q h1 h2).1, fun hq => absurd hq (by omega),
      fun _ => (hd.1 q h1 h2).2⟩⟩
  have ht := trialStartOf ring hbank root lane src R Base x h (R - 1) hS hd.2.1
  have e : vIdx R (R - 1) 0 = R - 1 := by unfold vIdx; split <;> omega
  rw [e] at ht
  exact ht

/-! ### The trial and the two outcomes -/

/-- The trial at index `m` (or its outcome) with the held clause, the labels and the attempt
class. Consumer: `trialRunMoment`, `successMoment`, `prepAttemptMoment`. -/
def TrialRun (Base : Bool → DigitAtom n → Prop) (m : Nat)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  HeldTrial ring hbank root lane src R m y ∧
    (CohortLayout ring hbank root src R y.1 ∧ TrialLabAt ring hbank root lane src R m y) ∧
    AttemptInv ring hbank root lane src R Base y

/-- **The labelled trial with the held clause reaches its outcome** `VTA R m` with all the
invariants, with the bound of `vAlignAtCoupled`. Consumer: `prepAttemptMoment`. -/
theorem trialRunMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop) (m : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInv ring hbank root lane src R Base x)
    (ht : TrialStart ring hbank root lane src R m x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => VTA R m (laneOfState ring hbank root lane src R y) ∧
        TrialRun ring hbank root lane src R Base m y) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x := by
  obtain ⟨hs, ⟨χ, hq⟩, σ, hL, hlt⟩ := ht
  exact momentKeepUntil (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (fun y => VTA R m (laneOfState ring hbank root lane src R y))
    (TrialRun ring hbank root lane src R Base m) N _ _
    (fun y e hy hnt => by
      have hvi : VIAt R m (laneOfState ring hbank root lane src R y) := by
        rcases hy.1.2.2.1 with hv | hv
        · exact hv
        · exact absurd hv hnt
      exact ⟨heldTrialStep ring hn hbank root lane src R hR hsrc hend m y e hy.1 hnt,
        trialLabCoupled ring hn hbank root lane src R hR hsrc hend m y e hy.2.1
          (viNotVtAt R m _ hvi),
        attemptInvStep ring hn hbank root lane src R (by omega) hsrc hend Base y hy.2.2 e⟩) x
    ⟨⟨h.1.1, h.1.2.1, Or.inl hs, χ, hq⟩, ⟨h.1.1, σ, hL, labTrialRun hlt, Or.inl hlt⟩, h⟩
    (vAlignAtCoupled ring hn hbank root lane src R hR hsrc hend N hN m x h.1.1 hs)

/-- The first `DigitCompletion` of the pair `(src, src + R)` with cut `0`. Consumer:
`attemptMoment` (the target `P`). -/
def PairDone (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  ∃ U, DigitCompletion ring x.2 root src (src + R) lane 0 U

/-- **The aligned outcome is finished**: `E[z^T] ≤ w^{R+1}`. Consumer: the second alternative
of `attemptMoment`'s outcome clause. -/
theorem successMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hv : VTA R (R - 1) (laneOfState ring hbank root lane src R y))
    (h : TrialRun ring hbank root lane src R Base (R - 1) y) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (PairDone ring hbank root lane src R) N (N ^ (R + 1)) ((N - n) ^ (R + 1)) y := by
  obtain ⟨⟨-, -, -, χ, hq⟩, ⟨-, hlab⟩, hA⟩ := h
  exact groupDoneMoment ring hn hbank root lane src R (by omega) hsrc hend N hN Base y hA.1 hv.1 χ
    hq hlab hA.2.2.2.2

/-- **The outgoing race edge to the completion**: from a misaligned outcome `VTA R m`
(`1 ≤ m ≤ R - 2`) in the attempt class, after the outgoing race edge the front clears the window
(`w^R`), the cleared window is the labelled trial of index `R - 1` with the held clause, which
ends aligned and is finished (`alignedMoment`): `E[z^T] ≤ w^{R + ((R+2)(2R+2) + (R+1))}`.
Consumer: the race alternative of `attemptMoment`'s outcome clause (`F_a`). -/
theorem raceMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (m : Nat)
    (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R) (N : Nat) (hN : n < N) (Base : Bool → DigitAtom n → Prop)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hv : VTA R m (laneOfState ring hbank root lane src R x))
    (h : AttemptInv ring hbank root lane src R Base x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (PairDone ring hbank root lane src R) N
      (N ^ R * (N ^ ((R + 2) * vK R) * N ^ (R + 1)))
      ((N - n) ^ R * ((N - n) ^ ((R + 2) * vK R) * (N - n) ^ (R + 1)))
      (nxt ring hn hbank x (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))) := by
  obtain ⟨hl0, hfi⟩ := frontOfRaceCoupled ring hn hbank root lane src R (R - 1) m hR hsrc hend
    hm1 hm2 x h.1.1 hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  have hF := momentKeep (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) _
    (AttemptInv ring hbank root lane src R Base) N _ _
    (fun y e hy => attemptInvStep ring hn hbank root lane src R (by omega) hsrc hend Base y hy e) _
    (attemptInvStep ring hn hbank root lane src R (by omega) hsrc hend Base x h _)
    (frontMomentCoupled ring hn hbank root lane src R (R - 1) (by omega) hsrc hend N hN _ hl0 hfi)
  refine momentSeq _ _ _ N _ _ _ _ _ (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.sub_le N n) _)
    (Nat.pow_le_pow_left (Nat.sub_le N n) _)) (fun y hy => ?_) hF
  obtain ⟨hd, hy'⟩ := hy
  obtain ⟨hs, ⟨χ, hq⟩, σ, hL, ht⟩ :=
    trialStartOfCleared ring hbank root lane src R (by omega) Base y hy' hd
  exact alignedMoment ring hn hbank root lane src R hR hsrc hend N hN Base y hy'.1 hy'.2.2.2.2 hs χ
    hq σ hL ht

/-- **The preparation of one attempt**: from the attempt class, phases U and retirement reach the
packet-only cut (`prepCutCoupled`), whose trial with the held clause and the labels ends at an
outcome `VTA R m`, `m ≥ 1`, with all the invariants:
`E[z^T] ≤ w^{uBudget R + 2R + (R+2)(2R+2)}`. Consumer: `attemptMoment` (`hprep`). -/
theorem prepAttemptMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInv ring hbank root lane src R Base x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => ∃ m, 1 ≤ m ∧ VTA R m (laneOfState ring hbank root lane src R y) ∧
        TrialRun ring hbank root lane src R Base m y) N
      (N ^ uBudget R * N ^ (2 * R) * N ^ ((R + 2) * vK R))
      ((N - n) ^ uBudget R * (N - n) ^ (2 * R) * (N - n) ^ ((R + 2) * vK R)) x := by
  have hcut := momentKeep (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) _
    (AttemptInv ring hbank root lane src R Base) N _ _
    (fun y e hy => attemptInvStep ring hn hbank root lane src R (by omega) hsrc hend Base y hy e) x
    h (prepCutCoupled ring hn hbank root lane src R hR hsrc hend N hN x h.1.1 h.2.1)
  refine momentSeq _ _ _ N _ _ _ _ x (Nat.pow_le_pow_left (Nat.sub_le N n) _)
    (fun y hy => ?_) hcut
  obtain ⟨⟨hP, -⟩, hy⟩ := hy
  obtain ⟨m, hm, hts⟩ := trialStartOfPacketOnly ring hbank root lane src R (by omega) Base y hy hP
  exact momentWeaken _ _ _ N _ _ (fun z hz => ⟨m, hm, hz⟩) y
    (trialRunMoment ring hn hbank root lane src R hR hsrc hend N hN Base m y hy hts)

/-! ### The attempt loop -/

/-- **The attempt loop of one pair.** At a width `N ≥ n (2C + 1)` with `C ≥ 4000` and the three
budgets inside `C` (`B_p ≤ C`, `R + 1 ≤ C`, `11 B_a ≤ 2C + 1`), from every state of the attempt
class the first `DigitCompletion` of the pair `(src, src + R)` with cut `0` has `E[z^τ] ≤ 6`,
`z = N / (N - n)`. Inputs of `attemptLoopWide`: preparation `prepAttemptMoment`; at an outcome
`VTA R m`: `m = R - 1` is finished (`successMoment`), `1 ≤ m ≤ R - 2` races, with
`Pend = VTA R m ∧ AttemptInv` kept off the race edges (`raceAlignStep`, `attemptInvStep`), the
outgoing edge to the completion (`raceMoment`) and the incoming edge back in the attempt class
(`attemptInvStep`). Consumer: the per-pair moment (`WidthStrictPairMoment` at BANK). -/
theorem attemptMoment (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N C : Nat)
    (hC : 4000 ≤ C) (hNC : n * (2 * C + 1) ≤ N) (Base : Bool → DigitAtom n → Prop)
    (hBp : uBudget R + 2 * R + (R + 2) * vK R ≤ C) (hBs : R + 1 ≤ C)
    (hBa : 11 * (R + ((R + 2) * vK R + (R + 1))) ≤ 2 * C + 1) :
    ∀ x, AttemptInv ring hbank root lane src R Base x →
      MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
        (PairDone ring hbank root lane src R) N (6 * (N - n) ^ C) ((N - n) ^ C) x := by
  have hN : n < N := by
    have : n * 2 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  refine L3.PacketMomentWide.attemptLoopWide (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (PairDone ring hbank root lane src R) (AttemptInv ring hbank root lane src R Base)
    (fun y => ∃ m, 1 ≤ m ∧ VTA R m (laneOfState ring hbank root lane src R y) ∧
      TrialRun ring hbank root lane src R Base m y)
    N C (uBudget R + 2 * R + (R + 2) * vK R) (R + 1) (R + ((R + 2) * vK R + (R + 1)))
    (by omega) hC hNC hBp hBs hBa
    (fun x hx => powSplitL _ _ N _ _ _ x
      (prepAttemptMoment ring hn hbank root lane src R hR hsrc hend N hN Base x hx)) ?_
  intro y hy
  obtain ⟨m, hm, hv, hr⟩ := hy
  by_cases hmR : m = R - 1
  · rw [hmR] at hv hr
    exact Or.inr (Or.inl (successMoment ring hn hbank root lane src R hR hsrc hend N hN Base y hv hr))
  · have hm2 : m + 2 ≤ R := by have := hv.1.1; omega
    refine Or.inr (Or.inr ⟨fun z => VTA R m (laneOfState ring hbank root lane src R z) ∧
        AttemptInv ring hbank root lane src R Base z,
      L3.DigitPacketRace.raceOut ring root src R (R - 1 - m),
      L3.DigitPacketRace.raceIn ring root src R (R - 1 - m), ⟨hv, hr.2.2⟩,
      fun he => L3.DigitPacketRace.raceInNe ring root src R (R - 1 - m) (by omega) (by omega)
        he.symm, ?_, ?_, ?_⟩)
    · intro z hz _ e ha hb
      exact ⟨(raceAlignStep ring hn hbank root lane src R m hR hsrc hend hm hm2 z hz.2.1.1 hz.1 e
        hb ha).2, attemptInvStep ring hn hbank root lane src R (by omega) hsrc hend Base z hz.2 e⟩
    · intro z hz _
      exact powSplitR _ _ N _ _ _ _
        (raceMoment ring hn hbank root lane src R hR hsrc hend m hm hm2 N hN Base z hz.1 hz.2)
    · intro z hz _
      exact attemptInvStep ring hn hbank root lane src R (by omega) hsrc hend Base z hz.2 _

/-- **The attempt loop at the BANK width**: `C = C_R`, `N = n (2 C_R + 1)`, `R ≥ 7`; the budgets
are `prepBudgetLe`, `C_R ≥ 4000` (`pairClockLarge`) and `afterBudgetShort`. Consumer: the
per-pair moment at BANK (`R = r = digitSpan ≥ 127`). -/
theorem attemptMomentBank (hR : 7 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (Base : Bool → DigitAtom n → Prop) :
    ∀ x, AttemptInv ring hbank root lane src R Base x →
      MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
        (PairDone ring hbank root lane src R) (n * (2 * bankRepairDigitPairClock R + 1))
        (6 * (n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R)
        ((n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R) x := by
  have hBp := L3.PacketMomentWide.prepBudgetLe R (by omega)
  have hBa := afterBudgetShort R (by omega)
  have hC := L3.PacketMomentWide.pairClockLarge R hR
  unfold afterBudget at hBa
  refine attemptMoment ring hn hbank root lane src R (by omega) hsrc hend _
    (bankRepairDigitPairClock R) hC (Nat.le_refl _) Base hBp (by omega) ?_
  generalize (R + 2) * vK R = V at hBa ⊢
  omega

end Coupled

end L3.PacketMomentAttempt

#print axioms L3.PacketMomentAttempt.powSplitL
#print axioms L3.PacketMomentAttempt.powSplitR
#print axioms L3.PacketMomentAttempt.attemptInvStep
#print axioms L3.PacketMomentAttempt.trialStartOf
#print axioms L3.PacketMomentAttempt.trialStartOfPacketOnly
#print axioms L3.PacketMomentAttempt.trialStartOfCleared
#print axioms L3.PacketMomentAttempt.trialRunMoment
#print axioms L3.PacketMomentAttempt.successMoment
#print axioms L3.PacketMomentAttempt.raceMoment
#print axioms L3.PacketMomentAttempt.prepAttemptMoment
#print axioms L3.PacketMomentAttempt.attemptMoment
#print axioms L3.PacketMomentAttempt.attemptMomentBank
