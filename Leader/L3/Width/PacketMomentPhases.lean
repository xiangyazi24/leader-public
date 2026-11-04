import Leader.L3.Width.PacketMomentTransport
import Leader.L3.Bank.RepairDigitPacketMomentTrialEnd

/-!
# Lemma e-packet at a digit reference: the lane phases of the attempt on the coupled chain

The lane phases of the e-packet chain (release, U, retirement, the renewal trial, the aligned
finish, the front after a won race, the race class) are lane statements; their `…Coupled` forms
in `Leader/L3/BankRepairDigitPacketMoment*.lean` use the BANK reference only through
`L3.DigitPacketTransport.laneStep`. Here they are restated at an arbitrary `WidthDigitReference`
with `hfix` (the singleton class fixes the word root) through `L3.WidthPacketMoment.widthLaneStep`
and `widthLaneTransfer`, with the budgets of the BANK statements:

* `widthReleaseMoment` (`R(2R+2)`), `widthUMoment` (`uBudget R`), `widthRetMoment` (`2R`),
  `widthPrepCut` (`uBudget R + 2R`), `widthVMoment`, `widthVMomentAt`, `widthVAlignAt`
  (`(R+2)(2R+2)`), `widthPrepMoment`, `widthFinishMoment` (`R + 1`), `widthFrontMoment` (`R`);
* `widthAfterRace` / `widthAfterRaceDone`: the success continuation after the outgoing race
  edge, `w^{afterBudget R + B_s}` and `w^{2R² + 8R + 5}`;
* `widthRaceAlignStep`, `widthRaceAlignPend`: the race class `VTA R m` and the race inputs of
  `L3.PacketMomentWide.attemptLoopWide`;
* `bankRaceAlignPendCheck`: the BANK instance is `L3.PacketMomentTrialEnd.raceAlignPend`.

The audit-ghost layer (`Cells`, `Labels`, `GroupLabels`, `Carry`) is not restated here.
-/

namespace L3.WidthPacketMoment

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Classical
open K2ArbitraryElimination.FiniteAccounting
open L3
open L3.PairMoment
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.WidthDigit
open L3.DigitPacketRelease
open L3.DigitPacketOrder
open L3.PacketMomentRelease
open L3.MarkedCells
open L3.PacketMomentRows
open L3.PacketMomentWindow
open L3.PacketMomentPending
open L3.PacketMomentU
open L3.PacketMomentRetire
open L3.PacketMomentV
open L3.PacketMomentVSerial
open L3.PacketMomentPrep
open L3.PacketMomentFinish
open L3.PacketMomentAfter
open L3.PacketMomentTrialEnd

section Phases

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
  (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
    WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (N : Nat) (hN : n < N)

include hfix hn hsrc hend hN

/-- **The release phase** at a digit reference (generic
`L3.PacketMomentRelease.releaseMomentCoupled`). Consumer: the per-pair moment at the band
reference. -/
theorem widthReleaseMoment (hR : 2 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => BorderFree R (widthLaneOfState ref root lane src R y)) N
      (N ^ (R * (2 * R + 2))) ((N - n) ^ (R * (2 * R + 2))) x :=
  widthLaneMoment ref hfix hn root lane src R hR hsrc hend (BorderFree R) N _ _ hN
    (releaseWeightLe R _) x hx
    (releaseMoment hR (by omega) N (Nat.le_of_lt hN) (fun k => digitSite ring root (src + k))
      (cohortEdgeOf root src R) (fun k hk => cohortEdgeOfSite ring root src R hend k hk) _)

/-- **Phase U** at a digit reference (generic `L3.PacketMomentU.uMomentCoupled`). Consumer:
`widthPrepCut`. -/
theorem widthUMoment (hR : 3 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hinv : Inv R (winOf R (widthLaneOfState ref root lane src R x)))
    (hbar : Barrier R (winOf R (widthLaneOfState ref root lane src R x))) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => ¬ WinSettled R (widthLaneOfState ref root lane src R y)) N
      (N ^ uBudget R) ((N - n) ^ uBudget R) x :=
  widthLaneTransfer ref hfix hn root lane src R (by omega) hsrc hend
    (uNext R (cohortEdgeOf root src R)) Prod.fst (fun _ _ => rfl) (fun s => ¬ WinSettled R s)
    N _ (uBudget R) hN (uPot_le R (by omega) _) x hx
    (widthLaneOfState ref root lane src R x, fun _ => False) rfl
    (uMoment R hR (by omega) N (Nat.le_of_lt hN) (fun k => digitSite ring root (src + k))
      (cohortEdgeOf root src R) (fun k hk => cohortEdgeOfSite ring root src R hend k hk) _
      (winStart R _ hinv hbar))

/-- **The retirement** at a digit reference (generic
`L3.PacketMomentRetire.retMomentCoupled`). Consumer: `widthPrepCut`. -/
theorem widthRetMoment (hR : 2 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hs : RetInv R (widthLaneOfState ref root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => PacketOnly R (widthLaneOfState ref root lane src R y)) N
      (N ^ (2 * R)) ((N - n) ^ (2 * R)) x :=
  widthLaneMoment ref hfix hn root lane src R hR hsrc hend (PacketOnly R) N _ _ hN
    (obS_le R _) x hx
    (retMoment R hR (by omega) N (Nat.le_of_lt hN) (fun k => digitSite ring root (src + k))
      (cohortEdgeOf root src R) (fun k hk => cohortEdgeOfSite ring root src R hend k hk) _ hs)

omit hN in
/-- **The aligned queue with the window invariants is kept** at a digit reference (generic
`L3.PacketMomentPrep.winAlignedCoupled`). Consumer: `widthPrepCut`. -/
theorem widthWinAlignedStep (hR : 2 ≤ R)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : WidthCohortLayout ref root src R y.1 ∧
      WinAligned R (widthLaneOfState ref root lane src R y)) :
    WidthCohortLayout ref root src R (widthDigitAuditNext ref y e).1 ∧
      WinAligned R (widthLaneOfState ref root lane src R (widthDigitAuditNext ref y e)) := by
  obtain ⟨h1, h2⟩ := widthLaneStep ref hfix hn root lane src R hR hsrc hend y h.1 e
  rw [h2]
  exact ⟨h1, winAlignedKeep R hR _ _ h.2⟩

/-- **Phase U and the retirement in the aligned queue** at a digit reference (generic
`L3.PacketMomentPrep.prepCutCoupled`). Consumer: `widthPrepMoment`; the failure return. -/
theorem widthPrepCut (hR : 3 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hs : WinAligned R (widthLaneOfState ref root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => PacketOnly R (widthLaneOfState ref root lane src R y) ∧
        (WidthCohortLayout ref root src R y.1 ∧
          WinAligned R (widthLaneOfState ref root lane src R y))) N
      (N ^ uBudget R * N ^ (2 * R)) ((N - n) ^ uBudget R * (N - n) ^ (2 * R)) x := by
  let next := widthDigitAuditNext ref
  let I : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop :=
    fun y => WidthCohortLayout ref root src R y.1 ∧
      WinAligned R (widthLaneOfState ref root lane src R y)
  have hI : ∀ y e, I y → I (next y e) := fun y e h =>
    widthWinAlignedStep ref hfix hn root lane src R hsrc hend (by omega) y e h
  have hU := momentKeep next _ I N _ _ hI x ⟨hx, hs⟩
    (widthUMoment ref hfix hn root lane src R hsrc hend N hN hR x hx hs.2.1 hs.2.2)
  refine momentSeq next _ _ N _ _ _ _ x
    (Nat.pow_le_pow_left (Nat.sub_le N n) _) (fun y hy => ?_) hU
  obtain ⟨hns, hl, hw⟩ := hy
  exact momentKeep next _ I N _ _ hI y ⟨hl, hw⟩
    (widthRetMoment ref hfix hn root lane src R hsrc hend N hN (by omega) y hl
      (retStartOfU R _ hns hw.2.2))

/-- **The renewal trial** at a digit reference (generic `L3.PacketMomentV.vMomentCoupled`).
Consumer: `widthPrepMoment`. -/
theorem widthVMoment (hR : 3 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hs : VI R (widthLaneOfState ref root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => VT R (widthLaneOfState ref root lane src R y)) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x :=
  widthLaneMoment ref hfix hn root lane src R (by omega) hsrc hend (VT R) N _ _ hN
    (vPotLe R _ hs) x hx
    (vMoment R hR (by omega) N (Nat.le_of_lt hN) (fun k => digitSite ring root (src + k))
      (cohortEdgeOf root src R) (fun k hk => cohortEdgeOfSite ring root src R hend k hk) _ hs)

/-- **U, retirement and the renewal trial composed** at a digit reference (generic
`L3.PacketMomentPrep.prepMomentCoupled`). Consumer: the attempt of the per-pair moment at the
band reference (`B_p` of `L3.PacketMomentWide.attemptLoopWide`). -/
theorem widthPrepMoment (hR : 3 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hs : WinAligned R (widthLaneOfState ref root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => VT R (widthLaneOfState ref root lane src R y)) N
      (N ^ uBudget R * N ^ (2 * R) * N ^ ((R + 2) * vK R))
      ((N - n) ^ uBudget R * (N - n) ^ (2 * R) * (N - n) ^ ((R + 2) * vK R)) x := by
  refine momentSeq _ _ _ N _ _ _ _ x
    (Nat.pow_le_pow_left (Nat.sub_le N n) _) (fun y hy => ?_)
    (widthPrepCut ref hfix hn root lane src R hsrc hend N hN hR x hx hs)
  obtain ⟨hP, hl, ⟨a, hA⟩, _⟩ := hy
  exact widthVMoment ref hfix hn root lane src R hsrc hend N hN hR y hl
    (viOfPacketOnly R a _ hA hP)

/-- **The renewal trial with its exact outcome** at a digit reference (generic
`L3.PacketMomentVSerial.vMomentAtCoupled`). Consumer: `widthAfterRaceGroup`. -/
theorem widthVMomentAt (hR : 3 ≤ R) (m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hs : VIAt R m (widthLaneOfState ref root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => VTAt R m (widthLaneOfState ref root lane src R y)) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x := by
  have hvi : VI R (widthLaneOfState ref root lane src R x) := by
    obtain ⟨a, i, hai, hA, hS, _⟩ := hs
    exact ⟨a, i, hai, hA, hS⟩
  exact widthLaneMoment ref hfix hn root lane src R (by omega) hsrc hend (VTAt R m) N _ _ hN
    (vPotLe R _ hvi) x hx
    (vMomentAt R hR (by omega) N (Nat.le_of_lt hN) (fun k => digitSite ring root (src + k))
      (cohortEdgeOf root src R) (fun k hk => cohortEdgeOfSite ring root src R hend k hk) m _ hs)

/-- **The renewal trial ends at a group boundary** at a digit reference (generic
`L3.PacketMomentTrialEnd.vAlignAtCoupled`). Consumer: the race class `VTA R m` of
`widthRaceAlignPend` at the band reference. -/
theorem widthVAlignAt (hR : 3 ≤ R) (m : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hs : VIAt R m (widthLaneOfState ref root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => VTA R m (widthLaneOfState ref root lane src R y)) N
      (N ^ ((R + 2) * vK R)) ((N - n) ^ ((R + 2) * vK R)) x := by
  have hvi : VI R (widthLaneOfState ref root lane src R x) := by
    obtain ⟨a, i, hai, hA, hS, _⟩ := hs
    exact ⟨a, i, hai, hA, hS⟩
  exact widthLaneMoment ref hfix hn root lane src R (by omega) hsrc hend (VTA R m) N _ _ hN
    (vPotLe R _ hvi) x hx
    (vAlignAt R hR (by omega) N (Nat.le_of_lt hN) (fun k => digitSite ring root (src + k))
      (cohortEdgeOf root src R) (fun k hk => cohortEdgeOfSite ring root src R hend k hk) m _ hs)

/-- **The aligned finish** at a digit reference (generic
`L3.PacketMomentFinish.finishMomentCoupled`). Consumer: `widthAfterRaceDone`. -/
theorem widthFinishMoment (hR : 2 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hs : AGroup R (widthLaneOfState ref root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => ADone R (widthLaneOfState ref root lane src R y)) N
      (N ^ (R + 1)) ((N - n) ^ (R + 1)) x :=
  widthLaneMoment ref hfix hn root lane src R hR hsrc hend (ADone R) N _ _ hN
    (aPotLe R _) x hx
    (finishMoment R hR (by omega) N (Nat.le_of_lt hN) (fun k => digitSite ring root (src + k))
      (cohortEdgeOf root src R) (fun k hk => cohortEdgeOfSite ring root src R hend k hk) _
      (Or.inl hs))

/-- **The front phase** at a digit reference (generic
`L3.PacketMomentAfter.frontMomentCoupled`). Consumer: `widthAfterRaceGroup`. -/
theorem widthFrontMoment (a : Nat) (hR : 2 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hs : FI R a (widthLaneOfState ref root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => DoneW R a (widthLaneOfState ref root lane src R y)) N
      (N ^ R) ((N - n) ^ R) x :=
  widthLaneMoment ref hfix hn root lane src R hR hsrc hend (DoneW R a) N _ _ hN
    (fPotLe R _) x hx
    (frontMoment R a hR (by omega) N (Nat.le_of_lt hN) (fun k => digitSite ring root (src + k))
      (cohortEdgeOf root src R) (fun k hk => cohortEdgeOfSite ring root src R hend k hk) _ hs)

omit hN in
/-- **The outgoing edge wins** at a digit reference (generic
`L3.PacketMomentAfter.frontOfRaceCoupled`). Consumer: `widthAfterRaceGroup`. -/
theorem widthFrontOfRace (a m : Nat) (hR : 3 ≤ R) (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hV : VTAt R m (widthLaneOfState ref root lane src R x))
    (hA : AlignExt R a (widthLaneOfState ref root lane src R x))
    (hI : Inv R (winOf R (widthLaneOfState ref root lane src R x)))
    (hB : Barrier R (winOf R (widthLaneOfState ref root lane src R x))) :
    WidthCohortLayout ref root src R
        (widthDigitAuditNext ref x (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))).1 ∧
      FI R a (widthLaneOfState ref root lane src R
        (widthDigitAuditNext ref x (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m)))) := by
  obtain ⟨h1, h2⟩ := widthLaneStep ref hfix hn root lane src R (by omega) hsrc hend x hx
    (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))
  refine ⟨h1, 2 * R - 1 - m, ?_⟩
  rw [h2]
  unfold L3.DigitPacketRace.raceOut
  rw [cohortEdgeOfSite ring root src R hend (R + (R - 1 - m)) (by omega),
    show R + (R - 1 - m) = 2 * R - 1 - m by omega]
  exact frontOfRace R a m hR hm1 hm2 _ hV hA hI hB

/-- **After the outgoing race edge, to the aligned group** at a digit reference (generic
`L3.PacketMomentAfter.afterRaceGroupMoment`), `E[z^T] ≤ w^{R + (R+2)(2R+2)}`. Consumer:
`widthAfterRace`. -/
theorem widthAfterRaceGroup (m : Nat) (hR : 3 ≤ R) (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hp : VTA R m (widthLaneOfState ref root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => AGroup R (widthLaneOfState ref root lane src R y) ∧
        WidthCohortLayout ref root src R y.1) N
      (N ^ R * N ^ ((R + 2) * vK R)) ((N - n) ^ R * (N - n) ^ ((R + 2) * vK R))
      (widthDigitAuditNext ref x (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))) := by
  let next := widthDigitAuditNext ref
  let I : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop :=
    fun y => WidthCohortLayout ref root src R y.1
  have hIs : ∀ y e, I y → I (next y e) := fun y e h =>
    (widthLaneStep ref hfix hn root lane src R (by omega) hsrc hend y h e).1
  obtain ⟨hl0, hfi⟩ := widthFrontOfRace ref hfix hn root lane src R hsrc hend (R - 1) m hR
    hm1 hm2 x hx hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  have hF := momentKeep next _ I N _ _ hIs _ hl0
    (widthFrontMoment ref hfix hn root lane src R hsrc hend N hN (R - 1) (by omega) _ hl0 hfi)
  refine momentSeq next _ _ N _ _ _ _ _
    (Nat.pow_le_pow_left (Nat.sub_le N n) _) (fun y hy => ?_) hF
  obtain ⟨hd, hly⟩ := hy
  exact momentKeep next _ I N _ _ hIs y hly
    (widthVMomentAt ref hfix hn root lane src R hsrc hend N hN hR (R - 1) y hly
      (viAtOfCleared R (by omega) _ hd))

/-- **`F_a`, the success continuation of the race**, at a digit reference (generic
`L3.PacketMomentTrialEnd.afterRaceAligned`): `E[z^T] ≤ w^{afterBudget R + B_s}`. Consumer:
`widthRaceAlignPend`, `widthAfterRaceDone`. -/
theorem widthAfterRace (m : Nat) (hR : 3 ≤ R) (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R)
    (P : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop) (Bs : Nat)
    (hP : ∀ y, WidthCohortLayout ref root src R y.1 →
      AGroup R (widthLaneOfState ref root lane src R y) →
      MomentBoundQ (widthDigitAuditNext ref) P N (N ^ Bs) ((N - n) ^ Bs) y)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hp : VTA R m (widthLaneOfState ref root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext ref) P N
      (N ^ (afterBudget R + Bs)) ((N - n) ^ (afterBudget R + Bs))
      (widthDigitAuditNext ref x (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))) := by
  have h := momentSeq (widthDigitAuditNext ref) P _ N _ _ _ _ _
    (Nat.pow_le_pow_left (Nat.sub_le N n) _) (fun y hy => hP y hy.2 hy.1)
    (widthAfterRaceGroup ref hfix hn root lane src R hsrc hend N hN m hR hm1 hm2 x hx hp)
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add] at h
  exact h

/-- **`F_a` to the finished group** at a digit reference (generic
`L3.PacketMomentTrialEnd.afterRaceDoneAligned`), `E[z^T] ≤ w^{2R² + 8R + 5}`, the post-race
budget checked by `L3.PacketMomentAfter.afterBudgetShort`. Consumer: the post-race success branch
of `L3.PacketMomentWide.attemptLoopWide` at the band reference. -/
theorem widthAfterRaceDone (m : Nat) (hR : 3 ≤ R) (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hp : VTA R m (widthLaneOfState ref root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext ref)
      (fun y => ADone R (widthLaneOfState ref root lane src R y) ∧
        WidthCohortLayout ref root src R y.1) N
      (N ^ (afterBudget R + (R + 1))) ((N - n) ^ (afterBudget R + (R + 1)))
      (widthDigitAuditNext ref x (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m))) :=
  widthAfterRace ref hfix hn root lane src R hsrc hend N hN m hR hm1 hm2 _ (R + 1)
    (fun y hy hg => momentKeep (widthDigitAuditNext ref) _
      (fun y => WidthCohortLayout ref root src R y.1) N _ _
      (fun z e hz => (widthLaneStep ref hfix hn root lane src R (by omega) hsrc hend z hz e).1) y hy
      (widthFinishMoment ref hfix hn root lane src R hsrc hend N hN (by omega) y hy hg))
    x hx hp

omit hN in
/-- **The race class** at a digit reference (generic
`L3.PacketMomentTrialEnd.raceAlignStep`): `VTA R m` and the layout are kept off the two race
edges. Consumer: `widthRaceAlignPend`. -/
theorem widthRaceAlignStep (m : Nat) (hR : 3 ≤ R) (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (hp : VTA R m (widthLaneOfState ref root lane src R x)) (e : Fin n)
    (h1 : e ≠ L3.DigitPacketRace.raceIn ring root src R (R - 1 - m))
    (h2 : e ≠ L3.DigitPacketRace.raceOut ring root src R (R - 1 - m)) :
    WidthCohortLayout ref root src R (widthDigitAuditNext ref x e).1 ∧
      VTA R m (widthLaneOfState ref root lane src R (widthDigitAuditNext ref x e)) := by
  obtain ⟨hl1, hl2⟩ := widthLaneStep ref hfix hn root lane src R (by omega) hsrc hend x hx e
  refine ⟨hl1, ?_⟩
  rw [hl2]
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  unfold cohortEdgeOf
  rw [cohortIdxSite ring root j hj]
  by_cases hin : src ≤ j ∧ j < src + 2 * R
  · rw [if_pos hin]
    have hk1 : j - src ≠ 2 * R - 2 - m := by
      intro hk
      exact h1 (by unfold L3.DigitPacketRace.raceIn; congr 1; omega)
    have hk2 : j - src ≠ 2 * R - 1 - m := by
      intro hk
      exact h2 (by unfold L3.DigitPacketRace.raceOut; congr 1; omega)
    exact raceKeep R m (j - src) hR hm1 hm2 _ hp hk1 hk2
  · rw [if_neg hin]
    exact hp

/-- **The race inputs of the wide attempt loop** at a digit reference (generic
`L3.PacketMomentTrialEnd.raceAlignPend`): distinct race edges, the race class kept off them, and
`F_a` after the outgoing edge. Consumer: the per-pair moment at the band reference (SMALL:
`hcmpMomentSmall` / `hwriterSmall` of the headline). -/
theorem widthRaceAlignPend (m : Nat) (hR : 3 ≤ R) (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R)
    (P : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop) (Bs : Nat)
    (hP : ∀ y, WidthCohortLayout ref root src R y.1 →
      AGroup R (widthLaneOfState ref root lane src R y) →
      MomentBoundQ (widthDigitAuditNext ref) P N (N ^ Bs) ((N - n) ^ Bs) y) :
    L3.DigitPacketRace.raceOut ring root src R (R - 1 - m) ≠
        L3.DigitPacketRace.raceIn ring root src R (R - 1 - m) ∧
      (∀ x, WidthCohortLayout ref root src R x.1 →
        VTA R m (widthLaneOfState ref root lane src R x) →
        ∀ e, e ≠ L3.DigitPacketRace.raceOut ring root src R (R - 1 - m) →
          e ≠ L3.DigitPacketRace.raceIn ring root src R (R - 1 - m) →
          WidthCohortLayout ref root src R (widthDigitAuditNext ref x e).1 ∧
            VTA R m (widthLaneOfState ref root lane src R (widthDigitAuditNext ref x e))) ∧
      (∀ x, WidthCohortLayout ref root src R x.1 →
        VTA R m (widthLaneOfState ref root lane src R x) →
        MomentBoundQ (widthDigitAuditNext ref) P N
          (N ^ (afterBudget R + Bs)) ((N - n) ^ (afterBudget R + Bs))
          (widthDigitAuditNext ref x (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m)))) :=
  ⟨fun he => L3.DigitPacketRace.raceInNe ring root src R (R - 1 - m) (by omega) (by omega) he.symm,
    fun x hx hp e ha hb => widthRaceAlignStep ref hfix hn root lane src R hsrc hend m hR
      hm1 hm2 x hx hp e hb ha,
    fun x hx hp => widthAfterRace ref hfix hn root lane src R hsrc hend N hN m hR hm1 hm2 P Bs hP
      x hx hp⟩

end Phases

/-- **Port check**: at the BANK reference the generic race inputs are
`L3.PacketMomentTrialEnd.raceAlignPend`. Consumer: none in the chain; it checks the port. -/
theorem bankRaceAlignPendCheck {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R m : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hm1 : 1 ≤ m) (hm2 : m + 2 ≤ R) (N : Nat) (hN : n < N)
    (P : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop)
    (Bs : Nat)
    (hP : ∀ y, CohortLayout ring hbank root src R y.1 →
      AGroup R (L3.DigitPacketTransport.laneOfState ring hbank root lane src R y) →
      MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) P N
        (N ^ Bs) ((N - n) ^ Bs) y) :
    L3.DigitPacketRace.raceOut ring root src R (R - 1 - m) ≠
        L3.DigitPacketRace.raceIn ring root src R (R - 1 - m) ∧
      (∀ x, CohortLayout ring hbank root src R x.1 →
        VTA R m (L3.DigitPacketTransport.laneOfState ring hbank root lane src R x) →
        ∀ e, e ≠ L3.DigitPacketRace.raceOut ring root src R (R - 1 - m) →
          e ≠ L3.DigitPacketRace.raceIn ring root src R (R - 1 - m) →
          CohortLayout ring hbank root src R
              (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).1 ∧
            VTA R m (L3.DigitPacketTransport.laneOfState ring hbank root lane src R
              (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e))) ∧
      (∀ x, CohortLayout ring hbank root src R x.1 →
        VTA R m (L3.DigitPacketTransport.laneOfState ring hbank root lane src R x) →
        MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) P N
          (N ^ (afterBudget R + Bs)) ((N - n) ^ (afterBudget R + Bs))
          (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
            (L3.DigitPacketRace.raceOut ring root src R (R - 1 - m)))) :=
  widthRaceAlignPend (bankWidthDigitReference ring hn hbank) (fun _ _ h => h.2) hn root lane src R
    hsrc hend N hN m hR hm1 hm2 P Bs hP

end L3.WidthPacketMoment

#print axioms L3.WidthPacketMoment.widthReleaseMoment
#print axioms L3.WidthPacketMoment.widthUMoment
#print axioms L3.WidthPacketMoment.widthRetMoment
#print axioms L3.WidthPacketMoment.widthPrepCut
#print axioms L3.WidthPacketMoment.widthPrepMoment
#print axioms L3.WidthPacketMoment.widthVMomentAt
#print axioms L3.WidthPacketMoment.widthVAlignAt
#print axioms L3.WidthPacketMoment.widthFinishMoment
#print axioms L3.WidthPacketMoment.widthFrontMoment
#print axioms L3.WidthPacketMoment.widthAfterRace
#print axioms L3.WidthPacketMoment.widthAfterRaceDone
#print axioms L3.WidthPacketMoment.widthRaceAlignPend
#print axioms L3.WidthPacketMoment.bankRaceAlignPendCheck
