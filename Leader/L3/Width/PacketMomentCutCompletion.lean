import Leader.L3.Bank.RepairDigitPacketMomentCutCompletion
import Leader.L3.Width.PacketMomentGroupCompletion
import Leader.L3.Width.PacketMomentCutLabels

/-!
# Lemma e-packet with a cut at a boundary reference: the aligned completion

Generic form of the coupled part of `L3.PacketMomentCutCompletion`
(BankRepairDigitPacketMomentCutCompletion) at an arbitrary `WidthBoundaryReference`:
`widthGroupCompletionC`, `widthGroupDoneMomentC`, `widthAlignedMomentC` (`DigitCompletion` with cut
`c` when the labels are stamped after `c`), by the ports `L3.WidthPacketMomentGroupCompletion`,
`L3.WidthPacketMomentCutLabels`, `L3.WidthPacketMomentHeldQueue`, `L3.WidthPacketMomentCarry`.
`completionOfChiC` is used as it is. Consumer: `L3.WidthPacketMomentCutAttempt`, the SMALL
comparison lane (`hcmpMomentSmall`).
-/

namespace L3.WidthPacketMomentCutCompletion

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
open L3.PacketMomentCutLabels
open L3.PacketMomentCutCompletion
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentAudit
open L3.WidthPacketMomentCarry
open L3.WidthPacketMomentHeldQueue
open L3.WidthPacketMomentGroupCompletion
open L3.WidthPacketMomentCutLabels

section Ported

variable {n : Nat} (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat)

include hn

/-- **`groupCompletion` with the cut**: if the group's input atoms are stamped after `cut`, the
terminal is a `DigitCompletion` with cut `cut`. Consumer: `widthGroupDoneMomentC`. -/
theorem widthGroupCompletionC (hR : 2 ≤ R) (cut : Nat)
    (y z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hpair : DigitCompletePair ring root z.2.start src (src + R))
    (hfoY : AuditFrameOrder y.2)
    (hg : AGroup R (widthLaneOfState ref.toWidthDigitReference root lane src R y))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hq : WidthHeldAt ring ref root lane src R y χ)
    (hsamp : ∀ j, j < R →
      SampledAt ring root lane src R y.2 (laneCells ring root lane src y.2.current (R + j)).input j ∧
        AfterCut cut (laneCells ring root lane src y.2.current (R + j)).input)
    (hext : AuditExt y.2 z.2) (hfo : AuditFrameOrder z.2)
    (hxv : ExportVal ring root lane src R z.2) (huv : UseVal ring root lane src R z.2)
    (hlo : LedgerOk ring root lane src R z.2) (hfe : L3.CloseReceipt.FramesExact ring z.2)
    (htime : ∀ (x : DigitExport (compileAdvice (ceilLogTwo n)) n) (id : DigitStamp n),
      DigitRecordedExport z.2 x → OnEdge ring root lane src R x →
      x.operand = some (.sampled id) → id.time < x.time ∧ x.time ≤ z.2.clock)
    (hdone : WidthTermDone ring ref root lane src R y.2.clock
      (fun j => (laneCells ring root lane src y.2.current (R + j)).input) z) :
    ∃ U, DigitCompletion ring z.2 root src (src + R) lane cut U := by
  obtain ⟨U, hU, hUl, hUs, -, L, hL, hLi, hLlen, hops⟩ := hdone
  obtain ⟨g1, g2, g3⟩ := widthHeldGroup ring ref hn root lane src R (by omega) y hg χ hq
  have hchiY : ∀ i, i < R → DelExport ring root lane src R y.2 (χ (R + (R - 1 - i))) :=
    fun i _ => (g1 (R - 1 - i) (by omega)).1
  have hchi : ∀ i, i < R → DigitRecordedExport z.2 (χ (R + (R - 1 - i))) ∧
      OnEdge ring root lane src R (χ (R + (R - 1 - i))) := by
    intro i hi
    obtain ⟨h1, h2, h3, -⟩ := hchiY i hi
    exact ⟨exportOfExt _ _ hext _ h1, h2, h3⟩
  have hpin : SitePin ring root lane src R z.2 (fun i => χ (R + (R - 1 - i))) := by
    intro i hi
    obtain ⟨-, smp, ha, hsite, hl, htl, hrec⟩ := (hsamp (R - 1 - i) (by omega)).1
    refine ⟨smp, ?_, sampleOfExt _ _ hext _ hrec, hl, hsite, htl⟩
    show (χ (R + (R - 1 - i))).operand = some (.sampled smp.id)
    rw [← (g1 (R - 1 - i) (by omega)).2]
    exact ha
  obtain ⟨samp, hsampR⟩ := chiSampledOf ring root lane src R hR z.2 hfo hxv htime
    (fun i => χ (R + (R - 1 - i))) hchi hpin
  have huse : UseTrack R y.2.clock U (fun i => χ (R + (R - 1 - i))) := by
    refine ⟨L, hL, hLi, fun j u hj => ?_⟩
    obtain ⟨ho, ht⟩ := hops j u hj
    have hjR : j < R := by
      have := lengthOfGet L.uses j u hj
      omega
    refine ⟨?_, ht⟩
    show u.operand = (χ (R + (R - 1 - (R - 1 - j)))).operand
    rw [show R - 1 - (R - 1 - j) = j by omega, ← (g1 j hjR).2]
    exact ho
  have hchi' : ∀ i, i < R → DigitRecordedExport z.2 (χ (R + (R - 1 - i))) ∧
      OnEdge ring root lane src R (χ (R + (R - 1 - i))) ∧
      ∃ id, (χ (R + (R - 1 - i))).operand = some (.sampled id) := by
    intro i hi
    obtain ⟨s, hs, -⟩ := hpin i hi
    exact ⟨(hchi i hi).1, (hchi i hi).2, s.id, hs⟩
  obtain ⟨L', hL', hLi', hlen', hok', hu'⟩ := closeUsesOf ring root lane src R hR z.2 hfo hxv huv
    hlo (fun i => χ (R + (R - 1 - i))) hchi' y.2.clock U hU hUl hUs huse
  have hUd : U.destination = digitSite ring root (src + 2 * R) := by
    rw [L3.CloseReceipt.terminalDest ring z.2 hfe U hU, hUs,
      ← L3.CloseReceipt.digitSiteSucc ring root]
    exact congrArg (digitSite ring root) (by omega)
  have hclk : U.time ≤ z.2.clock := by
    obtain ⟨f, hf, hft, -⟩ := hU
    rw [← hft]
    exact (hfo.2.1 f hf).2
  have hchiT : ∀ i, i < R → (χ (R + (R - 1 - i))).time ≤ y.2.clock :=
    fun i hi => recordedTimeLe y.2 hfoY _ (hchiY i hi).1
  refine ⟨U, completionOfChiC ring root lane src R hR cut z.2 hpair U hU hUl hUs hUd hclk
    (fun i => χ (R + (R - 1 - i))) (fun i hi => ⟨(hchi i hi).1, (hchi i hi).2, (hchiY i hi).2.2.2⟩)
    (fun a b hab hb => g2 (R - 1 - b) (R - 1 - a) (by omega) (by omega)) ?_ samp
    (fun i hi => ⟨(hsampR i hi).1, (hsampR i hi).2.1, (hsampR i hi).2.2.1, (hsampR i hi).2.2.2.1,
      (hsamp (R - 1 - i) (by omega)).2 _ (by rw [(g1 (R - 1 - i) (by omega)).2]; exact (hsampR i hi).2.1),
      (hsampR i hi).2.2.2.2.2⟩)
    y.2.clock hchiT L' hL' hLi' hlen' hok' hu'⟩
  intro x hx hon h0 h1
  have h1' : x.time ≤ y.2.clock := Nat.le_trans h1 (hchiT (R - 1) (by omega))
  have hxy : DigitRecordedExport y.2 x := hext.2.2.1 x hx h1'
  have hdx : x.destination = digitSite ring root (src + R) := by
    rw [L3.CloseReceipt.exportDest ring z.2 hfe x hx, hon.2,
      ← L3.CloseReceipt.digitSiteSucc ring root]
    exact congrArg (digitSite ring root) (by omega)
  have h0' : (χ (2 * R - 1)).time ≤ x.time := by
    have e : 2 * R - 1 = R + (R - 1 - 0) := by omega
    rw [e]
    exact h0
  obtain ⟨j, hj, rfl⟩ := g3 x ⟨hxy, hon.1, hon.2, hdx⟩ h0'
  refine ⟨R - 1 - j, by omega, ?_⟩
  show χ (R + j) = χ (R + (R - 1 - (R - 1 - j)))
  rw [show R - 1 - (R - 1 - j) = j by omega]


/-- **`groupDoneMoment` with the cut** (the labelled trial after the cut). Consumer:
`widthAlignedMomentC`, `successMomentC`. -/
theorem widthGroupDoneMomentC (hR : 2 ≤ R) (cut : Nat) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hP : WidthPairInv ring ref root lane src R Base y)
    (hg : AGroup R (widthLaneOfState ref.toWidthDigitReference root lane src R y))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hq : WidthHeldAt ring ref root lane src R y χ)
    (hlab : WidthTrialLabAtC ring ref root lane src R cut (R - 1) y)
    (hpair : DigitCompletePair ring root y.2.start src (src + R)) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (fun z => ∃ U, DigitCompletion ring z.2 root src (src + R) lane cut U) N
      (N ^ (R + 1)) ((N - n) ^ (R + 1)) y := by
  have hfin := widthFinishCarryMoment ring ref hn root lane src R hR hsrc hend N hN y.2.clock
    (fun j => (laneCells ring root lane src y.2.current (R + j)).input) y
    (widthFinInvStart ring ref hn root lane src R y hP.1 hg) hg
  have hk := momentKeep (widthDigitAuditNext (ref.toWidthDigitReference)) _
    (fun z => WidthPairInv ring ref root lane src R Base z ∧ AuditExt y.2 z.2) N _ _
    (fun z e hz => ⟨widthPairInvStep ring ref hn root lane src R hR hsrc hend Base z hz.1 e,
      auditExtStep ring (piD (ref.phys z.1)) y.2 z.2 e hz.2⟩) y ⟨hP, auditExtRefl y.2⟩ hfin
  refine momentWeaken _ _ _ N _ _ (fun z hz => ?_) y hk
  obtain ⟨⟨hd, hfi⟩, hPz, hext⟩ := hz
  have hpz : DigitCompletePair ring root z.2.start src (src + R) := by
    rw [hext.2.2.2]
    exact hpair
  exact widthGroupCompletionC ring ref hn root lane src R hR cut y z hpz hP.2.1 hg χ hq
    (fun j hj => widthGroupSamplesC ring ref hn root lane src R (by omega) cut y hg hlab j hj) hext hPz.2.1
    hPz.2.2.2.1.2.1 hPz.2.2.2.1.2.2.1 hPz.2.2.2.1.2.2.2 hPz.2.2.1 hPz.2.2.2.2.2.2.2.1
    (widthFinishTerminal ring ref hn root lane src R (by omega) _ _ z hd hfi)


/-- **`alignedMoment` with the cut**: from a labelled trial state of index `R - 1` whose labels are
stamped after `cut` (`LabelCut`), the completion with cut `cut` is reached with the same bound.
Consumer: `successMomentC`, `raceMomentC`. -/
theorem widthAlignedMomentC (hR : 3 ≤ R) (cut : Nat) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hP : WidthPairInv ring ref root lane src R Base x)
    (hpair : DigitCompletePair ring root x.2.start src (src + R))
    (hs : VIAt R (R - 1) (widthLaneOfState ref.toWidthDigitReference root lane src R x))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hq : WidthHeldAt ring ref root lane src R x χ) (σ : Nat → Option Nat)
    (hL : LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2)
    (hC : LabelCut ring root lane src R cut (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2)
    (ht : LabTrial R (R - 1) (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (fun z => ∃ U, DigitCompletion ring z.2 root src (src + R) lane cut U) N
      (N ^ ((R + 2) * vK R) * N ^ (R + 1)) ((N - n) ^ ((R + 2) * vK R) * (N - n) ^ (R + 1)) x := by
  have htr := momentKeepUntil (widthDigitAuditNext (ref.toWidthDigitReference))
    (fun y => VTA R (R - 1) (widthLaneOfState ref.toWidthDigitReference root lane src R y))
    (fun y => WidthHeldTrial ring ref root lane src R (R - 1) y ∧
      (WidthCohortLayout ref.toWidthDigitReference root src R y.1 ∧ WidthTrialLabAtC ring ref root lane src R cut (R - 1) y) ∧
      WidthPairInv ring ref root lane src R Base y ∧
      DigitCompletePair ring root y.2.start src (src + R)) N _ _
    (fun y e h hnt => by
      have hvi : VIAt R (R - 1) (widthLaneOfState ref.toWidthDigitReference root lane src R y) := by
        rcases h.1.2.2.1 with hv | hv
        · exact hv
        · exact absurd hv hnt
      exact ⟨widthHeldTrialStep ring ref hn root lane src R hR hsrc hend (R - 1) y e h.1 hnt,
        widthTrialLabCoupledC ring ref hn root lane src R hR hsrc hend cut (R - 1) y e h.2.1
          (viNotVtAt R (R - 1) _ hvi),
        widthPairInvStep ring ref hn root lane src R (by omega) hsrc hend Base y h.2.2.1 e,
        h.2.2.2⟩) x
    ⟨⟨hP.1, hP.2.1, Or.inl hs, χ, hq⟩, ⟨hP.1, σ, hL, hC, labTrialRun ht, Or.inl ht⟩, hP, hpair⟩
    (widthVAlignAt ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend N hN hR (R - 1) x hP.1 hs)
  refine momentSeq _ _ _ N _ _ _ _ x (Nat.pow_le_pow_left (Nat.sub_le N n) _) (fun y hy => ?_) htr
  obtain ⟨hv, ⟨-, -, -, χ', hq'⟩, ⟨-, hlab⟩, hPy, hpy⟩ := hy
  exact widthGroupDoneMomentC ring ref hn root lane src R (by omega) cut hsrc hend N hN Base y hPy hv.1 χ'
    hq' hlab hpy


end Ported

end L3.WidthPacketMomentCutCompletion

#print axioms L3.WidthPacketMomentCutCompletion.widthGroupCompletionC
#print axioms L3.WidthPacketMomentCutCompletion.widthGroupDoneMomentC
#print axioms L3.WidthPacketMomentCutCompletion.widthAlignedMomentC
