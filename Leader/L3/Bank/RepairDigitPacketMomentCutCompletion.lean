import Leader.L3.Bank.RepairDigitPacketMomentGroupCompletion
import Leader.L3.Bank.RepairDigitPacketMomentCutLabels

/-!
# Lemma e-packet with a cut: the aligned completion with cut `c`

`L3.PacketMomentGroupCompletion` with the cut of the completion as a parameter: when the labels of
the trial are stamped after `c` (`L3.PacketMomentCutLabels.LabelCut`), the aligned group's
terminal is a `DigitCompletion … lane c` (`completionOfChiC`, `groupCompletionC`,
`groupDoneMomentC`, `alignedMomentC`). Same proofs; the only new input is the time of the
group's samples (`groupSamplesC`). At `c = 0` these are the uncut statements.
-/

namespace L3.PacketMomentCutCompletion

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
open L3.GhostBridge
open L3.WidthDigit
open L3.DigitPacketTransport
open L3.DigitPacketQueue
open L3.CohortIdentity
open L3.CohortWindow
open L3.CohortLedger
open L3.HClose
open L3.ValueLedger
open L3.PacketMomentPrep
open L3.PacketMomentV
open L3.PacketMomentVSerial
open L3.PacketMomentFinish
open L3.PacketMomentCells
open L3.PacketMomentLabels
open L3.PacketMomentTrialLabels
open L3.PacketMomentGroupLabels
open L3.PacketMomentTrialEnd
open L3.PacketMomentCarry
open L3.PacketMomentHeldQueue
open L3.PacketMomentGroupCompletion
open L3.PacketMomentCutLabels

section Coupled

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat)

/-- **The receipt from a window on one audit** (`L3.CloseReceipt.completionOfReceipt` with every
clause read on the audit `A` itself): a window `chi` (`chi 0` the oldest crossing), sampled
exactly, gap-free on `A`, stamped at most `t0`, and a terminal recorded on `A` whose clean ledger
carries the crossings in reverse order after `t0`, give `DigitCompletion` with cut `cut` (`completionOfChi` with the cut).
Consumer: `groupCompletion`. -/
theorem completionOfChiC (hR : 2 ≤ R) (cut : Nat) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hpair : DigitCompletePair ring root A.start src (src + R))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (hU : DigitRecordedTerminal A U)
    (hUl : U.lane = lane) (hUs : U.source = digitSite ring root (src + (2 * R - 1)))
    (hUd : U.destination = digitSite ring root (src + 2 * R)) (hclk : U.time ≤ A.clock)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hrec : ∀ i, i < R → DigitRecordedExport A (chi i) ∧ OnEdge ring root lane src R (chi i) ∧
      (chi i).destination = digitSite ring root (src + R))
    (hinc : ∀ a b, a < b → b < R → (chi a).time < (chi b).time)
    (hextra : ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport A x →
      OnEdge ring root lane src R x → (chi 0).time ≤ x.time → x.time ≤ (chi (R - 1)).time →
      ∃ i, i < R ∧ x = chi i)
    (samp : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hsamp : ∀ i, i < R →
      DigitRecordedSample A (samp i) ∧ (chi i).operand = some (.sampled (samp i).id) ∧
      (samp i).id.lane = lane ∧ (samp i).id.site = digitSite ring root (src + (R - 1 - i)) ∧
      cut < (samp i).id.time ∧ (samp i).id.time < (chi i).time ∧
      (chi i).value = (samp i).value ∧ (chi i).tail = (samp i).tail ∧
      (samp i).tail = decide (R - 1 - i = 0))
    (t0 : Nat) (hchiT : ∀ i, i < R → (chi i).time ≤ t0)
    (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n) (hL : U.ledger = some L)
    (hLi : L.inherited = none) (hLl : L.uses.length = R)
    (hLu : L3.CohortLedger.UsesOk ring root src R U.time L.uses)
    (huse : ∀ j (u : DigitUse (compileAdvice (ceilLogTwo n)) n), L.uses[j]? = some u →
      u.operand = (chi (R - 1 - j)).operand ∧ u.value = (chi (R - 1 - j)).value ∧
      u.tail = (chi (R - 1 - j)).tail ∧ t0 < u.time) :
    DigitCompletion ring A root src (src + R) lane cut U := by
  have hspan : digitSpan (compileAdvice (ceilLogTwo n)) = R := by
    have := hpair.2.1
    omega
  refine ⟨hpair, hU, hUl, ?_, ?_, hclk, by omega, L,
    fun j => samp (R - 1 - j.val), fun j => chi (R - 1 - j.val),
    fun j => L.uses[j.val]'(by have := j.isLt; omega), hL, hLi, by omega, ?_, ?_, ?_⟩
  · rw [hUs]
    exact congrArg (digitSite ring root) (by omega)
  · rw [hUd]
    exact congrArg (digitSite ring root) (by omega)
  · intro j
    have hj := j.isLt
    have hjR : j.val < R := by omega
    have hi : R - 1 - j.val < R := by omega
    have hback : R - 1 - (R - 1 - j.val) = j.val := by omega
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hsamp (R - 1 - j.val) hi
    rw [hback] at s4 s9
    obtain ⟨x0, ⟨x1, x2⟩, x3⟩ := hrec (R - 1 - j.val) hi
    have hget : L.uses[j.val]? = some (L.uses[j.val]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    obtain ⟨u1, u2, u3, u4⟩ := huse j.val _ hget
    obtain ⟨v1, v2, -⟩ := hLu j.val _ hget
    have hct := hchiT (R - 1 - j.val) hi
    refine ⟨s1, s3, s4, s5, s9, x0, x1,
      x2.trans (congrArg (digitSite ring root) (by omega)), x3, s2, s7, s8, hget, v1,
      u1.trans s2, u2.trans s7, u3.trans s8, s6, Nat.lt_of_le_of_lt hct u4, v2⟩
  · intro i j hij
    have hj := j.isLt
    have hgi : L.uses[i.val]? = some (L.uses[i.val]'(by have := i.isLt; omega)) :=
      List.getElem?_eq_getElem (by have := i.isLt; omega)
    have hgj : L.uses[j.val]? = some (L.uses[j.val]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    exact ⟨hinc (R - 1 - j.val) (R - 1 - i.val) (by omega) (by omega),
      (hLu j.val _ hgj).2.2 i.val _ hij hgi⟩
  · intro other ho o1 o2 o3 o4 o5
    have e0 : R - 1 - (digitSpan (compileAdvice (ceilLogTwo n)) - 1) = 0 := by omega
    have e1 : R - 1 - 0 = R - 1 := by omega
    have o4' : (chi 0).time ≤ other.time := by
      have h4 := o4
      dsimp only at h4
      rw [e0] at h4
      exact h4
    have o5' : other.time ≤ (chi (R - 1)).time := by
      have h5 := o5
      dsimp only at h5
      rw [e1] at h5
      exact h5
    obtain ⟨i, hi, rfl⟩ := hextra other ho
      ⟨o1, o2.trans (congrArg (digitSite ring root) (by omega))⟩ o4' o5'
    refine ⟨⟨R - 1 - i, by omega⟩, ?_⟩
    show chi i = chi (R - 1 - (R - 1 - i))
    rw [show R - 1 - (R - 1 - i) = i by omega]


/-- **`groupCompletion` with the cut**: if the group's input atoms are stamped after `cut`, the
terminal is a `DigitCompletion` with cut `cut`. Consumer: `groupDoneMomentC`. -/
theorem groupCompletionC (hR : 2 ≤ R) (cut : Nat)
    (y z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hpair : DigitCompletePair ring root z.2.start src (src + R))
    (hfoY : AuditFrameOrder y.2)
    (hg : AGroup R (laneOfState ring hbank root lane src R y))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hq : HeldAt ring hbank root lane src R y χ)
    (hsamp : ∀ j, j < R →
      SampledAt ring root lane src R y.2 (laneCells ring root lane src y.2.current (R + j)).input j ∧
        AfterCut cut (laneCells ring root lane src y.2.current (R + j)).input)
    (hext : AuditExt y.2 z.2) (hfo : AuditFrameOrder z.2)
    (hxv : ExportVal ring root lane src R z.2) (huv : UseVal ring root lane src R z.2)
    (hlo : LedgerOk ring root lane src R z.2) (hfe : L3.CloseReceipt.FramesExact ring z.2)
    (htime : ∀ (x : DigitExport (compileAdvice (ceilLogTwo n)) n) (id : DigitStamp n),
      DigitRecordedExport z.2 x → OnEdge ring root lane src R x →
      x.operand = some (.sampled id) → id.time < x.time ∧ x.time ≤ z.2.clock)
    (hdone : TermDone ring hbank root lane src R y.2.clock
      (fun j => (laneCells ring root lane src y.2.current (R + j)).input) z) :
    ∃ U, DigitCompletion ring z.2 root src (src + R) lane cut U := by
  obtain ⟨U, hU, hUl, hUs, -, L, hL, hLi, hLlen, hops⟩ := hdone
  obtain ⟨g1, g2, g3⟩ := heldGroup ring hbank root lane src R (by omega) y hg χ hq
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
`alignedMomentC`, `successMomentC`. -/
theorem groupDoneMomentC (hR : 2 ≤ R) (cut : Nat) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop)
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hP : PairInv ring hbank root lane src R Base y)
    (hg : AGroup R (laneOfState ring hbank root lane src R y))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hq : HeldAt ring hbank root lane src R y χ)
    (hlab : TrialLabAtC ring hbank root lane src R cut (R - 1) y)
    (hpair : DigitCompletePair ring root y.2.start src (src + R)) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun z => ∃ U, DigitCompletion ring z.2 root src (src + R) lane cut U) N
      (N ^ (R + 1)) ((N - n) ^ (R + 1)) y := by
  have hfin := finishCarryMoment ring hn hbank root lane src R hR hsrc hend N hN y.2.clock
    (fun j => (laneCells ring root lane src y.2.current (R + j)).input) y
    (finInvStart ring hbank root lane src R y hP.1 hg) hg
  have hk := momentKeep (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) _
    (fun z => PairInv ring hbank root lane src R Base z ∧ AuditExt y.2 z.2) N _ _
    (fun z e hz => ⟨pairInvStep ring hn hbank root lane src R hR hsrc hend Base z hz.1 e,
      auditExtStep ring (piD z.1.val.1) y.2 z.2 e hz.2⟩) y ⟨hP, auditExtRefl y.2⟩ hfin
  refine momentWeaken _ _ _ N _ _ (fun z hz => ?_) y hk
  obtain ⟨⟨hd, hfi⟩, hPz, hext⟩ := hz
  have hpz : DigitCompletePair ring root z.2.start src (src + R) := by
    rw [hext.2.2.2]
    exact hpair
  exact groupCompletionC ring hbank root lane src R hR cut y z hpz hP.2.1 hg χ hq
    (fun j hj => groupSamplesC ring hbank root lane src R (by omega) cut y hg hlab j hj) hext hPz.2.1
    hPz.2.2.2.1.2.1 hPz.2.2.2.1.2.2.1 hPz.2.2.2.1.2.2.2 hPz.2.2.1 hPz.2.2.2.2.2.2.2.1
    (finishTerminal ring hbank root lane src R (by omega) _ _ z hd hfi)


/-- **`alignedMoment` with the cut**: from a labelled trial state of index `R - 1` whose labels are
stamped after `cut` (`LabelCut`), the completion with cut `cut` is reached with the same bound.
Consumer: `successMomentC`, `raceMomentC`. -/
theorem alignedMomentC (hR : 3 ≤ R) (cut : Nat) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (Base : Bool → DigitAtom n → Prop)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hP : PairInv ring hbank root lane src R Base x)
    (hpair : DigitCompletePair ring root x.2.start src (src + R))
    (hs : VIAt R (R - 1) (laneOfState ring hbank root lane src R x))
    (χ : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hq : HeldAt ring hbank root lane src R x χ) (σ : Nat → Option Nat)
    (hL : LabelOk ring root lane src R (laneOfState ring hbank root lane src R x) σ x.2)
    (hC : LabelCut ring root lane src R cut (laneOfState ring hbank root lane src R x) σ x.2)
    (ht : LabTrial R (R - 1) (laneOfState ring hbank root lane src R x) σ) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun z => ∃ U, DigitCompletion ring z.2 root src (src + R) lane cut U) N
      (N ^ ((R + 2) * vK R) * N ^ (R + 1)) ((N - n) ^ ((R + 2) * vK R) * (N - n) ^ (R + 1)) x := by
  have htr := momentKeepUntil (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (fun y => VTA R (R - 1) (laneOfState ring hbank root lane src R y))
    (fun y => HeldTrial ring hbank root lane src R (R - 1) y ∧
      (CohortLayout ring hbank root src R y.1 ∧ TrialLabAtC ring hbank root lane src R cut (R - 1) y) ∧
      PairInv ring hbank root lane src R Base y ∧
      DigitCompletePair ring root y.2.start src (src + R)) N _ _
    (fun y e h hnt => by
      have hvi : VIAt R (R - 1) (laneOfState ring hbank root lane src R y) := by
        rcases h.1.2.2.1 with hv | hv
        · exact hv
        · exact absurd hv hnt
      exact ⟨heldTrialStep ring hn hbank root lane src R hR hsrc hend (R - 1) y e h.1 hnt,
        trialLabCoupledC ring hn hbank root lane src R hR hsrc hend cut (R - 1) y e h.2.1
          (viNotVtAt R (R - 1) _ hvi),
        pairInvStep ring hn hbank root lane src R (by omega) hsrc hend Base y h.2.2.1 e,
        h.2.2.2⟩) x
    ⟨⟨hP.1, hP.2.1, Or.inl hs, χ, hq⟩, ⟨hP.1, σ, hL, hC, labTrialRun ht, Or.inl ht⟩, hP, hpair⟩
    (vAlignAtCoupled ring hn hbank root lane src R hR hsrc hend N hN (R - 1) x hP.1 hs)
  refine momentSeq _ _ _ N _ _ _ _ x (Nat.pow_le_pow_left (Nat.sub_le N n) _) (fun y hy => ?_) htr
  obtain ⟨hv, ⟨-, -, -, χ', hq'⟩, ⟨-, hlab⟩, hPy, hpy⟩ := hy
  exact groupDoneMomentC ring hn hbank root lane src R (by omega) cut hsrc hend N hN Base y hPy hv.1 χ'
    hq' hlab hpy


end Coupled

end L3.PacketMomentCutCompletion

#print axioms L3.PacketMomentCutCompletion.completionOfChiC
#print axioms L3.PacketMomentCutCompletion.groupCompletionC
#print axioms L3.PacketMomentCutCompletion.groupDoneMomentC
#print axioms L3.PacketMomentCutCompletion.alignedMomentC
