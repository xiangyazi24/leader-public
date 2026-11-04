import Leader.Wu.Coherence.ReplayCores
import Leader.Wu.Coherence.FootprintCoverFresh
import Leader.Wu.Coherence.ReachableScrubLResiduals
import Leader.Wu.Coherence.ReachableOpenRIncomingSeek

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReplayProducers

open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePrepaid R2CoherenceV31ReachablePlus3
open R2CoherenceV31ReachablePlus4 R2CoherenceV31ReachableSoundParametric
open R2CoherenceV31ReachableFreshBranches3 R2CoherenceV31ReplayExport
open R2CoherenceV31MainClearTruth
open R2CoherenceV31MainClearTruth.WeakFreshnessLayer
open R2CoherenceV31FreshnessClear

variable {n ψ κ τ : Nat}

private theorem birthTrace_rp
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ)
    (h : ReachableFromV31 (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring)
      hψ h2 ring C) : ReachableFromQuarantineV31 hψ h2 ring C :=
  (reachableFromV31_birth_iff hψ h2 ring C).1 h

private theorem traceStep_rp
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : ReachableFromQuarantineV31 hψ h2 ring C) :
    ReachableFromQuarantineV31 hψ h2 ring (stepV3 hψ h2 ring C e) := by
  rcases h with ⟨C0, w, hb, hC⟩
  refine ⟨C0, w ++ [e], hb, ?_⟩
  rw [List.foldl_append, ← hC]
  rfl

private theorem prefixSelf_rp
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    R2Coherence.prefixPos ring (eraseCfgV3 C) i (raw (C i)).label.val = i := by
  apply Fin.ext
  simp [R2Coherence.prefixPos, R2Coherence.back,
    Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

private theorem ownerFresh_of_localCover_rp
    (ring : DirectedRing n) (D : FC n ψ κ τ)
    (hFacts : ReachablePhaseFactsV31 ring D) (owner : Fin n)
    (hp : PendingOpenROwnerV31 ring D owner)
    (hCover : ∀ p, InOpenRFreshFootprintV31 ring D owner p →
      MainClearV3 (D p) ∨
      InGroupOwnedFootprintV31 ring D (ring.rightNeighbor owner) p) :
    OpenROwnerFreshV3 ring D owner := by
  unfold OpenROwnerFreshV3 GroupIntrinsicFreshV3 IntrinsicFreshAtV3
  intro j ko hOwner q hEq
  let f := R2Coherence.groupPos ring (eraseCfgV3 D) j q.val
  have hf : InOpenRFreshFootprintV31 ring D owner f := by
    let k : Fin ((raw (D f)).label.val + 1) :=
      ⟨(raw (D f)).label.val, Nat.lt_succ_self _⟩
    refine ⟨j, ko, q, hOwner, k, ?_⟩
    simpa [f, k] using prefixSelf_rp ring D f
  have hG := (hFacts.2.2.2.2.1 (ring.rightNeighbor owner) hp.1).2.2
  have hm : MainClearV3 (D f) := by
    rcases hCover f hf with hm | hg
    · exact hm
    · rcases hg with ⟨k, hk⟩
      have z := (hG k).1
      rw [hk] at z
      exact z
  have hn : (raw (D f)).state = .none := by
    unfold MainClearV3 R2CoherenceBranches.MainClear at hm
    exact hm.1
  rw [hn] at hEq
  cases hEq

private theorem scrubLReplayCore_birthEntrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hPayload : R2CoherenceV31FootprintCover3.Cover3PayloadReachableV31
      (κ:=κ) (τ:=τ) hψ h2 ring)
    (hForeign : R2CoherenceV31ReachableCover2.ScrubLContinuationForeignPrefixMainClearV31
      (κ:=κ) (τ:=τ) hψ h2 ring) :
    ScrubLReplayCoreFreshExportP
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring := by
  intro C e hg ht hf hb
  dsimp only
  have hq := birthTrace_rp hψ h2 ring C ht
  have hPlus := hPayload C hq
  let D := stepV3 hψ h2 ring C e
  change ReachablePhaseFactsV31 ring D ∧
    ScrubLIncomingOpenRFreshV31 ring D ∧ OpenRForwardFreshnessClearV31 ring D
  have h1 : ReachablePhaseFactsV31 ring D := by
    simpa [D] using R2CoherenceV31ReachableScrubL.reachablePhaseFacts_scrubL_step
      hψ h2 ring C e hg hq hPlus hb
  have h7 : ScrubLIncomingOpenRFreshV31 ring D := by
    intro owner hs hu hr
    have hpD : PendingOpenROwnerV31 ring D owner := ⟨hs, hu, hr⟩
    by_cases hpC : PendingOpenROwnerV31 ring C owner
    · have hOld := hf.2.1 owner hpC.1 hpC.2.1 hpC.2.2
      simpa [D] using
        R2CoherenceV31ReachableScrubL2.scrubLReplay_oldOwnerFresh
          hψ h2 ring C e owner hg hPlus hb hOld
    · have hn : R2CoherenceV31ReachableScrubL3.ScrubLContinuationNewPendingV31
          hψ h2 ring C e owner := ⟨by simpa [D] using hpD, hpC⟩
      have hc := R2CoherenceV31ReachableCover2.scrubLContinuationNewPendingCover_of_foreignPrefix
        (κ:=κ) (τ:=τ) hψ h2 ring hForeign C e owner hg hq hPlus hb hn
      apply ownerFresh_of_localCover_rp ring D h1 owner hpD
      intro p hp
      simpa [D] using hc p (by simpa [D] using hp)
  have hR1 : OpenRForwardFreshnessClearV31 ring D :=
    R2CoherenceV31FreshnessClear.openRForwardFreshnessClear_of_old ring D (by
      simpa [D] using R2CoherenceV31ReachableScrubL2.openRForwardMainClear_scrubL_step
        hψ h2 ring C e hg hPlus hb)
  exact ⟨h1, h7, hR1⟩

theorem scrubLFreshPrivateReplay_birthEntrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hPayload : R2CoherenceV31FootprintCover3.Cover3PayloadReachableV31
      (κ:=κ) (τ:=τ) hψ h2 ring)
    (hForeign : R2CoherenceV31ReachableCover2.ScrubLContinuationForeignPrefixMainClearV31
      (κ:=κ) (τ:=τ) hψ h2 ring) :
    ScrubLFreshPrivateReplayV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring :=
  scrubLReplayFresh_of_core _ hψ h2 ring
    (scrubLReplayCore_birthEntrance hψ h2 ring hPayload hForeign)

private theorem openRReplayCore_birthEntrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hPayload : R2CoherenceV31FootprintCover3.Cover3PayloadReachableV31
      (κ:=κ) (τ:=τ) hψ h2 ring)
    (hCover : R2CoherenceV31FootprintCover4.PendingFootprintCoveredReachableFreshV31
      (κ:=κ) (τ:=τ) hψ h2 ring) :
    OpenRReplayCoreFreshExportP
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring := by
  intro hNew C e hg ht hf hb
  dsimp only
  have hq := birthTrace_rp hψ h2 ring C ht
  have hPlus := hPayload C hq
  let D := stepV3 hψ h2 ring C e
  change ReachablePhaseFactsFreshP3V31 ring D ∧
    SeekIncomingSweepOpenROverlapFreshWideV31 ring D
  have h16 : R2CoherenceV31ReachableOpenR2.ReachablePhaseFactsP1P6StrongR2V31 ring D := by
    simpa [D] using R2CoherenceV31ReachableOpenR2.openRStep_reachable_P1_P6
      hψ h2 ring C e hPlus hg hq hb
  rcases h16 with ⟨h15, h6⟩
  rcases h15 with ⟨p1, p2, p3, p4, p5⟩
  have h1 : ReachablePhaseFactsV31 ring D := ⟨p1, p2, p3, p4, p5, h6⟩
  have h7 : ScrubLIncomingOpenRFreshV31 ring D := by
    simpa [D] using R2CoherenceV31ReachableOpenR3.scrubLIncomingOpenRFresh_openR_step
      hψ h2 ring C e hPlus hg hq hb
  have h8old : SweepOpenROverlapClearV31 ring D := by
    simpa [D] using R2CoherenceV31ReachableOpenR3.sweepOpenROverlapClear_openR_step
      hψ h2 ring C e hPlus hb
  have h9old : SweepOpenROverlapClearWideV31 ring D := by
    simpa [D] using R2CoherenceV31ReachableOpenR3.sweepOpenROverlapClearWide_openR_step
      hψ h2 ring C e hPlus hb
  have h8 := R2CoherenceV31FreshnessClear.sweepOpenROverlapFresh_of_old ring D h8old
  have h9 := R2CoherenceV31FreshnessClear.sweepOpenROverlapFreshWide_of_old ring D h9old
  have htD : ReachableFromQuarantineV31 hψ h2 ring D := by
    simpa [D] using traceStep_rp hψ h2 ring C e hq
  have hgD : ElectionGeometryV31 ring D := by
    simpa [D] using
      ((R2CoherenceV31Closure2.electionGeometryStepV31 (κ:=κ) (τ:=τ) hψ h2 ring) C e hg)
  have hcD := hCover D htD hgD
  have hPhase := R2CoherenceV31ReachableSweep.phaseMainClear_of_reachablePhaseFacts
    ring D h1
  have safeD : ∀ o p, PendingOpenROwnerV31 ring D o →
      SweepOpenRSafeFreshV31 ring D o p := by
    intro o p hp
    exact R2CoherenceV31OpenNoHazardServedCover.pendingSafeFresh_of_coveredFresh
      ring D hPhase hcD o p hp
  have hSD : SeekIncomingSweepOpenROverlapFreshWideV31 ring D := by
    intro pred owner hSeekD hPendD
    by_cases hnew : ring.rightNeighbor pred = e
    · have hbad := R2CoherenceV31ReachableOpenR5.openRReplay_newSeek_is_bad
        hψ h2 ring C e pred hb hnew (by simpa [D] using hSeekD)
      constructor
      · intro _
        exact ⟨safeD owner (ring.rightNeighbor (ring.rightNeighbor pred)) hPendD,
          fun d => safeD owner (R2Coherence.fwd ring (ring.rightNeighbor pred) d.val) hPendD⟩
      · intro hn hr
        simpa [D, hnew] using
          (hNew C e pred owner hg ht hf hb hbad hnew
            (by simpa [D] using hPendD)
            (by simpa [D, hnew] using hn) (by simpa [D, hnew] using hr))
    · have hOld := R2CoherenceV31ReachableOpenR5.openRReplay_oldSeekClearWide
        hψ h2 ring C e pred owner hPlus.2.1 hb hnew
        (by simpa [D] using hSeekD) (by simpa [D] using hPendD)
      dsimp only at hOld
      constructor
      · intro hr
        rcases hOld.1 (by simpa [D] using hr) with ⟨ha, ht⟩
        exact ⟨sweepOpenRSafeFresh_of_old ring D owner _ (by simpa [D] using ha),
          fun d => sweepOpenRSafeFresh_of_old ring D owner _
            (by simpa [D] using ht d)⟩
      · intro hn hr
        rcases hOld.2 (by simpa [D] using hn) (by simpa [D] using hr) with ⟨ha, ht⟩
        exact ⟨sweepOpenRSafeFresh_of_old ring D owner _ (by simpa [D] using ha),
          fun d => sweepOpenRSafeFresh_of_old ring D owner _
            (by simpa [D] using ht d)⟩
  exact ⟨⟨h1, h7, h8, h9⟩, hSD⟩

theorem openRFreshPrivateReplay_birthEntrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hPayload : R2CoherenceV31FootprintCover3.Cover3PayloadReachableV31
      (κ:=κ) (τ:=τ) hψ h2 ring)
    (hCover : R2CoherenceV31FootprintCover4.PendingFootprintCoveredReachableFreshV31
      (κ:=κ) (τ:=τ) hψ h2 ring) :
    OpenRFreshPrivateReplayV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 ring) hψ h2 ring :=
  openRReplayFresh_of_core _ hψ h2 ring
    (openRReplayCore_birthEntrance hψ h2 ring hPayload hCover)

end R2CoherenceV31ReplayProducers
