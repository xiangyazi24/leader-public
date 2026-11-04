import Leader.Wu.Coherence.ReachableScrubL
import Leader.Wu.Coherence.ReachableRootSpacing


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31RootSpacedScrubL


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableRootSpacing


variable {n ψ κ τ : Nat}


private theorem back_zero_rsp
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.back ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.back, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]


private theorem fwd_zero_rsp
    (ring : DirectedRing n) (i : Fin n) :
    R2Coherence.fwd ring i 0 = i := by
  apply Fin.ext
  simp [R2Coherence.fwd, Nat.mod_eq_of_lt i.isLt]


private theorem groupStart_root_rsp
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n)
    (hroot : atRootB (C i) = true) :
    R2Coherence.groupStart ring (eraseCfgV3 C) i = i := by
  have hz : (raw (C i)).label.val = 0 := by
    simpa [atRootB] using hroot
  unfold R2Coherence.groupStart
  change R2Coherence.back ring i (raw (C i)).label.val = i
  rw [hz]
  exact back_zero_rsp ring i


private theorem groupStart_succ_rsp
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n)
    (hs : successorB (C i) (C (ring.rightNeighbor i)) = true) :
    R2Coherence.groupStart ring (eraseCfgV3 C) i =
      R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor i) := by
  unfold R2Coherence.groupStart
  change R2Coherence.back ring i (raw (C i)).label.val =
    R2Coherence.back ring (ring.rightNeighbor i)
      (raw (C (ring.rightNeighbor i))).label.val
  have hv :
      (raw (C (ring.rightNeighbor i))).label.val =
        (raw (C i)).label.val + 1 := by
    simpa [successorB] using hs
  rw [hv]
  exact
    (R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach
      ring i (raw (C i)).label.val).symm


theorem scrubL_newPendingOwnerFresh_of_rootSpacing
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) {ring : DirectedRing n}
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hSpacing : RootSpacingV31 ring C)
    (hGeom : ElectionGeometryV31 ring C)
    (hFacts : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hOwnerE : ring.rightNeighbor owner = e)
    (hOwnerRoot : atRootB (C owner) = true)
    (hOwnerSucc : successorB (C owner) (C e) = true)
    (_hENonroot : atRootB (C e) = false)
    (_hENotScrubL : (C e).ctl.tok ≠ .scrubL) :
    OpenROwnerFreshV3 ring C owner := by
  have hBase : ReachablePhaseFactsV31 ring C := hFacts.1.1.1.1
  have hCurrent :=
    scrubL_guard_prepays_current_owner hψ h2 ring C e hBase hb
  have hRNonroot : atRootB (C (ring.rightNeighbor e)) = false := by
    cases h : atRootB (C (ring.rightNeighbor e)) with
    | false => rfl
    | true =>
        have hz : (raw (C (ring.rightNeighbor e))).label.val = 0 := by
          simpa [atRootB] using h
        exact (hCurrent.2.1 hz).elim
  have hSuccER :
      successorB (C e) (C (ring.rightNeighbor e)) = true := by
    simpa [ElectionGeometryV31, passiveEdgeOKV3, hRNonroot] using hGeom e
  have hOwner0 : (raw (C owner)).label.val = 0 := by
    simpa [atRootB] using hOwnerRoot
  have hStartOwner :
      R2Coherence.groupStart ring (eraseCfgV3 C) owner = owner :=
    groupStart_root_rsp ring C owner hOwnerRoot
  have hOwnerSuccRight :
      successorB (C owner) (C (ring.rightNeighbor owner)) = true := by
    simpa [hOwnerE] using hOwnerSucc
  have hStartOwnerRight :
      R2Coherence.groupStart ring (eraseCfgV3 C) owner =
        R2Coherence.groupStart ring (eraseCfgV3 C)
          (ring.rightNeighbor owner) :=
    groupStart_succ_rsp ring C owner hOwnerSuccRight
  have hStartOE :
      R2Coherence.groupStart ring (eraseCfgV3 C) owner =
        R2Coherence.groupStart ring (eraseCfgV3 C) e := by
    simpa [hOwnerE] using hStartOwnerRight
  have hStartER :
      R2Coherence.groupStart ring (eraseCfgV3 C) e =
        R2Coherence.groupStart ring (eraseCfgV3 C)
          (ring.rightNeighbor e) :=
    groupStart_succ_rsp ring C e hSuccER
  have hStartR :
      R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor e) =
        owner := by
    calc
      R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor e) =
          R2Coherence.groupStart ring (eraseCfgV3 C) e := hStartER.symm
      _ = R2Coherence.groupStart ring (eraseCfgV3 C) owner := hStartOE.symm
      _ = owner := hStartOwner
  unfold OpenROwnerFreshV3
  intro j k hHit
  have hLin :
      (raw (C (R2Coherence.groupPos ring (eraseCfgV3 C) j k.val))).label.val =
        k.val := hSpacing j k
  rw [hHit] at hLin
  have hk0 : k.val = 0 := by omega
  have hStartJ :
      R2Coherence.groupStart ring (eraseCfgV3 C) j = owner := by
    have hh := hHit
    unfold R2Coherence.groupPos at hh
    rw [hk0, fwd_zero_rsp ring] at hh
    exact hh
  unfold GroupIntrinsicFreshV3
  intro q
  unfold IntrinsicFreshAtV3
  intro hEq
  have hPos :
      R2Coherence.groupPos ring (eraseCfgV3 C)
          (ring.rightNeighbor e) q.val =
        R2Coherence.groupPos ring (eraseCfgV3 C) j q.val := by
    unfold R2Coherence.groupPos
    rw [hStartR, hStartJ]
  have hOwned := hCurrent.2.2 q
  change
    MainClearV3
        (C (R2Coherence.groupPos ring (eraseCfgV3 C)
          (ring.rightNeighbor e) q.val)) ∧
      PhaseOwnedV31
        (C (R2Coherence.groupPos ring (eraseCfgV3 C)
          (ring.rightNeighbor e) q.val)) at hOwned
  rw [hPos] at hOwned
  have hMain := hOwned.1
  unfold MainClearV3 R2CoherenceBranches.MainClear at hMain
  have hNone :
      (raw (C (R2Coherence.groupPos ring (eraseCfgV3 C) j q.val))).state =
        .none := hMain.1
  have hBad : MainState.none = MainState.equal := hNone.symm.trans hEq
  cases hBad


end R2CoherenceV31RootSpacedScrubL
