import Leader.Wu.Birth.InnerCountMono
import Leader.Wu.Birth.ShortDoneTerminalObserver
import Leader.Wu.Elimination.SinkTwoGapEpochSuccessor

set_option autoImplicit false

namespace BirthB1CountAlongNoBirth

open BirthShortDoneTerminalHost BirthSigMoveDisposalRepair PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair PPLLPathStallComparisonRepair
  K2BirthDispatcher K2BirthLeaderNormalize ExpiringK2Projection BirthShortDoneTerminalObserver
  BirthShortDoneCuts BirthShortWait PPLL PPLLRepair PPLLWallSweepRepair
  PPLLCompleteMultiLeaderCleanup BirthShortDoneTerminalEntryCut K2OutputSafety
open BirthB1RowCountFrame BirthB1CountStepReduction BirthB1InnerCountMono
  BirthB1LeaderlessResetFree BirthB1ResetFreeCountMono BirthB1InnerCountFrames BirthB1InnerFieldFrames

variable {n psi kappa tau : Nat}

/-! ## (A) No inner birth from leaderless inputs and the observer's no-birth test. -/

theorem newborn_false_leader {ψ κ τ : Nat} (old out : ExpiringAgentState ψ κ τ)
    (hold : old.core.core.leader = false) (h : newborn old out = false) :
    out.core.core.leader = false := by
  unfold newborn at h
  rw [hold] at h
  simpa using h

theorem expireOne_leader {ψ κ τ : Nat} (old out : ExpiringAgentState ψ κ τ) :
    (deletionPriorityExpireOne τ old out).core.core.leader = out.core.core.leader := by
  unfold deletionPriorityExpireOne
  split
  · rfl
  · unfold pathExpireOne
    split
    · rfl
    · split
      · rfl
      · rfl

theorem noInnerBirth_of_birthEvent_false (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (e : Fin n)
    (hL : Leaderless C)
    (hb : BirthShortDoneTerminalObserver.birthEvent hpsi (by decide : 0 < 2) h2 (C e) (C (ring.rightNeighbor e)) = false) :
    NoInnerBirth hpsi h2 ring C e := by
  have hnb :
      newborn (C e) (BirthShortDoneTerminalHost.metadata hpsi (by decide : 0 < 2) h2 (C e) (C (ring.rightNeighbor e))).1 = false ∧
      newborn (C (ring.rightNeighbor e))
        (BirthShortDoneTerminalHost.metadata hpsi (by decide : 0 < 2) h2 (C e) (C (ring.rightNeighbor e))).2 = false := by
    simpa only [BirthShortDoneTerminalObserver.birthEvent, Bool.or_eq_false_iff] using hb
  have hl1 := newborn_false_leader _ _ (hL e) hnb.1
  have hl2 := newborn_false_leader _ _ (hL (ring.rightNeighbor e)) hnb.2
  unfold BirthShortDoneTerminalHost.metadata doneMetadataEntryWidth at hl1 hl2
  dsimp only at hl1 hl2
  rw [normalizeLeader_leader, expireOne_leader] at hl1 hl2
  have hq := doneMetadataBoundedEntryWidth_erase hpsi (by decide : 0 < 2) h2
    (prepareExpiringDisposal hpsi (C e)).core
    (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e))).core
  have hq1 := congrArg (fun p => p.1.core.leader) hq
  have hq2 := congrArg (fun p => p.2.core.leader) hq
  simp only at hq1 hq2
  unfold NoInnerBirth
  dsimp only
  rw [<- hq1, <- hq2]
  exact ⟨hl1, hl2⟩

/-! ## (B) ResetFree is preserved by a letter with no inner birth. -/

def resetE {ψ κ τ : Nat} (q : ExpiringAgentState ψ κ τ) : Bool := q.core.erase.core.reset_cmd

theorem nonK2_reset {ψ κ τ : Nat} (q : ExpiringAgentState ψ κ τ) : resetE (nonK2 q) = resetE q := rfl

theorem finalPhysical_reset {ψ κ τ : Nat} (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ) :
    resetE (finalPhysical hψ oldL oldR metaL metaR).1 = resetE metaL ∧
      resetE (finalPhysical hψ oldL oldR metaL metaR).2 = resetE metaR := by
  have hf := finalPhysical_nonK2 hψ oldL oldR metaL metaR
  constructor
  · have h := congrArg resetE hf.1
    rwa [nonK2_reset, nonK2_reset] at h
  · have h := congrArg resetE hf.2
    rwa [nonK2_reset, nonK2_reset] at h

theorem normalizeLeader_reset {ψ κ τ : Nat} (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) :
    resetE (normalizeLeader hψ q) = resetE q := by
  unfold normalizeLeader
  split <;> rfl

theorem expireOne_reset {ψ κ τ : Nat} (old out : ExpiringAgentState ψ κ τ) :
    resetE (deletionPriorityExpireOne τ old out) = resetE out := by
  unfold deletionPriorityExpireOne
  split
  · rfl
  · unfold pathExpireOne
    split
    · rfl
    · split
      · rfl
      · rfl

theorem row_reset_eq (hψ : 0 < psi) {width : Nat} (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    let l0 := prepareExpiringDisposal hψ l
    let r0 := prepareExpiringDisposal hψ r
    let m := doneMetadataAuthorizedEntryWidth hψ hwidth hle kappa l0.core.erase r0.core.erase
    resetE (row hψ hwidth hle l r).1 = m.1.core.reset_cmd ∧
      resetE (row hψ hwidth hle l r).2 = m.2.core.reset_cmd := by
  intro l0 r0 m
  rw [row_real_host_witness hψ hwidth hle l r]
  have hq := doneMetadataBoundedEntryWidth_erase hψ hwidth hle l0.core r0.core
  have hq1 := congrArg Prod.fst hq
  have hq2 := congrArg Prod.snd hq
  simp only at hq1 hq2
  constructor
  · rw [(finalPhysical_reset hψ l r _ _).1, normalizeLeader_reset, expireOne_reset]
    show (doneMetadataBoundedEntryWidth hψ hwidth hle l0.core r0.core).1.erase.core.reset_cmd = m.1.core.reset_cmd
    rw [hq1]
  · rw [(finalPhysical_reset hψ l r _ _).2, normalizeLeader_reset, expireOne_reset]
    show (doneMetadataBoundedEntryWidth hψ hwidth hle l0.core r0.core).2.erase.core.reset_cmd = m.2.core.reset_cmd
    rw [hq2]

/-- The SUPPRESS stage cannot mint a reset bit without a leader. -/
theorem suppressSigResetKillWidth_reset_free {ψ width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : AgentState ψ) (hleader : l.leader = false)
    (hl : l.reset_cmd = false) (hr : r.reset_cmd = false) :
    (suppressSigResetKillWidth hψ hwidth hle l r).1.reset_cmd = false ∧
      (suppressSigResetKillWidth hψ hwidth hle l r).2.reset_cmd = false := by
  simp [suppressSigResetKillWidth, suppressPrefix, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal, shortCountReset, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish, hleader, hl, hr]

theorem authorizedSuppressWidth_reset_free {ψ width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : AuthorizedAgentState ψ) (hleader : l.core.leader = false)
    (hl : l.core.reset_cmd = false) (hr : r.core.reset_cmd = false) :
    (authorizedSuppressWidth hψ hwidth hle l r).1.core.reset_cmd = false ∧
      (authorizedSuppressWidth hψ hwidth hle l r).2.core.reset_cmd = false := by
  unfold authorizedSuppressWidth
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core (suppressSigResetKillWidth hψ hwidth hle) l r).1,
    (BirthB1InnerCountFrames.authorizedReconcile_core (suppressSigResetKillWidth hψ hwidth hle) l r).2]
  exact suppressSigResetKillWidth_reset_free hψ hwidth hle l.core r.core hleader hl hr

/-! ## Reset-freeness through the inner chain (mirrors the count assembly). -/

theorem afterCheckMetadataWidth_reset_false {ψ width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.reset_cmd = false) (hr : r.core.reset_cmd = false)
    (hlead : (afterCheckMetadataWidth hψ hwidth hle l r).1.core.leader = false) :
    (afterCheckMetadataWidth hψ hwidth hle l r).1.core.reset_cmd = false ∧
      (afterCheckMetadataWidth hψ hwidth hle l r).2.core.reset_cmd = false := by
  unfold afterCheckMetadataWidth beforeWriteWidth at hlead ⊢
  dsimp only at hlead ⊢
  have d0r := authorizedDisappear_reset_cmd hψ l r
  have c1r := authorizedCompareSigActionOne_reset_cmd hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2
  have hlead1 : (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1.core.leader = false := by
    rw [(stationaryPersistentAuthorizedRow_leader hψ (authorizedSuppressWidth hψ hwidth hle (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1 (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2).1 (authorizedSuppressWidth hψ hwidth hle (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1 (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2).2).1,
      (authorizedSuppressWidth_leader hψ hwidth hle (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1 (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2).1] at hlead
    exact hlead
  have hr1 : (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1.core.reset_cmd = false := by rw [c1r.1, d0r.1]; exact hl
  have hr2 : (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2.core.reset_cmd = false := by rw [c1r.2, d0r.2]; exact hr
  have s2 := authorizedSuppressWidth_reset_free hψ hwidth hle (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1 (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2 hlead1 hr1 hr2
  have s3 := stationaryPersistentAuthorizedRow_reset_cmd hψ (authorizedSuppressWidth hψ hwidth hle (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1 (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2).1 (authorizedSuppressWidth hψ hwidth hle (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1 (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2).2
  rw [s3.1, s3.2]
  exact s2

theorem doneOrdinaryMetadataEntryWidth_reset_false {ψ width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.reset_cmd = false) (hr : r.core.reset_cmd = false)
    (hlead : (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r).1.core.leader = false) :
    (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r).1.core.reset_cmd = false ∧
      (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r).2.core.reset_cmd = false := by
  unfold doneOrdinaryMetadataEntryWidth at hlead ⊢
  dsimp only at hlead ⊢
  have hm := markLeaderBirth_reset_cmd (K2BirthDispatcher.authBirth l r (afterCheckMetadataWidth hψ hwidth hle (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1 (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2)) (afterCheckMetadataWidth hψ hwidth hle (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1 (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2)
  have hml := markLeaderBirth_leader (K2BirthDispatcher.authBirth l r (afterCheckMetadataWidth hψ hwidth hle (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1 (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2)) (afterCheckMetadataWidth hψ hwidth hle (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1 (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2)
  rw [hml.1] at hlead
  have hcr := doneThroughCheckEntryWidth_reset_cmd hψ hwidth hle κ l r
  have ha := afterCheckMetadataWidth_reset_false hψ hwidth hle (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1 (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2
    (by rw [hcr.1]; exact hl) (by rw [hcr.2]; exact hr) hlead
  rw [hm.1, hm.2]
  exact ha

theorem doneMetadataAuthorizedEntryWidth_reset_false {ψ width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.reset_cmd = false) (hr : r.core.reset_cmd = false)
    (hlead : (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l r).1.core.leader = false) :
    (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l r).1.core.reset_cmd = false ∧
      (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l r).2.core.reset_cmd = false := by
  unfold doneMetadataAuthorizedEntryWidth at hlead ⊢
  dsimp only at hlead ⊢
  have nlr := normalizeDeletion_reset_cmd l
  have nrr := normalizeDeletion_reset_cmd r
  by_cases hA : deletionActive (normalizeDeletion r) = true
  · rw [if_pos hA] at hlead ⊢
    have he := authorizedEliminateSig_reset_cmd hψ (normalizeDeletion l) (normalizeDeletion r)
    rw [he.1, he.2, nlr, nrr]
    exact ⟨hl, hr⟩
  · rw [if_neg hA] at hlead ⊢
    by_cases hB : deletionActive (normalizeDeletion l) = true
    · rw [if_pos hB] at hlead ⊢
      rw [nlr, nrr]
      exact ⟨hl, hr⟩
    · rw [if_neg hB] at hlead ⊢
      exact doneOrdinaryMetadataEntryWidth_reset_false hψ hwidth hle κ (normalizeDeletion l) (normalizeDeletion r)
        (by rw [nlr]; exact hl) (by rw [nrr]; exact hr) hlead

theorem resetFree_step_noBirth (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (e : Fin n)
    (hR : ResetFree C) (hNB : NoInnerBirth hpsi h2 ring C e) :
    ResetFree (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) := by
  intro i
  have hin := doneMetadataAuthorizedEntryWidth_reset_false hpsi (by decide : 0 < 2) h2 kappa
    (prepareExpiringDisposal hpsi (C e)).core.erase
    (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e))).core.erase
    (by rw [prepare_reset_eq]; exact hR e)
    (by rw [prepare_reset_eq]; exact hR _)
    hNB.1
  have hrow := row_reset_eq hpsi (by decide : 0 < 2) h2 (C e) (C (ring.rightNeighbor e))
  show (BirthB1ResetFreeControlled.rawAt
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) i).reset_cmd = false
  unfold BirthB1ResetFreeControlled.rawAt
  rw [currentStep2_apply]
  by_cases hie : i = e
  · rw [if_pos hie]
    exact hrow.1.trans hin.1
  · rw [if_neg hie]
    by_cases hij : i = ring.rightNeighbor e
    · rw [if_pos hij]
      exact hrow.2.trans hin.2
    · rw [if_neg hij]
      exact hR i

/-! ## (C) Leaderless is preserved by a letter with no observed birth (K2 kernel never creates a leader). -/

theorem shadowRow_leader_false (a b : AgentState 1) (ha : a.leader = false) (hb : b.leader = false) :
    (shadowRow a b).1.leader = false ∧ (shadowRow a b).2.leader = false := by
  unfold shadowRow
  dsimp only
  have hsa : (signalView a).leader = a.leader := rfl
  have hsb : (signalView b).leader = b.leader := rfl
  rw [if_neg (by rw [hsa, hsb, ha]; simp)]
  have hk := LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation (by decide : (1 : Nat) > 0) (signalView a) (signalView b)
  exact ⟨hk.1 (by rw [hsa]; exact ha), hk.2 (by rw [hsb]; exact hb)⟩

theorem leaderless_step_noBirth (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (e : Fin n)
    (hL : Leaderless C)
    (hb : BirthShortDoneTerminalObserver.birthEvent hpsi (by decide : 0 < 2) h2 (C e) (C (ring.rightNeighbor e)) = false) :
    Leaderless (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) := by
  intro i
  have hobs := observe_step_of_no_birth hpsi (by decide : 0 < 2) h2 ring C e hb
  have hi := congrArg (fun f => (f i).leader) hobs
  simp only [observe] at hi
  have hl : (observeCell (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e i)).leader =
      (BirthB1ResetFreeControlled.rawAt (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) i).leader := rfl
  rw [<- hl]
  change (observeCell (BirthShortDoneTerminalConsumer.step hpsi (by decide : 0 < 2) h2 ring C e i)).leader = false
  rw [hi]
  unfold shadowStep updatePair
  try dsimp only
  have hoe : (observeCell (C e)).leader = false := hL e
  have hoj : (observeCell (C (ring.rightNeighbor e))).leader = false := hL _
  have hs := shadowRow_leader_false (observeCell (C e)) (observeCell (C (ring.rightNeighbor e))) hoe hoj
  by_cases hie : i = e
  · rw [if_pos hie]; exact hs.1
  · rw [if_neg hie]
    by_cases hij : i = ring.rightNeighbor e
    · rw [if_pos hij]; exact hs.2
    · rw [if_neg hij]; exact hL i

/-! ## (D) Along any birth-free word from a leaderless reset-free state, counts never decrease. -/

theorem along_noBirth (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (u : List (Fin n))
    (hL : Leaderless C) (hR : ResetFree C)
    (hNB : NoBirthAlong hpsi (by decide : 0 < 2) h2 ring C u) :
    CountMonoStep C (BirthB1ReacquireReentryMass.prefixEndpoint hpsi h2 ring C u) ∧
      Leaderless (BirthB1ReacquireReentryMass.prefixEndpoint hpsi h2 ring C u) ∧
      ResetFree (BirthB1ReacquireReentryMass.prefixEndpoint hpsi h2 ring C u) := by
  induction u generalizing C with
  | nil => exact ⟨fun i => Nat.le_refl _, hL, hR⟩
  | cons e u ih =>
      have hb : BirthShortDoneTerminalObserver.birthEvent hpsi (by decide : 0 < 2) h2 (C e) (C (ring.rightNeighbor e)) = false := hNB.1
      have hNI := noInnerBirth_of_birthEvent_false hpsi h2 ring C e hL hb
      have hstep := count_step_noBirth hpsi h2 ring C e hL hR hNI
      have hL' := leaderless_step_noBirth hpsi h2 ring C e hL hb
      have hR' := resetFree_step_noBirth hpsi h2 ring C e hR hNI
      have hrest : NoBirthAlong hpsi (by decide : 0 < 2) h2 ring
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) u := hNB.2
      have ih' := ih (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) hL' hR' hrest
      refine ⟨?_, ih'.2.1, ih'.2.2⟩
      intro i
      exact Nat.le_trans (hstep i) (ih'.1 i)

/-- B7's `hcount` on birth-free blocks. -/
theorem shortCount_le_of_noBirth (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (u : List (Fin n))
    (hL : Leaderless x) (hR : ResetFree x)
    (hNB : NoBirthAlong hpsi (by decide : 0 < 2) h2 ring x u) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor x <=
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseGenericRenewal.rawEndpoint (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) x u) :=
  (along_noBirth hpsi h2 ring x u hL hR hNB).1 (ring.rightNeighbor anchor)


end BirthB1CountAlongNoBirth
