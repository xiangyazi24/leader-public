import Leader.Wu.Birth.ShortDoneFixedSiteLoadBound


namespace BirthShortDoneFixedSiteScopeAudit


open PPLL PPLLResearchFormulation
open PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open BirthShortDoneParticipationBudget
open BirthShortDoneParticipationLoadMass
open BirthShortDoneFixedSiteConsumer
open BirthShortDoneFixedSiteLoadBound


set_option autoImplicit false
set_option pp.structureInstances false

variable {n ψ width κ τ : Nat}


private def ring8 : DirectedRing 8 := ⟨by decide⟩
private def ring1 : DirectedRing 1 := ⟨by decide⟩


private def zeroTimer {ψ κ τ : Nat} (u : Local ψ κ τ) : Local ψ κ τ :=
  ⟨u.core, ⟨0, by omega⟩⟩


/-- Site zero is genuinely fresh; every other physical timer is zero. -/
def mixed8 (i : Fin 8) : Local 2 2 2 :=
  let u := BirthCheckParametricWait.familyInitial 2 false false i
  if i = (0 : Fin 8) then u else zeroTimer u


theorem mixed8_fresh_selected_dirty_others :
    (mixed8 (0 : Fin 8)).stall.val = 2 ∧
      ∀ j : Fin 8, j ≠ 0 → (mixed8 j).stall.val = 0 := by
  constructor
  · simp [mixed8, BirthCheckParametricWait.familyInitial, freshStall]
  · intro j hj
    simp [mixed8, zeroTimer, hj]


/-- Concrete nonvacuity of the n>=2 exposure theorem.  Only site zero is fresh;
all seven other timers in `mixed8` are zero. -/
theorem mixed8_fixed_site_exposure_witness :
    actualZeroServiceNumerator
        (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)
        ring8 mixed8 (0 : Fin 8) 3 ≤ 8 ^ 3 := by
  have hf : (mixed8 (0 : Fin 8)).stall.val = 2 :=
    mixed8_fresh_selected_dirty_others.1
  have hs : 1 * (chooseCount 3 3 * 2 ^ 3) ≤ 8 ^ 3 := by decide
  have h := actual_fixed_site_exposure_crossmul
    (n := 8) (ψ := 2) (width := 1) (κ := 2) (τ := 2)
    (by decide) (by decide) (by decide) (by decide)
    ring8 mixed8 (0 : Fin 8) 3 1 hf hs
  simpa using h


/-- Exact tau=0 boundary: every physical stall is zero, so scheduling the
chosen site itself witnesses the zero-input-service event immediately. -/
theorem tau0_selected_first_service
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ 0) (i : Fin n) :
    fixedSiteZeroServiceBit ring
      (BirthShortDoneDispatcher.row hψ hwidth hle) i C [i] = 1 := by
  have hz : (C i).stall.val = 0 := by
    have hlt := (C i).stall.isLt
    omega
  simpa only [fixedSiteZeroServiceBit, if_pos rfl, if_pos hz, if_true]


private def one0 (_ : Fin 1) : Local 2 2 0 :=
  BirthCheckParametricWait.familyInitial 0 false false (0 : Fin 8)


/-- Exact one-site alias boundary: one raw edge charges the sole physical site
once, and at tau=0 that unique first service has zero input. -/
theorem ring1_tau0_alias_boundary :
    endpointParticipations ring1 (0 : Fin 1) [(0 : Fin 1)] = 1 ∧
    fixedSiteZeroServiceBit ring1
      (BirthShortDoneDispatcher.row (κ := 2) (τ := 0)
        (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2))
      (0 : Fin 1) one0 [(0 : Fin 1)] = 1 ∧
    actualZeroServiceNumerator
      (by decide : 0 < 2) (by decide : 0 < 1) (by decide : 1 ≤ 2)
      ring1 one0 (0 : Fin 1) 1 ≤ 1 := by
  constructor
  · simpa using ring1_load ring1 (0 : Fin 1) [(0 : Fin 1)]
  constructor
  · exact tau0_selected_first_service
      (κ := 2) (by decide) (by decide) (by decide)
      ring1 one0 (0 : Fin 1)
  · have hf : (one0 (0 : Fin 1)).stall.val = 0 := by
      have hlt := (one0 (0 : Fin 1)).stall.isLt
      omega
    have h := ring1_alias_badMass_le
      (ψ := 2) (width := 1) (κ := 2) (τ := 0)
      (by decide) (by decide) (by decide)
      ring1 one0 (0 : Fin 1) 1 hf
    simpa using h


/-- Zero input is not the same proposition as zero-static expiry.  On the
actual short-DONE metadata cut, an actual path-progress premise selects the
refresh result even though this scheduled input has stall zero; the full row
also exposes the fresh timer through the existing progress theorem. -/
theorem zero_input_progress_refresh
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ) (e : Fin n)
    (hz : (C e).stall.val = 0)
    (hp :
      let l0 := prepareExpiringDisposal hψ (C e)
      let r0 := prepareExpiringDisposal hψ (C (ring.rightNeighbor e))
      let q := BirthShortDoneCuts.doneMetadataBoundedWidth
        hψ hwidth hle l0.core r0.core
      PathProgressView.ofState q.1 ≠ PathProgressView.ofState l0.core) :
    fixedSiteZeroServiceBit ring
        (BirthShortDoneDispatcher.row hψ hwidth hle) e C [e] = 1 ∧
    (let l0 := prepareExpiringDisposal hψ (C e)
     let r0 := prepareExpiringDisposal hψ (C (ring.rightNeighbor e))
     let q := BirthShortDoneCuts.doneMetadataBoundedWidth
       hψ hwidth hle l0.core r0.core
     deletionPriorityExpireOne τ l0
       (⟨q.1, l0.stall⟩ : Local ψ κ τ) = ⟨q.1, freshStall τ⟩) ∧
    (BirthShortDoneDispatcher.row hψ hwidth hle
      (C e) (C (ring.rightNeighbor e))).1.stall = freshStall τ := by
  constructor
  · simpa only [fixedSiteZeroServiceBit, if_pos rfl, if_pos hz, if_true]
  constructor
  · let l0 := prepareExpiringDisposal hψ (C e)
    let r0 := prepareExpiringDisposal hψ (C (ring.rightNeighbor e))
    let q := BirthShortDoneCuts.doneMetadataBoundedWidth
      hψ hwidth hle l0.core r0.core
    change deletionPriorityExpireOne τ l0
      (⟨q.1, l0.stall⟩ : Local ψ κ τ) = ⟨q.1, freshStall τ⟩
    exact deletionPriorityExpireOne_of_progress τ l0
      (⟨q.1, l0.stall⟩ : Local ψ κ τ) (by
        dsimp only [l0, r0, q]
        simpa only using hp)
  · have hr := actual_row_progress_refresh (κ := κ) (τ := τ)
      hψ hwidth hle (C e) (C (ring.rightNeighbor e))
    dsimp only at hr hp
    exact hr.1 hp


#print axioms BirthShortDoneFixedSiteScopeAudit.mixed8_fresh_selected_dirty_others
#print axioms BirthShortDoneFixedSiteScopeAudit.mixed8_fixed_site_exposure_witness
#print axioms BirthShortDoneFixedSiteScopeAudit.tau0_selected_first_service
#print axioms BirthShortDoneFixedSiteScopeAudit.ring1_tau0_alias_boundary
#print axioms BirthShortDoneFixedSiteScopeAudit.zero_input_progress_refresh


end BirthShortDoneFixedSiteScopeAudit
