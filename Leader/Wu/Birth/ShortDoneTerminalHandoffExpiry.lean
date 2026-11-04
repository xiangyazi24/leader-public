import Leader.Wu.Birth.ShortDoneTerminalHandoffTail

namespace BirthShortDoneTerminalHandoffExpiry

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair BirthGenerationDone

open K2BirthDispatcher K2BirthLeaderNormalize
  BirthShortDoneTerminalHost BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalHandoffTail BirthResponderHazardRows

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ : Nat}

/-- Physical classification at one right-hand handoff boundary.  The middle
case is the active deletion/disposal case of the actual expiry call; the last
case is live only in that exact deletion-inactive sense. -/
def RightHandoffOutcome (moved : PathInfo)
    (u : ExpiringAgentState ψ κ τ) : Prop :=
  u.core.erase.core.path = .bot ∨
    (u.core.erase.core.path = moved ∧
      deletionActive u.core.erase = true ∧ u.stall = freshStall τ) ∨
    (u.core.erase.core.path = moved ∧
      deletionActive u.core.erase = false ∧ u.stall = freshStall τ)

/-- The prepared finite host really selects the ordinary branch from the
normalized inputs.  Right inactivity is derived from normalized path absence. -/
theorem prepared_ordinary_branch
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    let lE := prepareExpiringDisposal hψ l
    let rE := prepareExpiringDisposal hψ r
    let lA := normalizeDeletion lE.core.erase
    let rA := normalizeDeletion rE.core.erase
    deletionActive lA = false → rA.core.path = .bot →
    doneMetadataAuthorizedEntryWidth hψ hwidth hle κ
        lE.core.erase rE.core.erase =
      doneOrdinaryMetadataEntryWidth hψ hwidth hle κ lA rA := by
  let lE := prepareExpiringDisposal hψ l
  let rE := prepareExpiringDisposal hψ r
  let lA := normalizeDeletion lE.core.erase
  let rA := normalizeDeletion rE.core.erase
  change deletionActive lA = false → rA.core.path = .bot → _
  intro hL hbot
  have hR : deletionActive rA = false := by
    simp [deletionActive, pathPresent, hbot]
  have hstage :
      doneMetadataAuthorizedEntryWidth hψ hwidth hle κ
          lE.core.erase rE.core.erase =
        (if deletionActive rA then authorizedEliminateSig hψ lA rA
         else if deletionActive lA then (lA, rA)
         else doneOrdinaryMetadataEntryWidth hψ hwidth hle κ lA rA) := by
    unfold doneMetadataAuthorizedEntryWidth
    rfl
  rw [hstage]
  simp only [hR, hL, Bool.false_eq_true, if_false]
  rfl

/-- `ClearsOrKeeps` crosses the exact finite reification equality. -/
theorem bounded_right_from_move
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    let lE := prepareExpiringDisposal hψ l
    let rE := prepareExpiringDisposal hψ r
    let lA := normalizeDeletion lE.core.erase
    let rA := normalizeDeletion rE.core.erase
    let b := generationBeforeMoveEntryWidth hψ hwidth hle κ lA rA
    let m := authorizedDoneMove hψ b.1 b.2
    let q := doneMetadataBoundedEntryWidth hψ hwidth hle lE.core rE.core
    deletionActive lA = false → rA.core.path = .bot →
      ClearsOrKeeps m.2.core.path q.2.erase.core.path := by
  let lE := prepareExpiringDisposal hψ l
  let rE := prepareExpiringDisposal hψ r
  let lA := normalizeDeletion lE.core.erase
  let rA := normalizeDeletion rE.core.erase
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ lA rA
  let m := authorizedDoneMove hψ b.1 b.2
  let q := doneMetadataBoundedEntryWidth hψ hwidth hle lE.core rE.core
  change deletionActive lA = false → rA.core.path = .bot →
    ClearsOrKeeps m.2.core.path q.2.erase.core.path
  intro hL hbot
  have hb := prepared_ordinary_branch
    (κ := κ) (τ := τ) hψ hwidth hle l r
  change deletionActive lA = false → rA.core.path = .bot →
    doneMetadataAuthorizedEntryWidth hψ hwidth hle κ
        lE.core.erase rE.core.erase =
      doneOrdinaryMetadataEntryWidth hψ hwidth hle κ lA rA at hb
  have hb := hb hL hbot
  have he := doneMetadataBoundedEntryWidth_erase
    hψ hwidth hle lE.core rE.core
  have heR := congrArg
    (fun z : AuthorizedAgentState ψ × AuthorizedAgentState ψ => z.2.core.path) he
  change q.2.erase.core.path =
    (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ
      lE.core.erase rE.core.erase).2.core.path at heR
  rw [hb] at heR
  have ht := doneOrdinaryMetadataEntryWidth_right_from_move
    hψ hwidth hle κ lA rA
  change ClearsOrKeeps m.2.core.path
    (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ lA rA).2.core.path at ht
  rw [heR]
  exact ht

private theorem moved_right_nonempty
    (b m : AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (hm : pathMovedRight b.1.core b.2.core m.1.core m.2.core = true) :
    m.2.core.path ≠ .bot := by
  have h :
      b.1.core.path ≠ .bot ∧
      b.2.core.path = .bot ∧
      m.1.core.path = .bot ∧
      m.2.core.path = b.1.core.path := by
    simpa only [pathMovedRight, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hm
  have hsrc : b.1.core.path ≠ .bot := h.1
  have hdst : m.2.core.path = b.1.core.path := h.2.2.2
  intro hz
  exact hsrc (hdst.symm.trans hz)

private theorem expiry_preserves_absence
    (old out : ExpiringAgentState ψ κ τ)
    (h : out.core.erase.core.path = .bot) :
    (deletionPriorityExpireOne τ old out).core.erase.core.path = .bot := by
  unfold deletionPriorityExpireOne pathExpireOne
  split
  · exact h
  · split
    · exact h
    · split
      · rfl
      · exact h

/-- Complete bridge through the *actual* right expiry endpoint.  No path
survival or progress hypothesis is supplied: both are case-derived. -/
theorem doneMetadataEntryWidth_right_handoff_or_end
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    let lE := prepareExpiringDisposal hψ l
    let rE := prepareExpiringDisposal hψ r
    let lA := normalizeDeletion lE.core.erase
    let rA := normalizeDeletion rE.core.erase
    let b := generationBeforeMoveEntryWidth hψ hwidth hle κ lA rA
    let m := authorizedDoneMove hψ b.1 b.2
    deletionActive lA = false → rA.core.path = .bot →
    pathMovedRight b.1.core b.2.core m.1.core m.2.core = true →
    m.2.core.path ≠ .bot ∧
      RightHandoffOutcome m.2.core.path
        (doneMetadataEntryWidth hψ hwidth hle l r).2 := by
  let lE := prepareExpiringDisposal hψ l
  let rE := prepareExpiringDisposal hψ r
  let lA := normalizeDeletion lE.core.erase
  let rA := normalizeDeletion rE.core.erase
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ lA rA
  let m := authorizedDoneMove hψ b.1 b.2
  let q := doneMetadataBoundedEntryWidth hψ hwidth hle lE.core rE.core
  let base : ExpiringAgentState ψ κ τ := ⟨q.2, rE.stall⟩
  let eR := deletionPriorityExpireOne τ rE base
  change deletionActive lA = false → rA.core.path = .bot →
    pathMovedRight b.1.core b.2.core m.1.core m.2.core = true →
    m.2.core.path ≠ .bot ∧ RightHandoffOutcome m.2.core.path eR
  intro hL hbot hmove
  have hmne := moved_right_nonempty b m hmove
  refine ⟨hmne, ?_⟩
  have hk := bounded_right_from_move
    (κ := κ) (τ := τ) hψ hwidth hle l r
  change deletionActive lA = false → rA.core.path = .bot →
    ClearsOrKeeps m.2.core.path q.2.erase.core.path at hk
  have hk := hk hL hbot
  by_cases hqbot : q.2.erase.core.path = .bot
  · exact Or.inl (by
      dsimp only [eR]
      exact expiry_preserves_absence rE base hqbot)
  · have hqm := hk.retains hqbot
    by_cases ha : deletionActive q.2.erase = true
    · have he : eR = ⟨q.2, freshStall τ⟩ := by
        dsimp only [eR]
        exact deletionPriorityExpireOne_of_active τ rE base ha
      rw [he]
      exact Or.inr (Or.inl ⟨hqm, ha, rfl⟩)
    · have ha0 : deletionActive q.2.erase = false := by
        cases hx : deletionActive q.2.erase <;> simp_all
      have hold : rE.core.erase.core.path = .bot :=
        prepared_right_empty_of_normalized hψ r hbot
      have hprogress :
          PathProgressView.ofState base.core ≠
            PathProgressView.ofState rE.core := by
        intro hv
        have hp := congrArg PathProgressView.path hv
        change q.2.core.path = rE.core.core.path at hp
        have herase : q.2.erase.core.path = rE.core.erase.core.path := by
          simp only [AuthorizedBoundedAgentState.erase,
            BoundedAgentState.erase, hp]
        exact hqbot (herase.trans hold)
      have he : eR = ⟨q.2, freshStall τ⟩ := by
        dsimp only [eR]
        rw [deletionPriorityExpireOne, if_neg (by simp [base, ha0])]
        exact pathExpireOne_of_progress τ rE base hprogress
      rw [he]
      exact Or.inr (Or.inr ⟨hqm, ha0, rfl⟩)

private theorem normalizeLeader_expiry_frame
    (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    (K2BirthLeaderNormalize.normalizeLeader hψ u).core.erase.core.path =
        u.core.erase.core.path ∧
      (K2BirthLeaderNormalize.normalizeLeader hψ u).core.erase.core.state =
        u.core.erase.core.state ∧
      (K2BirthLeaderNormalize.normalizeLeader hψ u).stall = u.stall := by
  unfold K2BirthLeaderNormalize.normalizeLeader
  split <;> exact ⟨rfl, rfl, rfl⟩

private theorem metadata_right_stage
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (BirthShortDoneTerminalHost.metadata hψ hwidth hle l r).2 =
      K2BirthLeaderNormalize.normalizeLeader hψ
        (doneMetadataEntryWidth hψ hwidth hle l r).2 := by
  rfl

private theorem putSignals_expiry_frame
    (u : ExpiringAgentState ψ κ τ) (v : AgentState 1) :
    (ExpiringK2Projection.putSignals u v).core.erase.core.path =
        u.core.erase.core.path ∧
      (ExpiringK2Projection.putSignals u v).core.erase.core.state =
        u.core.erase.core.state ∧
      (ExpiringK2Projection.putSignals u v).stall = u.stall := by
  exact ⟨rfl, rfl, rfl⟩

attribute [local irreducible]
  BirthShortDoneTerminalHost.metadata
  BirthShortDoneTerminalHost.row

private theorem metadata_right_expiry_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    let e := (doneMetadataEntryWidth hψ hwidth hle l r).2
    let m := (metadata hψ hwidth hle l r).2
    m.core.erase.core.path = e.core.erase.core.path ∧
      m.core.erase.core.state = e.core.erase.core.state ∧ m.stall = e.stall := by
  let e := (doneMetadataEntryWidth hψ hwidth hle l r).2
  let m := (metadata hψ hwidth hle l r).2
  have hstage : m = K2BirthLeaderNormalize.normalizeLeader hψ e := by
    simpa only [m, e] using metadata_right_stage hψ hwidth hle l r
  have hn := normalizeLeader_expiry_frame (κ := κ) (τ := τ) hψ e
  have hp := congrArg
    (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.path) hstage
  have hs := congrArg
    (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.state) hstage
  have ht := congrArg ExpiringAgentState.stall hstage
  exact ⟨hp.trans hn.1, hs.trans hn.2.1, ht.trans hn.2.2⟩

private theorem row_right_expiry_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    let e := (doneMetadataEntryWidth hψ hwidth hle l r).2
    let out := (row hψ hwidth hle l r).2
    out.core.erase.core.path = e.core.erase.core.path ∧
      out.core.erase.core.state = e.core.erase.core.state ∧ out.stall = e.stall := by
  let e := (doneMetadataEntryWidth hψ hwidth hle l r).2
  let m := (metadata hψ hwidth hle l r).2
  let out := (row hψ hwidth hle l r).2
  have hm :
      m.core.erase.core.path = e.core.erase.core.path ∧
      m.core.erase.core.state = e.core.erase.core.state ∧ m.stall = e.stall := by
    simpa only [m, e] using metadata_right_expiry_frame hψ hwidth hle l r
  have hr :
      ExpiringK2Projection.putSignals out
          (ExpiringK2Projection.observeCell m) = m := by
    simpa only [out, m] using
      (BirthShortDoneTerminalHost.row_metadata_frame hψ hwidth hle l r).2
  have hk := putSignals_expiry_frame out
    (ExpiringK2Projection.observeCell m)
  have hp := congrArg
    (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.path) hr
  have hs := congrArg
    (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.state) hr
  have ht := congrArg ExpiringAgentState.stall hr
  have homP := hk.1.symm.trans hp
  have homS := hk.2.1.symm.trans hs
  have homT := hk.2.2.symm.trans ht
  exact ⟨homP.trans hm.1, homS.trans hm.2.1, homT.trans hm.2.2⟩

private theorem deletionActive_frame
    (a b : AuthorizedAgentState ψ)
    (hs : a.core.state = b.core.state) (hp : a.core.path = b.core.path) :
    deletionActive a = deletionActive b := by
  unfold deletionActive pathPresent
  rw [hs, hp]

/-- Full physical row: normalization and final K2/collision processing preserve
the expiry classification exactly on path/state/stall. -/
theorem row_right_handoff_or_end
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    let lE := prepareExpiringDisposal hψ l
    let rE := prepareExpiringDisposal hψ r
    let lA := normalizeDeletion lE.core.erase
    let rA := normalizeDeletion rE.core.erase
    let b := generationBeforeMoveEntryWidth hψ hwidth hle κ lA rA
    let m := authorizedDoneMove hψ b.1 b.2
    deletionActive lA = false → rA.core.path = .bot →
    pathMovedRight b.1.core b.2.core m.1.core m.2.core = true →
    m.2.core.path ≠ .bot ∧
      RightHandoffOutcome m.2.core.path (row hψ hwidth hle l r).2 := by
  let lE := prepareExpiringDisposal hψ l
  let rE := prepareExpiringDisposal hψ r
  let lA := normalizeDeletion lE.core.erase
  let rA := normalizeDeletion rE.core.erase
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ lA rA
  let m := authorizedDoneMove hψ b.1 b.2
  let e := (doneMetadataEntryWidth hψ hwidth hle l r).2
  let out := (row hψ hwidth hle l r).2
  change deletionActive lA = false → rA.core.path = .bot →
    pathMovedRight b.1.core b.2.core m.1.core m.2.core = true →
    m.2.core.path ≠ .bot ∧ RightHandoffOutcome m.2.core.path out
  intro hL hbot hmove
  have he0 := doneMetadataEntryWidth_right_handoff_or_end
    (κ := κ) (τ := τ) hψ hwidth hle l r
  change deletionActive lA = false → rA.core.path = .bot →
    pathMovedRight b.1.core b.2.core m.1.core m.2.core = true →
    m.2.core.path ≠ .bot ∧ RightHandoffOutcome m.2.core.path e at he0
  obtain ⟨hmne, he⟩ := he0 hL hbot hmove
  refine ⟨hmne, ?_⟩
  have hf :
      out.core.erase.core.path = e.core.erase.core.path ∧
      out.core.erase.core.state = e.core.erase.core.state ∧ out.stall = e.stall := by
    simpa only [out, e] using row_right_expiry_frame hψ hwidth hle l r
  have ha : deletionActive out.core.erase = deletionActive e.core.erase :=
    deletionActive_frame out.core.erase e.core.erase hf.2.1 hf.1
  unfold RightHandoffOutcome at he ⊢
  rcases he with hend | hdel | hlive
  · exact Or.inl (hf.1.trans hend)
  · exact Or.inr (Or.inl
      ⟨hf.1.trans hdel.1, ha.trans hdel.2.1, hf.2.2.trans hdel.2.2⟩)
  · exact Or.inr (Or.inr
      ⟨hf.1.trans hlive.1, ha.trans hlive.2.1, hf.2.2.trans hlive.2.2⟩)

#print axioms BirthShortDoneTerminalHandoffExpiry.prepared_ordinary_branch
#print axioms BirthShortDoneTerminalHandoffExpiry.bounded_right_from_move
#print axioms BirthShortDoneTerminalHandoffExpiry.doneMetadataEntryWidth_right_handoff_or_end
#print axioms BirthShortDoneTerminalHandoffExpiry.row_right_handoff_or_end

end BirthShortDoneTerminalHandoffExpiry
