import Leader.Wu.Birth.ShortDoneTerminalHost
import Leader.Wu.Birth.ResponderHazardRows

/-!
# Right-path handoff tail for terminal-entry DONE

Proof-side path facts only.  No protocol field or history token is added.
The key result is deliberately `ClearsOrKeeps`: it does not assume that a
moved component survives the rest of the row.
-/

namespace BirthShortDoneTerminalHandoffTail

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
  PPLLCompleteMultiLeaderCleanup BirthSigMoveDisposalRepair
  BirthGenerationDone BirthTossCheckPreservationRepair BirthShortWait
  BirthStationaryWrite

open K2BirthDispatcher K2BirthDispatcherDone
  BirthShortDoneCuts BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalHost BirthResponderHazardRows

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ : Nat}

/-! ## Prepared endpoint versus normalized authorized endpoint -/

private theorem normalizeDeletion_path_local
    (u : AuthorizedAgentState ψ) :
    (normalizeDeletion u).core.path = u.core.path := by
  unfold normalizeDeletion
  split <;> rfl

/-- The `rA.path = bot` premise really is an empty path on the
prepared expiring endpoint used as `old` by `deletionPriorityExpireOne`.
No equality of the whole normalized and prepared states is asserted. -/
theorem prepared_right_empty_of_normalized
    (hψ : 0 < ψ) (r : ExpiringAgentState ψ κ τ)
    (hbot :
      (normalizeDeletion
        (prepareExpiringDisposal hψ r).core.erase).core.path = .bot) :
    (prepareExpiringDisposal hψ r).core.erase.core.path = .bot := by
  exact
    (normalizeDeletion_path_local
      ((prepareExpiringDisposal hψ r).core.erase)).symm.trans hbot

/-! ## Short-SUPPRESS right-path frame -/

private theorem suppressStart_right_path (l r : AgentState ψ) :
    (suppressSigStart l r).2.path = r.path := by
  unfold suppressSigStart
  split <;> rfl

private theorem resetKill_right_path (r : AgentState ψ) :
    ClearsOrKeeps r.path (resetKillComparison r).path := by
  unfold resetKillComparison
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem suppressMove_right_path (l r : AgentState ψ) :
    (suppressSigMoveReset l r).2.path = r.path := by
  unfold suppressSigMoveReset
  split <;> rfl

private theorem shortReset_right_path
    (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    (shortCountReset hwidth hle l r).2.path = r.path := by
  unfold shortCountReset
  split <;> rfl

private theorem suppressTerminal_right_path
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    (suppressSigTerminal hψ l r).2.path = r.path := by
  unfold suppressSigTerminal
  split <;> rfl

private theorem suppressEcho_right_path (l r : AgentState ψ) :
    (suppressSigEcho l r).2.path = r.path := by
  unfold suppressSigEcho
  repeat (first | rfl | split)

private theorem suppressFinish_right_path (l r : AgentState ψ) :
    (suppressSigFinish l r).2.path = r.path := rfl

/-- The shortened count insertion is path-inert.  As in the full SUPPRESS,
the only possible main-path effect is one of the two literal reset kills. -/
theorem authorizedSuppressWidth_right
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) :
    ClearsOrKeeps r.core.path
      (authorizedSuppressWidth hψ hwidth hle l r).2.core.path := by
  change ClearsOrKeeps r.core.path
    (suppressSigResetKillWidth hψ hwidth hle l.core r.core).2.path
  unfold suppressSigResetKillWidth
  dsimp only
  rw [suppressFinish_right_path, suppressEcho_right_path,
    suppressTerminal_right_path, shortReset_right_path]
  unfold suppressPrefix
  dsimp only
  apply ClearsOrKeeps.trans (resetKill_right_path _)
  rw [suppressMove_right_path]
  apply ClearsOrKeeps.trans (resetKill_right_path _)
  exact Or.inr (suppressStart_right_path l.core r.core)

/-! ## Exact post-move tail -/

private theorem preserveTossCheck_right_path
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    (preserveTossCheck hψ l r).2.core.path = r.core.path := by
  by_cases ht : l.core.state = .toss ∨ r.core.state = .toss
  · rw [BirthTossCheckPreservationRepair.preserveTossCheck_of_toss
      hψ l r ht]
  · have hl : l.core.state ≠ .toss := fun h => ht (Or.inl h)
    have hr : r.core.state ≠ .toss := fun h => ht (Or.inr h)
    rw [BirthTossCheckPreservationRepair.preserveTossCheck_of_no_toss
      hψ l r hl hr]
    exact BirthResponderHazardRows.check_right_path_eq hψ l r

private theorem preserveDoneCheck_right_path
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    (preserveDoneCheck hψ l r).2.core.path = r.core.path := by
  by_cases hd : l.core.state = .done ∨ r.core.state = .done
  · rw [BirthGenerationDone.preserveDoneCheck_of_done hψ l r hd]
  · have hl : l.core.state ≠ .done := fun h => hd (Or.inl h)
    have hr : r.core.state ≠ .done := fun h => hd (Or.inr h)
    rw [BirthGenerationDone.preserveDoneCheck_of_no_done hψ l r hl hr]
    exact preserveTossCheck_right_path hψ l r

attribute [local irreducible]
  BirthStationaryWrite.stationaryPersistentRaw
  BirthStationaryWrite.stationaryPersistentAuthorizedRow

private theorem stationaryWriter_right_path
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    (stationaryPersistentAuthorizedRow hψ l r).2.core.path = r.core.path := by
  have hc := congrArg
    (fun q : AgentState ψ × AgentState ψ => q.2.path)
    (stationaryPersistentAuthorizedRow_core hψ l r)
  have h := stationaryPersistentRaw_comparison hψ l.core r.core
  exact hc.trans (congrArg (fun q => q.2.path) h)

/-! Only the outer stage shells are exposed here.  Their children remain
opaque to all later path proofs. -/

private theorem beforeWriteWidth_stage
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) :
    let d := authorizedDisappear hψ l r
    let c := authorizedCompareSigActionOne hψ d.1 d.2
    beforeWriteWidth hψ hwidth hle l r =
      authorizedSuppressWidth hψ hwidth hle c.1 c.2 := by
  rfl

private theorem afterCheckMetadataWidth_stage
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) :
    let b := beforeWriteWidth hψ hwidth hle l r
    afterCheckMetadataWidth hψ hwidth hle l r =
      stationaryPersistentAuthorizedRow hψ b.1 b.2 := by
  rfl

private theorem doneBeforeCheckEntryWidth_stage
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
    let m := authorizedDoneMove hψ b.1 b.2
    doneBeforeCheckEntryWidth hψ hwidth hle κ l r =
      sanitizeAuthorizedPair hψ (preCheckResetWall m.1 m.2) := by
  rfl

private theorem doneThroughCheckEntryWidth_stage
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    let d := doneBeforeCheckEntryWidth hψ hwidth hle κ l r
    doneThroughCheckEntryWidth hψ hwidth hle κ l r =
      preserveDoneCheck hψ d.1 d.2 := by
  rfl

private theorem doneOrdinaryMetadataEntryWidth_stage
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    let c := doneThroughCheckEntryWidth hψ hwidth hle κ l r
    let q := afterCheckMetadataWidth hψ hwidth hle c.1 c.2
    doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r =
      markLeaderBirth (authBirth l r q) q := by
  rfl

attribute [local irreducible]
  BirthShortDoneCuts.beforeWriteWidth
  BirthShortDoneCuts.afterCheckMetadataWidth
  BirthShortDoneTerminalEntryCut.doneBeforeCheckEntryWidth
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth

private theorem beforeWriteWidth_right
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) :
    ClearsOrKeeps r.core.path
      (beforeWriteWidth hψ hwidth hle l r).2.core.path := by
  let d := authorizedDisappear hψ l r
  let c := authorizedCompareSigActionOne hψ d.1 d.2
  let s := authorizedSuppressWidth hψ hwidth hle c.1 c.2
  have hd : d.2.core.path = r.core.path :=
    BirthResponderHazardRows.disappear_right_path hψ l r
  have hc : c.2.core.path = d.2.core.path :=
    BirthResponderHazardRows.compare_right_path hψ d.1 d.2
  have hs : ClearsOrKeeps c.2.core.path s.2.core.path :=
    authorizedSuppressWidth_right hψ hwidth hle c.1 c.2
  have hstage : beforeWriteWidth hψ hwidth hle l r = s :=
    beforeWriteWidth_stage hψ hwidth hle l r
  have hpath :
      (beforeWriteWidth hψ hwidth hle l r).2.core.path = s.2.core.path :=
    congrArg
      (fun q : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
        q.2.core.path) hstage
  rw [hpath]
  rw [hc, hd] at hs
  exact hs

private theorem afterCheckMetadataWidth_right
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) :
    ClearsOrKeeps r.core.path
      (afterCheckMetadataWidth hψ hwidth hle l r).2.core.path := by
  let b := beforeWriteWidth hψ hwidth hle l r
  let w := stationaryPersistentAuthorizedRow hψ b.1 b.2
  have hb : ClearsOrKeeps r.core.path b.2.core.path :=
    beforeWriteWidth_right hψ hwidth hle l r
  have hw : w.2.core.path = b.2.core.path :=
    stationaryWriter_right_path hψ b.1 b.2
  have hstage : afterCheckMetadataWidth hψ hwidth hle l r = w :=
    afterCheckMetadataWidth_stage hψ hwidth hle l r
  have hpath :
      (afterCheckMetadataWidth hψ hwidth hle l r).2.core.path =
        w.2.core.path :=
    congrArg
      (fun q : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
        q.2.core.path) hstage
  rw [hpath, hw]
  exact hb

/-- From the actual DONE movement cut through reset/sanitize/CHECK, the right
main path can only be cleared or retained.  CHECK itself never substitutes
another nonempty path. -/
theorem doneThroughCheckEntryWidth_right_from_move
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
    let m := authorizedDoneMove hψ b.1 b.2
    ClearsOrKeeps m.2.core.path
      (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core.path := by
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
  let m := authorizedDoneMove hψ b.1 b.2
  let p := preCheckResetWall m.1 m.2
  let s := sanitizeAuthorizedPair hψ p
  let d := doneBeforeCheckEntryWidth hψ hwidth hle κ l r
  have hp : ClearsOrKeeps m.2.core.path p.2.core.path :=
    BirthResponderHazardRows.reset_right m.1 m.2
  have hs : s.2.core.path = p.2.core.path :=
    BirthResponderHazardRows.sanitize_right_path hψ p.1 p.2
  have hc : (preserveDoneCheck hψ s.1 s.2).2.core.path = s.2.core.path :=
    preserveDoneCheck_right_path hψ s.1 s.2
  have hd : d = s :=
    doneBeforeCheckEntryWidth_stage hψ hwidth hle κ l r
  have ht0 : doneThroughCheckEntryWidth hψ hwidth hle κ l r =
      preserveDoneCheck hψ d.1 d.2 :=
    doneThroughCheckEntryWidth_stage hψ hwidth hle κ l r
  have ht : doneThroughCheckEntryWidth hψ hwidth hle κ l r =
      preserveDoneCheck hψ s.1 s.2 :=
    ht0.trans <| congrArg
      (fun q : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
        preserveDoneCheck hψ q.1 q.2) hd
  have hpath :
      (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core.path =
        (preserveDoneCheck hψ s.1 s.2).2.core.path :=
    congrArg
      (fun q : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
        q.2.core.path) ht
  rw [hpath, hc, hs]
  exact hp

/-- Earliest reusable no-substitution interface for the exact terminal-entry
ordinary metadata row.  No final path survival is assumed. -/
theorem doneOrdinaryMetadataEntryWidth_right_from_move
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
    let m := authorizedDoneMove hψ b.1 b.2
    ClearsOrKeeps m.2.core.path
      (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r).2.core.path := by
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
  let m := authorizedDoneMove hψ b.1 b.2
  let c := doneThroughCheckEntryWidth hψ hwidth hle κ l r
  let q := afterCheckMetadataWidth hψ hwidth hle c.1 c.2
  let out := markLeaderBirth (authBirth l r q) q
  have hc : ClearsOrKeeps m.2.core.path c.2.core.path :=
    doneThroughCheckEntryWidth_right_from_move hψ hwidth hle κ l r
  have hq : ClearsOrKeeps c.2.core.path q.2.core.path :=
    afterCheckMetadataWidth_right hψ hwidth hle c.1 c.2
  have ht : ClearsOrKeeps m.2.core.path q.2.core.path :=
    ClearsOrKeeps.trans hq hc
  have hm : out.2.core.path = q.2.core.path :=
    BirthResponderHazardRows.mark_right_path (authBirth l r q) q
  have hstage : doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r = out :=
    doneOrdinaryMetadataEntryWidth_stage hψ hwidth hle κ l r
  have hpath :
      (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r).2.core.path =
        out.2.core.path :=
    congrArg
      (fun z : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
        z.2.core.path) hstage
  rw [hpath, hm]
  exact ht

/-- In particular, any nonempty ordinary metadata output is literally the
post-`authorizedDoneMove` path; equal-valued refill cannot be hidden here. -/
theorem doneOrdinaryMetadataEntryWidth_right_nonempty_is_move
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
    let m := authorizedDoneMove hψ b.1 b.2
    let out := doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r
    out.2.core.path ≠ .bot → out.2.core.path = m.2.core.path := by
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
  let m := authorizedDoneMove hψ b.1 b.2
  let out := doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r
  change out.2.core.path ≠ .bot → out.2.core.path = m.2.core.path
  intro hne
  have ht : ClearsOrKeeps m.2.core.path out.2.core.path :=
    doneOrdinaryMetadataEntryWidth_right_from_move hψ hwidth hle κ l r
  exact ht.retains hne

#print axioms BirthShortDoneTerminalHandoffTail.prepared_right_empty_of_normalized
#print axioms BirthShortDoneTerminalHandoffTail.authorizedSuppressWidth_right
#print axioms BirthShortDoneTerminalHandoffTail.doneThroughCheckEntryWidth_right_from_move
#print axioms BirthShortDoneTerminalHandoffTail.doneOrdinaryMetadataEntryWidth_right_from_move
#print axioms BirthShortDoneTerminalHandoffTail.doneOrdinaryMetadataEntryWidth_right_nonempty_is_move

end BirthShortDoneTerminalHandoffTail
