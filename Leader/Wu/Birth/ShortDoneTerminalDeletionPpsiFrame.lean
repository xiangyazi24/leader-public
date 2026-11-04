import Leader.Wu.Birth.ShortDoneTerminalDeletionRank
import Leader.Wu.Birth.PpsiLeaderCreationRepair

namespace BirthShortDoneTerminalDeletionPpsiFrame

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  BirthSigMoveDisposalRepair

open PPLLPpsiLeaderCreationRepair
  BirthShortDoneTerminalDeletionRank

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ n : Nat}

/-- Exact endpoint condition needed by the current `normalizeLeader` seam.
A follower satisfies it vacuously; a leader must already be at label zero. -/
def LeaderLabelReady (hψ : 0 < ψ)
    (u : ExpiringAgentState ψ κ τ) : Prop :=
  u.core.core.leader = true →
    u.core.core.label = ⟨0, hψ⟩

/-! ## Local frames for source helpers that are private in the old Ppsi file -/

private theorem normalizeDeletion_ppsiControl_local
    (u : AuthorizedAgentState ψ) :
    PpsiControlView.ofState (normalizeDeletion u).core =
      PpsiControlView.ofState u.core := by
  unfold normalizeDeletion
  split <;> rfl

private theorem prepareDisposal_ppsiControl_local
    (hψ : 0 < ψ) (u : AuthorizedAgentState ψ) :
    PpsiControlView.ofState (prepareDisposal hψ u).core =
      PpsiControlView.ofState u.core := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl

private theorem prepareExpiringDisposal_ppsiControl_local
    (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    PpsiControlView.ofState
        (prepareExpiringDisposal hψ u).core.erase.core =
      PpsiControlView.ofState u.core.erase.core := by
  change
    PpsiControlView.ofState
        (prepareBoundedDisposal hψ u.core).erase.core =
      PpsiControlView.ofState u.core.erase.core
  have he := erase_prepareBoundedDisposal hψ u.core
  have hv := congrArg
    (fun a : AuthorizedAgentState ψ => PpsiControlView.ofState a.core) he
  exact hv.trans (prepareDisposal_ppsiControl_local hψ u.core.erase)

private theorem nonK2_ppsiControl_local
    (u : ExpiringAgentState ψ κ τ) :
    PpsiControlView.ofState
        (ExpiringK2Projection.nonK2 u).core.erase.core =
      PpsiControlView.ofState u.core.erase.core := by
  rfl

private theorem nonK2_eq_ppsiControl_local
    {a b : ExpiringAgentState ψ κ τ}
    (h : ExpiringK2Projection.nonK2 a =
      ExpiringK2Projection.nonK2 b) :
    PpsiControlView.ofState a.core.erase.core =
      PpsiControlView.ofState b.core.erase.core := by
  have hm := congrArg
    (fun u : ExpiringAgentState ψ κ τ =>
      PpsiControlView.ofState u.core.erase.core) h
  exact (nonK2_ppsiControl_local a).symm.trans
    (hm.trans (nonK2_ppsiControl_local b))

/-! ## Exact normalizeLeader seam -/

/-- `LeaderLabelReady` is sufficient for normalization to be invisible to the
old P-prime control projection. -/
theorem normalizeLeader_ppsiControl_of_ready
    (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ)
    (hready : LeaderLabelReady hψ u) :
    PpsiControlView.ofState
        (K2BirthLeaderNormalize.normalizeLeader hψ u).core.erase.core =
      PpsiControlView.ofState u.core.erase.core := by
  unfold K2BirthLeaderNormalize.normalizeLeader
  split
  · rename_i hleader
    have hzero : u.core.core.label = ⟨0, hψ⟩ := hready hleader
    have hsame :
        K2BirthLeaderNormalize.putLabel u ⟨0, hψ⟩ = u := by
      rw [← hzero]
      exact K2BirthLeaderNormalize.putLabel_self u
    rw [hsame]
  · rfl

/-- The seam premise is also necessary: this is the exact condition under
which `normalizeLeader` frames `(label, probe, phase)`. -/
theorem normalizeLeader_ppsiControl_iff_ready
    (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    PpsiControlView.ofState
        (K2BirthLeaderNormalize.normalizeLeader hψ u).core.erase.core =
      PpsiControlView.ofState u.core.erase.core ↔
    LeaderLabelReady hψ u := by
  constructor
  · intro hframe hleader
    have hlabel := congrArg PpsiControlView.label hframe
    change
      (K2BirthLeaderNormalize.normalizeLeader hψ u).core.core.label =
        u.core.core.label at hlabel
    have hnleader :
        (K2BirthLeaderNormalize.normalizeLeader hψ u).core.core.leader =
          true :=
      (K2BirthLeaderNormalize.normalizeLeader_leader hψ u).trans hleader
    have hzero :=
      K2BirthLeaderNormalize.normalizeLeader_label_zero hψ u hnleader
    exact hlabel.symm.trans hzero
  · exact normalizeLeader_ppsiControl_of_ready hψ u

/-! ## Active responder through preparation, finite reification and expiry -/

private theorem
    doneMetadataAuthorizedEntryWidth_active_responder_ppsiControlPair
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hr : deletionActive (normalizeDeletion r) = true) :
    authorizedPpsiControlPair
        (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
          hψ hwidth hle κ l r) =
      authorizedPpsiControlPair (l, r) := by
  unfold BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
  dsimp only
  rw [if_pos hr]
  calc
    authorizedPpsiControlPair
        (authorizedEliminateSig hψ
          (normalizeDeletion l) (normalizeDeletion r)) =
      authorizedPpsiControlPair
        (normalizeDeletion l, normalizeDeletion r) :=
      PPLLPpsiLeaderCreationRepair.authorizedEliminateSig_ppsiControlPair
        hψ (normalizeDeletion l) (normalizeDeletion r)
    _ = authorizedPpsiControlPair (l, r) := by
      change
        (PpsiControlView.ofState (normalizeDeletion l).core,
          PpsiControlView.ofState (normalizeDeletion r).core) =
        (PpsiControlView.ofState l.core,
          PpsiControlView.ofState r.core)
      exact Prod.ext
        (normalizeDeletion_ppsiControl_local l)
        (normalizeDeletion_ppsiControl_local r)

private theorem
    doneMetadataBoundedEntryWidth_active_responder_ppsiControlPair
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ)
    (hr : deletionActive (normalizeDeletion r.erase) = true) :
    boundedPpsiControlPair
        (BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
          hψ hwidth hle l r) =
      authorizedPpsiControlPair (l.erase, r.erase) := by
  let q := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
    hψ hwidth hle l r
  have he := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth_erase
    hψ hwidth hle l r
  change
    (q.1.erase, q.2.erase) =
      BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
        hψ hwidth hle κ l.erase r.erase at he
  have ha :=
    doneMetadataAuthorizedEntryWidth_active_responder_ppsiControlPair
      hψ hwidth hle κ l.erase r.erase hr
  change boundedPpsiControlPair q =
    authorizedPpsiControlPair (l.erase, r.erase)
  calc
    boundedPpsiControlPair q =
        authorizedPpsiControlPair (q.1.erase, q.2.erase) := rfl
    _ = authorizedPpsiControlPair
        (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
          hψ hwidth hle κ l.erase r.erase) :=
      congrArg
        (fun z : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
          authorizedPpsiControlPair z) he
    _ = authorizedPpsiControlPair (l.erase, r.erase) := ha

private theorem
    doneMetadataEntryWidth_active_responder_ppsiControlPair
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hactive : CurrentPreparedDeletionActive hψ r) :
    expiringPpsiControlPair
        (BirthShortDoneTerminalHost.doneMetadataEntryWidth
          hψ hwidth hle l r) =
      expiringPpsiControlPair (l, r) := by
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
    hψ hwidth hle l0.core r0.core
  let baseL : ExpiringAgentState ψ κ τ := ⟨q.1, l0.stall⟩
  let baseR : ExpiringAgentState ψ κ τ := ⟨q.2, r0.stall⟩

  have hactive0 :
      deletionActive (normalizeDeletion r0.core.erase) = true := by
    simpa only [r0, CurrentPreparedDeletionActive] using hactive

  have hq :=
    doneMetadataBoundedEntryWidth_active_responder_ppsiControlPair
      hψ hwidth hle l0.core r0.core hactive0
  change
    (PpsiControlView.ofState q.1.erase.core,
      PpsiControlView.ofState q.2.erase.core) =
    (PpsiControlView.ofState l0.core.erase.core,
      PpsiControlView.ofState r0.core.erase.core) at hq
  have hqL := congrArg Prod.fst hq
  have hqR := congrArg Prod.snd hq

  have hpL := prepareExpiringDisposal_ppsiControl_local hψ l
  have hpR := prepareExpiringDisposal_ppsiControl_local hψ r
  change
    PpsiControlView.ofState l0.core.erase.core =
      PpsiControlView.ofState l.core.erase.core at hpL
  change
    PpsiControlView.ofState r0.core.erase.core =
      PpsiControlView.ofState r.core.erase.core at hpR

  have heL :=
    PPLLPpsiLeaderCreationRepair.deletionPriorityExpireOne_ppsiControl
      l0 baseL
  have heR :=
    PPLLPpsiLeaderCreationRepair.deletionPriorityExpireOne_ppsiControl
      r0 baseR
  change
    PpsiControlView.ofState
        (deletionPriorityExpireOne τ l0 baseL).core.erase.core =
      PpsiControlView.ofState q.1.erase.core at heL
  change
    PpsiControlView.ofState
        (deletionPriorityExpireOne τ r0 baseR).core.erase.core =
      PpsiControlView.ofState q.2.erase.core at heR

  change
    (PpsiControlView.ofState
        (deletionPriorityExpireOne τ l0 baseL).core.erase.core,
      PpsiControlView.ofState
        (deletionPriorityExpireOne τ r0 baseR).core.erase.core) =
    (PpsiControlView.ofState l.core.erase.core,
      PpsiControlView.ofState r.core.erase.core)
  exact Prod.ext
    (heL.trans (hqL.trans hpL))
    (heR.trans (hqR.trans hpR))

/-! ## Complete current TerminalHost row -/

/-- The actual current row preserves the old drain's exact P-prime control
pair whenever the two endpoints reaching `normalizeLeader` are label-ready. -/
theorem row_prepared_responder_delete_ppsiControlPair
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hactive : CurrentPreparedDeletionActive hψ r)
    (hreadyL : LeaderLabelReady hψ
      (BirthShortDoneTerminalHost.doneMetadataEntryWidth
        hψ hwidth hle l r).1)
    (hreadyR : LeaderLabelReady hψ
      (BirthShortDoneTerminalHost.doneMetadataEntryWidth
        hψ hwidth hle l r).2) :
    expiringPpsiControlPair
        (BirthShortDoneTerminalHost.row hψ hwidth hle l r) =
      expiringPpsiControlPair (l, r) := by
  let e := BirthShortDoneTerminalHost.doneMetadataEntryWidth
    hψ hwidth hle l r
  let mL := K2BirthLeaderNormalize.normalizeLeader hψ e.1
  let mR := K2BirthLeaderNormalize.normalizeLeader hψ e.2

  have he := doneMetadataEntryWidth_active_responder_ppsiControlPair
    hψ hwidth hle l r hactive
  change expiringPpsiControlPair e =
    expiringPpsiControlPair (l, r) at he

  have hnL := normalizeLeader_ppsiControl_of_ready hψ e.1 (by
    simpa only [e] using hreadyL)
  have hnR := normalizeLeader_ppsiControl_of_ready hψ e.2 (by
    simpa only [e] using hreadyR)
  change
    PpsiControlView.ofState mL.core.erase.core =
      PpsiControlView.ofState e.1.core.erase.core at hnL
  change
    PpsiControlView.ofState mR.core.erase.core =
      PpsiControlView.ofState e.2.core.erase.core at hnR

  have hf := K2BirthDispatcher.finalPhysical_nonK2
    hψ l r mL mR
  have hfL := nonK2_eq_ppsiControl_local hf.1
  have hfR := nonK2_eq_ppsiControl_local hf.2

  have hrow :
      BirthShortDoneTerminalHost.row hψ hwidth hle l r =
        K2BirthDispatcher.finalPhysical hψ l r mL mR := by
    rfl
  rw [hrow]
  change
    (PpsiControlView.ofState
        (K2BirthDispatcher.finalPhysical hψ l r mL mR).1.core.erase.core,
      PpsiControlView.ofState
        (K2BirthDispatcher.finalPhysical hψ l r mL mR).2.core.erase.core) =
    (PpsiControlView.ofState l.core.erase.core,
      PpsiControlView.ofState r.core.erase.core)
  exact Prod.ext
    (hfL.trans (hnL.trans (congrArg Prod.fst he)))
    (hfR.trans (hnR.trans (congrArg Prod.snd he)))

/-! ## Finite obstruction when endpoint readiness is dropped -/

private theorem counter_psi_pos : 0 < 2 := by decide
private theorem counter_width_pos : 0 < 1 := by decide
private theorem counter_width_le : 1 ≤ 2 := by decide

/-- Full `psi = 2` initiator record: an already-existing leader at nonzero
label 1.  All other fields are explicitly neutral. -/
def counterexampleLeftRaw : AgentState 2 :=
  { leader := true
    probe := false
    phase := false
    bit := false
    wait := false
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := 1
    h_field := false
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 0
    shield := false
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false }

/-- Full responder record: label 0 with a present deletion-marked comparison
path.  Thus it selects the actual responder-priority branch. -/
def counterexampleRightRaw : AgentState 2 :=
  { leader := false
    probe := false
    phase := false
    bit := false
    wait := false
    state := .eliminate_signal
    path := .some 0 0
    reset := false
    carry := false
    count := 0
    label := 0
    h_field := false
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 0
    shield := false
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false }

private theorem counterexampleLeftRaw_domain :
    counterexampleLeftRaw.inProtocolDomain 0 := by
  simp [counterexampleLeftRaw, AgentState.inProtocolDomain]

private theorem counterexampleRightRaw_domain :
    counterexampleRightRaw.inProtocolDomain 0 := by
  simp [counterexampleRightRaw, AgentState.inProtocolDomain]

/-- `psi = 2`, `kappa = 0`, `tau = 0`. -/
def counterexampleLeft : ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain
      counterexampleLeftRaw counterexampleLeftRaw_domain, false⟩, 0⟩

/-- `psi = 2`, `kappa = 0`, `tau = 0`. -/
def counterexampleRight : ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain
      counterexampleRightRaw counterexampleRightRaw_domain, false⟩, 0⟩

private def counterPre :
    ExpiringAgentState 2 0 0 × ExpiringAgentState 2 0 0 :=
  BirthShortDoneTerminalHost.doneMetadataEntryWidth
    counter_psi_pos counter_width_pos counter_width_le
    counterexampleLeft counterexampleRight

private def counterOut :
    ExpiringAgentState 2 0 0 × ExpiringAgentState 2 0 0 :=
  BirthShortDoneTerminalHost.row
    counter_psi_pos counter_width_pos counter_width_le
    counterexampleLeft counterexampleRight

/-- Concrete failure of the unconditional Ppsi frame.  The active-responder
branch leaves the initiator as a leader at label 1 through expiry; the sole
failure is the following `normalizeLeader`, which changes that label to 0. -/
theorem leaderLabelReady_cannot_be_dropped :
    CurrentPreparedDeletionActive counter_psi_pos counterexampleRight ∧
      counterPre.1.core.erase.core.leader = true ∧
      counterPre.1.core.erase.core.label = (1 : Fin 2) ∧
      ¬ LeaderLabelReady counter_psi_pos counterPre.1 ∧
      PpsiControlView.ofState
          (K2BirthLeaderNormalize.normalizeLeader
            counter_psi_pos counterPre.1).core.erase.core ≠
        PpsiControlView.ofState counterPre.1.core.erase.core ∧
      counterOut.1.core.erase.core.label = (0 : Fin 2) ∧
      expiringPpsiControlPair counterOut ≠
        expiringPpsiControlPair
          (counterexampleLeft, counterexampleRight) := by
  have hactive :
      CurrentPreparedDeletionActive counter_psi_pos counterexampleRight := by
    unfold CurrentPreparedDeletionActive
    decide
  have hleader :
      counterPre.1.core.erase.core.leader = true := by
    decide
  have hlabel :
      counterPre.1.core.erase.core.label = (1 : Fin 2) := by
    decide
  have hnotready :
      ¬ LeaderLabelReady counter_psi_pos counterPre.1 := by
    unfold LeaderLabelReady
    intro hready
    have hzero : counterPre.1.core.core.label = (0 : Fin 2) :=
      hready (by decide)
    have hone : counterPre.1.core.core.label = (1 : Fin 2) := by
      decide
    exact (by decide : (1 : Fin 2) ≠ (0 : Fin 2))
      (hone.symm.trans hzero)
  have hnormalize :
      PpsiControlView.ofState
          (K2BirthLeaderNormalize.normalizeLeader
            counter_psi_pos counterPre.1).core.erase.core ≠
        PpsiControlView.ofState counterPre.1.core.erase.core := by
    intro hframe
    exact hnotready
      ((normalizeLeader_ppsiControl_iff_ready
        counter_psi_pos counterPre.1).1 hframe)
  have houtlabel :
      counterOut.1.core.erase.core.label = (0 : Fin 2) := by
    decide
  have hpairs :
      expiringPpsiControlPair counterOut ≠
        expiringPpsiControlPair
          (counterexampleLeft, counterexampleRight) := by
    intro hpair
    have hl := congrArg
      (fun q : PpsiControlView 2 × PpsiControlView 2 => q.1.label) hpair
    change
      counterOut.1.core.erase.core.label =
        counterexampleLeft.core.erase.core.label at hl
    have hinlabel :
        counterexampleLeft.core.erase.core.label = (1 : Fin 2) := by
      decide
    rw [houtlabel, hinlabel] at hl
    exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) hl
  exact ⟨hactive, hleader, hlabel, hnotready,
    hnormalize, houtlabel, hpairs⟩

/-! ## Actual localStep: rank contraction plus old-drain Ppsi frame -/

/-- On a real non-singleton ring, one current prepared-active responder edge
strictly contracts `comparisonPathCount` and simultaneously preserves the
pointwise P-prime control frame, provided exactly the two normalization
endpoints are `LeaderLabelReady`. -/
theorem localStep_prepared_responder_delete_count_lt_and_ppsiControlFrame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hactive : CurrentPreparedDeletionActive hψ
      (C (ring.rightNeighbor e)))
    (hreadyL : LeaderLabelReady hψ
      (BirthShortDoneTerminalHost.doneMetadataEntryWidth
        hψ hwidth hle (C e) (C (ring.rightNeighbor e))).1)
    (hreadyR : LeaderLabelReady hψ
      (BirthShortDoneTerminalHost.doneMetadataEntryWidth
        hψ hwidth hle (C e) (C (ring.rightNeighbor e))).2) :
    let D := localStep ring
      (BirthShortDoneTerminalHost.row hψ hwidth hle) C e
    comparisonPathCount D < comparisonPathCount C ∧
      PpsiControlConfigFrame C D := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let q := BirthShortDoneTerminalHost.row
    hψ hwidth hle (C e) (C j)
  let D := localStep ring
    (BirthShortDoneTerminalHost.row hψ hwidth hle) C e

  have hcount :=
    BirthShortDoneTerminalDeletionRank.localStep_prepared_responder_delete_count_lt
      hψ hwidth hle ring hn C e hactive
  change comparisonPathCount D < comparisonPathCount C at hcount

  have hpair := row_prepared_responder_delete_ppsiControlPair
    hψ hwidth hle (C e) (C j)
    (by simpa only [j] using hactive)
    (by simpa only [j] using hreadyL)
    (by simpa only [j] using hreadyR)
  change expiringPpsiControlPair q =
    expiringPpsiControlPair (C e, C j) at hpair

  have hleft : D e = q.1 := by
    simp [D, q, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, localStep, j, hje]

  refine ⟨hcount, ?_⟩
  change PpsiControlConfigFrame C D
  intro i
  by_cases hie : i = e
  · subst i
    rw [hleft]
    exact congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      rw [hright]
      exact congrArg Prod.snd hpair
    · have hsame : D i = C i := by
        simp [D, localStep, hie, hij, j]
      rw [hsame]

#print axioms BirthShortDoneTerminalDeletionPpsiFrame.normalizeLeader_ppsiControl_of_ready
#print axioms BirthShortDoneTerminalDeletionPpsiFrame.normalizeLeader_ppsiControl_iff_ready
#print axioms BirthShortDoneTerminalDeletionPpsiFrame.row_prepared_responder_delete_ppsiControlPair
#print axioms BirthShortDoneTerminalDeletionPpsiFrame.leaderLabelReady_cannot_be_dropped
#print axioms BirthShortDoneTerminalDeletionPpsiFrame.localStep_prepared_responder_delete_count_lt_and_ppsiControlFrame

end BirthShortDoneTerminalDeletionPpsiFrame
