import Leader.Wu.Birth.ShortDoneTerminalObserver

namespace BirthShortDoneTerminalBirthSources

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
  BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortWaitTerminalEntryRepair BirthSigMoveDisposalRepair
  BirthTossCheckPreservationRepair BirthCheckCongestGuardRepair
open K2BirthDispatcher K2BirthDispatcherDone ExpiringK2Projection
  BirthShortDoneCuts BirthShortDoneTerminalEntryCut

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ : Nat}

def pPrimeBirth (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) : Bool :=
  let q := authorizedPPsiLeaderResetProbeWall hψ l r
  authBirth l r q

def PPrimeBarrierBirthGuard (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) : Prop :=
  l.core.leader = false ∧ r.core.leader = false ∧
  l.core.reset_cmd = false ∧ r.core.probe = true ∧
  isBarrier hψ l.core r.core

def checkBirth (hψ : 0 < ψ)
    (b : AuthorizedAgentState ψ × AuthorizedAgentState ψ) : Bool :=
  let c := preserveDoneCheck hψ b.1 b.2
  authBirth b.1 b.2 c

def ActualCheckBirth (hψ : 0 < ψ)
    (b : AuthorizedAgentState ψ × AuthorizedAgentState ψ) : Prop :=
  b.1.core.state ≠ .done ∧ b.2.core.state ≠ .done ∧
  b.1.core.state ≠ .toss ∧ b.2.core.state ≠ .toss ∧
  b.1.core.state ≠ .congest ∧ b.2.core.state ≠ .congest ∧
  b.2.core.leader = false ∧
  (authorizedCheckSig hψ b.1 b.2).2.core.leader = true

private theorem leaders_of_signal
    {q p : AuthorizedAgentState ψ × AuthorizedAgentState ψ}
    (h : authSignalPair q = authSignalPair p) :
    q.1.core.leader = p.1.core.leader ∧ q.2.core.leader = p.2.core.leader := by
  exact ⟨congrArg (fun z : AgentState 1 × AgentState 1 => z.1.leader) h,
    congrArg (fun z : AgentState 1 × AgentState 1 => z.2.leader) h⟩

private theorem birth_output_congr (l r : AuthorizedAgentState ψ)
    {q p : AuthorizedAgentState ψ × AuthorizedAgentState ψ}
    (h : authSignalPair q = authSignalPair p) :
    authBirth l r q = authBirth l r p := by
  have hp := leaders_of_signal h
  unfold authBirth endpointLeaderBorn
  rw [hp.1, hp.2]

private theorem birth_input_congr
    {l r l' r' : AuthorizedAgentState ψ}
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (h : authSignalPair (l, r) = authSignalPair (l', r')) :
    authBirth l r q = authBirth l' r' q := by
  have hp := leaders_of_signal h
  unfold authBirth endpointLeaderBorn
  rw [hp.1, hp.2]

private theorem born_chain (a m z : Bool) (h : (!a && z) = true) :
    (!a && m) = true ∨ (!m && z) = true := by
  cases a <;> cases m
  · exact Or.inr h
  · exact Or.inl rfl
  · simp at h
  · simp at h

private theorem authBirth_chain (l r : AuthorizedAgentState ψ)
    (m q : AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (h : authBirth l r q = true) :
    authBirth l r m = true ∨ authBirth m.1 m.2 q = true := by
  unfold authBirth endpointLeaderBorn at h ⊢
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · rcases born_chain l.core.leader m.1.core.leader q.1.core.leader h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
  · rcases born_chain r.core.leader m.2.core.leader q.2.core.leader h with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

open PPLLRepair

private theorem genStart_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genSigSaturatedStart hψ l r) = signalPair (l, r) := by
  unfold genSigSaturatedStart; split <;> dsimp only <;> split <;> rfl
private theorem genEmit_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genCleanEmit hψ l r) = signalPair (l, r) := by
  unfold genCleanEmit; repeat (first | rfl | split)
private theorem genProp_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genCleanPropagate hψ l r) = signalPair (l, r) := by
  unfold genCleanPropagate; repeat (first | rfl | split)
private theorem genFinish_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genSigSaturatedFinish hψ l r) = signalPair (l, r) := by
  unfold genSigSaturatedFinish; repeat (first | rfl | split)
private theorem genEntry_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AgentState ψ) :
    signalPair (genCleanEntryWidth hψ hwidth hle κ l r) = signalPair (l, r) := by
  unfold genCleanEntryWidth
  dsimp only
  calc
    signalPair
        (genCleanAfterWait hψ
          (waitWidthEntry hψ hwidth hle κ l r).1
          (waitWidthEntry hψ hwidth hle κ l r).2) =
      signalPair
        ((waitWidthEntry hψ hwidth hle κ l r).1,
          (waitWidthEntry hψ hwidth hle κ l r).2) := by
      unfold genCleanAfterWait
      dsimp only
      rw [genFinish_signal, genProp_signal, genEmit_signal, genStart_signal]
    _ = signalPair (l, r) :=
      BirthShortDoneTerminalConsumer.waitWidthEntry_signal
        hψ hwidth hle κ l r

private theorem before_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authSignalPair (doneBeforeCheckEntryWidth hψ hwidth hle κ l r) =
      authSignalPair (authorizedPPsiLeaderResetProbeWall hψ l r) := by
  let p := authorizedPPsiLeaderResetProbeWall hψ l r
  let g := authorizedGenCleanEntryWidth hψ hwidth hle κ p.1 p.2
  have hg : authSignalPair g = authSignalPair p := by
    change signalPair (genCleanEntryWidth hψ hwidth hle κ p.1.core p.2.core) = _
    exact genEntry_signal hψ hwidth hle κ p.1.core p.2.core
  let c := authorizedCleanSig hψ g.1 g.2
  let b := authorizedEliminateSig hψ c.1 c.2
  have hb : authSignalPair b = authSignalPair p :=
    (eliminate_signal hψ c.1 c.2).trans ((clean_signal hψ g.1 g.2).trans hg)
  let m := authorizedDoneMove hψ b.1 b.2
  unfold doneBeforeCheckEntryWidth generationBeforeMoveEntryWidth
  exact (authSignalPair_of_peace
    (sanitizePreCheckResetWall_peaceViewPair hψ m)).trans
      ((authorizedDoneMove_signal hψ b.1 b.2).trans hb)

private theorem ordinary_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authSignalPair
      (BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
        hψ hwidth hle κ l r) =
    authSignalPair (doneThroughCheckEntryWidth hψ hwidth hle κ l r) := by
  unfold BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
  dsimp only
  generalize doneThroughCheckEntryWidth hψ hwidth hle κ l r = c
  exact (markBirth_signal _ _).trans
    (afterCheckMetadataWidth_signal hψ hwidth hle c.1 c.2)

/-- Exact expiring event bridge; no hypothesis on τ. -/
theorem birthEvent_eq_authorized (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle l r =
      authBirth (prepareExpiringDisposal hψ l).core.erase
        (prepareExpiringDisposal hψ r).core.erase
        (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
          hψ hwidth hle κ (prepareExpiringDisposal hψ l).core.erase
            (prepareExpiringDisposal hψ r).core.erase) := by
  have hl := congrArg AgentState.leader (prepareExpiring_signal hψ l)
  have hr := congrArg AgentState.leader (prepareExpiring_signal hψ r)
  change (prepareExpiringDisposal hψ l).core.core.leader =
    l.core.core.leader at hl
  change (prepareExpiringDisposal hψ r).core.core.leader =
    r.core.core.leader at hr
  have he := (BirthShortDoneTerminalConsumer.metadata_observation_raw
    hψ hwidth hle l r).trans
      (BirthShortDoneTerminalConsumer.doneMetadataEntryWidth_observation
        hψ hwidth hle l r)
  have h := congrArg (fun q : AgentState 1 × AgentState 1 =>
    (!l.core.core.leader && q.1.leader) ||
      (!r.core.core.leader && q.2.leader)) he
  unfold BirthShortDoneTerminalObserver.birthEvent K2BirthDispatcher.newborn
    authBirth endpointLeaderBorn
  change _ = ((! (prepareExpiringDisposal hψ l).core.core.leader && _) || _)
  rw [hl]
  change (prepareExpiringDisposal hψ r).core.erase.core.leader =
    r.core.core.leader at hr
  rw [hr]
  exact h

/-- Literal P′ necessity, at the actual prepared/normalized P′ input. -/
theorem pPrimeBirth_guard (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (h : pPrimeBirth hψ l r = true) : PPrimeBarrierBirthGuard hψ l r := by
  unfold pPrimeBirth PPrimeBarrierBirthGuard at *
  cases hl : l.core.leader <;> cases hr : r.core.leader <;>
  cases hx : l.core.reset_cmd <;> cases hp : r.core.probe <;>
    simp_all [authBirth, endpointLeaderBorn, authorizedPPsiLeaderResetProbeWall,
      pPsiLeaderResetProbeWall, pPsi, isBarrier]

private theorem check_left (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    (authorizedCheckSig hψ l r).1.core.leader = l.core.leader := by
  change (checkSig hψ l.core r.core).1.leader = l.core.leader
  exact PPLLVerify.checkSig_initiator_leader_eq hψ l.core r.core

private theorem check_birth_right (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (h : authBirth l r (authorizedCheckSig hψ l r) = true) :
    r.core.leader = false ∧ (authorizedCheckSig hψ l r).2.core.leader = true := by
  rw [authBirth, Bool.or_eq_true] at h
  rcases h with h | h
  · simp [endpointLeaderBorn, check_left] at h
  · unfold endpointLeaderBorn at h
    cases hr : r.core.leader <;>
      cases ho : (authorizedCheckSig hψ l r).2.core.leader <;> simp_all

/-- A positive guarded-CHECK cut means literal CHECK actually ran and birthed
its responder; done/toss/congest identity branches are excluded. -/
theorem checkBirth_guard (hψ : 0 < ψ)
    (b : AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (h : checkBirth hψ b = true) : ActualCheckBirth hψ b := by
  unfold checkBirth at h; dsimp only at h
  by_cases hd : b.1.core.state = .done ∨ b.2.core.state = .done
  · simp [preserveDoneCheck, hd, authBirth, endpointLeaderBorn] at h
  · have hdl := fun x => hd (Or.inl x); have hdr := fun x => hd (Or.inr x)
    rw [preserveDoneCheck_of_no_done hψ _ _ hdl hdr] at h
    by_cases ht : b.1.core.state = .toss ∨ b.2.core.state = .toss
    · rw [preserveTossCheck_of_toss hψ _ _ ht] at h
      simp [authBirth, endpointLeaderBorn] at h
    · have htl := fun x => ht (Or.inl x); have htr := fun x => ht (Or.inr x)
      rw [preserveTossCheck_of_no_toss hψ _ _ htl htr] at h
      by_cases hc : b.1.core.state = .congest ∨ b.2.core.state = .congest
      · rw [congestGuardCheck_of_congest hψ _ _ hc] at h
        simp [authBirth, endpointLeaderBorn] at h
      · have hcl := fun x => hc (Or.inl x); have hcr := fun x => hc (Or.inr x)
        rw [congestGuardCheck_of_clear hψ _ _ hcl hcr] at h
        have hb := check_birth_right hψ b.1 b.2 h
        exact ⟨hdl, hdr, htl, htr, hcl, hcr, hb.1, hb.2⟩

/-- Exhaustive authorized census. Priority branches cannot birth. -/
theorem authorized_birth_sources (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : AuthorizedAgentState ψ)
    (h : authBirth l r
      (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
        hψ hwidth hle κ l r) = true) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let b := doneBeforeCheckEntryWidth hψ hwidth hle κ l0 r0
    deletionActive r0 = false ∧ deletionActive l0 = false ∧
      (PPrimeBarrierBirthGuard hψ l0 r0 ∨ ActualCheckBirth hψ b) := by
  dsimp only
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  change deletionActive r0 = false ∧ deletionActive l0 = false ∧
    (PPrimeBarrierBirthGuard hψ l0 r0 ∨
      ActualCheckBirth hψ
        (doneBeforeCheckEntryWidth hψ hwidth hle κ l0 r0))
  cases hr : deletionActive r0 with
  | true =>
      have hs : authSignalPair
          (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
            hψ hwidth hle κ l r) = authSignalPair (l, r) := by
        simp [BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth,
          l0, r0, hr, eliminate_signal, normalize_pair_signal]
      have hz : authBirth l r
          (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
            hψ hwidth hle κ l r) = false := by
        calc
          _ = authBirth l r (l, r) := birth_output_congr l r hs
          _ = false := by simp [authBirth, endpointLeaderBorn]
      rw [hz] at h
      simp at h
  | false =>
      cases hl : deletionActive l0 with
      | true =>
          have hs : authSignalPair
              (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
                hψ hwidth hle κ l r) = authSignalPair (l, r) := by
            simpa [BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth,
              l0, r0, hr, hl] using normalize_pair_signal l r
          have hz : authBirth l r
              (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
                hψ hwidth hle κ l r) = false := by
            calc
              _ = authBirth l r (l, r) := birth_output_congr l r hs
              _ = false := by simp [authBirth, endpointLeaderBorn]
          rw [hz] at h
          simp at h
      | false =>
          refine ⟨rfl, rfl, ?_⟩
          let b := doneBeforeCheckEntryWidth hψ hwidth hle κ l0 r0
          let c := doneThroughCheckEntryWidth hψ hwidth hle κ l0 r0
          change PPrimeBarrierBirthGuard hψ l0 r0 ∨ ActualCheckBirth hψ b
          have hs : authSignalPair
              (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
                hψ hwidth hle κ l r) = authSignalPair c := by
            calc
              _ = authSignalPair
                  (BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
                    hψ hwidth hle κ l0 r0) := by
                    simp [BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth,
                      l0, r0, hr, hl]
              _ = authSignalPair c := by
                change authSignalPair
                    (BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
                      hψ hwidth hle κ l0 r0) =
                  authSignalPair
                    (doneThroughCheckEntryWidth hψ hwidth hle κ l0 r0)
                exact ordinary_signal hψ hwidth hle κ l0 r0
          have hc0 : authBirth l r c = true :=
            (birth_output_congr l r hs).symm.trans h
          have hn : authSignalPair (l0, r0) = authSignalPair (l, r) := by
            simpa [l0, r0] using normalize_pair_signal l r
          have h0 : authBirth l0 r0 c = true :=
            (birth_input_congr c hn).trans hc0
          rcases authBirth_chain l0 r0 b c h0 with hp | hc
          · change authBirth l0 r0
              (doneBeforeCheckEntryWidth hψ hwidth hle κ l0 r0) = true at hp
            have hp' : pPrimeBirth hψ l0 r0 = true := by
              unfold pPrimeBirth
              exact (birth_output_congr l0 r0
                (before_signal hψ hwidth hle κ l0 r0)).symm.trans hp
            exact Or.inl (pPrimeBirth_guard hψ l0 r0 hp')
          · change authBirth b.1 b.2
              (preserveDoneCheck hψ b.1 b.2) = true at hc
            have hc' : checkBirth hψ b = true := by
              unfold checkBirth
              dsimp only
              exact hc
            exact Or.inr (checkBirth_guard hψ b hc')

/-- Actual finite-carrier result, all legal widths and every τ including zero. -/
theorem birthEvent_sources (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (h : BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle l r = true) :
    let pl := prepareExpiringDisposal hψ l
    let pr := prepareExpiringDisposal hψ r
    let l0 := normalizeDeletion pl.core.erase
    let r0 := normalizeDeletion pr.core.erase
    let b := doneBeforeCheckEntryWidth hψ hwidth hle κ l0 r0
    deletionActive r0 = false ∧ deletionActive l0 = false ∧
      (PPrimeBarrierBirthGuard hψ l0 r0 ∨ ActualCheckBirth hψ b) := by
  rw [birthEvent_eq_authorized hψ hwidth hle l r] at h
  exact authorized_birth_sources hψ hwidth hle _ _ h

end BirthShortDoneTerminalBirthSources

#print axioms BirthShortDoneTerminalBirthSources.birthEvent_eq_authorized
#print axioms BirthShortDoneTerminalBirthSources.pPrimeBirth_guard
#print axioms BirthShortDoneTerminalBirthSources.checkBirth_guard
#print axioms BirthShortDoneTerminalBirthSources.authorized_birth_sources
#print axioms BirthShortDoneTerminalBirthSources.birthEvent_sources
