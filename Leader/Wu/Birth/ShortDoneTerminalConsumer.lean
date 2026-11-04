import Leader.Wu.Birth.ShortDoneTerminalHost


/-!
# Concrete consumers of the terminal-entry repaired DONE host


No scheduler-word invariant is stored.  The transition below is exactly
`BirthShortDoneTerminalHost.row`.
-/


namespace BirthShortDoneTerminalConsumer


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthConditionTwoFrames PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol BirthGenerationControlRepair
  BirthShortWait BirthSigMoveDisposalRepair BirthGenerationDone K2OutputSafety


open K2BirthDispatcher K2BirthDispatcherDone ExpiringK2Projection
  K2BirthLeaderNormalize BirthShortDoneCuts BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalHost BirthShortWaitTerminalEntryRepair


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


variable {ψ width κ τ n : Nat}


/-! ## The repaired WAIT is invisible to the physical four-field view -/


private theorem waitPrep_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (waitSaturatedPrepare hψ l r) = signalPair (l, r) := by
  unfold waitSaturatedPrepare
  repeat (first | rfl | split)


private theorem terminalClear_signal (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : AgentState ψ) :
    signalPair (terminalInactiveClear hwidth hle l r) = signalPair (l, r) := by
  unfold terminalInactiveClear
  split <;> rfl


private theorem waitCarry_signal (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AgentState ψ) :
    signalPair (waitWidthCarry hwidth hle κ l r) = signalPair (l, r) := by
  unfold waitWidthCarry
  repeat (first | rfl | split)


private theorem waitReset_signal (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    signalPair (waitWidthReset hwidth hle l r) = signalPair (l, r) := by
  unfold waitWidthReset
  repeat (first | rfl | split)


private theorem waitFinish_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AgentState ψ) :
    signalPair (waitWidthFinish hψ hwidth hle κ l r) = signalPair (l, r) := by
  unfold waitWidthFinish
  split <;> dsimp only <;> split <;> rfl


/-- The new inserted stage changes only carry/reset; the surrounding WAIT
clock/control work cannot change leader/shield/bullet/signal_B. -/
theorem waitWidthEntry_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AgentState ψ) :
    signalPair (waitWidthEntry hψ hwidth hle κ l r) = signalPair (l, r) := by
  unfold waitWidthEntry
  dsimp only
  rw [waitFinish_signal, waitReset_signal, waitCarry_signal,
    terminalClear_signal, waitPrep_signal]


private theorem genStart_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genSigSaturatedStart hψ l r) = signalPair (l, r) := by
  unfold genSigSaturatedStart
  split <;> dsimp only <;> split <;> rfl


private theorem genEmit_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genCleanEmit hψ l r) = signalPair (l, r) := by
  unfold genCleanEmit
  repeat (first | rfl | split)


private theorem genPropagate_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genCleanPropagate hψ l r) = signalPair (l, r) := by
  unfold genCleanPropagate
  repeat (first | rfl | split)


private theorem genFinish_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genSigSaturatedFinish hψ l r) = signalPair (l, r) := by
  unfold genSigSaturatedFinish
  repeat (first | rfl | split)


private theorem genAfter_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genCleanAfterWait hψ l r) = signalPair (l, r) := by
  unfold genCleanAfterWait
  dsimp only
  rw [genFinish_signal, genPropagate_signal, genEmit_signal, genStart_signal]


private theorem genEntry_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AgentState ψ) :
    signalPair (genCleanEntryWidth hψ hwidth hle κ l r) = signalPair (l, r) := by
  unfold genCleanEntryWidth
  dsimp only
  rw [genAfter_signal, waitWidthEntry_signal]


private theorem generation_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authSignalPair (generationBeforeMoveEntryWidth hψ hwidth hle κ l r) =
      authSignalPair (authorizedPPsiLeaderResetProbeWall hψ l r) := by
  let q0 := authorizedPPsiLeaderResetProbeWall hψ l r
  let q1 := authorizedGenCleanEntryWidth hψ hwidth hle κ q0.1 q0.2
  let q2 := authorizedCleanSig hψ q1.1 q1.2
  have hg : authSignalPair q1 = authSignalPair q0 := by
    change signalPair (genCleanEntryWidth hψ hwidth hle κ q0.1.core q0.2.core) =
      signalPair (q0.1.core, q0.2.core)
    exact genEntry_signal hψ hwidth hle κ q0.1.core q0.2.core
  unfold generationBeforeMoveEntryWidth
  exact (eliminate_signal hψ q2.1 q2.2).trans
    ((clean_signal hψ q1.1 q1.2).trans hg)


private theorem doneBefore_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authSignalPair (doneBeforeCheckEntryWidth hψ hwidth hle κ l r) =
      authSignalPair (authorizedPPsiLeaderResetProbeWall hψ l r) := by
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
  let q := authorizedDoneMove hψ b.1 b.2
  unfold doneBeforeCheckEntryWidth
  exact (authSignalPair_of_peace
      (sanitizePreCheckResetWall_peaceViewPair hψ q)).trans
    ((authorizedDoneMove_signal hψ b.1 b.2).trans
      (generation_signal hψ hwidth hle κ l r))


private theorem doneBefore_bridge (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authSignalPair (doneBeforeCheckEntryWidth hψ hwidth hle κ l r) =
      authSignalPair (BirthGenerationDone.doneBeforeCheck hψ κ l r) :=
  (doneBefore_signal hψ hwidth hle κ l r).trans
    (K2BirthDispatcherDone.doneBeforeCheck_signal hψ κ l r).symm


private theorem authSignalPair_leaders_eq
    {q p : AuthorizedAgentState ψ × AuthorizedAgentState ψ}
    (h : authSignalPair q = authSignalPair p) :
    q.1.core.leader = p.1.core.leader ∧
      q.2.core.leader = p.2.core.leader := by
  have hL := congrArg
    (fun z : AgentState 1 × AgentState 1 => z.1.leader) h
  have hR := congrArg
    (fun z : AgentState 1 × AgentState 1 => z.2.leader) h
  change q.1.core.leader = p.1.core.leader at hL
  change q.2.core.leader = p.2.core.leader at hR
  exact ⟨hL, hR⟩


private theorem doneBefore_bullets (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (doneBeforeCheckEntryWidth hψ hwidth hle κ l r) =
      authorizedBulletFieldPair (l, r) :=
  (authBullets_of_signal (doneBefore_bridge hψ hwidth hle κ l r)).trans
    (K2BirthDispatcherDone.doneBeforeCheck_bullets hψ κ l r)


private theorem doneBefore_leaders (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true →
      (doneBeforeCheckEntryWidth hψ hwidth hle κ l r).1.core.leader = true) ∧
    (r.core.leader = true →
      (doneBeforeCheckEntryWidth hψ hwidth hle κ l r).2.core.leader = true) := by
  have hs := doneBefore_bridge hψ hwidth hle κ l r
  have ho := K2BirthDispatcherDone.doneBeforeCheck_leaders hψ κ l r
  generalize doneBeforeCheckEntryWidth hψ hwidth hle κ l r = s at hs ⊢
  generalize BirthGenerationDone.doneBeforeCheck hψ κ l r = o at hs ho
  have hso := authSignalPair_leaders_eq hs
  exact ⟨fun hl => hso.1.trans (ho.1 hl),
    fun hr => hso.2.trans (ho.2 hr)⟩


private theorem through_bullets (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (doneThroughCheckEntryWidth hψ hwidth hle κ l r) =
      authorizedBulletFieldPair (l, r) := by
  unfold doneThroughCheckEntryWidth
  dsimp only
  exact (preserveDoneCheck_bullets hψ _ _).trans
    (doneBefore_bullets hψ hwidth hle κ l r)


private theorem through_leaders (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true →
      (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1.core.leader = true) ∧
    (r.core.leader = true →
      (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core.leader = true) := by
  have hb := doneBefore_leaders hψ hwidth hle κ l r
  unfold doneThroughCheckEntryWidth
  dsimp only
  generalize doneBeforeCheckEntryWidth hψ hwidth hle κ l r = b at hb ⊢
  have hc := preserveDoneCheck_leaders hψ b.1 b.2
  exact ⟨fun hl => hc.1 (hb.1 hl),
    fun hr => hc.2 (hb.2 hr)⟩


private theorem ordinary_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authSignalPair (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r) =
      authSignalPair (doneThroughCheckEntryWidth hψ hwidth hle κ l r) := by
  unfold doneOrdinaryMetadataEntryWidth
  dsimp only
  generalize doneThroughCheckEntryWidth hψ hwidth hle κ l r = c
  have hq := afterCheckMetadataWidth_signal hψ hwidth hle c.1 c.2
  generalize afterCheckMetadataWidth hψ hwidth hle c.1 c.2 = q at hq ⊢
  exact (markBirth_signal (authBirth l r q) q).trans hq


private theorem ordinary_bullets (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r) =
      authorizedBulletFieldPair (l, r) :=
  (authBullets_of_signal (ordinary_signal hψ hwidth hle κ l r)).trans
    (through_bullets hψ hwidth hle κ l r)


private theorem ordinary_leaders (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true →
      (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r).1.core.leader = true) ∧
    (r.core.leader = true →
      (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r).2.core.leader = true) := by
  have hs := ordinary_signal hψ hwidth hle κ l r
  have hc := through_leaders hψ hwidth hle κ l r
  generalize doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r = o at hs ⊢
  generalize doneThroughCheckEntryWidth hψ hwidth hle κ l r = c at hs hc
  have hoc := authSignalPair_leaders_eq hs
  exact ⟨fun hl => hoc.1.trans (hc.1 hl),
    fun hr => hoc.2.trans (hc.2 hr)⟩


/-! ## Exact authorized and expiring metadata frames -/


theorem doneMetadataAuthorizedEntryWidth_bullets (hψ : 0 < ψ)
    (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair
        (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l r) =
      authorizedBulletFieldPair (l, r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have h0 := authBullets_of_signal (normalize_pair_signal l r)
  unfold doneMetadataAuthorizedEntryWidth
  dsimp only
  split
  · exact (authBullets_of_signal (eliminate_signal hψ l0 r0)).trans h0
  · split
    · exact h0
    · exact (ordinary_bullets hψ hwidth hle κ l0 r0).trans h0


theorem doneMetadataAuthorizedEntryWidth_leaders (hψ : 0 < ψ)
    (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true →
      (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l r).1.core.leader = true) ∧
    (r.core.leader = true →
      (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l r).2.core.leader = true) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 : l0.core.leader = l.core.leader :=
    congrArg (fun u : AgentState 1 => u.leader) (normalize_signal l)
  have hr0 : r0.core.leader = r.core.leader :=
    congrArg (fun u : AgentState 1 => u.leader) (normalize_signal r)
  unfold doneMetadataAuthorizedEntryWidth
  dsimp only
  split
  · have he := eliminate_signal hψ l0 r0
    exact ⟨fun hl => (congrArg (fun q => q.1.leader) he).trans (hl0.trans hl),
      fun hr => (congrArg (fun q => q.2.leader) he).trans (hr0.trans hr)⟩
  · split
    · exact ⟨fun hl => hl0.trans hl, fun hr => hr0.trans hr⟩
    · have he := ordinary_leaders hψ hwidth hle κ l0 r0
      exact ⟨fun hl => he.1 (hl0.trans hl), fun hr => he.2 (hr0.trans hr)⟩


theorem doneMetadataEntryWidth_observation (hψ : 0 < ψ)
    (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (observeCell (doneMetadataEntryWidth hψ hwidth hle l r).1,
      observeCell (doneMetadataEntryWidth hψ hwidth hle l r).2) =
      authSignalPair (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ
        (prepareExpiringDisposal hψ l).core.erase
        (prepareExpiringDisposal hψ r).core.erase) := by
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := doneMetadataBoundedEntryWidth hψ hwidth hle l0.core r0.core
  have he := congrArg authSignalPair
    (doneMetadataBoundedEntryWidth_erase hψ hwidth hle l0.core r0.core)
  have hx :
      (observeCell (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩),
        observeCell (deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩)) =
      (observeCell (⟨q.1, l0.stall⟩ : ExpiringAgentState ψ κ τ),
        observeCell (⟨q.2, r0.stall⟩ : ExpiringAgentState ψ κ τ)) :=
    Prod.ext (priority_expiry_observation l0 ⟨q.1, l0.stall⟩)
      (priority_expiry_observation r0 ⟨q.2, r0.stall⟩)
  unfold doneMetadataEntryWidth
  exact hx.trans he


theorem metadata_field_frame (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    putLabel (metadata hψ hwidth hle l r).1
        (doneMetadataEntryWidth hψ hwidth hle l r).1.core.core.label =
        (doneMetadataEntryWidth hψ hwidth hle l r).1 ∧
      putLabel (metadata hψ hwidth hle l r).2
        (doneMetadataEntryWidth hψ hwidth hle l r).2.core.core.label =
        (doneMetadataEntryWidth hψ hwidth hle l r).2 := by
  unfold BirthShortDoneTerminalHost.metadata
  dsimp only
  exact ⟨normalizeLeader_field_frame hψ _, normalizeLeader_field_frame hψ _⟩


theorem metadata_observation_raw (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    (observeCell (metadata hψ hwidth hle l r).1,
      observeCell (metadata hψ hwidth hle l r).2) =
    (observeCell (doneMetadataEntryWidth hψ hwidth hle l r).1,
      observeCell (doneMetadataEntryWidth hψ hwidth hle l r).2) := by
  unfold BirthShortDoneTerminalHost.metadata
  dsimp only
  rw [normalizeLeader_observation, normalizeLeader_observation]


theorem metadata_existing_leaders (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    (l.core.core.leader = true →
      (metadata hψ hwidth hle l r).1.core.core.leader = true) ∧
    (r.core.core.leader = true →
      (metadata hψ hwidth hle l r).2.core.core.leader = true) := by
  have hs := doneMetadataAuthorizedEntryWidth_leaders hψ hwidth hle κ
    (prepareExpiringDisposal hψ l).core.erase
    (prepareExpiringDisposal hψ r).core.erase
  have he := (metadata_observation_raw hψ hwidth hle l r).trans
    (doneMetadataEntryWidth_observation hψ hwidth hle l r)
  have hl := congrArg AgentState.leader (prepareExpiring_signal hψ l)
  have hr := congrArg AgentState.leader (prepareExpiring_signal hψ r)
  exact ⟨fun h => (congrArg (fun q => q.1.leader) he).trans (hs.1 (hl.trans h)),
    fun h => (congrArg (fun q => q.2.leader) he).trans (hs.2 (hr.trans h))⟩


/-- Parameter-free exact projection of shield/bullet/signal_B. -/
def bulletView {m : Nat} (u : AgentState m) : Bool × Fin 3 × Fin 2 :=
  (u.shield, u.bullet, u.signal_B)


def expiringBulletPair
    (q : ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ) :
    (Bool × Fin 3 × Fin 2) × (Bool × Fin 3 × Fin 2) :=
  (bulletView q.1.core.core.erase, bulletView q.2.core.core.erase)


private def signalBulletPair (q : AgentState 1 × AgentState 1) :=
  (bulletView q.1, bulletView q.2)


private def authBulletPair
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :=
  (bulletView q.1.core, bulletView q.2.core)


private theorem authBulletPair_of_fields
    {q p : AuthorizedAgentState ψ × AuthorizedAgentState ψ}
    (h : authorizedBulletFieldPair q = authorizedBulletFieldPair p) :
    authBulletPair q = authBulletPair p := by
  simpa [authBulletPair, bulletView, authorizedBulletFieldPair,
    bulletFieldPair, BulletFields.ofState] using
    congrArg (fun z : BulletFields ψ × BulletFields ψ =>
      ((z.1.shield, z.1.bullet, z.1.signal_B),
        (z.2.shield, z.2.bullet, z.2.signal_B))) h


private theorem authBulletPair_of_expiring_views
    (l0 r0 l r : ExpiringAgentState ψ κ τ)
    (hL : bulletView l0.core.core.erase = bulletView l.core.core.erase)
    (hR : bulletView r0.core.core.erase = bulletView r.core.core.erase) :
    authBulletPair (l0.core.erase, r0.core.erase) =
      expiringBulletPair (l, r) := by
  unfold authBulletPair expiringBulletPair
  exact Prod.ext hL hR


/-- Exact physical shield/bullet/signal_B frame after expiry and normalization. -/
theorem metadata_bullets (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    expiringBulletPair (metadata hψ hwidth hle l r) =
      expiringBulletPair (l, r) := by
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  have he := (metadata_observation_raw hψ hwidth hle l r).trans
    (doneMetadataEntryWidth_observation hψ hwidth hle l r)
  have heB : expiringBulletPair (metadata hψ hwidth hle l r) =
      authBulletPair (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ
        l0.core.erase r0.core.erase) := by
    simpa [expiringBulletPair, authBulletPair, signalBulletPair, bulletView,
      ExpiringK2Projection.observeCell, authSignalPair, signalPair,
      K2OutputSafety.signalView, PeaceView.toState] using congrArg signalBulletPair he
  have hb := authBulletPair_of_fields
    (doneMetadataAuthorizedEntryWidth_bullets hψ hwidth hle κ
      l0.core.erase r0.core.erase)
  have hpL : bulletView l0.core.core.erase = bulletView l.core.core.erase := by
    simpa [bulletView, ExpiringK2Projection.observeCell, K2OutputSafety.signalView, PeaceView.toState]
      using congrArg (fun u : AgentState 1 => bulletView u)
        (prepareExpiring_signal hψ l)
  have hpR : bulletView r0.core.core.erase = bulletView r.core.core.erase := by
    simpa [bulletView, ExpiringK2Projection.observeCell, K2OutputSafety.signalView, PeaceView.toState]
      using congrArg (fun u : AgentState 1 => bulletView u)
        (prepareExpiring_signal hψ r)
  have hp : authBulletPair (l0.core.erase, r0.core.erase) =
      expiringBulletPair (l, r) :=
    authBulletPair_of_expiring_views l0 r0 l r hpL hpR
  exact heB.trans (hb.trans hp)


/-! ## Exactly two expiry calls, then the actual finite protocol -/


private theorem nonK2_stall_eq
    {a b : ExpiringAgentState ψ κ τ}
    (h : nonK2 a = nonK2 b) : a.stall = b.stall := by
  have hs := congrArg ExpiringAgentState.stall h
  change a.stall = b.stall at hs
  exact hs


private theorem normalizeLeader_stall (hψ : 0 < ψ)
    (q : ExpiringAgentState ψ κ τ) :
    (normalizeLeader hψ q).stall = q.stall := by
  unfold normalizeLeader
  split <;> rfl


theorem row_timers_once (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    let l0 := prepareExpiringDisposal hψ l
    let r0 := prepareExpiringDisposal hψ r
    let q := doneMetadataBoundedEntryWidth hψ hwidth hle l0.core r0.core
    (row hψ hwidth hle l r).1.stall =
        (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩).stall ∧
      (row hψ hwidth hle l r).2.stall =
        (deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩).stall := by
  dsimp only
  unfold BirthShortDoneTerminalHost.row
  dsimp only
  unfold BirthShortDoneTerminalHost.metadata
  dsimp only
  unfold BirthShortDoneTerminalHost.doneMetadataEntryWidth
  dsimp only
  generalize prepareExpiringDisposal hψ l = l0
  generalize prepareExpiringDisposal hψ r = r0
  generalize doneMetadataBoundedEntryWidth hψ hwidth hle l0.core r0.core = q0
  generalize deletionPriorityExpireOne τ l0 ⟨q0.1, l0.stall⟩ = eL
  generalize deletionPriorityExpireOne τ r0 ⟨q0.2, r0.stall⟩ = eR
  have hf := K2BirthDispatcher.finalPhysical_nonK2 hψ l r
    (normalizeLeader hψ eL) (normalizeLeader hψ eR)
  have hL := nonK2_stall_eq hf.1
  have hR := nonK2_stall_eq hf.2
  exact ⟨hL.trans (normalizeLeader_stall hψ eL),
    hR.trans (normalizeLeader_stall hψ eR)⟩


def protocol (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ τ : Nat) : PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := Bool
  transition := BirthShortDoneTerminalHost.row hψ hwidth hle
  output := fun q => q.core.core.leader


def step (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (e : Fin n) : Fin n → ExpiringAgentState ψ κ τ :=
  (protocol hψ hwidth hle κ τ).step ring C e


def stateCertificate (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ τ : Nat) :
    ExhaustiveList (protocol hψ hwidth hle κ τ).Q :=
  K2BirthDispatcher.stateCertificate hψ κ τ


theorem finite_state_bound (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ τ : Nat) :
    Function.Injective (stateCertificate hψ hwidth hle κ τ).decode ∧
    Function.Surjective (stateCertificate hψ hwidth hle κ τ).decode ∧
    (stateCertificate hψ hwidth hle κ τ).values.length ≤
      ExpiringK2Projection.localBound ψ κ τ :=
  K2BirthDispatcher.finite_state_bound hψ κ τ


theorem step_other (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    step hψ hwidth hle ring C e i = C i := by
  simp only [step, PopulationProtocol.step, protocol, if_neg hi, if_neg hj]


/-- On an actual self-edge, PopulationProtocol.step keeps its left-output
priority; there is no responder overwrite and no second host-row call. -/
theorem step_alias (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (ha : ring.rightNeighbor e = e) :
    step hψ hwidth hle ring C e e =
      (BirthShortDoneTerminalHost.row hψ hwidth hle (C e) (C e)).1 := by
  simp only [step, PopulationProtocol.step, protocol, ha, if_true]


end BirthShortDoneTerminalConsumer

#print axioms BirthShortDoneTerminalConsumer.waitWidthEntry_signal
#print axioms BirthShortDoneTerminalConsumer.doneMetadataAuthorizedEntryWidth_bullets
#print axioms BirthShortDoneTerminalConsumer.doneMetadataAuthorizedEntryWidth_leaders
#print axioms BirthShortDoneTerminalConsumer.doneMetadataEntryWidth_observation
#print axioms BirthShortDoneTerminalConsumer.metadata_field_frame
#print axioms BirthShortDoneTerminalConsumer.metadata_observation_raw
#print axioms BirthShortDoneTerminalConsumer.metadata_existing_leaders
#print axioms BirthShortDoneTerminalConsumer.metadata_bullets
#print axioms BirthShortDoneTerminalConsumer.row_timers_once
#print axioms BirthShortDoneTerminalConsumer.finite_state_bound
#print axioms BirthShortDoneTerminalConsumer.step_other
#print axioms BirthShortDoneTerminalConsumer.step_alias
