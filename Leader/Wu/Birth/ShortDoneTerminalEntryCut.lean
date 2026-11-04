import Leader.Wu.Birth.ShortDoneCuts
import Leader.Wu.Birth.ShortWaitTerminalEntryRepair

/-!
# Insert terminal-entry WAIT at the actual GEN cut

The full-psi ruler runs first.  Only the following GEN call is replaced by
`waitWidthEntry`; the raw GEN tail, CLEAN, ELIMINATE, DONE movement,
pre-CHECK sanitize and CHECK order are unchanged.
-/

namespace BirthShortDoneTerminalEntryCut

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthConditionTwoFrames PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol PPLLNoCheckBirthLeaderFrames
  BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortWaitDomainWitness BirthShortWaitTerminalEntryRepair
  PPLLTerminalEqualSupportRepair BirthSigMoveDisposalRepair

open K2BirthDispatcher K2BirthDispatcherDone BirthShortDoneCuts

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ : Nat}

/-- Corrected shortened WAIT at the exact raw GEN position; every later raw
GEN stage is the existing `genCleanAfterWait`. -/
def genCleanEntryWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := waitWidthEntry hψ hwidth hle κ l r
  genCleanAfterWait hψ q.1 q.2

/-- Numeric closure is exactly corrected WAIT closure followed by the already
checked full-psi GEN tail closure. -/
theorem genCleanEntryWidth_inProtocolDomain
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ)
    (hl : l.inProtocolDomain κ) (hr : r.inProtocolDomain κ) :
    let q := genCleanEntryWidth hψ hwidth hle κ l r
    q.1.inProtocolDomain κ ∧ q.2.inProtocolDomain κ := by
  let w := waitWidthEntry hψ hwidth hle κ l r
  have hw := waitWidthEntry_inProtocolDomain
    hψ hwidth hle l r hl hr
  exact BirthShortWaitDomainWitness.genCleanAfterWait_inProtocolDomain
    hψ w.1 w.2 hw.1 hw.2

/-- At full width this is the existing raw `genClean`, field-for-field. -/
theorem genCleanEntryWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AgentState ψ) :
    genCleanEntryWidth hψ hψ (Nat.le_refl ψ) κ l r =
      genClean hψ κ l r := by
  unfold genCleanEntryWidth genClean
  dsimp only
  rw [waitWidthEntry_full hψ κ l r]

/-- Same authorization/reconciliation cut as `authorizedGenClean`; only its
raw function argument is changed. -/
def authorizedGenCleanEntryWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  authorizedReconcile (genCleanEntryWidth hψ hwidth hle κ) l r

theorem authorizedGenCleanEntryWidth_domain
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (authorizedGenCleanEntryWidth hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (authorizedGenCleanEntryWidth hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  exact authorizedReconcile_inProtocolDomain
    (genCleanEntryWidth hψ hwidth hle κ) l r
    (genCleanEntryWidth_inProtocolDomain hψ hwidth hle l.core r.core hl hr)

theorem authorizedGenCleanEntryWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authorizedGenCleanEntryWidth hψ hψ (Nat.le_refl ψ) κ l r =
      authorizedGenClean hψ κ l r := by
  unfold authorizedGenCleanEntryWidth authorizedGenClean
  have hfun :
      genCleanEntryWidth (ψ := ψ) (width := ψ)
          hψ hψ (Nat.le_refl ψ) κ =
        genClean hψ κ := by
    funext a b
    exact genCleanEntryWidth_full hψ κ a b
  exact congrArg (fun f => authorizedReconcile f l r) hfun

/-- Actual placement: ruler first, corrected WAIT inside GEN second, then the
unchanged CLEAN and ELIMINATE calls. -/
def generationBeforeMoveEntryWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q0 := authorizedPPsiLeaderResetProbeWall hψ l r
  let q1 := authorizedGenCleanEntryWidth hψ hwidth hle κ q0.1 q0.2
  let q2 := authorizedCleanSig hψ q1.1 q1.2
  authorizedEliminateSig hψ q2.1 q2.2

theorem generationBeforeMoveEntryWidth_domain
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  let q0 := authorizedPPsiLeaderResetProbeWall hψ l r
  have h0 := authorizedPPsiLeaderResetProbeWall_inProtocolDomain hψ l r hl hr
  let q1 := authorizedGenCleanEntryWidth hψ hwidth hle κ q0.1 q0.2
  have h1 := authorizedGenCleanEntryWidth_domain
    hψ hwidth hle κ q0.1 q0.2 h0.1 h0.2
  let q2 := authorizedCleanSig hψ q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain (cleanSig hψ) q1.1 q1.2
    (cleanSig_inProtocolDomain hψ q1.1.core q1.2.core h1.1 h1.2)
  exact authorizedReconcile_inProtocolDomain (eliminateSig hψ) q2.1 q2.2
    (eliminateSig_inProtocolDomain hψ q2.1.core q2.2.core h2.1 h2.2)

/-- Full-width host regression through ruler/GEN/CLEAN/ELIMINATE. -/
theorem generationBeforeMoveEntryWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    generationBeforeMoveEntryWidth hψ hψ (Nat.le_refl ψ) κ l r =
      BirthGenerationControlRepair.generationBeforeMove hψ κ l r := by
  let q0 := authorizedPPsiLeaderResetProbeWall hψ l r
  let tail :
      (AuthorizedAgentState ψ × AuthorizedAgentState ψ) →
        (AuthorizedAgentState ψ × AuthorizedAgentState ψ) := fun q1 =>
    let q2 := authorizedCleanSig hψ q1.1 q1.2
    authorizedEliminateSig hψ q2.1 q2.2
  change
    tail (authorizedGenCleanEntryWidth hψ hψ (Nat.le_refl ψ) κ q0.1 q0.2) =
      tail (authorizedGenClean hψ κ q0.1 q0.2)
  exact congrArg tail
    (authorizedGenCleanEntryWidth_full hψ κ q0.1 q0.2)

attribute [local irreducible]
  generationBeforeMoveEntryWidth authorizedDoneMove
  authorizedPPsiLeaderResetProbeWall

/-- Existing DONE movement and pre-CHECK sanitize, now fed by the correctly
placed GEN cut. -/
def doneBeforeCheckEntryWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
  let q := authorizedDoneMove hψ b.1 b.2
  sanitizeAuthorizedPair hψ (preCheckResetWall q.1 q.2)

theorem doneBeforeCheckEntryWidth_domain
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (doneBeforeCheckEntryWidth hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (doneBeforeCheckEntryWidth hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
  have hb := generationBeforeMoveEntryWidth_domain
    hψ hwidth hle κ l r hl hr
  have hm := authorizedDoneMove_inProtocolDomain hψ b.1 b.2 hb.1 hb.2
  let m := authorizedDoneMove hψ b.1 b.2
  have hw := preCheckResetWall_inProtocolDomain m.1 m.2 hm.1 hm.2
  exact ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hψ _ hw.1,
    sanitizeAuthorizedTerminalEqual_inProtocolDomain hψ _ hw.2⟩

theorem doneBeforeCheckEntryWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    doneBeforeCheckEntryWidth hψ hψ (Nat.le_refl ψ) κ l r =
      BirthGenerationDone.doneBeforeCheck hψ κ l r := by
  let tail :
      (AuthorizedAgentState ψ × AuthorizedAgentState ψ) →
        (AuthorizedAgentState ψ × AuthorizedAgentState ψ) := fun b =>
    let q := authorizedDoneMove hψ b.1 b.2
    sanitizeAuthorizedPair hψ (preCheckResetWall q.1 q.2)
  change
    tail (generationBeforeMoveEntryWidth hψ hψ (Nat.le_refl ψ) κ l r) =
      tail (BirthGenerationControlRepair.generationBeforeMove hψ κ l r)
  exact congrArg tail
    (generationBeforeMoveEntryWidth_full hψ κ l r)

/-- Through-CHECK insertion.  `preserveDoneCheck` is the existing CHECK call;
no post-CHECK metadata, expiry or K2 call is duplicated here. -/
def doneThroughCheckEntryWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let b := doneBeforeCheckEntryWidth hψ hwidth hle κ l r
  preserveDoneCheck hψ b.1 b.2

theorem doneThroughCheckEntryWidth_domain
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  let b := doneBeforeCheckEntryWidth hψ hwidth hle κ l r
  have hb := doneBeforeCheckEntryWidth_domain
    hψ hwidth hle κ l r hl hr
  exact preserveDoneCheck_inProtocolDomain hψ b.1 b.2 hb.1 hb.2

/-- Full-width equality through CHECK to the existing accepted DONE stage. -/
theorem doneThroughCheckEntryWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    doneThroughCheckEntryWidth hψ hψ (Nat.le_refl ψ) κ l r =
      K2BirthDispatcherDone.doneThroughCheck hψ κ l r := by
  unfold doneThroughCheckEntryWidth K2BirthDispatcherDone.doneThroughCheck
  rw [doneBeforeCheckEntryWidth_full hψ]

#print axioms BirthShortDoneTerminalEntryCut.genCleanEntryWidth_inProtocolDomain
#print axioms BirthShortDoneTerminalEntryCut.genCleanEntryWidth_full
#print axioms BirthShortDoneTerminalEntryCut.authorizedGenCleanEntryWidth_domain
#print axioms BirthShortDoneTerminalEntryCut.authorizedGenCleanEntryWidth_full
#print axioms BirthShortDoneTerminalEntryCut.generationBeforeMoveEntryWidth_domain
#print axioms BirthShortDoneTerminalEntryCut.generationBeforeMoveEntryWidth_full
#print axioms BirthShortDoneTerminalEntryCut.doneBeforeCheckEntryWidth_domain
#print axioms BirthShortDoneTerminalEntryCut.doneBeforeCheckEntryWidth_full
#print axioms BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth_domain
#print axioms BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth_full

end BirthShortDoneTerminalEntryCut
