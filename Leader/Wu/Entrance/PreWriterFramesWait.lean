import Leader.Wu.Entrance.WriteSeqGenerateDisabled

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6PreWriterFramesA

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLWallSweepRepair PPLLWallSweepFinite
open BirthGenerationControlRepair BirthShortWait
  BirthShortWaitTerminalEntryRepair BirthShortDoneTerminalEntryCut

variable {ψ κ width : Nat}

structure PreWriterFrameView where
  leftLeader : Bool
  rightBit : Bool
  rightPath3 : Option Path3Info
  rightWrite : WriteAction
  rightWriteState : WriteState

def rawPreWriterFrame
    (q : AgentState ψ × AgentState ψ) : PreWriterFrameView :=
  ⟨q.1.leader, q.2.bit, q.2.path3, q.2.write, q.2.write_state⟩

/-- Left leader and the four responder fields needed at Algorithm 18. -/
def PreWriterFrame
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    PreWriterFrameView :=
  rawPreWriterFrame (q.1.core, q.2.core)

/-- Authorization reconciliation changes permits, not the raw frame. -/
theorem authorizedReconcile_frame
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, rawPreWriterFrame (f a b) = rawPreWriterFrame (a, b))
    (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (authorizedReconcile f l r) = PreWriterFrame (l, r) := by
  unfold PreWriterFrame authorizedReconcile
  dsimp only
  exact hf l.core r.core

private theorem rawPPrime_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (pPsiLeaderResetProbeWall hψ l r) =
      rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame pPsiLeaderResetProbeWall pPsi
  dsimp only
  repeat (first | rfl | split)

/-- P-prime may create a responder leader, but frames this asymmetric view. -/
theorem pprime_frame (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (authorizedPPsiLeaderResetProbeWall hψ l r) =
      PreWriterFrame (l, r) := by
  unfold PreWriterFrame
  exact (congrArg rawPreWriterFrame
      (authorizedPPsiLeaderResetProbeWall_core hψ l r)).trans
    (rawPPrime_frame hψ l.core r.core)

private theorem waitPrepare_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (waitSaturatedPrepare hψ l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame waitSaturatedPrepare
  dsimp only
  repeat (first | rfl | split)

private theorem waitClear_frame (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    rawPreWriterFrame (terminalInactiveClear hwidth hle l r) =
      rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame terminalInactiveClear
  repeat (first | rfl | split)

private theorem waitCarry_frame (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AgentState ψ) :
    rawPreWriterFrame (waitWidthCarry hwidth hle κ l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame waitWidthCarry
  repeat (first | rfl | split)

private theorem waitReset_frame (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    rawPreWriterFrame (waitWidthReset hwidth hle l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame waitWidthReset
  repeat (first | rfl | split)

private theorem waitFinish_frame (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AgentState ψ) :
    rawPreWriterFrame (waitWidthFinish hψ hwidth hle κ l r) =
      rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame waitWidthFinish
  dsimp only
  repeat (first | rfl | split)

/-- Corrected shortened WAIT frames the five B6 pre-writer fields. -/
theorem waitEntry_frame (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AgentState ψ) :
    rawPreWriterFrame (waitWidthEntry hψ hwidth hle κ l r) =
      rawPreWriterFrame (l, r) := by
  let p := waitSaturatedPrepare hψ l r
  let e := terminalInactiveClear hwidth hle p.1 p.2
  let c := waitWidthCarry hwidth hle κ e.1 e.2
  let t := waitWidthReset hwidth hle c.1 c.2
  change rawPreWriterFrame (waitWidthFinish hψ hwidth hle κ t.1 t.2) = _
  exact (waitFinish_frame hψ hwidth hle κ t.1 t.2).trans
    ((waitReset_frame hwidth hle c.1 c.2).trans
      ((waitCarry_frame hwidth hle κ e.1 e.2).trans
        ((waitClear_frame hwidth hle p.1 p.2).trans
          (waitPrepare_frame hψ l r))))

private theorem genStart_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (genSigSaturatedStart hψ l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame genSigSaturatedStart
  dsimp only
  repeat (first | rfl | split)

private theorem genEmit_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (genCleanEmit hψ l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame genCleanEmit
  dsimp only
  repeat (first | rfl | split)

private theorem genPropagate_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (genCleanPropagate hψ l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame genCleanPropagate
  repeat (first | rfl | split)

private theorem genFinish_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (genSigSaturatedFinish hψ l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame genSigSaturatedFinish
  dsimp only
  repeat (first | rfl | split)

/-- The post-WAIT GENSIG tail frames the same five fields. -/
theorem genAfterWait_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (genCleanAfterWait hψ l r) = rawPreWriterFrame (l, r) := by
  let s := genSigSaturatedStart hψ l r
  let e := genCleanEmit hψ s.1 s.2
  let p := genCleanPropagate hψ e.1 e.2
  change rawPreWriterFrame (genSigSaturatedFinish hψ p.1 p.2) = _
  exact (genFinish_frame hψ p.1 p.2).trans
    ((genPropagate_frame hψ e.1 e.2).trans
      ((genEmit_frame hψ s.1 s.2).trans (genStart_frame hψ l r)))

private theorem genEntryRaw_frame (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AgentState ψ) :
    rawPreWriterFrame (genCleanEntryWidth hψ hwidth hle κ l r) =
      rawPreWriterFrame (l, r) := by
  let w := waitWidthEntry hψ hwidth hle κ l r
  change rawPreWriterFrame (genCleanAfterWait hψ w.1 w.2) = _
  exact (genAfterWait_frame hψ w.1 w.2).trans
    (waitEntry_frame hψ hwidth hle κ l r)

/-- The actual authorized corrected GEN call frames the B6 pre-writer view. -/
theorem genEntry_frame (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (authorizedGenCleanEntryWidth hψ hwidth hle κ l r) =
      PreWriterFrame (l, r) := by
  unfold authorizedGenCleanEntryWidth
  exact authorizedReconcile_frame _ (genEntryRaw_frame hψ hwidth hle κ) l r

end B6PreWriterFramesA

#print axioms B6PreWriterFramesA.pprime_frame
#print axioms B6PreWriterFramesA.waitEntry_frame
#print axioms B6PreWriterFramesA.genAfterWait_frame
#print axioms B6PreWriterFramesA.genEntry_frame
