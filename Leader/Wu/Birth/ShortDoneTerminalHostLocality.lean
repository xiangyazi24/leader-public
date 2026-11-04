import Leader.Wu.Birth.ShortDoneTerminalHost
import Leader.Wu.Birth.ShortDoneDispatcher
import Leader.Wu.Birth.WaitPassiveRows

namespace BirthShortDoneTerminalHostLocalityQ10325

open PPLL PPLLRepair PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite
open BirthSigMoveDisposalRepair BirthWaitPassive BirthShortWait
  BirthShortWaitTerminalEntryRepair

set_option autoImplicit false
set_option pp.structureInstances false

/-- Physical width-two terminal, with only the two repaired WAIT bits dirty. -/
def dirtyA4 : Registers 4 :=
  ⟨(1 : Fin 4), false, true, true, 0, true, false, false, .none⟩

/-- Real cyclic successor outside the width-two active prefix. -/
def outsideB4 : Registers 4 :=
  ⟨(2 : Fin 4), false, false, false, 0, true, false, false, .none⟩

theorem dirtyA4_domain : (cell dirtyA4).inProtocolDomain 0 := by
  simp [dirtyA4, cell, AgentState.inProtocolDomain]

theorem outsideB4_domain : (cell outsideB4).inProtocolDomain 0 := by
  simp [outsideB4, cell, AgentState.inProtocolDomain]

theorem adjacent4 :
    outsideB4.label =
      ⟨(dirtyA4.label.val + 1) % 4, by decide⟩ := by
  decide

def dirtyL4 : ExpiringAgentState 4 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain (cell dirtyA4) dirtyA4_domain, false⟩, 0⟩

def outsideR4 : ExpiringAgentState 4 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain (cell outsideB4) outsideB4_domain, false⟩, 0⟩

/-- These are genuine bounded inputs whose erasures are exactly the two cells. -/
theorem input_erasures4 :
    dirtyL4.core.core.erase = cell dirtyA4 ∧
      outsideR4.core.core.erase = cell outsideB4 := by
  simp [dirtyL4, outsideR4, BoundedAgentState.erase_ofDomain]

/-- The actual ordinary metadata path is open: disposal preparation and
normalization do not divert either endpoint into deletion priority. -/
theorem ordinary_branch_open4 :
    let lp := prepareExpiringDisposal (by decide : 0 < 4) dirtyL4
    let rp := prepareExpiringDisposal (by decide : 0 < 4) outsideR4
    let la := normalizeDeletion lp.core.erase
    let ra := normalizeDeletion rp.core.erase
    deletionActive la = false ∧ deletionActive ra = false := by
  decide

/-- Literal physical state seen by the inserted clear, including the actual
finite preparation/disposal, deletion normalization, full-psi ruler, and WAIT
prepare stages. -/
def actualPrepared4 : AgentState 4 × AgentState 4 :=
  let lp := prepareExpiringDisposal (by decide : 0 < 4) dirtyL4
  let rp := prepareExpiringDisposal (by decide : 0 < 4) outsideR4
  let la := normalizeDeletion lp.core.erase
  let ra := normalizeDeletion rp.core.erase
  let q0 := authorizedPPsiLeaderResetProbeWall
    (by decide : 0 < 4) la ra
  waitSaturatedPrepare (by decide : 0 < 4) q0.1.core q0.2.core

/-- The new guard is genuinely true on the actual prepared host input.  The
left dirty fields have not already disappeared before the new stage. -/
theorem actual_prepared_guard4 :
    actualPrepared4.1.reset = true ∧
      actualPrepared4.1.carry = true ∧
      actualPrepared4.1.label =
        widthTerminal (psi := 4) (width := 2) (by decide) (by decide) ∧
      ¬ activePair 2 actualPrepared4.1 actualPrepared4.2 := by
  decide

/-- Hence the inserted stage takes its new branch exactly. -/
theorem clear_fires4 :
    terminalInactiveClear (psi := 4) (width := 2)
        (by decide) (by decide) actualPrepared4.1 actualPrepared4.2 =
      ({ actualPrepared4.1 with carry := false, reset := false },
       actualPrepared4.2) := by
  exact terminalInactiveClear_exact (by decide) (by decide)
    actualPrepared4.1 actualPrepared4.2
    actual_prepared_guard4.2.2.1 actual_prepared_guard4.2.2.2

/-- Earliest exact semantic split, before asking anything of the later host. -/
theorem wait_stage_split4 :
    let fixed := waitWidthEntry (psi := 4) (width := 2)
      (by decide) (by decide) (by decide) 0 (cell dirtyA4) (cell outsideB4)
    let old := BirthShortWait.waitWidth (psi := 4) (width := 2)
      (by decide) (by decide) (by decide) 0 (cell dirtyA4) (cell outsideB4)
    fixed.1.reset = false ∧ fixed.1.carry = false ∧
      old.1.reset = true ∧ old.1.carry = true := by
  decide

set_option maxRecDepth 32768 in
/-- Crucially, the complete repaired physical host retains the cleanup. -/
theorem repaired_row_clear4 :
    let q := BirthShortDoneTerminalHost.row
      (ψ := 4) (width := 2) (κ := 0) (τ := 0)
      (by decide) (by decide) (by decide) dirtyL4 outsideR4
    q.1.core.core.erase.reset = false ∧
      q.1.core.core.erase.carry = false := by
  decide

set_option maxRecDepth 32768 in
/-- The old short Dispatcher on the identical finite input retains both dirty
WAIT fields all the way through its own literal physical tail. -/
theorem old_row_dirty4 :
    let q := BirthShortDoneDispatcher.row
      (ψ := 4) (width := 2) (κ := 0) (τ := 0)
      (by decide) (by decide) (by decide) dirtyL4 outsideR4
    q.1.core.core.erase.reset = true ∧
      q.1.core.core.erase.carry = true := by
  decide

/-- Whole-row inequality, witnessed by the actual final physical reset field. -/
theorem rows_ne4 :
    BirthShortDoneTerminalHost.row
        (ψ := 4) (width := 2) (κ := 0) (τ := 0)
        (by decide) (by decide) (by decide) dirtyL4 outsideR4 ≠
      BirthShortDoneDispatcher.row
        (ψ := 4) (width := 2) (κ := 0) (τ := 0)
        (by decide) (by decide) (by decide) dirtyL4 outsideR4 := by
  intro h
  have hr := congrArg
    (fun q => q.1.core.core.erase.reset) h
  have hn := repaired_row_clear4
  have ho := old_row_dirty4
  simpa [hn.1, ho.1] using hr

#print axioms BirthShortDoneTerminalHostLocalityQ10325.actual_prepared_guard4
#print axioms BirthShortDoneTerminalHostLocalityQ10325.wait_stage_split4
#print axioms BirthShortDoneTerminalHostLocalityQ10325.repaired_row_clear4
#print axioms BirthShortDoneTerminalHostLocalityQ10325.old_row_dirty4
#print axioms BirthShortDoneTerminalHostLocalityQ10325.rows_ne4

end BirthShortDoneTerminalHostLocalityQ10325
