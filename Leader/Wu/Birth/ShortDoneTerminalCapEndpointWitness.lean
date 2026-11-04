import Leader.Wu.Birth.ShortDoneTerminalPassivePreCap
import Leader.Wu.Birth.ShortDoneTerminalHost

/-!
# Width-two first-cap endpoint audit for the repaired TerminalHost

This is a finite endpoint witness only.  It does not assert inclusive passive
closure, a stopped-word law, or equality of the full host with the WAIT row.
-/

namespace BirthShortDoneTerminalCapEndpointAudit

open PPLL PPLLRepair PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open BirthGenerationControlRepair BirthWaitPassive BirthShortWait
open BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR1

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

private theorem h2 : 0 < 2 := by decide
private theorem hle2 : 2 ≤ 2 := by decide

/-- Exact passive label-zero input.  `h=true` is the clock bit that launches
    the cap-producing carry; every other physical field is fixed by `cell`. -/
private def a : Registers 2 where
  label := 0
  h := true
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

/-- Exact passive width terminal. -/
private def b : Registers 2 where
  label := 1
  h := true
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

/-- Exact finite/expiry wrappers whose raw states are literally the two cells. -/
private def L : ExpiringAgentState 2 1 0 :=
  ⟨⟨BoundedAgentState.ofDomain (cell a) (by simp [AgentState.inProtocolDomain, cell, a]), false⟩, 0⟩

private def R : ExpiringAgentState 2 1 0 :=
  ⟨⟨BoundedAgentState.ofDomain (cell b) (by simp [AgentState.inProtocolDomain, cell, b]), false⟩, 0⟩

private def w : AgentState 2 × AgentState 2 :=
  waitWidthEntry h2 h2 hle2 1 (raw L) (raw R)

private def s : AgentState 2 × AgentState 2 :=
  genSigSaturatedStart h2 w.1 w.2

private def g : AgentState 2 × AgentState 2 :=
  genCleanAfterWait h2 w.1 w.2

private def q : ExpiringAgentState 2 1 0 × ExpiringAgentState 2 1 0 :=
  BirthShortDoneTerminalHost.row h2 h2 hle2 L R

/-- Full input scope: exact passive cells, WAIT armed, with the real cyclic
    labels `0 -> 1`. -/
theorem input_scope :
    raw L = cell a ∧ raw R = cell b ∧
      Passive (raw L) ∧ Passive (raw R) ∧
      (raw R).label =
        ⟨((raw L).label.val + 1) % 2, Nat.mod_lt _ h2⟩ := by
  unfold Passive Metadata InertWriter
  decide

/-- This interaction itself produces the first cap.  Finish releases label
    zero, so the pre-cap hypothesis is correctly false at the endpoint. -/
theorem cap_wait_endpoint :
    (raw R).count = 0 ∧ w.2.count = 1 ∧
      w.1.wait = false ∧ w.2.wait = true ∧
      ¬ PreCapEntry2 h2 hle2 1 (raw L) (raw R) := by
  unfold PreCapEntry2
  decide

/-- GEN starts in the cap-producing row.  The unchanged GEN tail then reaches
    its recognizable departing state while retaining the terminal cap count. -/
theorem cap_gen_endpoint :
    s.1.state = .produce ∧ s.2.state = .produce ∧
      g.1.state = .depart ∧ g.2.state = .depart ∧
      g.1.path = .some 0 0 ∧ g.2.path = .some 1 0 ∧
      g.2.count = 1 := by
  decide

set_option maxRecDepth 32768 in
/-- Endpoint witness for the *actual repaired TerminalHost*.  The final
    responder retains the cap count.  No passive/full-WAIT projection is
    asserted, because GEN has already started in this row. -/
theorem actual_terminal_host_cap :
    (raw q.2).count = 1 := by
  decide

end BirthShortDoneTerminalCapEndpointAudit

#print axioms BirthShortDoneTerminalCapEndpointAudit.input_scope
#print axioms BirthShortDoneTerminalCapEndpointAudit.cap_wait_endpoint
#print axioms BirthShortDoneTerminalCapEndpointAudit.cap_gen_endpoint
#print axioms BirthShortDoneTerminalCapEndpointAudit.actual_terminal_host_cap
