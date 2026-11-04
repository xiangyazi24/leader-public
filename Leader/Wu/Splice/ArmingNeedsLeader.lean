import Leader.Wu.Splice.ProvenanceTicketTable
set_option autoImplicit false

/-! The arming rows need a physical leader; on a leaderless served pair they cannot fire. -/

namespace B9SpliceV10cLeaderlessExclusion
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
variable {psi width kappa tau : Nat}

theorem leftDeletionCandidate_needs_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : SpliceAgentState psi kappa tau) (hl : l.base.core.core.leader = false) :
    ¬ LeftDeletionCandidate hpsi hwidth hle l r := by
  intro h
  have h1 := h.1
  rw [hl] at h1
  cases h1

theorem armA_needs_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) (hl : l.splice.base.core.core.leader = false) :
    ¬ ArmAGuard hpsi hwidth hle l r :=
  fun h => leftDeletionCandidate_needs_leader hpsi hwidth hle l.splice r.splice hl h.2.2.2.2

theorem armB_needs_leader
    (l r : R1AgentState psi kappa tau) (hr : r.splice.base.core.core.leader = false) :
    ¬ ArmBGuard l r := by
  intro h
  have h1 := h.2.2.2.2
  rw [hr] at h1
  cases h1

theorem delete_needs_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) (hl : l.splice.base.core.core.leader = false) :
    ¬ DeleteGuard hpsi hwidth hle l r :=
  fun h => leftDeletionCandidate_needs_leader hpsi hwidth hle l.splice r.splice hl h.2.2.2.2

theorem pendingHold_needs_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) (hl : l.splice.base.core.core.leader = false) :
    ¬ PendingHoldGuard hpsi hwidth hle l r :=
  fun h => leftDeletionCandidate_needs_leader hpsi hwidth hle l.splice r.splice hl h.2.2.2.2

theorem pendingAbort_needs_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) (hl : l.splice.base.core.core.leader = false) :
    ¬ PendingAbortGuard hpsi hwidth hle l r := by
  intro h
  have h1 := h.2.2.2.2.1
  rw [hl] at h1
  cases h1

end B9SpliceV10cLeaderlessExclusion
