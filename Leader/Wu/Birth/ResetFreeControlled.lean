import Leader.Wu.Birth.CountFloorCounterexample

namespace BirthB1ResetFreeControlled

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair PPLLWallSweepRepair
open BirthShortWait

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

def rawAt (C : FC n psi kappa tau) (i : Fin n) : AgentState psi :=
  (C i).core.erase.core

/-- The physical short clock is stored at the clockwise successor of `anchor`.
A reset can reach it only through `anchor`, so these are the two sites which
must be protected by the B1/Reacquire proof invariant. -/
def trackedTerminal (ring : DirectedRing n) (anchor : Fin n) : Fin n :=
  ring.rightNeighbor anchor

/-- Boundary-level name for the only kind of current-host row which can undo
B4 progress.  A census of the host sources shows that every strict count decrease in
this host is one of the two SUPPRESS zeroing writes (`shortCountReset` or
`suppressSigTerminal`).  Keeping this tag extensional avoids adding a new
protocol branch bit merely for the proof. -/
def TrackedResetZeroingBranch
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  let D := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e
  BirthPhaseWait2BlockProgress.shortCountAt ring anchor D <
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C

/-- Proof-side protected-suffix invariant.  The two visible clauses exclude a
live reset at the tracked terminal and its immediate upstream feed.  The last
clause is the history/transition part: while the B1 target is still false, no
fresh or transported reset is allowed to enter either SUPPRESS zeroing branch.
It is deliberately a Prop, not protocol state. -/
structure ResetFreeTrackedTerminal
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop where
  upstream_free : (rawAt C anchor).reset_cmd = false
  terminal_free : (rawAt C (trackedTerminal ring anchor)).reset_cmd = false
  no_reset_zeroing :
    forall e : Fin n,
      BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring C [e] = false ->
      ¬ TrackedResetZeroingBranch hpsi h2 ring anchor C e

/-- Prefix form used by a controlled suffix.  Thus a reset is absent before
and after every selected service, rather than merely at the entrance. -/
def ResetFreeTrackedTerminalAlong
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (anchor : Fin n) :
    FC n psi kappa tau -> List (Fin n) -> Prop
  | C, [] => ResetFreeTrackedTerminal hpsi h2 kappa ring anchor C
  | C, e :: es =>
      ResetFreeTrackedTerminal hpsi h2 kappa ring anchor C ∧
      ResetFreeTrackedTerminalAlong hpsi h2 kappa ring anchor
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) es

/-! Source census for reset creation. -/

/-- Algorithm 14 cannot create a reset at `suppressSigStart` from a follower. -/
theorem suppressSigStart_follower_no_fresh_reset
    (l r : AgentState psi) (hl : l.leader = false) :
    (suppressSigStart l r).1.reset_cmd = l.reset_cmd := by
  simp [suppressSigStart, hl]

/-- Reset movement is transport only: if the upstream endpoint has no reset,
that stage is literally the identity pair. -/
theorem suppressSigMoveReset_of_upstream_free
    (l r : AgentState psi) (hl : l.reset_cmd = false) :
    suppressSigMoveReset l r = (l, r) := by
  simp [suppressSigMoveReset, hl]

/-- At the actual shortened SUPPRESS cut, a follower/reset-free pair frames
both counts.  This isolates the two downward writers without changing them. -/
theorem suppressSigResetKillWidth_count_frame_of_reset_free
    {width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi)
    (hleader : l.leader = false)
    (hlreset : l.reset_cmd = false) (hrreset : r.reset_cmd = false) :
    let q := suppressSigResetKillWidth hpsi hwidth hle l r
    q.1.count = l.count ∧ q.2.count = r.count := by
  simp [suppressSigResetKillWidth, suppressPrefix,
    suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal,
    shortCountReset, suppressSigTerminal, suppressSigEcho, suppressSigFinish,
    hleader, hlreset, hrreset]

/-- The B1/Reacquire one-step no-undo law for the unchanged executable host. -/
theorem currentStep2_reset_free_no_undo
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (anchor e : Fin n)
    (C : FC n psi kappa tau)
    (hfree : ResetFreeTrackedTerminal hpsi h2 kappa ring anchor C)
    (htarget :
      BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring C [e] = false) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <=
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) := by
  exact Nat.le_of_not_gt (hfree.no_reset_zeroing e htarget)

/-! Controlled-entrance strengthening. -/

def ResetFreeControlled
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop)
    (C : FC n psi kappa tau) : Prop :=
  Controlled C ∧ ResetFreeTrackedTerminal hpsi h2 kappa ring anchor C

/-- Same entrance target, but its controlled endpoint must now also be
reset-free at the tracked terminal/feed. -/
def ResetFreeControlledEntranceSuccess
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring C u = true ∨
    let D := BirthB1ReacquireReentryMass.prefixEndpoint hpsi h2 ring C u
    (BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor D ∧
      ResetFreeControlled hpsi h2 kappa ring anchor Controlled D) ∧
      BirthPhaseWait2BlockProgress.rank kappa ring anchor D <=
        BirthPhaseWait2BlockProgress.rank kappa ring anchor C

/-- No new asymptotic or numerical entrance charge is introduced by making
reset-freedom part of the controlled endpoint.  Proving the corresponding mass
statement is stronger, but its adopted budget/denominator stay unchanged. -/
abbrev resetFreeControlledEntranceL (n : Nat) : Nat := 16 * n * n
abbrev resetFreeControlledEntranceQ : Nat := 8

theorem reset_free_controlled_constants (n : Nat) :
    resetFreeControlledEntranceL n = 16 * n * n ∧
      resetFreeControlledEntranceQ = 8 := by
  exact ⟨rfl, rfl⟩

#print axioms BirthB1ResetFreeControlled.suppressSigStart_follower_no_fresh_reset
#print axioms BirthB1ResetFreeControlled.suppressSigMoveReset_of_upstream_free
#print axioms BirthB1ResetFreeControlled.suppressSigResetKillWidth_count_frame_of_reset_free
#print axioms BirthB1ResetFreeControlled.currentStep2_reset_free_no_undo
#print axioms BirthB1ResetFreeControlled.reset_free_controlled_constants

end BirthB1ResetFreeControlled
