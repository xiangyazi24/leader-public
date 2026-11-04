import Leader.Wu.ZeroDivisible.BoundaryEquality

/-!
Round-two candidates for boundary equality with K4.  The emergency rule uses
actual input leader bits, not bullet provenance: a nonempty interacting pair
must stay nonempty.  Rescue transfers to the responder only after a fatal
transition; Anchor restores the original leader as a negative control.  Neither
rule adds a field.  Head puts the emergency responder at label zero to avoid
immediate WRITE migration back to the killed site.  This is a separate
candidate, not a claimed convergence repair.  WRITE migration carries the
elimination bundle with it.

Pair conservation is an unconditional safety property.  It is not a claim of
convergence or eventual stationary output; the census must test both separately.
-/
namespace PPLLAstraDesign2

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard PPLLFableDesignR1

inductive Design where
  | rescue | anchor | head
  deriving DecidableEq

/-- Initialize an emergency replacement with a shield and no forged bullet or
absence signal.  The existing comparison and write cleanup uses no extra state. -/
def replacement {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  { clearCmp u with leader := true, shield := true, bullet := 0, signal_B := 0 }

/-- Preserve the elimination registers on the existing finite WRITE migration.
The move is still Algorithm 16's responder-label test; this adds no new motion. -/
def writeWithBundle {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := writeSeq hψ l r
  if r.leader = true ∧ r.label.val ≠ 0 ∧ l.leader = false then
    ({ q.1 with shield := r.shield, bullet := r.bullet, signal_B := r.signal_B },
     { q.2 with shield := false, bullet := 0, signal_B := 0 })
  else q

/-- Repair an empty output pair only when an actual input leader was present.
The rescue variant chooses the responder; the anchor control chooses the old
leader's site.  In particular a pair containing no input leader is unaffected. -/
def conserve {ψ : Nat} (d : Design) (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) : AgentState ψ × AgentState ψ :=
  if (l.leader || r.leader) && !(q.1.leader || q.2.leader) then
    if d = .head then
      (q.1, { replacement q.2 with label := ⟨0, Nat.zero_lt_of_lt q.2.label.isLt⟩ })
    else if d = .rescue then (q.1, replacement q.2)
    else if l.leader then (replacement q.1, q.2)
    else (q.1, replacement q.2)
  else q

/-- The unmodified BEQ full-wall stages through suppression. -/
def beforeElimination {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q := pPsiProbeWall hψ l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := cleanSig hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := sigMoveF hψ true .dropMisaligned q.1 q.2
  let q := (dropStale q.1, dropStale q.2)
  let q := preCheckReset q.1 q.2
  let q := checkSigF hψ κ false q.1 q.2
  let q := disappear hψ q.1 q.2
  let q := compareSigF κ false true q.1 q.2
  suppressSigResetKill hψ q.1 q.2

/-- BEQ and K4 remain the proposal stages; the final conservation guard has
priority over their loss of all leaders in a nonempty input pair. -/
def pipeline {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (d : Design)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := beforeElimination hψ κ l r
  let q := k4Kernel hψ q.1 q.2
  let q := writeWithBundle hψ q.1 q.2
  conserve d l r q

def variants : List (String × Design) :=
  [("astR2RescueK4", .rescue), ("astR2AnchorK4", .anchor), ("astR2HeadK4", .head)]

/-- Every nonempty input pair remains nonempty, for arbitrary ancillary fields.
This is the local implication that excludes a global positive-to-zero step. -/
theorem conserve_nonempty {ψ : Nat} (d : Design) (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) (h : l.leader = true ∨ r.leader = true) :
    (conserve d l r q).1.leader = true ∨ (conserve d l r q).2.leader = true := by
  unfold conserve
  cases hl : l.leader <;> cases hr : r.leader <;>
    cases hq₁ : q.1.leader <;> cases hq₂ : q.2.leader <;>
    cases d <;> simp_all [replacement, clearCmp]

/-- Full-pipeline local support conservation.  Global nonzero count follows
because a step changes only its two endpoints.  No convergence is asserted. -/
theorem pipeline_nonempty {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (d : Design)
    (l r : AgentState ψ) (h : l.leader = true ∨ r.leader = true) :
    (pipeline hψ κ d l r).1.leader = true ∨ (pipeline hψ κ d l r).2.leader = true := by
  exact conserve_nonempty d l r _ h

end PPLLAstraDesign2
