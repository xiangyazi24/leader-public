import Leader.Wu.Comparison.AuthorizedRepairCounterexample

/-!
# Host-aligned ephemeral comparison authorization

The first executable authorization repair normalized `true` using only the
payload label. Its seven-state counterexample parks a forged payload-zero marker
at physical label one forever. This second, separately named repair validates a
marker only while both payload and current host labels are zero.

A stable terminal-to-zero SIGMOVE creates exactly that host alignment. If the
next physical interaction finds an adjacent path, COMPARE consumes permission;
if the path moves onward first, permission is cleared and can be re-established
only at a later stable wrap. The return-priority comparison state machine and
one-Boolean physical carrier are reused unchanged. This module must re-pass the
old T9/T18 regressions and reject both edges of the seven-state trap before any
cleanup or convergence claim is attempted.
-/

namespace PPLLHostAlignedComparisonRepair

open PPLL PPLLRepair PPLLResearchFormulation PPLLDomain
open PPLLAuthorizedComparisonRepair

/-- Host-aligned normalization: authorization is live only on payload zero at
physical label zero. -/
def normalizeHostPermit (hψ : ψ > 0)
    (s : AgentState ψ) (permit : Bool) : Bool :=
  match s.path with
  | .some 0 _ => decide (s.label = ⟨0, hψ⟩) && permit
  | _ => false

/-- Generic fail-closed update for stages without a new stable-wrap event. -/
def reconcileHostPermit (hψ : ψ > 0)
    (old : AuthorizedAgentState ψ) (out : AgentState ψ) : Bool :=
  if out.path = old.core.path then
    normalizeHostPermit hψ out old.path0Crossed
  else false

/-- Pair adapter using host-aligned reconciliation. -/
def hostReconcile (hψ : ψ > 0)
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := f l.core r.core
  (⟨q.1, reconcileHostPermit hψ l q.1⟩,
    ⟨q.2, reconcileHostPermit hψ r q.2⟩)

/-- Algorithm 2 additionally clears permission whenever labels change. -/
def hostAuthorizedPPsi (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := pPsi hψ l.core r.core
  let lp := if q.1.label = l.core.label then
    reconcileHostPermit hψ l q.1 else false
  let rp := if q.2.label = r.core.label then
    reconcileHostPermit hψ r q.2 else false
  (⟨q.1, lp⟩, ⟨q.2, rp⟩)

/-- Saturated GENSIG birth and path replacement clear host authorization. -/
def hostAuthorizedGenSig (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  hostReconcile hψ (genSigSaturated hψ κ) l r

/-- CLEAN_SIG reconciles authorization against its output paths. -/
def hostAuthorizedCleanSig (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  hostReconcile hψ (cleanSig hψ) l r

/-- ELIMINATE_SIG clears authorization with an eliminated path. -/
def hostAuthorizedEliminateSig (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  hostReconcile hψ (eliminateSig hψ) l r

/-- SIGMOVE is the sole authorization-creation event. A stable wrap puts
payload zero at physical label zero, so stronger normalization preserves true;
all non-wrap hosts clear it. -/
def hostAuthorizedSigMove (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := sigMove hψ l.core r.core
  if _hmoved : pathMovedRight l.core r.core q.1 q.2 = true then
    let receiverPermit := match l.core.path with
      | .some 0 _ =>
          if stableSuccessor hψ l.core r.core then
            l.path0Crossed || stableWrap hψ l.core r.core
          else false
      | _ => false
    (⟨q.1, false⟩,
      ⟨q.2, normalizeHostPermit hψ q.2 receiverPermit⟩)
  else
    (⟨q.1, reconcileHostPermit hψ l q.1⟩,
      ⟨q.2, reconcileHostPermit hψ r q.2⟩)

/-- CHECK changes no path host and uses ordinary host reconciliation. -/
def hostAuthorizedCheckSig (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  hostReconcile hψ (checkSig hψ) l r

/-- DISAPPEAR changes comparison controls but not path hosting. -/
def hostAuthorizedDisappear (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  hostReconcile hψ (disappear hψ) l r

/-- Reuse the repaired Algorithm-7/8 physical behavior, then enforce stronger
host normalization on both resulting markers. -/
def hostAuthorizedCompareSig (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := authorizedCompareSig hψ l r
  (⟨q.1.core, normalizeHostPermit hψ q.1.core q.1.path0Crossed⟩,
    ⟨q.2.core, normalizeHostPermit hψ q.2.core q.2.path0Crossed⟩)

/-- Host-aligned prefix through SIGMOVE. -/
def hostBeforeCheck (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := hostAuthorizedPPsi hψ l r
  let q := hostAuthorizedGenSig hψ κ q.1 q.2
  let q := hostAuthorizedCleanSig hψ q.1 q.2
  let q := hostAuthorizedEliminateSig hψ q.1 q.2
  hostAuthorizedSigMove hψ q.1 q.2

/-- Host-aligned prefix through COMPARE. -/
def hostBeforeSuppress (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := hostBeforeCheck hψ κ l r
  let q := hostAuthorizedCheckSig hψ q.1 q.2
  let q := hostAuthorizedDisappear hψ q.1 q.2
  hostAuthorizedCompareSig hψ q.1 q.2

/-- Full host-aligned research transition. -/
def ppllHostAlignedRepair (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := hostBeforeSuppress hψ κ l r
  let q := hostReconcile hψ (suppressSig hψ) q.1 q.2
  let q := hostReconcile hψ (eliminateLeadersNoCollision hψ) q.1 q.2
  hostReconcile hψ (writeSeq hψ) q.1 q.2

/-! ## Counterexample and genuine-route regressions -/

private def wrappedPath0 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .depart with path := .some 0 0 }, false⟩

private def emptyLabel0 : AuthorizedAgentState 2 :=
  ⟨PPLLCounterexample.state2 0, false⟩

/-- A genuine stable terminal-to-zero transfer still creates permission at the
label-zero receiver. -/
theorem hostAligned_stable_wrap_sets_permission :
    let q := hostAuthorizedSigMove (by omega : 2 > 0) wrappedPath0 emptyLabel0
    q.1.path0Crossed = false ∧ q.2.core.path = .some 0 0 ∧
      q.2.core.label = 0 ∧ q.2.path0Crossed = true := by
  decide

private def movedLabel0 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .depart with path := .some 0 0 }, true⟩

private def frontLabel1 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .depart with path := .some 1 0 }, false⟩

/-- On the next blocked movement edge, COMPARE starts and consumes the genuine
host-aligned permission. -/
theorem hostAligned_moved_carrier_starts_and_consumes :
    let q := hostAuthorizedCompareSig (by omega : 2 > 0)
      movedLabel0 frontLabel1
    q.1.core.state = .congest ∧ q.2.core.state = .congest ∧
      q.1.path0Crossed = false := by
  decide

/-- The old trap is rejected even when its forged carrier is the responder. -/
theorem hostAligned_breaks_trap_edge0 :
    let q := ppllHostAlignedRepair (by omega : 2 > 0) 0
      PPLLAuthorizedRepairCounterexample.trapInitial.1
      PPLLAuthorizedRepairCounterexample.trapInitial.2
    q.2.path0Crossed = false := by
  decide

/-- The old trap is also rejected when its forged carrier initiates. -/
theorem hostAligned_breaks_trap_edge1 :
    let q := ppllHostAlignedRepair (by omega : 2 > 0) 0
      PPLLAuthorizedRepairCounterexample.trapInitial.2
      PPLLAuthorizedRepairCounterexample.trapInitial.1
    q.1.path0Crossed = false := by
  decide

end PPLLHostAlignedComparisonRepair
