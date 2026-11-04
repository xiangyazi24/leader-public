import Leader.Wu.Splice.CheckStructuralTheorem
import Leader.Wu.Comparison.HistoryLiftGenClean
import Leader.Wu.Comparison.HistoryLiftDoneCheck
import Leader.Wu.Comparison.HistoryLiftCompare
import Leader.Wu.Comparison.HistoryLateLifts
import Leader.Wu.Comparison.HistoryTrustImmediateLift
import Leader.Wu.Birth.DoneLineageLeaseGuardedHostStep

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9CheckWholeStep

open PPLL PPLLRepair PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLComparisonHistory
open BirthPhaseCohortDesign
open B9CheckStructuralCensus
open BirthDoneLineageQuarantineDesign
open BirthDoneLineageLeaseTransitions
open BirthDoneLineageLeaseHostStep
open BirthDoneLineageLeaseGuardedHostStep

variable {n psi kappa tau width : Nat}

/-! ## 1. Exact compatibility seams of the literal current step

These are the five genuine source-join premises in the current stage table:
GEN/CLEAN, DONE departure, CHECK, DISAPPEAR carry, and COMPARE action one.
The structure stores the marked states at those literal cuts.  Once the marked
whole-step trace exists, these fields are computed from its pre-step pair; they
are not additional protocol state.
-/

structure StepHistoryCuts (n psi : Nat) where
  sourcePos : Fin n
  genInput :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi
  doneInput : MarkedAgentState n psi × MarkedAgentState n psi
  checkInput :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi
  disappearInput : MarkedAgentState n psi × MarkedAgentState n psi
  compareInput :
    MarkedAuthorizedAgentState n psi × MarkedAuthorizedAgentState n psi

/-- The DISAPPEAR compatibility premise at the exact internal carry cut. -/
def DisappearCompatibleAt (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi) : Prop :=
  let q0 := markedDisappearStartR hpsi l r
  let q1 := markedDisappearStartL hpsi q0.1 q0.2
  DisappearCarryCompatible hpsi q1.1 q1.2

/-- All source-join premises required by the literal current consumer row.
There is no extra epoch, lease value, or protocol state in this proposition. -/
def StepHistoryCompatible
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (cuts : StepHistoryCuts n psi) : Prop :=
  CurrentGenCleanEntryWidthCompatible
      hpsi hwidth hle kappa cuts.sourcePos
        cuts.genInput.1 cuts.genInput.2 ∧
    CurrentDoneMoveCompatible
      hpsi cuts.doneInput.1 cuts.doneInput.2 ∧
    PreserveDoneCheckCompatible
      hpsi cuts.checkInput.1 cuts.checkInput.2 ∧
    DisappearCompatibleAt
      hpsi cuts.disappearInput.1 cuts.disappearInput.2 ∧
    CurrentCompareSigActionOneCompatible
      hpsi cuts.compareInput.1 cuts.compareInput.2

theorem StepHistoryCompatible.gen
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (cuts : StepHistoryCuts n psi)
    (h : StepHistoryCompatible hpsi hwidth hle kappa cuts) :
    CurrentGenCleanEntryWidthCompatible
      hpsi hwidth hle kappa cuts.sourcePos
        cuts.genInput.1 cuts.genInput.2 := h.1

theorem StepHistoryCompatible.done
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (cuts : StepHistoryCuts n psi)
    (h : StepHistoryCompatible hpsi hwidth hle kappa cuts) :
    CurrentDoneMoveCompatible
      hpsi cuts.doneInput.1 cuts.doneInput.2 := h.2.1

theorem StepHistoryCompatible.check
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (cuts : StepHistoryCuts n psi)
    (h : StepHistoryCompatible hpsi hwidth hle kappa cuts) :
    PreserveDoneCheckCompatible
      hpsi cuts.checkInput.1 cuts.checkInput.2 := h.2.2.1

theorem StepHistoryCompatible.disappear
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (cuts : StepHistoryCuts n psi)
    (h : StepHistoryCompatible hpsi hwidth hle kappa cuts) :
    DisappearCompatibleAt
      hpsi cuts.disappearInput.1 cuts.disappearInput.2 := h.2.2.2.1

theorem StepHistoryCompatible.compare
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (cuts : StepHistoryCuts n psi)
    (h : StepHistoryCompatible hpsi hwidth hle kappa cuts) :
    CurrentCompareSigActionOneCompatible
      hpsi cuts.compareInput.1 cuts.compareInput.2 := h.2.2.2.2

/-! ## 2. The exact current DONE blocker

The whole-step theorem needs this Full-strength promotion.  On
current main the corresponding exported theorem ends at
`AuditLocalHistoryTrusted`; the three new CHECK-side lifts already have their
Full-strength statements.
-/

def CurrentDoneMoveFullPreservation (hpsi : 0 < psi) : Prop :=
  ∀ (l r : MarkedAgentState n psi),
    FullLocalHistoryTrusted l.concrete l.history →
    FullLocalHistoryTrusted r.concrete r.history →
    CurrentDoneMoveCompatible hpsi l r →
    let q := markedDoneCaptureSigMove hpsi l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history

/-- What current main does prove at DONE, even when the inputs have Full
history trust.  This is the exact point where a naïve whole-step composition
currently loses the fourth `pCarry` conjunct. -/
theorem current_done_move_audit_of_full_inputs
    (hpsi : 0 < psi) (l r : MarkedAgentState n psi)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history)
    (hcompat : CurrentDoneMoveCompatible hpsi l r) :
    let q := markedDoneCaptureSigMove hpsi l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  exact markedDoneCaptureSigMove_preserves_auditLocalHistoryTrusted
    hpsi l r hl.1 hr.1 hcompat

/-! ## 3. The four B9 structural predicates

These are exactly the hypotheses consumed by
`checkBlockedAt_of_structural_certificate`.  Keeping them bundled makes the
global closure obligation explicit instead of conflating it with local field
history.
-/

def StructuralCertificate
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  leader_delimited_peak_safe hpsi ring C ∧
    comparison_route_certified hpsi h2 ring C ∧
    crossed_id_survival_bound hpsi h2 ring C ∧
    leader_boundary_clearing hpsi h2 ring C

/-- Immediate consumer of the bundled certificate. -/
theorem checkBlockedAt_of_certificate
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (h : StructuralCertificate hpsi h2 ring C) :
    ∀ e, BirthPhaseCohortDesign.CheckBlockedAt hpsi h2 ring C e := by
  rcases h with ⟨hPeak, hRoute, hCross, hBoundary⟩
  exact
    B9CheckStructuralTheorem.checkBlockedAt_of_structural_certificate
      hpsi h2 ring C hPeak hRoute hCross hBoundary

/-- Exact global statement still needed for one physical consumer step.
This is not a consequence of `FullLocalHistoryTrusted` alone: the four fields
above include segment geometry, route carriers, live group IDs, and leader
boundary clearing. -/
def StructuralStepClosure
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n),
    StructuralCertificate hpsi h2 ring C →
    StructuralCertificate hpsi h2 ring
      (BirthShortDoneTerminalConsumer.step
        hpsi (by decide : 0 < 2) h2 ring C e)

/-- Once the true global one-step closure is supplied, CHECK blocking in the
successor is an immediate application of the already-proved structural theorem. -/
theorem checkBlockedAt_after_step_of_structuralStepClosure
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hclose : StructuralStepClosure
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n)
    (hC : StructuralCertificate hpsi h2 ring C) :
    ∀ j, BirthPhaseCohortDesign.CheckBlockedAt hpsi h2 ring
      (BirthShortDoneTerminalConsumer.step
        hpsi (by decide : 0 < 2) h2 ring C e) j := by
  exact checkBlockedAt_of_certificate hpsi h2 ring _ (hclose C e hC)

/-! ## 4. Exact guarded-lineage obligation

`LDR-BIRTH-B9-LINEAGE-LEASE-GUARDED-SAFETY` is the natural provider of the
DONE source-join part.  Current `LeaseSafe` already survives
`guardedLeaseHostStep`; the missing adapter is that its certified cuts imply
`CurrentDoneMoveCompatible` at every live successor cut.
-/

def GuardedLeaseSuppliesDoneCompatibility
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  ∀ (S : LeaseHostConfig n psi) (e : Fin n),
    LeaseSafe hpsi ring S.marked S.role →
    (∀ i : Fin n,
      GrantProducerPremise hpsi
        (S.marked i) (S.marked (ring.rightNeighbor i))
        (S.role i) (S.role (ring.rightNeighbor i))) →
    let T := guardedLeaseHostStep hpsi ring S e
    ∀ i : Fin n,
      CurrentDoneMoveCompatible hpsi
        (T.marked i) (T.marked (ring.rightNeighbor i))

/-- Full local-history adapter required from the B9 invariant once a literal
marked whole-step trace exposes its five stage cuts. -/
def GuardedLeaseSuppliesStepHistoryCompatible
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (ring : DirectedRing n)
    (cutsOf : LeaseHostConfig n psi → Fin n → StepHistoryCuts n psi) : Prop :=
  ∀ (S : LeaseHostConfig n psi) (e : Fin n),
    LeaseSafe hpsi ring S.marked S.role →
    (∀ i : Fin n,
      GrantProducerPremise hpsi
        (S.marked i) (S.marked (ring.rightNeighbor i))
        (S.role i) (S.role (ring.rightNeighbor i))) →
    StepHistoryCompatible hpsi hwidth hle kappa (cutsOf S e)

/-- The exact two-part B9 obligation for this route: the guarded lineage/lease
invariant must provide all five local source joins on the literal marked trace,
and the global B9 certificate must be closed by the same physical step. -/
def GuardedB9WholeStepObligation
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (cutsOf : LeaseHostConfig n psi → Fin n → StepHistoryCuts n psi) : Prop :=
  GuardedLeaseSuppliesStepHistoryCompatible
      hpsi (by decide : 0 < 2) h2 kappa ring cutsOf ∧
    StructuralStepClosure (kappa := kappa) (tau := tau) hpsi h2 ring

#check @PPLLComparisonHistory.markedAuthorizedGenCleanEntryWidth_preserves_fullLocalHistoryTrusted
#check @PPLLComparisonHistory.markedDoneCaptureSigMove_preserves_auditLocalHistoryTrusted
#check @PPLLComparisonHistory.markedPreserveDoneCheck_preserves_fullLocalHistoryTrusted
#check @PPLLComparisonHistory.markedDisappear_preserves_fullLocalHistoryTrusted
#check @PPLLComparisonHistory.markedAuthorizedCompareSigActionOne_preserves_fullLocalHistoryTrusted
#check @BirthDoneLineageLeaseGuardedHostStep.guardedLeaseHostStep_preserves_leaseSafe

end B9CheckWholeStep

#print axioms B9CheckWholeStep.StepHistoryCompatible.gen
#print axioms B9CheckWholeStep.StepHistoryCompatible.done
#print axioms B9CheckWholeStep.current_done_move_audit_of_full_inputs
#print axioms B9CheckWholeStep.checkBlockedAt_of_certificate
#print axioms B9CheckWholeStep.checkBlockedAt_after_step_of_structuralStepClosure
