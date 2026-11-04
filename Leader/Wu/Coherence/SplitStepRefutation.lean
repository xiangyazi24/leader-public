import Leader.Wu.Coherence.QuarantineReach

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31SplitClosure

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach

variable {n ψ κ τ : Nat}

/-- Branch-local split closure with both geometries available.  The stronger
`AdmittedPostBirthGeometryV3` premise is included exactly as requested; the
counterexample below satisfies it as well. -/
def SplitStepBranchV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (b : BranchV3) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    AdmittedPostBirthGeometryV3 hψ ring C →
    QuarantineSplitV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b →
      QuarantineSplitV31 ring (stepV3 hψ h2 ring C e)

abbrev splitStep_seek
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SplitStepBranchV31 (κ := κ) (τ := τ) hψ h2 ring .seek

abbrev splitStep_sweep
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SplitStepBranchV31 (κ := κ) (τ := τ) hψ h2 ring .sweep

abbrev splitStep_commit
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SplitStepBranchV31 (κ := κ) (τ := τ) hψ h2 ring .commit

abbrev splitStep_release
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SplitStepBranchV31 (κ := κ) (τ := τ) hψ h2 ring .release

abbrev splitStep_scrubL
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SplitStepBranchV31 (κ := κ) (τ := τ) hψ h2 ring .scrubL

abbrev splitStep_openR
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SplitStepBranchV31 (κ := κ) (τ := τ) hψ h2 ring .openR

abbrev splitStep_sealed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SplitStepBranchV31 (κ := κ) (τ := τ) hψ h2 ring .sealed

abbrev splitStep_openHazard
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SplitStepBranchV31 (κ := κ) (τ := τ) hψ h2 ring .openHazard

abbrev splitStep_openNoHazard
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SplitStepBranchV31 (κ := κ) (τ := τ) hψ h2 ring .openNoHazard

abbrev splitStep_mixed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SplitStepBranchV31 (κ := κ) (τ := τ) hψ h2 ring .mixed



namespace SweepStructuralCounterexample

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩

/-- Physical literal whose main `path` is exactly the fresh resident component.
All resident bits are false, so `.some lab 0` is fresh at label `lab`. -/
private def literal
    (lab : Fin 3) (state : MainState := .none) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
      leader := false
      shield := false
      gen_ws := false
      label := lab
      state := state
      path := .some lab 0
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false
  }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

private def cell
    (p : R2.Cell 3 3 48)
    (m : R2Coherence.Mark) (t : TokenV3) : Cell 3 3 48 :=
  ⟨p, ⟨m, t⟩⟩

/-- Labels are 0,1,2 around the ring.

* label 0 owns a live root sweep; its strict swept prefix is empty;
* label 2 owns `openR` and is an equal frontier;
* all three stored prefix components are initially fresh.
-/
private def pre : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => cell (literal 0) .closing .sweep
  | 1 => cell (literal 1) .closing .none
  | _ => cell (literal 2 .equal) .releasing .openR

private def after : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 pre 0

/-- The counterexample has the requested strong post-birth label geometry. -/
theorem pre_admitted :
    AdmittedPostBirthGeometryV3 h3 ring3 pre := by
  decide +kernel

/-- Hence it also has the deletion-closed election geometry. -/
theorem pre_election :
    ElectionGeometryV31 ring3 pre := by
  decide +kernel

/-- The `openR` owner is genuinely fresh before the sweep. -/
theorem pre_openR_fresh :
    OpenROwnerFreshV3 ring3 pre 2 := by
  decide +kernel

/-- Structural half holds before the step. -/
theorem pre_structural :
    ControllerShapeStructuralV31 ring3 pre := by
  decide +kernel

/-- Phase half holds before the step.  The only live phase obligation is the
label-0 sweep, whose strict prefix is `Fin 0`, hence vacuous. -/
theorem pre_phase :
    PhaseMainClearV31 ring3 pre := by
  decide +kernel

theorem pre_split :
    QuarantineSplitV31 ring3 pre := by
  exact ⟨pre_structural, pre_phase⟩

/-- Dispatcher really selects the sweep branch on edge 0 -> 1. -/
theorem pre_branch :
    branchAtV3 h3 h23 (pre 0) (pre (ring3.rightNeighbor 0)) = .sweep := by
  decide +kernel

/-- The phase/main-clear half survives this sweep. -/
theorem after_phase :
    PhaseMainClearV31 ring3 after := by
  exact phaseMainClear_sweep_step h3 h23 ring3 pre 0
    pre_election pre_phase pre_branch

/-- Concrete mechanism: the sweep clears labels 0 and 1, but the remote
label-2 equal/openR frontier survives. -/
theorem after_fields :
    (raw (after 0)).path = .bot ∧
    (raw (after 1)).path = .bot ∧
    (raw (after 2)).state = .equal ∧
    (raw (after 2)).path = .some 2 0 ∧
    (after 2).ctl.mark = .releasing ∧
    (after 2).ctl.tok = .openR := by
  decide +kernel

/-- The surviving `openR` owner is no longer intrinsically fresh: its equal
frontier still reads the cleared component at label 0. -/
theorem after_openR_not_fresh :
    ¬ OpenROwnerFreshV3 ring3 after 2 := by
  decide +kernel

/-- Therefore the structural half dies although the phase half survived. -/
theorem after_not_structural :
    ¬ ControllerShapeStructuralV31 ring3 after := by
  decide +kernel

theorem after_not_split :
    ¬ QuarantineSplitV31 ring3 after := by
  intro h
  exact after_not_structural h.1

/-- Kernel refutation of the requested sweep branch law, even with both
geometry premises. -/
theorem not_splitStep_sweep :
    ¬ splitStep_sweep (κ := 3) (τ := 48) h3 h23 ring3 := by
  intro h
  have hout := h pre 0 pre_election pre_admitted pre_split pre_branch
  exact after_not_split (by simpa [after] using hout)

/-- Consequently the stronger global closure leaf is false as stated. -/
theorem quarantineSplitStepV31_false :
    ¬ QuarantineSplitStepV31 (κ := 3) (τ := 48) h3 h23 ring3 := by
  intro h
  have hout := h pre 0 pre_election pre_split
  exact after_not_split (by simpa [after] using hout)

/-- The exact third-death statement: phase sweep preservation and structural
failure hold simultaneously on one legal service. -/
theorem sweep_phase_survives_structural_dies :
    PhaseMainClearV31 ring3 after ∧
      ¬ ControllerShapeStructuralV31 ring3 after :=
  ⟨after_phase, after_not_structural⟩

end SweepStructuralCounterexample



/-!
Branch audit stopped here because `.sweep` already refutes the global design.
No `sorry`/axiom placeholders are introduced for the remaining branches.

Source status / precise obstruction:

* `.sweep`: REFUTED above.  `PhaseMainClearV31` preservation is proved,
  but clearing a component can destroy a remote surviving `openR` owner's
  `OpenROwnerFreshV3`, so `ControllerShapeStructuralV31` is not closed.

* `.openHazard`: not needed after the refutation.  Source shows its selected
  arm physically holds both endpoints and only starts closing control, so its
  physical half is the easy case; a full proof would transport the old phase
  obligations and same-physical `OpenROwnerFreshV3`.

* `.mixed`: not needed after the refutation.  Under `ElectionGeometryV31`, the
  admitted passive edge takes either identity or control-only `startClosing`;
  again the physical half is inert.

* `.openNoHazard`: still intrinsically nontrivial.  The served pair is
  open/none, hence neither served endpoint is itself `PhaseOwnedV31`; so a
  `GroupOwnedClearV31` obligation cannot simply authorize writing that cell.
  However an `openR` freshness window is *not* a `GroupOwnedClearV31` window.
  The open/no-hazard proposal may create a new `.equal` while preserving
  bit/label/path; preserving `OpenROwnerFreshV3` is therefore tied to the
  existing `OpenNoHazardNewEqualPrefixV31`-style freshness problem.

* `.seek`: expected local repair: physical state is held; the only new phase
  token is a root `.sweep`, whose strict prefix is empty.  Not pursued after
  the decisive sweep refutation.

* `.commit`, `.release`, `.sealed`: require whole-group `GroupOwnedClearV31`
  transport to the newly moved/installed phase owner.  Not pursued.

* `.scrubL`: in addition to whole-group ownership transport, the root handoff
  creates `.openR`; the new owner-freshness proof is a separate structural
  obligation.  Not pursued.

* `.openR`: reopening removes ownership while moving the `openR` frontier;
  preservation of `OpenROwnerFreshV3` is the delicate structural obligation.
  Not pursued.

Therefore the next viable invariant cannot be only
`ControllerShapeStructuralV31 ∧ PhaseMainClearV31`.  It needs a compatibility
clause excluding exactly this forged coexistence, e.g. a per-group phase-wave
lineage/exclusivity invariant saying that a clear-capable sweep/commit/release/
scrub wave cannot overlap a live `openR` freshness window in a way that leaves
an equal frontier depending on a cell the clear wave may erase.  Proving that
compatibility only on `ReachableFromQuarantineV31` is the natural next gate.
-/



end R2CoherenceV31SplitClosure
