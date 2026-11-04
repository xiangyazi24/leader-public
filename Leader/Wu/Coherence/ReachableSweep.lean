import Leader.Wu.Coherence.ReachableFacts

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableSweep

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts

variable {n ψ κ τ : Nat}

/-- Exact requested sweep induction step.  This is the target proposition;
Its phase half is closed below but the openR-freshness half is not claimed
without the missing trace-order/provenance lemma. -/
def SweepStepReachableV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep →
      ReachablePhaseFactsV31 ring (stepV3 hψ h2 ring C e)

abbrev sweepStep_reachable
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SweepStepReachableV31 (κ := κ) (τ := τ) hψ h2 ring

/-- The B-multi payload projects to exactly the five clauses of
`PhaseMainClearV31`. -/
theorem phaseMainClear_of_reachablePhaseFacts
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : ReachablePhaseFactsV31 ring C) :
    PhaseMainClearV31 ring C := by
  rcases h with
    ⟨hSweep, hCommit, hSealed, hRelease, hScrub, _⟩
  refine ⟨hSweep, hCommit, hSealed, ?_, ?_⟩
  · intro i hi
    exact (hRelease i hi).2
  · intro i hi
    exact (hScrub i hi).2.2

/-- Election geometry follows along every actual quarantine trace; this is the
same fold induction used earlier, now separated from the false split
closure. -/
theorem electionGeometry_of_quarantineTrace
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C) :
    ElectionGeometryV31 ring C := by
  rcases hTrace with ⟨C0, w, hBirth, rfl⟩
  have preserve :
      ∀ (v : List (Fin n)) (D : FC n ψ κ τ),
        ElectionGeometryV31 ring D →
          ElectionGeometryV31 ring
            (v.foldl (stepV3 hψ h2 ring) D) := by
    intro v
    induction v with
    | nil =>
        intro D hElection
        simpa using hElection
    | cons e v ih =>
        intro D hElection
        simp only [List.foldl_cons]
        exact ih _
          ((electionGeometryStepV31
            (κ := κ) (τ := τ) hψ h2 ring)
            D e hElection)
  exact preserve w C0 hBirth.2

/-- Certified half of `sweepStep_reachable`: all sweep/commit/sealed/release/
scrubL ownership debt survives a reachable sweep. -/
theorem sweepStep_reachable_phase
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hFacts : ReachablePhaseFactsV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    PhaseMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  exact phaseMainClear_sweep_step hψ h2 ring C e
    (electionGeometry_of_quarantineTrace hψ h2 ring C hTrace)
    (phaseMainClear_of_reachablePhaseFacts ring C hFacts)
    hb

/-- Arithmetic ψ-group equality.  Labels are step-invariant, so this relation
is stable under V3.1 services. -/
def SamePsiGroupV31
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (i j : Fin n) : Prop :=
  R2Coherence.groupStart ring (eraseCfgV3 C) i =
    R2Coherence.groupStart ring (eraseCfgV3 C) j

/-- First tempting trace fact: an openR owner does not coexist with a sweep
front in its ψ-group.  The closed witness in Part 3 shows this is NOT preserved
by `.seek` on arbitrary fact-good states. -/
def OpenRImpliesNoSweepInGroupV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (owner sweep : Fin n),
    (C owner).ctl.tok = .openR →
    (C sweep).ctl.tok = .sweep →
    SamePsiGroupV31 ring C owner sweep → False

instance openRImpliesNoSweepInGroupV31Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    Decidable (OpenRImpliesNoSweepInGroupV31 ring C) := by
  unfold OpenRImpliesNoSweepInGroupV31 SamePsiGroupV31
  infer_instance

/-- Directional refinement forced by the `.seek` counterexample: while openR
is live, every same-group seek must be strictly ahead of it in label order.
A responder seek has higher row priority than an initiator openR, so such a
front must meet/preempt openR before it can travel back to the root. -/
def OpenRSeekAheadV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (owner seek : Fin n),
    (C owner).ctl.tok = .openR →
    (C seek).ctl.tok = .seek →
    SamePsiGroupV31 ring C owner seek →
      (raw (C owner)).label.val < (raw (C seek)).label.val

instance openRSeekAheadV31Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    Decidable (OpenRSeekAheadV31 ring C) := by
  unfold OpenRSeekAheadV31 SamePsiGroupV31
  infer_instance

/-- The trace-level barrier that would be useful for the sweep branch.  This is
only a target in this round.  Its preservation requires proving that services
behind a live openR cannot create a new behind-seek; `openHazard` is the first
source branch that can do so via `startClosing`. -/
def ReachableOpenRBarrierV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    ReachableFromQuarantineV31 hψ h2 ring C →
      OpenRImpliesNoSweepInGroupV31 ring C ∧
      OpenRSeekAheadV31 ring C

namespace SeekBreaksNoSweep

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩

/-- Same fresh physical literal style as the compiled witness. -/
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

/-- No sweep initially.  The seek is BEHIND the live openR in the same group.
All physical prefix components are fresh, so the openR clause itself is true. -/
private def pre : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => cell (literal 0) .closing .none
  | 1 => cell (literal 1) .closing .seek
  | _ => cell (literal 2 .equal) .releasing .openR

private def after : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 pre 0

theorem pre_election :
    ElectionGeometryV31 ring3 pre := by
  decide +kernel

theorem pre_facts :
    ReachablePhaseFactsV31 ring3 pre := by
  decide +kernel

theorem pre_no_sweep :
    OpenRImpliesNoSweepInGroupV31 ring3 pre := by
  decide +kernel

/-- This is exactly the missing positional information: seek@1 is behind
openR@2. -/
theorem pre_not_seek_ahead :
    ¬ OpenRSeekAheadV31 ring3 pre := by
  decide +kernel

/-- Edge 0 -> 1 is dispatched as `.seek`; `seekStageV3` sees a root left
endpoint and emits root `.sweep`. -/
theorem pre_branch :
    branchAtV3 h3 h23 (pre 0) (pre (ring3.rightNeighbor 0)) = .seek := by
  decide +kernel

theorem after_tokens :
    (after 0).ctl.tok = .sweep ∧
    (after 1).ctl.tok = .none ∧
    (after 2).ctl.tok = .openR := by
  decide +kernel

/-- The B-multi causal payload still holds: root sweep prefix is vacuous and
the remote openR is physically unchanged/fresh. -/
theorem after_facts :
    ReachablePhaseFactsV31 ring3 after := by
  decide +kernel

/-- Therefore the simple no-sweep/openR fact is not branch-closed. -/
theorem after_not_no_sweep :
    ¬ OpenRImpliesNoSweepInGroupV31 ring3 after := by
  decide +kernel

/-- Closed source-level diagnosis: `.seek`, not `.sweep`, is the first branch
that destroys the tempting no-sweep/openR current-state invariant while both
pre and post satisfy the certified B-multi payload.  NO trace claim is made. -/
theorem seek_breaks_openR_noSweep :
    ∃ (C : FC 3 3 3 48) (e : Fin 3),
      ElectionGeometryV31 ring3 C ∧
      ReachablePhaseFactsV31 ring3 C ∧
      OpenRImpliesNoSweepInGroupV31 ring3 C ∧
      branchAtV3 h3 h23 (C e) (C (ring3.rightNeighbor e)) = .seek ∧
      ReachablePhaseFactsV31 ring3 (stepV3 h3 h23 ring3 C e) ∧
      ¬ OpenRImpliesNoSweepInGroupV31 ring3
        (stepV3 h3 h23 ring3 C e) := by
  exact ⟨pre, 0, pre_election, pre_facts, pre_no_sweep,
    pre_branch, after_facts, after_not_no_sweep⟩



end SeekBreaksNoSweep


