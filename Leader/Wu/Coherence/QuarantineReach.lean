import Leader.Wu.Coherence.BirthQuarantine
import Leader.Wu.Coherence.PhaseMainClear

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31QuarantineReach

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31Mission R2CoherenceV31Step
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31PhaseMainClear

variable {n ψ κ τ : Nat}

/-- Split invariant used for the quarantine reachability argument. -/
def QuarantineSplitV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ControllerShapeStructuralV31 ring C ∧
    PhaseMainClearV31 ring C

/-- The quarantine initializer satisfies the structural half vacuously:
there are no release/scrubL/openR tokens. -/
theorem quarantineInit_structural
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    ControllerShapeStructuralV31 ring (quarantineInitV31 C) := by
  unfold ControllerShapeStructuralV31
  refine ⟨?_, ?_, ?_⟩
  · intro i h
    simp [quarantineInitV31, setControl] at h
  · intro i h
    simp [quarantineInitV31, setControl] at h
  · intro i h
    simp [quarantineInitV31, setControl] at h

/-- The quarantine initializer satisfies the phase/main-clear half vacuously.
In particular the sealed-mark clause is vacuous because every mark is
`.closing`, not `.sealed`. -/
theorem quarantineInit_phaseMainClear
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    PhaseMainClearV31 ring (quarantineInitV31 C) := by
  unfold PhaseMainClearV31
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i h
    simp [quarantineInitV31, setControl] at h
  · intro i h
    simp [quarantineInitV31, setControl] at h
  · intro i h
    simp [quarantineInitV31, setControl] at h
  · intro i h
    simp [quarantineInitV31, setControl] at h
  · intro i h
    simp [quarantineInitV31, setControl] at h

theorem quarantineInit_split
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    QuarantineSplitV31 ring (quarantineInitV31 C) := by
  exact ⟨quarantineInit_structural ring C,
    quarantineInit_phaseMainClear ring C⟩

/-- `GroupOwnedClearV31` contains the old main-clear obligation as its first
projection. -/
theorem groupOwnedClear_mainClear
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n)
    (h : GroupOwnedClearV31 ring C i) :
    GroupMainClearV3 ring C i := by
  intro k
  exact (h k).1

/-- The split is stronger than the old current-state controller shape. -/
theorem controllerShapeV3_of_split
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : QuarantineSplitV31 ring C) :
    ControllerShapeV3 ring C := by
  rcases h with ⟨hStruct, hPhase⟩
  rcases hStruct with ⟨hReleaseS, hScrubS, hOpenRS⟩
  rcases hPhase with ⟨_, _, hSealedP, hReleaseP, hScrubP⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    exact groupOwnedClear_mainClear ring C i (hSealedP i hi)
  · intro i hi
    exact ⟨hReleaseS i hi,
      groupOwnedClear_mainClear ring C i (hReleaseP i hi)⟩
  · intro i hi
    rcases hScrubS i hi with ⟨hm, hz⟩
    exact ⟨hm, hz,
      groupOwnedClear_mainClear ring C i (hScrubP i hi)⟩
  · intro i hi
    exact hOpenRS i hi



/-- Reachability from the concrete quarantine entrance. -/
def ReachableFromQuarantineV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) : Prop :=
  ∃ (C0 : FC n ψ κ τ) (w : List (Fin n)),
    BirthEntranceV1 hψ h2 ring C0 ∧
      C = w.foldl (stepV3 hψ h2 ring) C0

/-- Exact remaining split-invariant implementation leaf.  The `PhaseMainClearV31`
half for branch `.sweep` is already supplied; the other branch halves remain to
be discharged. -/
def QuarantineSplitStepV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    QuarantineSplitV31 ring C →
      QuarantineSplitV31 ring (stepV3 hψ h2 ring C e)

/-- One already-closed branch-half. -/
theorem phaseMainClear_sweep_available
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hElection : ElectionGeometryV31 ring C)
    (hPhase : PhaseMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    PhaseMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  exact phaseMainClear_sweep_step hψ h2 ring C e
    hElection hPhase hb

/-- If the missing all-branch split-step leaf is supplied, every state reachable
from the quarantine entrance satisfies the split invariant. -/
theorem reachable_split_of_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hStep : QuarantineSplitStepV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ)
    (hReach : ReachableFromQuarantineV31 hψ h2 ring C) :
    QuarantineSplitV31 ring C := by
  rcases hReach with ⟨C0, w, hBirth, rfl⟩
  have hSplit0 : QuarantineSplitV31 ring C0 := by
    rcases hBirth.1 with ⟨_, D, _, hC0⟩
    rw [hC0]
    exact quarantineInit_split ring D
  have preserve :
      ∀ (v : List (Fin n)) (D : FC n ψ κ τ),
        ElectionGeometryV31 ring D →
        QuarantineSplitV31 ring D →
        QuarantineSplitV31 ring
          (v.foldl (stepV3 hψ h2 ring) D) := by
    intro v
    induction v with
    | nil =>
        intro D _ hSplit
        simpa using hSplit
    | cons e v ih =>
        intro D hElection hSplit
        simp only [List.foldl_cons]
        apply ih
        · exact
            (electionGeometryStepV31
              (κ := κ) (τ := τ) hψ h2 ring)
              D e hElection
        · exact hStep D e hElection hSplit
  exact preserve w C0 hBirth.2 hSplit0

/-- The split-step leaf is sufficient for the actual `ControllerSoundV3`
required by the entrance bridge. -/
theorem controllerSoundV3_of_split_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hStep : QuarantineSplitStepV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ)
    (hBirth : BirthEntranceV1 hψ h2 ring C) :
    ControllerSoundV3 hψ h2 ring C := by
  intro w
  apply controllerShapeV3_of_split ring _
  exact reachable_split_of_step hψ h2 ring hStep
    (w.foldl (stepV3 hψ h2 ring) C)
    ⟨C, w, hBirth, rfl⟩



/-! The private forged-commit and forged-sweep fixtures are restated literally so this file does
not rely on private declarations. -/

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩

private def literalReach
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
      path := .bot
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

private def cellReach
    (p : R2.Cell 3 3 48)
    (m : R2Coherence.Mark) (t : TokenV3) : Cell 3 3 48 :=
  ⟨p, ⟨m, t⟩⟩

/-- Literal forged commit. -/
def commitProxyReach : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => cellReach (literalReach 0) .open .commit
  | 1 => cellReach (literalReach 1 .compare1) .open .none
  | _ => cellReach (literalReach 2) .open .none

/-- Literal forged sweep. -/
def sweepProxyReach : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => cellReach (literalReach 0 .compare1) .open .none
  | 1 => cellReach (literalReach 1) .closing .sweep
  | _ => cellReach (literalReach 2) .closing .none

/-- Source-level exclusion already established. -/
theorem commitProxyReach_not_phaseMainClear :
    ¬ PhaseMainClearV31 ring3 commitProxyReach := by
  decide +kernel

/-- Source-level exclusion already established. -/
theorem sweepProxyReach_not_phaseMainClear :
    ¬ PhaseMainClearV31 ring3 sweepProxyReach := by
  decide +kernel

/-- Conditional reachability verdict for the forged commit.  This becomes an unconditional
`¬ ReachableFromQuarantineV31 ...` exactly when `QuarantineSplitStepV31` is
proved; current source does not yet provide that theorem. -/
theorem commitProxyReach_not_reachable_of_split_step
    (hStep : QuarantineSplitStepV31
      (κ := 3) (τ := 48) h3 h23 ring3) :
    ¬ ReachableFromQuarantineV31
      (κ := 3) (τ := 48) h3 h23 ring3 commitProxyReach := by
  intro hReach
  have hSplit := reachable_split_of_step
    h3 h23 ring3 hStep commitProxyReach hReach
  exact commitProxyReach_not_phaseMainClear hSplit.2

/-- Conditional reachability verdict for the forged sweep. -/
theorem sweepProxyReach_not_reachable_of_split_step
    (hStep : QuarantineSplitStepV31
      (κ := 3) (τ := 48) h3 h23 ring3) :
    ¬ ReachableFromQuarantineV31
      (κ := 3) (τ := 48) h3 h23 ring3 sweepProxyReach := by
  intro hReach
  have hSplit := reachable_split_of_step
    h3 h23 ring3 hStep sweepProxyReach hReach
  exact sweepProxyReach_not_phaseMainClear hSplit.2



/-- Branch-local form of the remaining split-step work. -/
def QuarantineSplitBranchV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (b : BranchV3) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    QuarantineSplitV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b →
      QuarantineSplitV31 ring (stepV3 hψ h2 ring C e)

/-- Assemble the ten branch laws into the reachable-domain split closure. -/
theorem quarantineSplitStep_of_branches
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hSeek : QuarantineSplitBranchV31 (κ := κ) (τ := τ)
      hψ h2 ring .seek)
    (hSweep : QuarantineSplitBranchV31 (κ := κ) (τ := τ)
      hψ h2 ring .sweep)
    (hCommit : QuarantineSplitBranchV31 (κ := κ) (τ := τ)
      hψ h2 ring .commit)
    (hRelease : QuarantineSplitBranchV31 (κ := κ) (τ := τ)
      hψ h2 ring .release)
    (hScrubL : QuarantineSplitBranchV31 (κ := κ) (τ := τ)
      hψ h2 ring .scrubL)
    (hOpenR : QuarantineSplitBranchV31 (κ := κ) (τ := τ)
      hψ h2 ring .openR)
    (hSealed : QuarantineSplitBranchV31 (κ := κ) (τ := τ)
      hψ h2 ring .sealed)
    (hOpenHazard : QuarantineSplitBranchV31 (κ := κ) (τ := τ)
      hψ h2 ring .openHazard)
    (hOpenNoHazard : QuarantineSplitBranchV31 (κ := κ) (τ := τ)
      hψ h2 ring .openNoHazard)
    (hMixed : QuarantineSplitBranchV31 (κ := κ) (τ := τ)
      hψ h2 ring .mixed) :
    QuarantineSplitStepV31 (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hElection hSplit
  cases hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) with
  | seek => exact hSeek C e hElection hSplit hb
  | sweep => exact hSweep C e hElection hSplit hb
  | commit => exact hCommit C e hElection hSplit hb
  | release => exact hRelease C e hElection hSplit hb
  | scrubL => exact hScrubL C e hElection hSplit hb
  | openR => exact hOpenR C e hElection hSplit hb
  | sealed => exact hSealed C e hElection hSplit hb
  | openHazard => exact hOpenHazard C e hElection hSplit hb
  | openNoHazard => exact hOpenNoHazard C e hElection hSplit hb
  | mixed => exact hMixed C e hElection hSplit hb

/-!
Exact source census:

* `PhaseMainClearV31`: `.sweep` is proved by
  `R2CoherenceV31PhaseMainClear.phaseMainClear_sweep_step`.
  Still open as compiled branch lemmas: `.seek`, `.commit`, `.release`,
  `.scrubL`, `.openR`, `.sealed`, `.openHazard`, `.openNoHazard`, `.mixed`.
* `ControllerShapeStructuralV31`: defined, but no general
  branch-step theorem is proved.  Thus all ten structural branch halves remain open in
  the compiled source.

The locally easiest next branches are `seek`, `openHazard`, and `mixed`: their
selected arms are physical holds/control quarantine on admitted geometry and do
not create release/scrubL/openR obligations.  `sealed`, `commit`, `release`, and
`scrubL` move whole-group phase ownership and need the corresponding
`GroupOwnedClearV31` transport.  `openR` is delicate because it removes phase
ownership while reopening.  `openNoHazard` is also nontrivial because the
physical proposal must preserve any remote `OpenROwnerFreshV3` structural
obligation.

Therefore `ControllerSoundV3` is not closed by the results above alone.  The exact
accepted stronger route is `QuarantineSplitStepV31`; once that is proved,
`controllerSoundV3_of_split_step` above closes the real third conjunct of
`BirthQuarantineEntranceClosedBridgeV31V1`.
-/



end R2CoherenceV31QuarantineReach
