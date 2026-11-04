import Leader.Wu.Coherence.RecoveryProxyIncomplete


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ShapeCommit


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceV31Drift
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31ProxyComplete


variable {n ψ κ τ : Nat}


/-- Repair candidate: keep every accepted V31 shape obligation and add
one obligation for a currently live commit owner. -/
def ControllerShapeV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ControllerShapeV3 ring C ∧
    ∀ i : Fin n, (C i).ctl.tok = .commit →
      GroupMainClearV3 ring C i


instance controllerShapeV32Decidable
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    Decidable (ControllerShapeV32 ring C) := by
  unfold ControllerShapeV32
  infer_instance


/-- Executable current-state proxy corresponding to the strengthened shape. -/
def RecoveryProxyV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ControllerShapeV32 ring C ∧ CoherentPrefixesV3 ring C


/-- Future-closed version of the strengthened shape. -/
def ControllerSoundV32
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) : Prop :=
  ∀ w : List (Fin n),
    ControllerShapeV32 ring
      (w.foldl (stepV3 hψ h2 ring) C)


/-- Recovered state using V32 shape rather than the accepted V31 shape. -/
def RecoveredV32
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) : Prop :=
  AdmittedPostBirthGeometryV3 hψ ring C ∧
    CoherentPrefixesV3 ring C ∧
    ControllerSoundV32 hψ h2 ring C


/-- The proxy-completeness bridge we would need after the commit repair. -/
def RecoveryProxyCompleteV32
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    AdmittedPostBirthGeometryV3 hψ ring C →
    RecoveryProxyV32 ring C →
    RecoveredV32 hψ h2 ring C


/-- Exact one-step closure leaf for the strengthened shape. -/
def ControllerShapeStepClosedV32
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    AdmittedPostBirthGeometryV3 hψ ring C →
    ControllerShapeV32 ring C →
    CoherentPrefixesV3 ring C →
    ControllerShapeV32 ring (stepV3 hψ h2 ring C e)

/-- Any live commit over a non-main-clear group is rejected by V32 shape.
This is the abstract form of "the forged-commit `commitProxy` is excluded". -/
theorem live_commit_dirty_group_not_shapeV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n)
    (hCommit : (C i).ctl.tok = .commit)
    (hDirty : ¬ GroupMainClearV3 ring C i) :
    ¬ ControllerShapeV32 ring C := by
  intro hShape
  exact hDirty (hShape.2 i hCommit)


/-- Existing release shape already pre-pays the owner group before the
release branch can fall back to commit. -/
theorem release_owner_groupMainClear_of_shapeV32
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n)
    (hShape : ControllerShapeV32 ring C)
    (hRelease : (C i).ctl.tok = .release) :
    GroupMainClearV3 ring C i := by
  exact (hShape.1.2.1 i hRelease).2


/-- The terminal sweep arm creates a fresh commit at the responder. -/
theorem sweepStageV3_terminal_creates_commit
    (l r : Cell ψ κ τ)
    (hSucc : successorB l r = true)
    (hTerminal : atTerminalB r = true) :
    (sweepStageV3 l r).2.ctl.tok = .commit := by
  simp [sweepStageV3, hSucc, hTerminal, setControl, clearMain]


/-- The nonquiet interior release fallback creates a fresh commit at its
initiator, but it is control-only: no physical field is changed on that arm. -/
theorem releaseStageV3_nonquiet_creates_commit
    (l r : Cell ψ κ τ)
    (hSucc : successorB l r = true)
    (hQuiet : writerQuiet r = false)
    (hRoot : atRootB l = false) :
    (releaseStageV3 l r).1.ctl.tok = .commit ∧
      (releaseStageV3 l r).1.phys = l.phys ∧
      (releaseStageV3 l r).2.phys = r.phys := by
  simp [releaseStageV3, hSucc, hQuiet, hRoot, setControl]


/-- Interior commit service propagates an already-live commit one cell left;
it is not a fresh commit from a commit-free pair. -/
theorem commitStageV3_interior_propagates_commit
    (l r : Cell ψ κ τ)
    (hr : atRootB r = false)
    (hl : atRootB l = false) :
    (commitStageV3 l r).1.ctl.tok = .commit := by
  simp [commitStageV3, hr, hl, setControl, clearMain]


/-
Direct branch audit for creation/propagation of `.commit`:


* seek         : no commit output; creates/moves `.sweep`/`.seek` only.
* sweep        : YES.  A successor service with terminal responder creates
                 `.commit` at the responder.  V32 has no sweep-prefix premise;
                 this is the failing branch certified below.
* commit       : may propagate an already-live `.commit` to the left on the
                 interior arm.  The incoming responder commit is covered by
                 V32; admitted non-root geometry keeps the propagated owner in
                 the same group, and `clearMain` only removes main material.
* release      : YES.  Nonquiet successor + nonroot initiator creates commit
                 at the initiator.  Safe with respect to the new clause under
                 V32 because old ControllerShapeV3 already gives
                 GroupMainClearV3 for every live release owner, and this arm is
                 physically inert (proved above).
* scrubL       : no commit output; only scrubL/openR/seek/none.
* openR        : no commit output; only openR/seek/open-none.
* sealed       : no commit output; its active handoff creates `.release`.
* openHazard   : no commit output; quarantine creates `.seek`.
* openNoHazard : no direct commit output; it installs the physical proposal.
                 A separate full preservation proof would still have to check
                 remote pre-existing commit groups against this physical write,
                 but it is not a fresh-commit creator.
* mixed        : no commit output; admitted normalization creates `.seek`.


Thus the first direct predecessor hole in the proposed clause is `.sweep`.
-/

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩


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


private def cell
    (p : R2.Cell 3 3 48)
    (m : R2Coherence.Mark) (t : TokenV3) : Cell 3 3 48 :=
  ⟨p, ⟨m, t⟩⟩


/-- V32-proxy-good forged sweep.  The dirty label-zero cell is behind the
sweep front and therefore survives the terminal handoff. -/
private def sweepProxy : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => cell (literal 0 .compare1) .open .none
  | 1 => cell (literal 1) .closing .sweep
  | _ => cell (literal 2) .closing .none


/-- Edge 1 -> 2 services the terminal sweep. -/
private def sweepAfter : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 sweepProxy 1


theorem sweepProxy_geometry :
    AdmittedPostBirthGeometryV3 h3 ring3 sweepProxy := by
  decide +kernel


theorem sweepProxy_shapeV32 :
    ControllerShapeV32 ring3 sweepProxy := by
  decide +kernel


theorem sweepProxy_coherent :
    CoherentPrefixesV3 ring3 sweepProxy := by
  decide +kernel


theorem sweepProxy_proxyV32 :
    RecoveryProxyV32 ring3 sweepProxy := by
  exact ⟨sweepProxy_shapeV32, sweepProxy_coherent⟩


theorem sweepProxy_branch :
    branchAtV3 h3 h23
      (sweepProxy 1) (sweepProxy (ring3.rightNeighbor 1)) = .sweep := by
  decide +kernel


/-- The legal terminal sweep installs the new commit at label 2. -/
theorem sweepAfter_terminal_commit :
    (sweepAfter 2).ctl.tok = .commit := by
  decide +kernel


/-- The remote label-zero `compare1` is not touched by edge 1 -> 2. -/
theorem sweepAfter_remote_dirty :
    ¬ MainClearV3 (sweepAfter 0) := by
  decide +kernel


/-- Therefore the freshly-created commit owner does not have a clear group. -/
theorem sweepAfter_commit_group_not_clear :
    ¬ GroupMainClearV3 ring3 sweepAfter 2 := by
  decide +kernel


/-- The new commit clause is lost in one legal sweep step. -/
theorem sweepAfter_not_shapeV32 :
    ¬ ControllerShapeV32 ring3 sweepAfter := by
  exact live_commit_dirty_group_not_shapeV32
    ring3 sweepAfter 2
    sweepAfter_terminal_commit sweepAfter_commit_group_not_clear


/-- Exact branch-local preservation statement is false already for `.sweep`. -/
theorem sweep_shapeV32_preservation_false :
    ¬ (∀ (C : FC 3 3 3 48) (e : Fin 3),
        AdmittedPostBirthGeometryV3 h3 ring3 C →
        ControllerShapeV32 ring3 C →
        CoherentPrefixesV3 ring3 C →
        branchAtV3 h3 h23 (C e) (C (ring3.rightNeighbor e)) = .sweep →
        ControllerShapeV32 ring3 (stepV3 h3 h23 ring3 C e)) := by
  intro h
  exact sweepAfter_not_shapeV32
    (h sweepProxy 1 sweepProxy_geometry sweepProxy_shapeV32
      sweepProxy_coherent sweepProxy_branch)


/-- Hence the unrestricted one-step V32 shape closure leaf is false. -/
theorem controllerShapeStepClosedV32_false :
    ¬ ControllerShapeStepClosedV32
      (κ := 3) (τ := 48) h3 h23 ring3 := by
  intro h
  exact sweepAfter_not_shapeV32
    (h sweepProxy 1 sweepProxy_geometry
      sweepProxy_shapeV32 sweepProxy_coherent)


/-- The one-letter word `[1]` witnesses failure of V32 controller soundness. -/
theorem sweepProxy_not_soundV32 :
    ¬ ControllerSoundV32 h3 h23 ring3 sweepProxy := by
  intro hSound
  apply sweepAfter_not_shapeV32
  simpa [sweepAfter] using hSound [1]


/-- Admitted geometry and V32 current proxy still do not imply V32 recovery. -/
theorem sweepProxy_not_recoveredV32 :
    ¬ RecoveredV32 h3 h23 ring3 sweepProxy := by
  intro h
  exact sweepProxy_not_soundV32 h.2.2


/-- Verdict: commit-only proxy completeness is false. -/
theorem recoveryProxyCompleteV32_false :
    ¬ RecoveryProxyCompleteV32
      (κ := 3) (τ := 48) h3 h23 ring3 := by
  intro hBridge
  have hRecovered :=
    hBridge sweepProxy sweepProxy_geometry sweepProxy_proxyV32
  exact sweepProxy_not_recoveredV32 hRecovered


end R2CoherenceV31ShapeCommit
