import Leader.Wu.ShortGap.CleanupSurfaceIntegration
import Leader.Wu.Protocol.RepairedAgentState

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace CleanupFinalContract

open PPLLExpiringComparisonRepair
open ShortGapCaptureCommitRows

variable {n psi kappa tau mu omega : Nat}

/-- Final finite carrier together with the already-physical capture controller. -/
structure FinalIntegratedAgentState
    (psi kappa tau mu omega : Nat) where
  core : PPLLFinalAgentState.FinalAgentState psi kappa tau mu omega
  capture : ShortGapCaptureCommitRows.CNode
  deriving DecidableEq

abbrev FinalConfig
    (n psi kappa tau mu omega : Nat) :=
  Fin n -> FinalIntegratedAgentState psi kappa tau mu omega

/-- Forget only the coordinates beyond the old cleanup carrier. -/
def toCleanupState
    (u : FinalIntegratedAgentState psi kappa tau mu omega) :
    ExpiringAgentState psi kappa tau :=
  PPLLFinalAgentState.FinalAgentState.toExpiring u.core

/-- Projection to the integrated carrier already audited in
`CleanupSurfaceIntegration`. -/
def toSurfaceState
    (u : FinalIntegratedAgentState psi kappa tau mu omega) :
    CleanupSurfaceIntegration.IntegratedAgentState psi kappa tau :=
  ⟨toCleanupState u, u.capture⟩

def toCleanupConfig
    (C : FinalConfig n psi kappa tau mu omega) :
    CleanupOwnedEntry.Config n psi kappa tau :=
  fun i => toCleanupState (C i)

def toSurfaceConfig
    (C : FinalConfig n psi kappa tau mu omega) :
    CleanupSurfaceIntegration.Config n psi kappa tau :=
  fun i => toSurfaceState (C i)

/-- Replace the shared expiration coordinate after the cleanup row while
leaving move fuel, writer age, bootstrap and writer-reset controls untouched. -/
def replaceExpiring
    (s : PPLLFinalAgentState.FinalAgentState psi kappa tau mu omega)
    (u : ExpiringAgentState psi kappa tau) :
    PPLLFinalAgentState.FinalAgentState psi kappa tau mu omega :=
  { s with
    core := { s.core with core := u.core }
    stall := u.stall }

@[simp] theorem toExpiring_replaceExpiring
    (s : PPLLFinalAgentState.FinalAgentState psi kappa tau mu omega)
    (u : ExpiringAgentState psi kappa tau) :
    PPLLFinalAgentState.FinalAgentState.toExpiring
        (replaceExpiring s u) = u := by
  cases u
  rfl

/-- Lift one output of the already-integrated cleanup/capture row back to the
final carrier, preserving all final-only coordinates. -/
def mergeSurfaceOutput
    (old : FinalIntegratedAgentState psi kappa tau mu omega)
    (out : CleanupSurfaceIntegration.IntegratedAgentState psi kappa tau) :
    FinalIntegratedAgentState psi kappa tau mu omega :=
  ⟨replaceExpiring old.core out.core, out.capture⟩

@[simp] theorem toSurfaceState_mergeSurfaceOutput
    (old : FinalIntegratedAgentState psi kappa tau mu omega)
    (out : CleanupSurfaceIntegration.IntegratedAgentState psi kappa tau) :
    toSurfaceState (mergeSurfaceOutput old out) = out := by
  cases out
  rfl

private def surfacePair
    (q : FinalIntegratedAgentState psi kappa tau mu omega ×
      FinalIntegratedAgentState psi kappa tau mu omega) :=
  (toSurfaceState q.1, toSurfaceState q.2)

private def cleanupPair
    (q : FinalIntegratedAgentState psi kappa tau mu omega ×
      FinalIntegratedAgentState psi kappa tau mu omega) :=
  (toCleanupState q.1, toCleanupState q.2)

private def capturePair
    (q : FinalIntegratedAgentState psi kappa tau mu omega ×
      FinalIntegratedAgentState psi kappa tau mu omega) :=
  (q.1.capture, q.2.capture)

/-- Final integrated local row.  The physical cleanup and capture coordinates
execute the accepted product row; the final-only coordinates are framed. -/
def literalRow
    (hpsi : 0 < psi)
    (l r : FinalIntegratedAgentState psi kappa tau mu omega) :
    FinalIntegratedAgentState psi kappa tau mu omega ×
      FinalIntegratedAgentState psi kappa tau mu omega :=
  let q := CleanupSurfaceIntegration.literalRow hpsi
    (toSurfaceState l) (toSurfaceState r)
  (mergeSurfaceOutput l q.1, mergeSurfaceOutput r q.2)

/-- Exact refinement to the already-proved integrated row. -/
theorem literalRow_surface_projection
    (hpsi : 0 < psi)
    (l r : FinalIntegratedAgentState psi kappa tau mu omega) :
    surfacePair (literalRow hpsi l r) =
      CleanupSurfaceIntegration.literalRow hpsi
        (toSurfaceState l) (toSurfaceState r) := by
  unfold surfacePair literalRow
  dsimp only
  rw [toSurfaceState_mergeSurfaceOutput,
    toSurfaceState_mergeSurfaceOutput]

/-- The old cleanup row is the first projection, by composition with
`CleanupSurfaceIntegration.literalRow_base_projection`. -/
theorem literalRow_cleanup_projection
    (hpsi : 0 < psi)
    (l r : FinalIntegratedAgentState psi kappa tau mu omega) :
    cleanupPair (literalRow hpsi l r) =
      CleanupSurfaceIntegration.baseRow hpsi
        (toCleanupState l) (toCleanupState r) := by
  have hs := congrArg
    (fun q :
      CleanupSurfaceIntegration.IntegratedAgentState psi kappa tau ×
        CleanupSurfaceIntegration.IntegratedAgentState psi kappa tau =>
      (q.1.core, q.2.core))
    (literalRow_surface_projection hpsi l r)
  change cleanupPair (literalRow hpsi l r) =
    ((CleanupSurfaceIntegration.literalRow hpsi
      (toSurfaceState l) (toSurfaceState r)).1.core,
     (CleanupSurfaceIntegration.literalRow hpsi
      (toSurfaceState l) (toSurfaceState r)).2.core) at hs
  have hb := CleanupSurfaceIntegration.literalRow_base_projection
    hpsi (toSurfaceState l) (toSurfaceState r)
  change
    ((CleanupSurfaceIntegration.literalRow hpsi
      (toSurfaceState l) (toSurfaceState r)).1.core,
     (CleanupSurfaceIntegration.literalRow hpsi
      (toSurfaceState l) (toSurfaceState r)).2.core) =
      CleanupSurfaceIntegration.baseRow hpsi
        (toCleanupState l) (toCleanupState r) at hb
  exact hs.trans hb

/-- The full short-gap commit dispatcher is likewise the second projection. -/
theorem literalRow_commit_projection
    (hpsi : 0 < psi)
    (l r : FinalIntegratedAgentState psi kappa tau mu omega) :
    capturePair (literalRow hpsi l r) =
      ShortGapCaptureCommitRows.commitRow l.capture r.capture := by
  have hs := congrArg
    (fun q :
      CleanupSurfaceIntegration.IntegratedAgentState psi kappa tau ×
        CleanupSurfaceIntegration.IntegratedAgentState psi kappa tau =>
      (q.1.capture, q.2.capture))
    (literalRow_surface_projection hpsi l r)
  change capturePair (literalRow hpsi l r) =
    ((CleanupSurfaceIntegration.literalRow hpsi
      (toSurfaceState l) (toSurfaceState r)).1.capture,
     (CleanupSurfaceIntegration.literalRow hpsi
      (toSurfaceState l) (toSurfaceState r)).2.capture) at hs
  have hc := CleanupSurfaceIntegration.literalRow_commit_projection
    hpsi (toSurfaceState l) (toSurfaceState r)
  change
    ((CleanupSurfaceIntegration.literalRow hpsi
      (toSurfaceState l) (toSurfaceState r)).1.capture,
     (CleanupSurfaceIntegration.literalRow hpsi
      (toSurfaceState l) (toSurfaceState r)).2.capture) =
      ShortGapCaptureCommitRows.commitRow l.capture r.capture at hc
  exact hs.trans hc

/-- Ring lift of the final integrated row. -/
def literalStep
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FinalConfig n psi kappa tau mu omega) (e : Fin n) :
    FinalConfig n psi kappa tau mu omega :=
  let j := ring.rightNeighbor e
  let q := literalRow hpsi (C e) (C j)
  fun i => if i = e then q.1 else if i = j then q.2 else C i

/-- Small scheduler skeleton used to keep the heavy local row opaque. -/
private def stepFunction {α : Type}
    (ring : DirectedRing n) (row : α -> α -> α × α)
    (C : Fin n -> α) (e : Fin n) : Fin n -> α :=
  let j := ring.rightNeighbor e
  let q := row (C e) (C j)
  fun i => if i = e then q.1 else if i = j then q.2 else C i

private theorem protocolStep_eq_stepFunction
    (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e : Fin n) :
    P.step ring C e = stepFunction ring P.transition C e := by
  funext i
  unfold PopulationProtocol.step stepFunction
  generalize hq :
    P.transition (C e) (C (ring.rightNeighbor e)) = q
  cases q
  rfl

private theorem stepFunction_projection
    {α β : Type}
    (ring : DirectedRing n)
    (rowA : α -> α -> α × α)
    (rowB : β -> β -> β × β)
    (project : α -> β)
    (C : Fin n -> α) (e : Fin n)
    (hrow : forall l r,
      (project (rowA l r).1, project (rowA l r).2) =
        rowB (project l) (project r)) :
    (fun i => project (stepFunction ring rowA C e i)) =
      stepFunction ring rowB (fun i => project (C i)) e := by
  let q := rowA (C e) (C (ring.rightNeighbor e))
  let s := rowB (project (C e))
    (project (C (ring.rightNeighbor e)))
  have hq : (project q.1, project q.2) = s := by
    simpa [q, s] using hrow (C e) (C (ring.rightNeighbor e))
  have hL : project q.1 = s.1 := congrArg Prod.fst hq
  have hR : project q.2 = s.2 := congrArg Prod.snd hq
  funext i
  change project
      (if i = e then q.1
       else if i = ring.rightNeighbor e then q.2 else C i) =
    (if i = e then s.1
     else if i = ring.rightNeighbor e then s.2 else project (C i))
  by_cases hi : i = e
  · rw [if_pos hi, if_pos hi]; exact hL
  · by_cases hj : i = ring.rightNeighbor e
    · simp only [if_neg hi, if_pos hj]; exact hR
    · simp [hi, hj]

private theorem literalStep_eq_stepFunction
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FinalConfig n psi kappa tau mu omega) (e : Fin n) :
    literalStep hpsi ring C e =
      stepFunction ring (literalRow hpsi) C e := by
  rfl

private theorem surfaceLiteralStep_eq_stepFunction
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : CleanupSurfaceIntegration.Config n psi kappa tau) (e : Fin n) :
    CleanupSurfaceIntegration.literalStep hpsi ring C e =
      stepFunction ring (CleanupSurfaceIntegration.literalRow hpsi) C e := by
  rfl

private theorem cleanupLiteralStep_eq_stepFunction
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : CleanupOwnedEntry.Config n psi kappa tau) (e : Fin n) :
    CleanupOwnedEntry.literalStep hpsi ring C e =
      stepFunction ring (CleanupSurfaceIntegration.baseRow hpsi) C e := by
  unfold CleanupOwnedEntry.literalStep
  exact
    (protocolStep_eq_stepFunction
      (PPLLExpiringComparisonRepair.expiringProtocol hpsi kappa tau)
      ring C e)

/-- Scheduler-level refinement to `CleanupSurfaceIntegration.literalStep`. -/
theorem literalStep_surface_projection
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FinalConfig n psi kappa tau mu omega) (e : Fin n) :
    toSurfaceConfig (literalStep hpsi ring C e) =
      CleanupSurfaceIntegration.literalStep hpsi ring
        (toSurfaceConfig C) e := by
  rw [literalStep_eq_stepFunction hpsi ring C e,
    surfaceLiteralStep_eq_stepFunction hpsi ring (toSurfaceConfig C) e]
  exact
    (stepFunction_projection ring
      (literalRow hpsi)
      (CleanupSurfaceIntegration.literalRow hpsi)
      toSurfaceState C e
      (fun l r => by
        simpa only [surfacePair] using
          literalRow_surface_projection hpsi l r))

/-- Scheduler-level refinement all the way to the old cleanup row. -/
theorem literalStep_cleanup_projection
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FinalConfig n psi kappa tau mu omega) (e : Fin n) :
    toCleanupConfig (literalStep hpsi ring C e) =
      CleanupOwnedEntry.literalStep hpsi ring (toCleanupConfig C) e := by
  rw [literalStep_eq_stepFunction hpsi ring C e,
    cleanupLiteralStep_eq_stepFunction hpsi ring (toCleanupConfig C) e]
  exact
    (stepFunction_projection ring
      (literalRow hpsi)
      (CleanupSurfaceIntegration.baseRow hpsi)
      toCleanupState C e
      (fun l r => by
        simpa only [cleanupPair] using
          literalRow_cleanup_projection hpsi l r))

/-- Both projections required of the final physical row. -/
def FinalIntegratedRowRefinement
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  (forall l r : FinalIntegratedAgentState psi kappa tau mu omega,
    surfacePair (literalRow hpsi l r) =
      CleanupSurfaceIntegration.literalRow hpsi
        (toSurfaceState l) (toSurfaceState r)) /\
  (forall C : FinalConfig n psi kappa tau mu omega,
    forall e : Fin n,
      toCleanupConfig (literalStep hpsi ring C e) =
        CleanupOwnedEntry.literalStep hpsi ring (toCleanupConfig C) e)

theorem finalIntegratedRowRefinement
    (hpsi : 0 < psi) (ring : DirectedRing n) :
    FinalIntegratedRowRefinement
      (kappa := kappa) (tau := tau)
      (mu := mu) (omega := omega) hpsi ring := by
  refine And.intro ?_ ?_
  · intro l r
    exact literalRow_surface_projection hpsi l r
  · intro C e
    exact literalStep_cleanup_projection hpsi ring C e

/-- Final cleanup contract: keep the already-proved legacy surface contract and
certify that the actual final integrated row refines its literal rows. -/
def cleanupFinalContract
    (A : CleanupOwnedEntry.CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n) : Prop :=
  CleanupOwnedEntry.cleanupOwnedEntryContract A hpsi ring /\
    FinalIntegratedRowRefinement
      (kappa := kappa) (tau := tau)
      (mu := mu) (omega := omega) hpsi ring

/-- Every legacy clause transfers unchanged. -/
theorem cleanupFinalContract_transfer
    (A : CleanupOwnedEntry.CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (h : cleanupFinalContract
      (mu := mu) (omega := omega) A hpsi ring) :
    CleanupOwnedEntry.cleanupOwnedEntryContract A hpsi ring :=
  h.1

/-- Conversely, row refinement is unconditional, so the final contract is
exactly equivalent to the old contract on its projected cleanup surface. -/
theorem cleanupFinalContract_iff_legacy
    (A : CleanupOwnedEntry.CleanupSurface n psi kappa tau)
    (hpsi : 0 < psi) (ring : DirectedRing n) :
    cleanupFinalContract (mu := mu) (omega := omega) A hpsi ring <->
      CleanupOwnedEntry.cleanupOwnedEntryContract A hpsi ring := by
  constructor
  · intro h
    exact cleanupFinalContract_transfer A hpsi ring h
  · intro h
    exact ⟨h, finalIntegratedRowRefinement
      (kappa := kappa) (tau := tau)
      (mu := mu) (omega := omega) hpsi ring⟩

/-! The legacy clauses transfer, but the physical capture surface itself cannot
be reconstructed from the erased cleanup state.  This is why the contract above
retains the legacy `CleanupSurface` witness rather than synthesizing one. -/

private def idleCapture : ShortGapCaptureCommitRows.CNode :=
  ShortGapCaptureCommitRows.embed ShortGapCaptureCommitRows.emptyRaw false

private def commitCapture : ShortGapCaptureCommitRows.CNode :=
  { idleCapture with carrier := .commit }

/-- Smallest closed witness: equal legacy/raw projection, different live-carrier
observation.  This is a descent obstruction, not a failed cleanup clause. -/
theorem capture_surface_does_not_descend :
    idleCapture.raw = commitCapture.raw /\
      CleanupSurfaceIntegration.tagLiveCarrier
          (CleanupSurfaceIntegration.surfaceTag idleCapture) = false /\
      CleanupSurfaceIntegration.tagLiveCarrier
          (CleanupSurfaceIntegration.surfaceTag commitCapture) = true := by
  decide

/-- State count of `FinalAgentState × CNode`. -/
def finalIntegratedStateCount
    (psi kappa tau mu omega : Nat) : Nat :=
  CleanupSurfaceIntegration.integratedStateCount
    (PPLLFinalAgentState.finalAgentState
      psi kappa tau mu omega).values.length

/-- Exact final multiplier: no extra cleanup-surface coordinate is counted. -/
theorem finalIntegratedStateCount_eq
    (psi kappa tau mu omega : Nat) :
    finalIntegratedStateCount psi kappa tau mu omega =
      (PPLLFinalAgentState.finalAgentState
        psi kappa tau mu omega).values.length * 39960 := by
  exact CleanupSurfaceIntegration.integratedStateCount_eq _

/-- Any existing upper bound on the final base carrier inherits the same
constant multiplier. -/
theorem finalIntegratedStateCount_le
    (psi kappa tau mu omega bound : Nat)
    (h : (PPLLFinalAgentState.finalAgentState
      psi kappa tau mu omega).values.length <= bound) :
    finalIntegratedStateCount psi kappa tau mu omega <=
      bound * 39960 := by
  unfold finalIntegratedStateCount
  exact CleanupSurfaceIntegration.integratedStateCount_mono _ _ h

end CleanupFinalContract

#print axioms CleanupFinalContract.toExpiring_replaceExpiring
#print axioms CleanupFinalContract.literalRow_surface_projection
#print axioms CleanupFinalContract.literalRow_cleanup_projection
#print axioms CleanupFinalContract.literalRow_commit_projection
#print axioms CleanupFinalContract.literalStep_surface_projection
#print axioms CleanupFinalContract.literalStep_cleanup_projection
#print axioms CleanupFinalContract.finalIntegratedRowRefinement
#print axioms CleanupFinalContract.cleanupFinalContract_transfer
#print axioms CleanupFinalContract.cleanupFinalContract_iff_legacy
#print axioms CleanupFinalContract.capture_surface_does_not_descend
#print axioms CleanupFinalContract.finalIntegratedStateCount_eq
#print axioms CleanupFinalContract.finalIntegratedStateCount_le
