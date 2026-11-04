import Leader.Wu.Coherence.ReachableSeekStrong
import Leader.Wu.Coherence.ReachableSoundInstances

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableSeek3

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard3

variable {n ψ κ τ : Nat}

/-- Root responder: the incoming seek is consumed into a live sweep. -/
theorem seekStageV3_right_root_seek3
    (l r : Cell ψ κ τ) (hr : atRootB r = true) :
    seekStageV3 l r = (l, setControl r .closing .sweep) := by
  simp [seekStageV3, hr]

/-- Root initiator: the incoming seek is consumed into a live left sweep. -/
theorem seekStageV3_left_root_seek3
    (l r : Cell ψ κ τ)
    (hr : atRootB r = false) (hl : atRootB l = true) :
    seekStageV3 l r =
      (setControl l .closing .sweep, setControl r .closing .none) := by
  simp [seekStageV3, hr, hl]

/-- Nonroot/nonroot is the obstruction for S: SEEK moves, rather than
consumes, the token. -/
theorem seekStageV3_nonroot_nonroot_seek3
    (l r : Cell ψ κ τ)
    (hr : atRootB r = false) (hl : atRootB l = false) :
    seekStageV3 l r =
      (setControl l .closing .seek, setControl r .closing .none) := by
  simp [seekStageV3, hr, hl]

/-- At a root the strict swept-prefix footprint is empty. -/
theorem sweptOwnedFootprint_empty_at_root_seek3
    (ring : DirectedRing n) (C : FC n ψ κ τ) (sweep p : Fin n)
    (hr : atRootB (C sweep) = true) :
    ¬ InSweptOwnedFootprintV31 ring C sweep p := by
  rintro ⟨k, _hk⟩
  have hz : (raw (C sweep)).label.val = 0 := by
    simpa [atRootB] using hr
  have hk0 : k.val < 0 := by
    simpa only [hz] using k.isLt
  omega

/-- But strong R2 uses the wide-read footprint, not the strict swept prefix:
distance zero already puts the sweep front in that read. -/
theorem sweepFront_in_wideRead_seek3
    (ring : DirectedRing n) (C : FC n ψ κ τ) (sweep : Fin n) :
    InSweepWideReadV31 ring C sweep sweep := by
  right
  have hpos : 0 < ψ - (raw (C sweep)).label.val :=
    Nat.sub_pos_of_lt (raw (C sweep)).label.isLt
  let d0 : Fin (ψ - (raw (C sweep)).label.val) := ⟨0, hpos⟩
  refine ⟨d0, ?_⟩
  apply Fin.ext
  simp [R2Coherence.fwd, d0, Nat.mod_eq_of_lt sweep.isLt]

/-!
STOP.

The first common source clause needed to finish both requested declarations is
already named in `R2CoherenceV31ReachableFreshSeek`:

  `PendingOpenRFootprintInScrubGroupV31 ring C`.

For S it turns every pending-owner footprint hit into P5 main-clear, while
non-hits use the second disjunct of `SweepOpenRSafeAtV31`.  For the fresh-sweep
strong-R2 clause, the same P5 group supplies `PhaseOwnedV31` directly.

Current main does not prove its reachable form from the installed birth
contract: `ReachableFreshSeek2` reduces it to `PsiWindowLinearReachableV31`,
and `ReachableRootSpacing` identifies the missing base as
`BirthRootSpacingV31`; the weaker local route in `ReachableRootSpacing2` still
has the terminal-RELEASE new-owner anchoring gap.  Therefore declaring
`seekSPreservationV31` or `seekStrongR2PreservationV31` here would hide an
unproved upstream geometric assumption, contrary to the request not to add
residuals.
-/

end R2CoherenceV31ReachableSeek3
