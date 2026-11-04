import Leader.Wu.WallSweep.ClockwiseRetryScheduler
import Leader.Wu.Safety.SafeConfig

/-!
# Unshielded unique-leader retry boundary

The binary scheduler is abstract over its field invariant.  This module states
the exact source-covered retry boundary for the corrected protocol and closes
the one-time deletion-drain interface.  The remaining obligation is the
per-attempt seed/handoff/collision preservation and the zero-rank full pass.
-/

namespace PPLLWallSweepUnshieldedRetry

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLWallSweepRepair
  PPLLWallSweepFiniteCleanup PPLLWallSweepNormalResetContract
  PPLLWallSweepPreCheckResetRepair PPLLWallSweepPreCheckResetContracts
  PPLLWallSweepEchoRank PPLLWallSweepClockwiseScheduler
  PPLLNoCheckBirthConditionTwoPhysical

variable {n psi kappa tau : Nat}

/-- Paper-faithful retry geometry: the designated label-zero leader is unique,
and every barrier enters a leader.  The closing predecessor-to-leader edge may
therefore be a nonfree barrier when `psi` does not divide `n`. -/
structure RootedRetryGeometry
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop where
  leader_alive : (C leader).core.erase.core.leader = true
  leader_zero : (C leader).core.erase.core.label = ⟨0, hpsi⟩
  unique_leader : ∀ i, i ≠ leader →
    (C i).core.erase.core.leader = false
  no_free_barrier : noFreeBarrier hpsi ring
    (fun i => (C i).core.erase.core)

/-- Non-wrap successor alignment derived from the rooted paper geometry. -/
theorem RootedRetryGeometry.successor_label_of_right_ne
    {hpsi : psi > 0} {ring : DirectedRing n} {leader : Fin n}
    {C : EConfig n psi kappa tau}
    (h : RootedRetryGeometry hpsi ring leader C)
    (i : Fin n) (hright : ring.rightNeighbor i ≠ leader) :
    (C (ring.rightNeighbor i)).core.erase.core.label =
      ⟨((C i).core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := by
  apply successor_label_of_noFreeBarrier_of_right_not_leader
    hpsi ring (fun j => (C j).core.erase.core) h.no_free_barrier i
  intro hleader
  change (C (ring.rightNeighbor i)).core.erase.core.leader = true at hleader
  have hfollower := h.unique_leader (ring.rightNeighbor i) hright
  rw [hfollower] at hleader
  simp at hleader

/-- Rooted unshielded boundary valid for arbitrary positive ring size and
label modulus. -/
structure RootedUnshieldedRetrySeed
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop
    extends RootedRetryGeometry hpsi ring leader C where
  leader_unshielded : (C leader).core.erase.core.shield = false
  bullets_zero : ∀ i,
    (C i).core.erase.core.bullet = ⟨0, by omega⟩
  leader_signal_zero :
    (C leader).core.erase.core.signal_B = ⟨0, by omega⟩

/-- Strong cyclic sublane used by the existing shield scheduler.  Its final
field is strictly stronger than the paper stable-ID geometry and implies
`psi ∣ n`; it is retained only until the closing-edge split is connected. -/
structure UnshieldedRetrySeed
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop
    extends RootedUnshieldedRetrySeed hpsi ring leader C where
  stable_labels : ∀ i,
    (C (ring.rightNeighbor i)).core.erase.core.label =
      ⟨((C i).core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩

/-- The existing cyclic retry seed is available only in the divisible branch. -/
theorem UnshieldedRetrySeed.dvd
    {hpsi : psi > 0} {ring : DirectedRing n} {leader : Fin n}
    {C : EConfig n psi kappa tau}
    (h : UnshieldedRetrySeed hpsi ring leader C) :
    psi ∣ n :=
  dvd_of_all_successor_labels (ψ := psi) (n := n) hpsi ring
    (fun i => (C i).core.erase.core) h.stable_labels

/-- Restart boundary: the source fields plus deletion freedom. -/
structure RootedClockwiseRetryReady
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop
    extends RootedUnshieldedRetrySeed hpsi ring leader C where
  no_active : NoActiveDeletion C

/-- Strong divisible-sublane restart boundary. -/
structure ClockwiseRetryReady
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop
    extends UnshieldedRetrySeed hpsi ring leader C where
  no_active : NoActiveDeletion C

/-- Honest endpoint of the zero-rank full pass.  The leader signal is omitted:
the final wrap may set it to one, and the schedule stops before firing. -/
structure ClockwiseRetryDone
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop where
  stable_labels : ∀ i,
    (C (ring.rightNeighbor i)).core.erase.core.label =
      ⟨((C i).core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩
  leader_alive : (C leader).core.erase.core.leader = true
  leader_zero : (C leader).core.erase.core.label = ⟨0, hpsi⟩
  unique_leader : ∀ i, i ≠ leader →
    (C i).core.erase.core.leader = false
  leader_unshielded : (C leader).core.erase.core.shield = false
  bullets_zero : ∀ i,
    (C i).core.erase.core.bullet = ⟨0, by omega⟩
  comparison_neutral : ∀ i, ComparisonNeutral (C i).core.erase.core

/-- Sharp zero-pass endpoint used by the terminal shield step.  The wrap has
returned the propagated absence signal and reset token to the designated
leader; all followers have already relinquished reset.  Follower echoes are
intentionally unrestricted because terminal crossings may recreate them
behind the moving frontier. -/
structure ClockwiseRetryDoneExact
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop
    extends ClockwiseRetryDone hpsi ring leader C where
  leader_signal_one :
    (C leader).core.erase.core.signal_B = ⟨1, by omega⟩
  leader_reset_true :
    (C leader).core.erase.core.reset_cmd = true
  follower_reset_false : ∀ i, i ≠ leader →
    (C i).core.erase.core.reset_cmd = false
  leader_echo_false :
    (C leader).core.erase.core.echo = false

/-- Exact zero-pass endpoint for the rooted nondivisible lane.  The closing
barrier returns the reset token but blocks the absence signal, so the leader
remains signal-zero and unshielded while every comparison carrier is neutral. -/
structure RootedClockwiseRetryDoneExact
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop
    extends RootedUnshieldedRetrySeed hpsi ring leader C where
  comparison_neutral : ∀ i, ComparisonNeutral (C i).core.erase.core
  leader_reset_true :
    (C leader).core.erase.core.reset_cmd = true
  follower_reset_false : ∀ i, i ≠ leader →
    (C i).core.erase.core.reset_cmd = false
  leader_echo_false :
    (C leader).core.erase.core.echo = false

/-- Exact zero-pass endpoint for the separately named responder-leader signal
sink repair.  Unlike the source Algorithm-15 endpoint above, the closing edge
has delivered the returning absence signal to the designated leader. -/
structure RootedLeaderSinkRetryDoneExact
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop
    extends RootedRetryGeometry hpsi ring leader C where
  leader_unshielded : (C leader).core.erase.core.shield = false
  bullets_zero : ∀ i,
    (C i).core.erase.core.bullet = ⟨0, by omega⟩
  comparison_neutral : ∀ i, ComparisonNeutral (C i).core.erase.core
  leader_signal_one :
    (C leader).core.erase.core.signal_B = ⟨1, by omega⟩
  leader_reset_true :
    (C leader).core.erase.core.reset_cmd = true
  follower_reset_false : ∀ i, i ≠ leader →
    (C i).core.erase.core.reset_cmd = false
  leader_echo_false :
    (C leader).core.erase.core.echo = false

private theorem peaceView_leader_eq
    {C D : EConfig n psi kappa tau}
    (h : PeaceViewConfigFrame C D) (i : Fin n) :
    (D i).core.erase.core.leader = (C i).core.erase.core.leader :=
  congrArg PeaceView.leader (h i)

private theorem peaceView_label_eq
    {C D : EConfig n psi kappa tau}
    (h : PeaceViewConfigFrame C D) (i : Fin n) :
    (D i).core.erase.core.label = (C i).core.erase.core.label :=
  congrArg PeaceView.label (h i)

private theorem peaceView_shield_eq
    {C D : EConfig n psi kappa tau}
    (h : PeaceViewConfigFrame C D) (i : Fin n) :
    (D i).core.erase.core.shield = (C i).core.erase.core.shield :=
  congrArg PeaceView.shield (h i)

private theorem peaceView_bullet_eq
    {C D : EConfig n psi kappa tau}
    (h : PeaceViewConfigFrame C D) (i : Fin n) :
    (D i).core.erase.core.bullet = (C i).core.erase.core.bullet :=
  congrArg PeaceView.bullet (h i)

private theorem peaceView_signal_eq
    {C D : EConfig n psi kappa tau}
    (h : PeaceViewConfigFrame C D) (i : Fin n) :
    (D i).core.erase.core.signal_B = (C i).core.erase.core.signal_B :=
  congrArg PeaceView.signal_B (h i)

/-- A deletion drain that frames the physical view reconstructs the rooted
retry boundary without imposing cyclic label alignment. -/
theorem RootedClockwiseRetryReady.of_seed_frame
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    {C D : EConfig n psi kappa tau}
    (hseed : RootedUnshieldedRetrySeed hpsi ring leader C)
    (hnoActive : NoActiveDeletion D)
    (hframe : PeaceResetEchoConfigFrame C D) :
    RootedClockwiseRetryReady hpsi ring leader D := by
  have hnoFreeD : noFreeBarrier hpsi ring
      (fun i => (D i).core.erase.core) := by
    intro i
    dsimp only
    intro hbarrierD
    have hbarrierC : isBarrier hpsi
        (C i).core.erase.core
        (C (ring.rightNeighbor i)).core.erase.core := by
      intro halignC
      apply hbarrierD
      apply Fin.ext
      have hright := congrArg Fin.val
        (peaceView_label_eq hframe.peaceView (ring.rightNeighbor i))
      have hleft := congrArg Fin.val
        (peaceView_label_eq hframe.peaceView i)
      have halignVal := congrArg Fin.val halignC
      dsimp only at halignVal ⊢
      calc
        (D (ring.rightNeighbor i)).core.erase.core.label.val =
            (C (ring.rightNeighbor i)).core.erase.core.label.val := hright
        _ = ((C i).core.erase.core.label.val + 1) % psi := halignVal
        _ = ((D i).core.erase.core.label.val + 1) % psi := by rw [hleft]
    have hleaderC := hseed.no_free_barrier i hbarrierC
    exact (peaceView_leader_eq hframe.peaceView
      (ring.rightNeighbor i)).trans hleaderC
  exact {
    leader_alive := (peaceView_leader_eq hframe.peaceView leader).trans
      hseed.leader_alive
    leader_zero := (peaceView_label_eq hframe.peaceView leader).trans
      hseed.leader_zero
    unique_leader := by
      intro i hi
      exact (peaceView_leader_eq hframe.peaceView i).trans
        (hseed.unique_leader i hi)
    no_free_barrier := hnoFreeD
    leader_unshielded :=
      (peaceView_shield_eq hframe.peaceView leader).trans
        hseed.leader_unshielded
    bullets_zero := by
      intro i
      exact (peaceView_bullet_eq hframe.peaceView i).trans
        (hseed.bullets_zero i)
    leader_signal_zero :=
      (peaceView_signal_eq hframe.peaceView leader).trans
        hseed.leader_signal_zero
    no_active := hnoActive
  }

/-- The combined PeaceView/reset/echo frame reconstructs the full retry-ready
boundary after the deletion drain. -/
theorem ClockwiseRetryReady.of_seed_frame
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    {C D : EConfig n psi kappa tau}
    (hseed : UnshieldedRetrySeed hpsi ring leader C)
    (hnoActive : NoActiveDeletion D)
    (hframe : PeaceResetEchoConfigFrame C D) :
    ClockwiseRetryReady hpsi ring leader D := by
  have hlabelsD : ∀ i,
      (D (ring.rightNeighbor i)).core.erase.core.label =
        ⟨((D i).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by
    intro i
    have hright := peaceView_label_eq hframe.peaceView
      (ring.rightNeighbor i)
    have hleft := peaceView_label_eq hframe.peaceView i
    rw [hright, hleft]
    exact hseed.stable_labels i
  have hnoFreeD : noFreeBarrier hpsi ring
      (fun i => (D i).core.erase.core) := by
    intro i
    dsimp only
    intro hbarrier
    exact False.elim (hbarrier (hlabelsD i))
  have hseedD : UnshieldedRetrySeed hpsi ring leader D := by
    exact {
      leader_alive := (peaceView_leader_eq hframe.peaceView leader).trans
        hseed.leader_alive
      leader_zero := (peaceView_label_eq hframe.peaceView leader).trans
        hseed.leader_zero
      unique_leader := by
        intro i hi
        exact (peaceView_leader_eq hframe.peaceView i).trans
          (hseed.unique_leader i hi)
      no_free_barrier := hnoFreeD
      leader_unshielded :=
        (peaceView_shield_eq hframe.peaceView leader).trans
          hseed.leader_unshielded
      bullets_zero := by
        intro i
        exact (peaceView_bullet_eq hframe.peaceView i).trans
          (hseed.bullets_zero i)
      leader_signal_zero :=
        (peaceView_signal_eq hframe.peaceView leader).trans
          hseed.leader_signal_zero
      stable_labels := hlabelsD
    }
  exact ⟨hseedD, hnoActive⟩

/-- The strengthened corrected-transition drain supplies the abstract one-drain
contract used by the rank scheduler. -/
theorem preCheckResetOneDrainContract
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) :
    ClockwiseOneDrainContract
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
      ring (UnshieldedRetrySeed hpsi ring leader)
        (ClockwiseRetryReady hpsi ring leader) where
  drain := by
    intro C _hseed
    obtain ⟨schedule, hlength, _hempty, hnoActive,
      hreset, _hshield, hpeace⟩ :=
      exists_wallSweepPreCheckResetDeletionDrain_peaceFrame
        hpsi ring hn C
    let D := runLocalSchedule ring
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C schedule
    exact ⟨schedule, D, rfl, hlength, hnoActive,
      ⟨hpeace, hreset⟩⟩
  ready_of_frame := by
    intro C D hseed hnoActive hframe
    exact ClockwiseRetryReady.of_seed_frame
      hpsi ring leader hseed hnoActive hframe

/-- The same one-time physical deletion drain reconstructs the regime-correct
rooted retry boundary. -/
theorem preCheckResetRootedOneDrainContract
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) :
    ClockwiseOneDrainContract
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
      ring (RootedUnshieldedRetrySeed hpsi ring leader)
        (RootedClockwiseRetryReady hpsi ring leader) where
  drain := by
    intro C _hseed
    obtain ⟨schedule, hlength, _hempty, hnoActive,
      hreset, _hshield, hpeace⟩ :=
      exists_wallSweepPreCheckResetDeletionDrain_peaceFrame
        hpsi ring hn C
    let D := runLocalSchedule ring
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C schedule
    exact ⟨schedule, D, rfl, hlength, hnoActive,
      ⟨hpeace, hreset⟩⟩
  ready_of_frame := by
    intro C D hseed hnoActive hframe
    exact RootedClockwiseRetryReady.of_seed_frame
      hpsi ring leader hseed hnoActive hframe

/-- The rooted leader-sink repair uses the same one-time deletion-drain
interface, with active-host agreement supplying the unchanged physical
frames and path-count bound. -/
theorem preCheckResetLeaderSinkRootedOneDrainContract
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) :
    ClockwiseOneDrainContract
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau)
      ring (RootedUnshieldedRetrySeed hpsi ring leader)
        (RootedClockwiseRetryReady hpsi ring leader) where
  drain := by
    intro C _hseed
    obtain ⟨schedule, hlength, _hempty, hnoActive,
      hreset, _hshield, hpeace⟩ :=
      exists_wallSweepPreCheckResetLeaderSinkDeletionDrain_peaceFrame
        hpsi ring hn C
    let D := runLocalSchedule ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C schedule
    exact ⟨schedule, D, rfl, hlength, hnoActive,
      ⟨hpeace, hreset⟩⟩
  ready_of_frame := by
    intro C D hseed hnoActive hframe
    exact RootedClockwiseRetryReady.of_seed_frame
      hpsi ring leader hseed hnoActive hframe

end PPLLWallSweepUnshieldedRetry
