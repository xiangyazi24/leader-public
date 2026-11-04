import Leader.Wu.Entrance.EnvelopeHostLaws
import Leader.Wu.Entrance.TrafficPairFrame

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceEnvelopeFrame

open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV3

variable {n psi kappa tau : Nat}
variable {ring : DirectedRing n}

private theorem rawCell_leader
    (q : Phys psi kappa tau) :
    (B6Sanitation.rawCell q).leader = q.core.core.leader := by
  rfl

private theorem hostLeaderless_raw_follower
    (C : PConfig n (Phys psi kappa tau))
    (hC : HostLeaderless (fun q : Phys psi kappa tau => q) C)
    (i : Fin n) :
    (B6Sanitation.rawCell (C i)).leader = false := by
  unfold HostLeaderless physConfig
    BirthShortDoneTerminalFirstHit.Leaderless at hC
  exact (rawCell_leader (C i)).trans (hC i)

private theorem r1_pair_resetEcho_clear
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Phys psi kappa tau)
    (hlFollower : (B6Sanitation.rawCell l).leader = false)
    (hrFollower : (B6Sanitation.rawCell r).leader = false)
    (hlClear : ResetEchoClearCell l)
    (hrClear : ResetEchoClearCell r) :
    ResetEchoClearCell
        ((B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2).row l r).1 ∧
      ResetEchoClearCell
        ((B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2).row l r).2 := by
  have hl :
      (B6Sanitation.rawCell l).reset_cmd = false ∧
        (B6Sanitation.rawCell l).echo = false := by
    simpa only [ResetEchoClearCell] using hlClear
  have hr :
      (B6Sanitation.rawCell r).reset_cmd = false ∧
        (B6Sanitation.rawCell r).echo = false := by
    simpa only [ResetEchoClearCell] using hrClear
  have h := B6TrafficPairFrame.r1_follower_resetEcho_frame
    (kappa := kappa) (tau := tau) hpsi h2 l r
    hlFollower hrFollower hl.1 hl.2 hr.1 hr.2
  dsimp only at h
  constructor
  · unfold ResetEchoClearCell
    exact ⟨h.1, h.2.1⟩
  · unfold ResetEchoClearCell
    exact ⟨h.2.2.1, h.2.2.2⟩

theorem r1_internal_step_env_resetEcho_frame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi kappa tau)) (e : Fin n)
    (hLeaderless :
      HostLeaderless (fun q : Phys psi kappa tau => q) C)
    (hClear :
      EnvAll (fun q : Phys psi kappa tau => q)
        X ResetEchoClearCell C)
    (he : internal X.env.I e) :
    EnvAll (fun q : Phys psi kappa tau => q)
      X ResetEchoClearCell
      (B9Host.hostStep
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        ring C e) := by
  unfold EnvAll at hClear ⊢
  have hInternal := (internal_iff X.env.I e).mp he
  have hL : ResetEchoClearCell (C e) :=
    hClear e hInternal.1
  have hR : ResetEchoClearCell (C (ring.rightNeighbor e)) :=
    hClear (ring.rightNeighbor e) hInternal.2
  have hPair := r1_pair_resetEcho_clear
    (kappa := kappa) (tau := tau) hpsi h2
    (C e) (C (ring.rightNeighbor e))
    (hostLeaderless_raw_follower C hLeaderless e)
    (hostLeaderless_raw_follower C hLeaderless (ring.rightNeighbor e))
    hL hR
  intro i hiEnv
  by_cases hie : i = e
  · subst i
    simpa only [B9Host.hostStep, if_pos] using hPair.1
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simpa only [B9Host.hostStep, if_neg hie, if_pos] using hPair.2
    · simpa only [B9Host.hostStep, if_neg hie, if_neg hir] using
        hClear i hiEnv

section Boundary

variable {P : Type}

/-- Exactly the collar part omitted by the old core-only `TrafficAt`:
every envelope-supported site outside the core is reset/echo clear. -/
def EnvelopeBoundaryResetEchoClear
    (view : P → Phys psi kappa tau)
    (X : Workspace ring psi) (C : PConfig n P) : Prop :=
  ∀ i, support X.env.I i = true →
    support X.core.J i = false →
    ResetEchoClearCell (view (C i))

/-- The boundary predicate above is precisely the extra content needed to
upgrade the old core-wide traffic predicate to V3's envelope-wide predicate. -/
theorem trafficAtEnv_iff_trafficAt_and_boundary
    (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P)
    (X : Workspace ring psi) (C : PConfig n P) :
    TrafficAtEnv view WP X C ↔
      TrafficAt view WP X C ∧
        EnvelopeBoundaryResetEchoClear view X C := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · refine ⟨h.1, ?_⟩
      intro i hiCore
      exact h.2 i (X.core.subset i hiCore)
    · intro i hiEnv _hiCore
      exact h.2 i hiEnv
  · rintro ⟨hT, hB⟩
    refine ⟨hT.1, ?_⟩
    intro i hiEnv
    cases hCore : support X.core.J i with
    | false => exact hB i hiEnv hCore
    | true => exact hT.2 i hCore

end Boundary

end B6EntranceEnvelopeFrame
