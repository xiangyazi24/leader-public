import Leader.Wu.Comparison.ExpiringK2Projection

/-! Physical interpretation and closure for the replacement stage only. -/

namespace ExpiringK2Projection

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  LDSinkBoundedKernel K2OutputSafety LDSinkGapCleanup
  PPLLNoCheckBirthConditionTwoGeometry

set_option autoImplicit false

variable {ψ κ τ n : Nat}

/-- Sum the actual expiring endpoints' physical leader bits. -/
def count (C : Fin n → ExpiringAgentState ψ κ τ) : Nat :=
  K2GlobalGapClosure.physicalLeaderCount (physicalConfig C)

theorem count_eq_observe (C : Fin n → ExpiringAgentState ψ κ τ) :
    count C = K2GlobalGapClosure.physicalLeaderCount (observe C) := rfl

theorem run_count (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n)) :
    count (run (step hψ ring) C es) =
      K2GlobalGapClosure.physicalLeaderCount
        (run (rawStep (by decide) ring) (observe C) es) := by
  rw [count_eq_observe, observe_run]

theorem count_step_le (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n) :
    count (step hψ ring C e) ≤ count C := by
  rw [count_eq_observe, count_eq_observe, observe_step]
  exact K2GlobalGapClosure.physical_count_nonincrease (by decide) ring _ e

def SignalGlobal (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) : Prop :=
  K2GlobalGapClosure.GlobalInvariant (by decide) ring (observe C)

/-- Both physical spacing and the full quantified signal order are literal
properties of the old carrier. No condition is placed on its stored labels. -/
theorem signalGlobal_iff (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) :
    SignalGlobal ring C ↔
      K2GlobalGapClosure.Separated ring (physicalConfig C) ∧
      (∀ G : GapFrame n, GapEndpointsPresent G (physicalConfig C) →
        GapInteriorFollowers G (physicalConfig C) →
        GapSignalBelowBullets G (physicalConfig C)) := by
  constructor
  · intro h
    exact ⟨h.separated, h.signal⟩
  · rintro ⟨hsep, hsig⟩
    exact ⟨hsep, cyclicLabels_one ring (observe C), hsig⟩

theorem signalGlobal_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (hC : SignalGlobal ring C)
    (e : Fin n) : SignalGlobal ring (step hψ ring C e) := by
  unfold SignalGlobal
  rw [observe_step]
  exact K2GlobalGapClosure.global_step (by decide) ring _ hC e

theorem signalGlobal_run (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (hC : SignalGlobal ring C)
    (es : List (Fin n)) : SignalGlobal ring (run (step hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih _ (signalGlobal_step hψ ring C hC e)

/-- Expand nearest peacefulness directly in physical Expiring fields. The
first clockwise leader, including every wraparound interval site, is used. -/
def PhysicalNearestPeaceful (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) : Prop :=
  ∀ start, (C start).core.core.bullet = 2 → ∃ d,
    d < n ∧
    (C (cwPos ring start d)).core.core.leader = true ∧
    (C (cwPos ring start d)).core.core.shield = true ∧
    (∀ k, k ≤ d → (C (cwPos ring start k)).core.core.signal_B = 0) ∧
    (∀ k, k < d → (C (cwPos ring start k)).core.core.leader = false)

theorem nearest_iff_physical (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) :
    K2PeacefulGlobal.NearestPeaceful ring (observe C) ↔
      PhysicalNearestPeaceful ring C := by
  constructor
  · intro h start hb
    obtain ⟨d, hd⟩ := h start hb
    exact ⟨d, hd.distance_lt, hd.target_leader, hd.target_shield,
      hd.signal_zero, hd.before_follower⟩
  · intro h start hb
    obtain ⟨d, hd, hl, hs, hz, hf⟩ := h start hb
    exact ⟨d, hd, hl, hs, hz, hf⟩

def PeacefulGlobal (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) : Prop :=
  hasLeader n (observe C) ∧ K2PeacefulGlobal.NearestPeaceful ring (observe C)

theorem peacefulGlobal_iff (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) :
    PeacefulGlobal ring C ↔
      (∃ i, (C i).core.core.leader = true) ∧ PhysicalNearestPeaceful ring C := by
  exact and_congr Iff.rfl (nearest_iff_physical ring C)

theorem peacefulGlobal_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (hC : PeacefulGlobal ring C)
    (e : Fin n) : PeacefulGlobal ring (step hψ ring C e) := by
  unfold PeacefulGlobal
  rw [observe_step]
  exact ⟨K2PeacefulGlobal.hasLeader_rawStep hn ring _ hC.2 hC.1 e,
    K2PeacefulGlobal.nearest_rawStep hn ring _ hC.2 e⟩

theorem peacefulGlobal_run (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (hC : PeacefulGlobal ring C)
    (es : List (Fin n)) : PeacefulGlobal ring (run (step hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih _ (peacefulGlobal_step hψ hn ring C hC e)

theorem peacefulGlobal_count_pos (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (hC : PeacefulGlobal ring C) :
    0 < count C := by
  obtain ⟨p, hp⟩ := hC.1
  obtain ⟨k, hk, _⟩ := List.mem_iff_getElem.mp
    ((K2CyclicLayout.mem_leaderSites (observe C) p).mpr hp)
  have hh : k < count C := by
    simpa only [K2CyclicLayout.leaderSites_length, ← count_eq_observe] using hk
  omega

/-- Same-word count and the two current domain predicates agree with an
independently supplied UCell configuration. Its controller is not generated. -/
theorem ucell_domain_iff (C : Fin n → ExpiringAgentState ψ κ τ)
    (D : Fin n → StateBoundUnifiedCell.UCell ψ κ) (ring : DirectedRing n)
    (h : observe C = LabelFreeElimination.observe D) :
    count C = K2FiniteProgress.count D ∧
    (SignalGlobal ring C ↔ LabelFreeElimination.SignalGlobal ring D) ∧
    (PeacefulGlobal ring C ↔ K2PeacefulGlobal.PeacefulGlobal ring D) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [count_eq_observe, K2FiniteProgress.count_eq_observe, h]
  · unfold SignalGlobal LabelFreeElimination.SignalGlobal
    rw [h]
  · unfold PeacefulGlobal K2PeacefulGlobal.PeacefulGlobal
    rw [h]

end ExpiringK2Projection

#print axioms ExpiringK2Projection.run_count
#print axioms ExpiringK2Projection.signalGlobal_iff
#print axioms ExpiringK2Projection.nearest_iff_physical
#print axioms ExpiringK2Projection.peacefulGlobal_run
#print axioms ExpiringK2Projection.ucell_domain_iff
