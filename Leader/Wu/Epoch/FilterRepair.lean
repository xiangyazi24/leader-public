import Leader.Wu.Epoch.ProtectedSweep
import Leader.Wu.Protocol.BoundedProtocol

/-!
# A P_PLL-derived protected-epoch repair baseline

This module runs the actual finite integrated P_PLL candidate at every local
interaction and then applies a physical ring-indexed epoch filter.  The filter
retains the integrated transition's proposed stable `bit` and `label` values,
but removes all transient comparison, bullet, reset, and write controls and
derives the leader role from `slot : Fin n`.

The resulting protocol is deliberately a strong research repair, not a silent
interpretation of Wu's pseudocode.  It supplies a concrete corrected-closedness
baseline and an arbitrary-state finite convergence theorem while paying the
exact factor-`n` certificate cost.  The weak one-schedule probability bound is
not the WHP/runtime conclusion of Theorem 4.1.13.
-/

namespace PPLLDerivedEpochRepair

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLProtectedEpochProtocol PPLLProtectedEpochSweep

/-! ## Physical transition and its exact P_PLL seam -/

/-- Execute the finite integrated P_PLL core, then enforce the epoch slot edge
and sanitize both outputs.  Stable data proposals `bit` and `label` from the
integrated transition survive sanitization; every active lifecycle field is
removed, and output leadership is recomputed from the physical slot. -/
def ppllEpochFilterTransition (hψ : ψ > 0) (κ : Nat) (hn : n > 0)
    (l r : EpochAgentState n ψ κ) :
    EpochAgentState n ψ κ × EpochAgentState n ψ κ :=
  let coreq := integratedBoundedTransition hψ κ l.core r.core
  let lOut := sanitizeEpochState ⟨coreq.1, l.slot⟩
  let rOut := sanitizeEpochState ⟨coreq.2, nextSlot hn l.slot⟩
  (lOut, rOut)

/-- The filtered transition genuinely consumes the integrated P_PLL result:
its two retained stable fields are exactly the integrated outputs, not the raw
inputs or an unrelated epoch-only computation. -/
theorem ppllEpochFilter_retains_integrated_data
    (hψ : ψ > 0) (κ : Nat) (hn : n > 0)
    (l r : EpochAgentState n ψ κ) :
    let coreq := integratedBoundedTransition hψ κ l.core r.core
    let q := ppllEpochFilterTransition hψ κ hn l r
    q.1.core.bit = coreq.1.bit ∧ q.1.core.label = coreq.1.label ∧
      q.2.core.bit = coreq.2.bit ∧ q.2.core.label = coreq.2.label := by
  simp [ppllEpochFilterTransition, sanitizeEpochState, sanitizeEpochCore]

/-- The epoch filter has the local contract needed for both closure and the
ordered sweep: the initiator slot is framed, the responder becomes its modular
successor, and both outputs are clean independently of arbitrary input junk. -/
theorem ppllEpochFilter_local_contract
    (hψ : ψ > 0) (κ : Nat) (hn : n > 0)
    (l r : EpochAgentState n ψ κ) :
    let q := ppllEpochFilterTransition hψ κ hn l r
    q.1.slot = l.slot ∧
      q.2.slot = nextSlot hn q.1.slot ∧
      EpochClean q.1 ∧ EpochClean q.2 := by
  unfold ppllEpochFilterTransition
  dsimp only
  exact ⟨rfl, rfl,
    sanitizeEpochState_idempotent _, sanitizeEpochState_idempotent _⟩

/-- The finite physical protocol obtained from the integrated P_PLL core and
the ring-indexed epoch filter. -/
def ppllEpochFilterProtocol (hψ : ψ > 0) (κ : Nat) (hn : n > 0) :
    PopulationProtocol :=
  { epochProtocol hn ψ κ with
    transition := ppllEpochFilterTransition hψ κ hn }

/-- Filtering changes the transition but not the output interpretation of an
epoch state.  This small bridge avoids unfolding the large integrated
transition when transferring slot-uniqueness results. -/
theorem ppllEpochFilter_output_eq_epoch
    (hψ : ψ > 0) (κ : Nat) (hn : n > 0)
    (u : EpochAgentState n ψ κ) :
    (ppllEpochFilterProtocol hψ κ hn).output u =
      (epochProtocol hn ψ κ).output u := by
  change (if u.core.leader then LeaderOutput.leader else .follower) =
    (if u.core.leader then LeaderOutput.leader else .follower)
  rfl

/-- The filtered protocol reuses the duplicate-free factor-`n` epoch carrier. -/
def ppllEpochFilterStateCertificate (n ψ κ : Nat) :
    ExhaustiveList (EpochAgentState n ψ κ) :=
  epochAgentState n ψ κ

/-- Exact semantic finite-index certificate for the filtered local state. -/
theorem ppllEpochFilterState_decode_bijective (n ψ κ : Nat) :
    Function.Injective (ppllEpochFilterStateCertificate n ψ κ).decode ∧
      Function.Surjective (ppllEpochFilterStateCertificate n ψ κ).decode :=
  epochAgentState_decode_bijective n ψ κ

/-- The P_PLL-derived filter has the same exact factor-`n` state count as the
pure epoch baseline. -/
theorem ppllEpochFilterState_values_length (n ψ κ : Nat) :
    (ppllEpochFilterStateCertificate n ψ κ).values.length =
      (PPLLFinite.boundedAgentState ψ κ).values.length * n :=
  epochAgentState_values_length n ψ κ

/-! ## Corrected closedness -/

private theorem filtered_step_slot_eq
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ)
    (hC : ProtectedEpoch ring.hn ring C) (e i : Fin n) :
    (PopulationProtocol.step
      (ppllEpochFilterProtocol hψ κ ring.hn) ring C e i).slot =
        (C i).slot := by
  obtain ⟨anchor, hrot, hcovered, hclean⟩ := hC
  let j := ring.rightNeighbor e
  let q := ppllEpochFilterTransition hψ κ ring.hn (C e) (C j)
  have hq := ppllEpochFilter_local_contract hψ κ ring.hn (C e) (C j)
  change q.1.slot = (C e).slot ∧
    q.2.slot = nextSlot ring.hn q.1.slot ∧
    EpochClean q.1 ∧ EpochClean q.2 at hq
  change (if i = e then q.1 else if i = j then q.2 else C i).slot =
    (C i).slot
  by_cases hie : i = e
  · subst i
    simpa using hq.1
  · by_cases hij : i = j
    · subst i
      rw [if_neg hie, if_pos rfl, hq.2.1, hq.1]
      exact (hcovered e).symm
    · simp [hie, hij]

private theorem filtered_step_clean
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ)
    (hC : ProtectedEpoch ring.hn ring C) (e i : Fin n) :
    EpochClean (PopulationProtocol.step
      (ppllEpochFilterProtocol hψ κ ring.hn) ring C e i) := by
  obtain ⟨anchor, hrot, hcovered, hclean⟩ := hC
  let j := ring.rightNeighbor e
  let q := ppllEpochFilterTransition hψ κ ring.hn (C e) (C j)
  have hq := ppllEpochFilter_local_contract hψ κ ring.hn (C e) (C j)
  change q.1.slot = (C e).slot ∧
    q.2.slot = nextSlot ring.hn q.1.slot ∧
    EpochClean q.1 ∧ EpochClean q.2 at hq
  change EpochClean (if i = e then q.1 else if i = j then q.2 else C i)
  by_cases hie : i = e
  · simpa [hie] using hq.2.2.1
  · by_cases hij : i = j
    · subst i
      simpa [hie] using hq.2.2.2
    · simpa [hie, hij] using hclean i

/-- The protected rotation is one-step closed under the actual P_PLL-derived
filtered transition.  This is the corrected analogue of Lemma 4.1.1 for this
explicit repair; it is not a theorem about the literal five-condition set. -/
theorem ppllEpochFilter_closed
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (ppllEpochFilterProtocol hψ κ ring.hn) ring
      (ProtectedEpoch ring.hn ring) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  obtain ⟨anchor, hrot, hcovered, hclean⟩ := hC
  refine ⟨anchor, ?_, ?_, ?_⟩
  · intro i
    rw [show (PopulationProtocol.step
      (ppllEpochFilterProtocol hψ κ ring.hn) ring C e i).slot.val =
        (C i).slot.val from congrArg Fin.val
          (filtered_step_slot_eq hψ κ ring C
            ⟨anchor, hrot, hcovered, hclean⟩ e i)]
    exact hrot i
  · intro i
    rw [filtered_step_slot_eq hψ κ ring C
      ⟨anchor, hrot, hcovered, hclean⟩ e (ring.rightNeighbor i),
      filtered_step_slot_eq hψ κ ring C
        ⟨anchor, hrot, hcovered, hclean⟩ e i]
    exact hcovered i
  · exact filtered_step_clean hψ κ ring C
      ⟨anchor, hrot, hcovered, hclean⟩ e

private theorem filtered_output_eq_slot_of_clean
    (hψ : ψ > 0) (κ : Nat) (hn : n > 0)
    (u : EpochAgentState n ψ κ) (hu : EpochClean u) :
    (ppllEpochFilterProtocol hψ κ hn).output u =
      if slotLeader u.slot then .leader else .follower := by
  change (if u.core.leader then LeaderOutput.leader else .follower) = _
  rw [EpochClean.leader_eq hu]
  rfl

/-- A protected filtered step preserves every output even though the retained
P_PLL `bit` and `label` fields may continue to change. -/
theorem ppllEpochFilter_step_output
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) :
    StepOutputPreservingOn (ppllEpochFilterProtocol hψ κ ring.hn) ring
      (ProtectedEpoch ring.hn ring) := by
  intro C hC C' hstep i
  obtain ⟨e, rfl⟩ := hstep
  obtain ⟨anchor, hrot, hcovered, hclean⟩ := hC
  have hC' : ProtectedEpoch ring.hn ring C :=
    ⟨anchor, hrot, hcovered, hclean⟩
  have hbefore := hclean i
  have hafter := filtered_step_clean hψ κ ring C hC' e i
  rw [filtered_output_eq_slot_of_clean hψ κ ring.hn _ hafter,
    filtered_output_eq_slot_of_clean hψ κ ring.hn _ hbefore,
    filtered_step_slot_eq hψ κ ring C hC' e i]

/-- A protected rotation has unique leader output for the filtered protocol;
uniqueness depends only on slots and cleanliness, not on its transition. -/
theorem ppllEpochFilter_unique
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ)
    (hC : ProtectedEpoch ring.hn ring C) :
    UniqueLeaderOutput (ppllEpochFilterProtocol hψ κ ring.hn)
      n C isLeaderOutput := by
  obtain ⟨root, hroot, honly⟩ := protectedEpoch_unique ring.hn ring C hC
  refine ⟨root, ?_, ?_⟩
  · rw [ppllEpochFilter_output_eq_epoch hψ κ ring.hn]
    exact hroot
  · intro j hj
    rw [ppllEpochFilter_output_eq_epoch hψ κ ring.hn] at hj
    exact honly j hj

/-- Membership in the repaired protected set implies Wu's Definition-1 output
safety for the P_PLL-derived filtered protocol. -/
theorem ppllEpochFilter_isSafe
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    {C : Fin n → EpochAgentState n ψ κ}
    (hC : ProtectedEpoch ring.hn ring C) :
    PopulationProtocol.IsSafe (ppllEpochFilterProtocol hψ κ ring.hn)
      ring C isLeaderOutput := by
  exact isSafe_of_operational_legitimacy
    (ppllEpochFilterProtocol hψ κ ring.hn) ring isLeaderOutput
    (ProtectedEpoch ring.hn ring)
    (ppllEpochFilter_closed hψ κ ring)
    (ppllEpochFilter_unique hψ κ ring)
    (ppllEpochFilter_step_output hψ κ ring) hC

end PPLLDerivedEpochRepair
