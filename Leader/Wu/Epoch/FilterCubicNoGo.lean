import Leader.Wu.Epoch.VoterRuntimeObstruction
import Leader.Wu.Epoch.FilterRepair

/-!
# Cubic finite-horizon obstruction for the filtered P_PLL epoch rule

The filtered protocol's epoch colors evolve exactly as the directed voter
process.  This file lifts the finite-tree voter obstruction back to physical
epoch states.  It constructs arbitrary clean epoch states with any prescribed
color word, proves equality of the complete color-miss trees, and compares
color consensus with the stronger protected target.

For an even ring and a canonical midpoint two-domain start, failure at most
`1/8` therefore forces a cubic interaction horizon.  This rules out using the
current slot-copy rule as the thesis-order WHP repair; it does not rule out a
different epoch control or P_PLL's intended lottery mechanism.
-/

namespace PPLLDerivedEpochRuntimeNoGo

open PPLLResearchFormulation PPLLProtectedEpochProtocol
  PPLLDerivedEpochRepair PPLLEpochVoterReduction
  PPLLEpochVoterTwoDomain PPLLEpochVoterFiniteTree
  PPLLEpochVoterRuntimeObstruction

/-! ## Physical realization of arbitrary voter colors -/

/-- Epoch slot realizing color `color` at physical position `i`. -/
def slotOfColor (hn : n > 0) (color i : Fin n) : Fin n :=
  ⟨(color.val + i.val) % n, Nat.mod_lt _ hn⟩

/-- Clean physical epoch configuration realizing an arbitrary voter-color word
over any supplied bounded P_PLL cores. -/
def epochConfigOfColors
    (base : Fin n → BoundedAgentState ψ κ) (colors : Fin n → Fin n) :
    Fin n → EpochAgentState n ψ κ :=
  fun i => sanitizeEpochState ⟨base i, slotOfColor (by exact i.pos) (colors i) i⟩

/-- The physical realization has exactly the requested color projection. -/
theorem epochColorConfig_epochConfigOfColors
    (base : Fin n → BoundedAgentState ψ κ) (colors : Fin n → Fin n) :
    epochColorConfig (epochConfigOfColors base colors) = colors := by
  funext i
  apply epochColor_eq_of_rotation (colors i) i
  rfl

/-! ## Exact physical and projected miss trees -/

/-- Exact scheduler-tree count that has not yet reached epoch-color consensus
under the filtered P_PLL transition. -/
noncomputable def filteredColorMissTree
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) :
    (Fin n → EpochAgentState n ψ κ) → Nat → Nat
  | C, 0 => @ite Nat (EpochColorConsensus C)
      (Classical.propDecidable _) 0 1
  | C, t + 1 => @ite Nat (EpochColorConsensus C)
      (Classical.propDecidable _) 0
      ((List.ofFn (fun e : Fin n =>
        filteredColorMissTree hψ κ ring
          (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e) t)).sum)

/-- Exact scheduler-tree count that has not yet reached the full protected
physical predicate. -/
noncomputable def filteredProtectedMissTree
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) :
    (Fin n → EpochAgentState n ψ κ) → Nat → Nat
  | C, 0 => @ite Nat (ProtectedEpoch ring.hn ring C)
      (Classical.propDecidable _) 0 1
  | C, t + 1 => @ite Nat (ProtectedEpoch ring.hn ring C)
      (Classical.propDecidable _) 0
      ((List.ofFn (fun e : Fin n =>
        filteredProtectedMissTree hψ κ ring
          (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e) t)).sum)

/-- The entire physical color-miss tree equals the directed-voter miss tree,
not merely one-step projections. -/
theorem filteredColorMissTree_eq_voterMissTree
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat) :
    filteredColorMissTree hψ κ ring C t =
      voterMissTree ring (epochColorConfig C) t := by
  induction t generalizing C with
  | zero =>
      simp only [filteredColorMissTree, voterMissTree]
      rfl
  | succ t ih =>
      simp only [filteredColorMissTree, voterMissTree]
      by_cases hcons : EpochColorConsensus C
      · have hv : VoterConsensus (epochColorConfig C) := hcons
        rw [if_pos hcons, if_pos hv]
      · have hv : ¬VoterConsensus (epochColorConfig C) := hcons
        rw [if_neg hcons, if_neg hv]
        have hfun :
            (fun e : Fin n => filteredColorMissTree hψ κ ring
              (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e) t) =
            (fun e : Fin n => voterMissTree ring
              (directedVoterStep ring (epochColorConfig C) e) t) := by
          funext e
          rw [ih, epochColorConfig_localStep]
        rw [hfun]

private theorem sum_ofFn_le
    (f g : Fin n → Nat) (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

/-- Missing color consensus is a subset of missing the stronger protected
predicate, at every horizon. -/
theorem filteredColorMissTree_le_protected
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat) :
    filteredColorMissTree hψ κ ring C t ≤
      filteredProtectedMissTree hψ κ ring C t := by
  induction t generalizing C with
  | zero =>
      simp only [filteredColorMissTree, filteredProtectedMissTree]
      by_cases hcolor : EpochColorConsensus C
      · rw [if_pos hcolor]
        omega
      · have hnot : ¬ProtectedEpoch ring.hn ring C := by
          intro hp
          exact hcolor ((protectedEpoch_iff_colorConsensus_clean ring C).1 hp).1
        rw [if_neg hcolor, if_neg hnot]
        exact Nat.le_refl 1
  | succ t ih =>
      simp only [filteredColorMissTree, filteredProtectedMissTree]
      by_cases hcolor : EpochColorConsensus C
      · rw [if_pos hcolor]
        omega
      · have hnot : ¬ProtectedEpoch ring.hn ring C := by
          intro hp
          exact hcolor ((protectedEpoch_iff_colorConsensus_clean ring C).1 hp).1
        rw [if_neg hcolor, if_neg hnot]
        exact sum_ofFn_le _ _ (fun e => ih
          (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e))

/-! ## Cubic physical finite-horizon no-go -/

/-- Clean physical midpoint two-domain start over arbitrary bounded P_PLL cores. -/
def filteredMidpointTwoDomainStart
    (m : Nat) (hm : 4 ≤ m)
    (base : Fin (2 * m) → BoundedAgentState ψ κ) :
    Fin (2 * m) → EpochAgentState (2 * m) ψ κ :=
  epochConfigOfColors base
    (canonicalTwoDomain (by omega : 1 < 2 * m) m (by omega))

/-- Exact color projection of the physical midpoint start. -/
theorem filteredMidpointTwoDomainStart_colors
    (m : Nat) (hm : 4 ≤ m)
    (base : Fin (2 * m) → BoundedAgentState ψ κ) :
    epochColorConfig (filteredMidpointTwoDomainStart m hm base) =
      canonicalTwoDomain (by omega : 1 < 2 * m) m (by omega) :=
  epochColorConfig_epochConfigOfColors _ _

/-- If the actual filtered P_PLL protocol reaches its protected set with
failure at most `1/8` from the physical midpoint two-domain start, its horizon
must be cubic. -/
theorem filteredProtected_failure_eighth_forces_cubic_horizon
    (m t : Nat) (hm : 4 ≤ m)
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing (2 * m))
    (base : Fin (2 * m) → BoundedAgentState ψ κ)
    (hfail : 8 * filteredProtectedMissTree hψ κ ring
        (filteredMidpointTwoDomainStart m hm base) t ≤ (2 * m) ^ t) :
    m ^ 3 ≤ 2 * t := by
  have hsub := filteredColorMissTree_le_protected hψ κ ring
    (filteredMidpointTwoDomainStart m hm base) t
  have hcolorfail : 8 * filteredColorMissTree hψ κ ring
      (filteredMidpointTwoDomainStart m hm base) t ≤ (2 * m) ^ t :=
    Nat.le_trans (Nat.mul_le_mul_left 8 hsub) hfail
  rw [filteredColorMissTree_eq_voterMissTree,
    filteredMidpointTwoDomainStart_colors] at hcolorfail
  exact voter_midpoint_failure_eighth_forces_cubic_horizon
    m t hm ring hcolorfail

end PPLLDerivedEpochRuntimeNoGo
