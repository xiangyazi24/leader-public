import Leader.Wu.Epoch.VoterSumTools
import Leader.Wu.Epoch.VoterColorDrift
import Leader.Wu.Epoch.VoterActionTree
import Leader.Wu.Epoch.FilterProtectedPotential
import Leader.Wu.Epoch.FilterProtectedActionTree
import Leader.Wu.Epoch.FilterCubicBlock
import Leader.Wu.Epoch.FilterSweep

/-!
# Definition-1 lower bridge for the filtered epoch voter process

The cubic obstruction for the midpoint two-domain start is stated for missing
epoch-color consensus (and hence for missing `ProtectedEpoch`).  The polynomial
upper bound reaches Wu's semantic `IsSafe` predicate in the opposite direction,
using `ProtectedEpoch -> IsSafe`.  This file supplies the missing lower bridge.

The key semantic fact is stronger than the midpoint specialization: on every
nontrivial ring, a configuration that is Definition-1 safe for the filtered
epoch protocol must already have voter-color consensus.  To expose any chosen
color, a consecutive suffix of directed edges propagates it to physical
position zero; the standard non-wrap sweep then produces a protected rotation
with that color.  Definition-1 output preservation forces all such protected
endpoints to have the same color, so the original word was constant.
-/

namespace PPLLEpochVoterDefinitionOneLower

open PPLLResearchFormulation PPLLProtectedEpochProtocol
  PPLLProtectedEpochSweep PPLLDerivedEpochRepair
  PPLLDerivedEpochSweep PPLLEpochVoterReduction
  PPLLEpochVoterTwoDomain PPLLEpochVoterFiniteTree
  PPLLEpochVoterRuntimeObstruction PPLLDerivedEpochRuntimeNoGo
  PPLLEpochVoterPolynomialUpper

/-! ## Consecutive directed schedules -/

/-- The consecutive directed edges
`start, start+1, ..., start+len-1`, with no arithmetic wrap in their indices.
The final edge may still act across the physical wrap edge. -/
def forwardIntervalSchedule (n start : Nat) :
    (len : Nat) -> start + len <= n -> DetSchedule n
  | 0, _ => []
  | len + 1, h =>
      forwardIntervalSchedule n start len (by omega) ++
        [⟨start + len, by omega⟩]

/-- The interval starting at zero is the existing ordered sweep prefix. -/
theorem forwardIntervalSchedule_zero_eq_epochSweepPrefix
    (n len : Nat) (h : len <= n) :
    forwardIntervalSchedule n 0 len (by omega) =
      epochSweepPrefix n len h := by
  induction len with
  | zero => rfl
  | succ len ih =>
      simp only [forwardIntervalSchedule, epochSweepPrefix]
      have hprev := ih (by omega : len <= n)
      rw [hprev]
      congr 2
      apply Fin.ext
      simp

private theorem runDirectedVoterSchedule_append
    (ring : DirectedRing n) (D : Fin n -> Fin n)
    (s t : DetSchedule n) :
    runDirectedVoterSchedule ring D (s ++ t) =
      runDirectedVoterSchedule ring
        (runDirectedVoterSchedule ring D s) t := by
  induction s generalizing D with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runDirectedVoterSchedule]
      exact ih (directedVoterStep ring D e)

/-- A consecutive interval propagates its starting color to the endpoint after
the last edge, including the possible wrap from `n-1` to zero. -/
theorem runDirectedVoterSchedule_forwardInterval_endpoint
    (hn2 : 1 < n) (ring : DirectedRing n)
    (D : Fin n -> Fin n) (start len : Nat)
    (hstart : start < n) (hbound : start + len <= n) :
    runDirectedVoterSchedule ring D
        (forwardIntervalSchedule n start len hbound)
        ⟨(start + len) % n, Nat.mod_lt _ ring.hn⟩ =
      D ⟨start, hstart⟩ := by
  induction len with
  | zero =>
      have hindex :
          (⟨(start + 0) % n, Nat.mod_lt _ ring.hn⟩ : Fin n) =
            ⟨start, hstart⟩ := by
        apply Fin.ext
        simpa using Nat.mod_eq_of_lt hstart
      rw [hindex]
      rfl
  | succ len ih =>
      rw [forwardIntervalSchedule, runDirectedVoterSchedule_append]
      simp only [runDirectedVoterSchedule]
      let e : Fin n := ⟨start + len, by omega⟩
      let endpoint : Fin n :=
        ⟨(start + (len + 1)) % n, Nat.mod_lt _ ring.hn⟩
      have hprev := ih (by omega : start + len <= n)
      have hneighbor : ring.rightNeighbor e = endpoint := by
        apply Fin.ext
        simp [e, endpoint, DirectedRing.rightNeighbor, Nat.add_assoc]
      change directedVoterStep ring
          (runDirectedVoterSchedule ring D
            (forwardIntervalSchedule n start len (by omega))) e endpoint =
        D ⟨start, hstart⟩
      rw [<- hneighbor]
      have hne := PPLLEpochVoterPolynomialUpper.rightNeighbor_ne
        hn2 ring e
      unfold directedVoterStep
      rw [if_neg hne, if_pos rfl]
      have hprevIndex :
          (⟨(start + len) % n, Nat.mod_lt _ ring.hn⟩ : Fin n) = e := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (by omega)
      rw [<- hprevIndex]
      exact hprev

/-- Consecutively propagating from position `i` through the wrap edge writes
the original color at `i` into physical position zero. -/
def colorToZeroSchedule (i : Fin n) : DetSchedule n :=
  forwardIntervalSchedule n i.val (n - i.val) (by omega)

theorem runDirectedVoterSchedule_colorToZero_at_zero
    (hn2 : 1 < n) (ring : DirectedRing n)
    (D : Fin n -> Fin n) (i : Fin n) :
    runDirectedVoterSchedule ring D (colorToZeroSchedule i)
        ⟨0, ring.hn⟩ = D i := by
  have h := runDirectedVoterSchedule_forwardInterval_endpoint
    hn2 ring D i.val (n - i.val) i.isLt (by omega)
  have hsum : i.val + (n - i.val) = n := by omega
  simpa [colorToZeroSchedule, hsum] using h

/-! ## Reachable protected endpoints expose the chosen color -/

/-- Every explicit filtered schedule is a genuine abstract-protocol reachable
execution. -/
theorem filteredRunLocalSchedule_reachable
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n -> EpochAgentState n ψ κ) (s : DetSchedule n) :
    PopulationProtocol.Reachable
      (ppllEpochFilterProtocol hψ κ ring.hn) ring C
      (runLocalSchedule ring
        (ppllEpochFilterTransition hψ κ ring.hn) C s) := by
  induction s generalizing C with
  | nil =>
      exact @PopulationProtocol.Reachable.refl n
        (ppllEpochFilterProtocol hψ κ ring.hn) ring C
  | cons e rest ih =>
      exact (PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩).trans
        (ih (localStep ring
          (ppllEpochFilterTransition hψ κ ring.hn) C e))

/-- The protected endpoint of the standard non-wrap sweep has constant epoch
color equal to the input color at physical position zero. -/
theorem epochColorConfig_ppllEpochFilterPreWrapRun
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n -> EpochAgentState n ψ κ) (i : Fin n) :
    epochColorConfig
        (ppllEpochFilterPreWrapRun hψ κ hn2 ring C) i =
      epochColorConfig C ⟨0, ring.hn⟩ := by
  let P := ppllEpochFilterPreWrapRun hψ κ hn2 ring C
  have hprotected : ProtectedEpoch ring.hn ring P :=
    ppllEpochFilter_sweep_enters_protected hψ κ hn2 ring C
  obtain ⟨a, ha⟩ :=
    ((protectedEpoch_iff_colorConsensus_clean ring P).1 hprotected).1
  let last : Fin n := ⟨n - 1, by omega⟩
  have hprop := runDirectedVoterSchedule_forwardInterval_endpoint
    hn2 ring (epochColorConfig C) 0 (n - 1) (by omega) (by omega)
  have hsched : forwardIntervalSchedule n 0 (n - 1) (by omega) =
      epochPreWrapSweep n hn2 := by
    exact forwardIntervalSchedule_zero_eq_epochSweepPrefix
      n (n - 1) (by omega)
  rw [hsched] at hprop
  have hproject := epochColorConfig_runLocalSchedule
    hψ κ ring C (epochPreWrapSweep n hn2)
  change epochColorConfig P =
      runDirectedVoterSchedule ring (epochColorConfig C)
        (epochPreWrapSweep n hn2) at hproject
  have hendpoint :
      (⟨(0 + (n - 1)) % n, Nat.mod_lt _ ring.hn⟩ : Fin n) = last := by
    apply Fin.ext
    simp [last, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  rw [hendpoint] at hprop
  have hlast : epochColorConfig P last =
      epochColorConfig C ⟨0, ring.hn⟩ := by
    rw [hproject]
    exact hprop
  calc
    epochColorConfig P i = a := ha i
    _ = epochColorConfig P last := (ha last).symm
    _ = epochColorConfig C ⟨0, ring.hn⟩ := hlast

/-- Running the suffix schedule exposes the chosen original color at position
zero of the resulting physical configuration. -/
theorem epochColorConfig_run_colorToZero_at_zero
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n -> EpochAgentState n ψ κ) (i : Fin n) :
    epochColorConfig
        (runLocalSchedule ring
          (ppllEpochFilterTransition hψ κ ring.hn) C
          (colorToZeroSchedule i)) ⟨0, ring.hn⟩ =
      epochColorConfig C i := by
  rw [epochColorConfig_runLocalSchedule]
  exact runDirectedVoterSchedule_colorToZero_at_zero
    hn2 ring (epochColorConfig C) i

private theorem clean_slot_zero_of_leader_output
    (hψ : ψ > 0) (κ : Nat) (hn : n > 0)
    (u : EpochAgentState n ψ κ) (hu : EpochClean u)
    (hout : isLeaderOutput
      ((ppllEpochFilterProtocol hψ κ hn).output u) = true) :
    u.slot.val = 0 := by
  have hleader := hu.leader_eq
  change isLeaderOutput
    (if u.core.leader then LeaderOutput.leader else .follower) = true at hout
  rw [hleader] at hout
  cases hs : slotLeader u.slot
  · simp [hs, isLeaderOutput] at hout
  · simpa [slotLeader] using hs

/-- Two protected configurations with the same pointwise outputs have the same
epoch-color word. -/
theorem protectedEpoch_color_eq_of_output_eq
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (A B : Fin n -> EpochAgentState n ψ κ)
    (hA : ProtectedEpoch ring.hn ring A)
    (hB : ProtectedEpoch ring.hn ring B)
    (hout : ∀ i, (ppllEpochFilterProtocol hψ κ ring.hn).output (A i) =
      (ppllEpochFilterProtocol hψ κ ring.hn).output (B i)) :
    epochColorConfig A = epochColorConfig B := by
  obtain ⟨⟨a, ha⟩, hcleanA⟩ :=
    (protectedEpoch_iff_colorConsensus_clean ring A).1 hA
  obtain ⟨⟨b, hb⟩, hcleanB⟩ :=
    (protectedEpoch_iff_colorConsensus_clean ring B).1 hB
  obtain ⟨leader, hleader, _⟩ := ppllEpochFilter_unique hψ κ ring A hA
  have hleaderB : isLeaderOutput
      ((ppllEpochFilterProtocol hψ κ ring.hn).output (B leader)) = true := by
    rw [<- hout leader]
    exact hleader
  have hzeroA := clean_slot_zero_of_leader_output
    hψ κ ring.hn (A leader) (hcleanA leader) hleader
  have hzeroB := clean_slot_zero_of_leader_output
    hψ κ ring.hn (B leader) (hcleanB leader) hleaderB
  have hslot : (A leader).slot = (B leader).slot := by
    apply Fin.ext
    omega
  have hcolorAt : epochColorConfig A leader = epochColorConfig B leader := by
    unfold epochColorConfig epochColor
    rw [hslot]
  have hab : a = b := (ha leader).symm.trans (hcolorAt.trans (hb leader))
  funext i
  rw [ha i, hb i, hab]

/-! ## Definition-1 safety forces voter consensus -/

/-- On every nontrivial ring, semantic Definition-1 safety for the filtered
epoch protocol forces epoch-color consensus.  No cleanliness or authorized
initialization premise is used. -/
theorem epochColorConsensus_of_filtered_isSafe
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n -> EpochAgentState n ψ κ)
    (hsafe : PopulationProtocol.IsSafe
      (ppllEpochFilterProtocol hψ κ ring.hn) ring C isLeaderOutput) :
    EpochColorConsensus C := by
  let zero : Fin n := ⟨0, ring.hn⟩
  let base := ppllEpochFilterPreWrapRun hψ κ hn2 ring C
  have hbaseProtected : ProtectedEpoch ring.hn ring base :=
    ppllEpochFilter_sweep_enters_protected hψ κ hn2 ring C
  have hbaseReach : PopulationProtocol.Reachable
      (ppllEpochFilterProtocol hψ κ ring.hn) ring C base :=
    ppllEpochFilter_sweep_reachable hψ κ hn2 ring C
  refine ⟨epochColorConfig C zero, ?_⟩
  intro i
  let moved := runLocalSchedule ring
    (ppllEpochFilterTransition hψ κ ring.hn) C (colorToZeroSchedule i)
  let exposed := ppllEpochFilterPreWrapRun hψ κ hn2 ring moved
  have hmovedReach : PopulationProtocol.Reachable
      (ppllEpochFilterProtocol hψ κ ring.hn) ring C moved :=
    filteredRunLocalSchedule_reachable hψ κ ring C
      (colorToZeroSchedule i)
  have hexposedProtected : ProtectedEpoch ring.hn ring exposed :=
    ppllEpochFilter_sweep_enters_protected hψ κ hn2 ring moved
  have hexposedReach : PopulationProtocol.Reachable
      (ppllEpochFilterProtocol hψ κ ring.hn) ring C exposed :=
    hmovedReach.trans
      (ppllEpochFilter_sweep_reachable hψ κ hn2 ring moved)
  have hout : ∀ j,
      (ppllEpochFilterProtocol hψ κ ring.hn).output (base j) =
        (ppllEpochFilterProtocol hψ κ ring.hn).output (exposed j) := by
    intro j
    exact (hsafe.2 base hbaseReach j).trans
      (hsafe.2 exposed hexposedReach j).symm
  have hcolors := protectedEpoch_color_eq_of_output_eq
    hψ κ ring base exposed hbaseProtected hexposedProtected hout
  have hbaseColor := epochColorConfig_ppllEpochFilterPreWrapRun
    hn2 hψ κ ring C zero
  have hexposedColor := epochColorConfig_ppllEpochFilterPreWrapRun
    hn2 hψ κ ring moved zero
  have hmovedColor := epochColorConfig_run_colorToZero_at_zero
    hn2 hψ κ ring C i
  have hatZero := congrFun hcolors zero
  change epochColorConfig base zero = epochColorConfig exposed zero at hatZero
  rw [hbaseColor, hexposedColor, hmovedColor] at hatZero
  exact hatZero.symm

theorem filtered_not_isSafe_of_not_colorConsensus
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n -> EpochAgentState n ψ κ)
    (hC : ¬ EpochColorConsensus C) :
    ¬ PopulationProtocol.IsSafe
      (ppllEpochFilterProtocol hψ κ ring.hn) ring C isLeaderOutput := by
  intro hsafe
  exact hC (epochColorConsensus_of_filtered_isSafe
    hn2 hψ κ ring C hsafe)

/-! ## Exact miss-tree lower bridge and cubic consequence -/

private theorem sum_ofFn_le
    (f g : Fin n -> Nat) (hfg : ∀ i, f i <= g i) :
    (List.ofFn f).sum <= (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

/-- Every scheduler word that still misses epoch-color consensus at time `t`
ends at a configuration that is not Definition-1 safe. -/
theorem filteredColorMissTree_le_definitionOneFinalMissTree
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n -> EpochAgentState n ψ κ) (t : Nat) :
    filteredColorMissTree hψ κ ring C t <=
      filteredDefinitionOneFinalMissTree hψ κ ring C t := by
  induction t generalizing C with
  | zero =>
      simp only [filteredColorMissTree,
        filteredDefinitionOneFinalMissTree]
      by_cases hC : EpochColorConsensus C
      · rw [if_pos hC]
        exact Nat.zero_le _
      · have hunsafe := filtered_not_isSafe_of_not_colorConsensus
          hn2 hψ κ ring C hC
        rw [if_neg hC, if_neg hunsafe]
        omega
  | succ t ih =>
      simp only [filteredColorMissTree,
        filteredDefinitionOneFinalMissTree]
      by_cases hC : EpochColorConsensus C
      · rw [if_pos hC]
        exact Nat.zero_le _
      · rw [if_neg hC]
        exact sum_ofFn_le _ _ (fun e => ih
          (localStep ring
            (ppllEpochFilterTransition hψ κ ring.hn) C e))

/-- Definition-1 failure at most `1/8` from R27's clean midpoint two-domain
start already forces a cubic interaction horizon. -/
theorem filteredDefinitionOne_midpoint_failure_eighth_forces_cubic_horizon
    (m t : Nat) (hm : 4 <= m)
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing (2 * m))
    (base : Fin (2 * m) -> BoundedAgentState ψ κ)
    (hfail : 8 * filteredDefinitionOneFinalMissTree hψ κ ring
        (filteredMidpointTwoDomainStart m hm base) t <= (2 * m) ^ t) :
    m ^ 3 <= 2 * t := by
  have hsub := filteredColorMissTree_le_definitionOneFinalMissTree
    (by omega : 1 < 2 * m) hψ κ ring
      (filteredMidpointTwoDomainStart m hm base) t
  have hcolorfail : 8 * filteredColorMissTree hψ κ ring
      (filteredMidpointTwoDomainStart m hm base) t <= (2 * m) ^ t :=
    Nat.le_trans (Nat.mul_le_mul_left 8 hsub) hfail
  rw [filteredColorMissTree_eq_voterMissTree,
    filteredMidpointTwoDomainStart_colors] at hcolorfail
  exact voter_midpoint_failure_eighth_forces_cubic_horizon
    m t hm ring hcolorfail

end PPLLEpochVoterDefinitionOneLower
