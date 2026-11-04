import Leader.Wu.Epoch.ProtectedProtocol
import Leader.Core.RemoteLeaderGuardNoGo
import Leader.Wu.Safety.Counterexamples

/-!
# Non-vacuity and no-go escape for the protected epoch

A canonical `n=4` slot rotation over arbitrary bounded T1 cores is protected and
Definition-1 safe.  The required negative control uses the same physical cores
with every slot forged to zero: selecting the remote edge creates a transient
second leader.  Thus the protocol deliberately does not satisfy
`RemoteEdge2Protected` on every arbitrary unique-leader state; it escapes the
locality no-go by allowing unsafe/multi-leader states before protected entry.
-/

namespace PPLLProtectedEpochRegression

open PPLL PPLLCounterexample PPLLProtectedEpochProtocol
  PPLLRemoteLeaderGuardNoGo

private def boundedT1Core : Fin 4 → BoundedAgentState 2 10 := fun i =>
  BoundedAgentState.ofDomain (counterConfig i)
    (counterConfig_inProtocolDomain i)

/-- Canonical factor-four epoch over an adversarial old P_PLL physical core. -/
def canonicalEpochT1 : Fin 4 → EpochAgentState 4 2 10 :=
  canonicalEpochConfig boundedT1Core

/-- The canonical rotation is a non-vacuous protected configuration. -/
theorem canonicalEpochT1_protected :
    ProtectedEpoch (by omega : 4 > 0) ring4 canonicalEpochT1 :=
  canonicalEpochConfig_protected (by omega) ring4 boundedT1Core

/-- The canonical epoch already satisfies Wu's exact Definition-1 output
safety for the separately named epoch protocol. -/
theorem canonicalEpochT1_isSafe :
    PopulationProtocol.IsSafe
      (epochProtocol (by omega : 4 > 0) 2 10)
      ring4 canonicalEpochT1 isLeaderOutput :=
  protectedEpoch_isSafe (by omega) ring4 canonicalEpochT1_protected

/-- Arbitrary epoch corruption: retain T1's old physical leaders/carriers but
forge every slot to zero. -/
def inconsistentEpochT1 : Fin 4 → EpochAgentState 4 2 10 := fun i =>
  ⟨boundedT1Core i, 0⟩

/-- Select the edge disjoint from the old leader. -/
def inconsistentEpochT1After : Fin 4 → EpochAgentState 4 2 10 :=
  PopulationProtocol.step (epochProtocol (by omega) 2 10)
    ring4 inconsistentEpochT1 2

/-- The arbitrary unique-leader state is intentionally not immediately safe:
role repair makes position two another pre-entry leader while position zero is
untouched. This negative control is exactly how the design avoids the generic
remote-guard no-go. -/
theorem inconsistent_epoch_allows_preentry_second_leader :
    (inconsistentEpochT1 0).core.leader = true ∧
      (inconsistentEpochT1 2).core.leader = false ∧
      (inconsistentEpochT1After 0).core.leader = true ∧
      (inconsistentEpochT1After 2).core.leader = true := by
  decide

/-- Repeating only the same covered edge preserves the two-leader pre-entry
state; convergence relies on the explicit sweep, not arbitrary fairness prose. -/
theorem inconsistentEpochT1After_edge2_fixed :
    PopulationProtocol.step (epochProtocol (by omega : 4 > 0) 2 10)
      ring4 inconsistentEpochT1After 2 = inconsistentEpochT1After := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

/-- The forged-slot start has exactly the remote unique-leader output required
by the generic no-go premise. -/
theorem inconsistentEpochT1_unique_at_zero :
    UniqueLeaderAtZero4 (epochProtocol (by omega : 4 > 0) 2 10)
      isLeaderOutput inconsistentEpochT1 := by
  constructor
  · decide
  · intro i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · contradiction
    · decide
    · decide
    · decide

/-- The epoch protocol explicitly fails immediate remote protection before
entry, so it lies outside the hypothesis class of `RemoteLeaderGuardNoGo`. -/
theorem epochProtocol_not_remoteEdge2Protected :
    ¬RemoteEdge2Protected (epochProtocol (by omega : 4 > 0) 2 10)
      isLeaderOutput := by
  intro hprot
  have h := hprot inconsistentEpochT1 inconsistentEpochT1_unique_at_zero
  have hfollow := h.1
  have hlead : isLeaderOutput
      ((epochProtocol (by omega : 4 > 0) 2 10).output
        (PopulationProtocol.step (epochProtocol (by omega : 4 > 0) 2 10)
          fourRing inconsistentEpochT1 2 2)) = true := by decide
  rw [hlead] at hfollow
  contradiction

/-- The inconsistent all-zero slot assignment is outside the protected epoch. -/
theorem inconsistentEpochT1_not_protected :
    ¬ProtectedEpoch (by omega : 4 > 0) ring4 inconsistentEpochT1 := by
  intro h
  obtain ⟨anchor, rotation, covered, clean⟩ := h
  have hc := covered 0
  simp [inconsistentEpochT1, nextSlot, DirectedRing.rightNeighbor] at hc

end PPLLProtectedEpochRegression
