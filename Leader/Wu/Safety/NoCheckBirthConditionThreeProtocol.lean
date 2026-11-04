import Leader.Wu.Safety.NoCheckBirthConditionTwoProtocol

/-!
# Exact finite corrected condition 3

This module proves condition 3 (`noFreeBarrier`) for the same packaged finite
no-CHECK-birth protocol used by corrected conditions 1 and 2.  The physical
refinement from condition 2 says that every exact step is `PeaceView`-equal
either to its input (a deletion-priority branch) or to the isolated repaired
Algorithm-15 update (the normal branch).  Both alternatives preserve every
label, and output safety makes Algorithm 15 preserve every leader bit.  Hence a
barrier after the physical step was already a barrier before it, where its
right endpoint was already the unique leader.

The result needs no nontrivial-ring premise: unlike the literal peaceful-bullet
predicate, `noFreeBarrier` is meaningful on a self-edge.  Authorization bits
and stall timers remain arbitrary because the hypothesis constrains only the
erased physical configuration.
-/

namespace PPLLNoCheckBirthConditionThreeProtocol

open PPLL PPLLRepair PPLLNoCheckBirthRepair
  PPLLExpiringComparisonRepair PPLLNoCheckBirthPhysicalConditionOne
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoGlobal
  PPLLNoCheckBirthConditionTwoProtocol

/-- On output-safe input, an exact packaged no-CHECK-birth step preserves each
physical leader bit at its original ring position. -/
theorem noCheckBirthProtocol_step_leader_eq
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hSafe : OutputSafeConfig hψ ring (eraseExpiringConfig C))
    (e k : Fin n) :
    (eraseExpiringConfig
      ((noCheckBirthProtocol hψ κ τ).step ring C e) k).leader =
      (eraseExpiringConfig C k).leader := by
  have hclass := noCheckBirthProtocol_step_peaceView_classification
    hψ κ τ ring C hSafe e
  rcases hclass with hidentity | hkernel
  · exact congrArg PeaceView.leader (hidentity k)
  · exact (congrArg PeaceView.leader (hkernel k)).trans
      (noCollisionStep_leader_eq hψ ring
        (eraseExpiringConfig C) hSafe e k)

/-- On output-safe input, an exact packaged no-CHECK-birth step preserves each
physical label at its original ring position. -/
theorem noCheckBirthProtocol_step_label_eq
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hSafe : OutputSafeConfig hψ ring (eraseExpiringConfig C))
    (e k : Fin n) :
    (eraseExpiringConfig
      ((noCheckBirthProtocol hψ κ τ).step ring C e) k).label =
      (eraseExpiringConfig C k).label := by
  have hclass := noCheckBirthProtocol_step_peaceView_classification
    hψ κ τ ring C hSafe e
  rcases hclass with hidentity | hkernel
  · exact congrArg PeaceView.label (hidentity k)
  · exact (congrArg PeaceView.label (hkernel k)).trans
      (noCollisionStep_label_eq hψ ring (eraseExpiringConfig C) e k)

/-- **Finite physical corrected condition 3.**  One exact step of the packaged
bounded no-CHECK-birth protocol preserves `noFreeBarrier` from output-safe
erased input.  The theorem covers every ring size and arbitrary executable
authorization bits and stall timers. -/
theorem noFreeBarrier_preserved_noCheckBirthProtocol
    (hψ : ψ > 0) (κ τ : Nat) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hSafe : OutputSafeConfig hψ ring (eraseExpiringConfig C))
    (e : Fin n) :
    noFreeBarrier hψ ring
      (eraseExpiringConfig
        ((noCheckBirthProtocol hψ κ τ).step ring C e)) := by
  intro i
  dsimp only
  intro hbarrier
  have hleft := noCheckBirthProtocol_step_label_eq
    hψ κ τ ring C hSafe e i
  have hright := noCheckBirthProtocol_step_label_eq
    hψ κ τ ring C hSafe e (ring.rightNeighbor i)
  have hbarrierOld : isBarrier hψ
      (eraseExpiringConfig C i)
      (eraseExpiringConfig C (ring.rightNeighbor i)) := by
    unfold isBarrier at hbarrier ⊢
    simpa only [hleft, hright] using hbarrier
  have hrightLeader := hSafe.no_free_barrier i hbarrierOld
  have hleader := noCheckBirthProtocol_step_leader_eq
    hψ κ τ ring C hSafe e (ring.rightNeighbor i)
  unfold AgentState.isLeader at hrightLeader ⊢
  rw [hleader]
  exact hrightLeader

end PPLLNoCheckBirthConditionThreeProtocol
