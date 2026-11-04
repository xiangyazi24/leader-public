import Leader.Wu.Birth.ShortDoneTerminalObserver
import Leader.Wu.Elimination.GapClosure

/-!
# Metadata birth survives the actual terminal physical tail

`birthEvent` is computed on normalized metadata.  A true event is not simply
assumed to survive: the proof follows initializeNewborn, the explicit
both-leader collision, and the real K2 C-kernel.
-/

namespace BirthShortDoneTerminalBirthPhysical

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open K2BirthDispatcher ExpiringK2Projection LDSinkKernelC

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ n : Nat}

/-- A left leader protected by a true shield cannot be deleted by the K2 row
when the responder is a follower.  This is the exact case produced by a
left-only `initializeNewborn`. -/
private theorem k2_left_protected_leader
    (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ)
    (hl : l.core.core.leader = true)
    (hs : l.core.core.shield = true)
    (hr : r.core.core.leader = false) :
    (ExpiringK2Projection.row hψ l r).1.core.core.leader = true := by
  have ho := ExpiringK2Projection.observe_row hψ l r
  have hl' : (ExpiringK2Projection.observeCell l).leader = true := hl
  have hs' : (ExpiringK2Projection.observeCell l).shield = true := hs
  have hr' : (ExpiringK2Projection.observeCell r).leader = false := hr
  have hk :
      (sinkKernelC (by decide : 0 < 1)
        (ExpiringK2Projection.observeCell l)
        (ExpiringK2Projection.observeCell r)).1.leader = true := by
    cases h :
        (sinkKernelC (by decide : 0 < 1)
          (ExpiringK2Projection.observeCell l)
          (ExpiringK2Projection.observeCell r)).1.leader with
    | true => rfl
    | false =>
        have hd := (K2GlobalGapClosure.kernel_delete_iff
          (by decide : 0 < 1)
          (ExpiringK2Projection.observeCell l)
          (ExpiringK2Projection.observeCell r) hl' hr').mp h
        have hbad : (true : Bool) = false := hs'.symm.trans hd.1
        cases hbad
  have he := congrArg
    (fun q : AgentState 1 × AgentState 1 => q.1.leader) ho
  change (ExpiringK2Projection.row hψ l r).1.core.core.leader =
    (sinkKernelC (by decide : 0 < 1)
      (ExpiringK2Projection.observeCell l)
      (ExpiringK2Projection.observeCell r)).1.leader at he
  exact he.trans hk

/-- The responder leader bit is framed exactly by the K2 C-kernel. -/
private theorem k2_right_leader
    (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ)
    (hr : r.core.core.leader = true) :
    (ExpiringK2Projection.row hψ l r).2.core.core.leader = true := by
  have ho := ExpiringK2Projection.observe_row hψ l r
  have hk := LDSinkTwoGapEpochSuccessor.kernelC_right_leader_eq
    (by decide : 0 < 1)
    (ExpiringK2Projection.observeCell l)
    (ExpiringK2Projection.observeCell r)
  have hr' : (ExpiringK2Projection.observeCell r).leader = true := hr
  have he := congrArg
    (fun q : AgentState 1 × AgentState 1 => q.2.leader) ho
  change (ExpiringK2Projection.row hψ l r).2.core.core.leader =
    (sinkKernelC (by decide : 0 < 1)
      (ExpiringK2Projection.observeCell l)
      (ExpiringK2Projection.observeCell r)).2.leader at he
  exact he.trans (hk.trans hr')

/-- A true newborn bit on either role survives the complete physical tail as
at least one physical leader. -/
private theorem finalPhysical_birth_has_leader
    (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ)
    (hb : K2BirthDispatcher.newborn oldL metaL = true ∨
      K2BirthDispatcher.newborn oldR metaR = true) :
    (K2BirthDispatcher.finalPhysical hψ oldL oldR metaL metaR).1.core.core.leader = true ∨
      (K2BirthDispatcher.finalPhysical hψ oldL oldR metaL metaR).2.core.core.leader = true := by
  let iL := K2BirthDispatcher.initializeNewborn oldL metaL
  let iR := K2BirthDispatcher.initializeNewborn oldR metaR
  change
    (K2BirthDispatcher.collisionRow hψ iL iR).1.core.core.leader = true ∨
      (K2BirthDispatcher.collisionRow hψ iL iR).2.core.core.leader = true
  rcases hb with hbL | hbR
  · have hx := K2BirthDispatcher.initializeNewborn_exact oldL metaL hbL
    have hL : iL.core.core.leader = true := hx.2.1
    have hS : iL.core.core.shield = true := hx.2.2.2.1
    by_cases hR : iR.core.core.leader = true
    · exact Or.inr
        (K2BirthDispatcher.collisionRow_of_both hψ iL iR hL hR).2.1
    · have hRf : iR.core.core.leader = false := by
        cases h : iR.core.core.leader with
        | false => rfl
        | true => exact (hR h).elim
      have hnot : ¬ (iL.core.core.leader = true ∧ iR.core.core.leader = true) :=
        fun h => hR h.2
      rw [K2BirthDispatcher.collisionRow_of_not_both hψ iL iR hnot]
      exact Or.inl (k2_left_protected_leader hψ iL iR hL hS hRf)
  · have hx := K2BirthDispatcher.initializeNewborn_exact oldR metaR hbR
    have hR : iR.core.core.leader = true := hx.2.1
    by_cases hL : iL.core.core.leader = true
    · exact Or.inr
        (K2BirthDispatcher.collisionRow_of_both hψ iL iR hL hR).2.1
    · have hnot : ¬ (iL.core.core.leader = true ∧ iR.core.core.leader = true) :=
        fun h => hL h.1
      rw [K2BirthDispatcher.collisionRow_of_not_both hψ iL iR hnot]
      exact Or.inr (k2_right_leader hψ iL iR hR)

/-- Actual repaired terminal row: the observer's metadata birth event implies
at least one physical leader after newborn initialization, collision, and K2. -/
theorem birthEvent_true_row_has_physical_leader
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hb : BirthShortDoneTerminalObserver.birthEvent
      hψ hwidth hle l r = true) :
    (BirthShortDoneTerminalHost.row hψ hwidth hle l r).1.core.core.leader = true ∨
      (BirthShortDoneTerminalHost.row hψ hwidth hle l r).2.core.core.leader = true := by
  let q := BirthShortDoneTerminalHost.metadata hψ hwidth hle l r
  have hb' :
      K2BirthDispatcher.newborn l q.1 = true ∨
        K2BirthDispatcher.newborn r q.2 = true := by
    change (K2BirthDispatcher.newborn l q.1 ||
      K2BirthDispatcher.newborn r q.2) = true at hb
    simpa only [Bool.or_eq_true] using hb
  change
    (K2BirthDispatcher.finalPhysical hψ l r q.1 q.2).1.core.core.leader = true ∨
      (K2BirthDispatcher.finalPhysical hψ l r q.1 q.2).2.core.core.leader = true
  exact finalPhysical_birth_has_leader hψ l r q.1 q.2 hb'

/-! ## Ring lift: only for genuinely distinct endpoints -/

private theorem terminal_step_left
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (e : Fin n) :
    BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e e =
      (BirthShortDoneTerminalHost.row hψ hwidth hle
        (C e) (C (ring.rightNeighbor e))).1 := by
  simp only [BirthShortDoneTerminalConsumer.step, PopulationProtocol.step,
    BirthShortDoneTerminalConsumer.protocol, updatePair, if_true]

private theorem terminal_step_right
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e) :
    BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e
        (ring.rightNeighbor e) =
      (BirthShortDoneTerminalHost.row hψ hwidth hle
        (C e) (C (ring.rightNeighbor e))).2 := by
  simp only [BirthShortDoneTerminalConsumer.step, PopulationProtocol.step,
    BirthShortDoneTerminalConsumer.protocol, updatePair, if_neg hne, if_true]

/-- On a distinct physical edge, whichever local row output carries the
surviving leader is actually inserted into the successor configuration. -/
theorem birthEvent_true_step_has_physical_leader_of_distinct
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (hb : BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle
      (C e) (C (ring.rightNeighbor e)) = true) :
    ∃ i : Fin n,
      (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e i).core.core.leader = true := by
  have hrow := birthEvent_true_row_has_physical_leader hψ hwidth hle
    (C e) (C (ring.rightNeighbor e)) hb
  rcases hrow with hL | hR
  · refine ⟨e, ?_⟩
    rw [terminal_step_left hψ hwidth hle ring C e]
    exact hL
  · refine ⟨ring.rightNeighbor e, ?_⟩
    rw [terminal_step_right hψ hwidth hle ring C e hne]
    exact hR

/-- Hence every non-singleton directed ring gets the distinct-edge lift. -/
theorem birthEvent_true_step_has_physical_leader_of_one_lt
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hb : BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle
      (C e) (C (ring.rightNeighbor e)) = true) :
    ∃ i : Fin n,
      (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e i).core.core.leader = true :=
  birthEvent_true_step_has_physical_leader_of_distinct
    hψ hwidth hle ring C e
      (rightNeighbor_ne_self_of_one_lt ring hn e) hb

#print axioms BirthShortDoneTerminalBirthPhysical.birthEvent_true_row_has_physical_leader
#print axioms BirthShortDoneTerminalBirthPhysical.birthEvent_true_step_has_physical_leader_of_distinct
#print axioms BirthShortDoneTerminalBirthPhysical.birthEvent_true_step_has_physical_leader_of_one_lt

end BirthShortDoneTerminalBirthPhysical
