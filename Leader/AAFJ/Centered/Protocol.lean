import Leader.AAFJ.BarrierAlgebra

/-!
# Centered-renewal variant of generalized AAFJ `P_k`

This module records a proposed protocol modification, not a theorem imported
from Angluin--Aspnes--Fischer--Jiang.  It keeps the same five-field carrier and
all non-barrier behavior.  A phase-one barrier always advances and explicitly
clears the responder probe.  The latter reset is needed because the responder
becomes the new barrier tail.

No stabilization or runtime claim is made in this module.
-/

namespace AAFJPK
namespace CenteredRenewal

set_option autoImplicit false

/-- Modified barrier branch.  Source-order tail-probe conversion still occurs
before the renewal action. -/
def barrierStep {k : Nat} (hk : 0 < k) (u v : State k) : State k × State k :=
  let u₁ := probeHitsBarrier u
  if u₁.phase = false then
    let u₂ := { u₁ with phase := true }
    let v₂ :=
      if v.leader = false then
        { v with probe := true }
      else
        v
    (u₂, v₂)
  else
    (u₁,
      { v with
        label := succLabel hk u₁.label
        phase := false
        bullet := false
        probe := false })

/-- The centered-renewal transition changes only the barrier branch. -/
def transition {k : Nat} (hk : 0 < k) (u v : State k) : State k × State k :=
  if IsBarrier hk u v then
    barrierStep hk u v
  else
    nonBarrierStep u v

/-- Packaged protocol.  Its output remains the physical leader bit. -/
def protocol (k : Nat) (hk : 0 < k) : PopulationProtocol where
  Q := State k
  Y := Bool
  transition := fun u v => transition hk u v
  output := fun q => q.leader

@[simp] theorem protocol_output_eq_leader (k : Nat) (hk : 0 < k)
    (q : State k) :
    (protocol k hk).output q = q.leader := rfl

@[simp] theorem transition_of_barrier {k : Nat} (hk : 0 < k)
    (u v : State k) (h : IsBarrier hk u v) :
    transition hk u v = barrierStep hk u v := by
  simp [transition, h]

@[simp] theorem transition_of_nonbarrier {k : Nat} (hk : 0 < k)
    (u v : State k) (h : ¬ IsBarrier hk u v) :
    transition hk u v = nonBarrierStep u v := by
  simp [transition, h]

/-- The first renewal hit arms the tail and leaves both labels unchanged. -/
theorem barrierStep_phase_zero {k : Nat} (hk : 0 < k)
    (u v : State k) (hphase : u.phase = false) :
    barrierStep hk u v =
      ({ probeHitsBarrier u with phase := true },
        if v.leader = false then { v with probe := true } else v) := by
  simp [barrierStep, hphase]

/-- The second renewal hit always advances, independently of the old head
probe, and sanitizes every mobile field on the new tail. -/
theorem barrierStep_phase_one {k : Nat} (hk : 0 < k)
    (u v : State k) (hphase : u.phase = true) :
    barrierStep hk u v =
      (probeHitsBarrier u,
        { v with
          label := succLabel hk u.label
          phase := false
          bullet := false
          probe := false }) := by
  simp [barrierStep, hphase]

theorem barrierStep_phase_zero_labels {k : Nat} (hk : 0 < k)
    (u v : State k) (hphase : u.phase = false) :
    (barrierStep hk u v).1.label = u.label ∧
      (barrierStep hk u v).2.label = v.label := by
  by_cases hv : v.leader = false <;>
    simp [barrierStep_phase_zero hk u v hphase, hv]

theorem barrierStep_phase_one_labels {k : Nat} (hk : 0 < k)
    (u v : State k) (hphase : u.phase = true) :
    (barrierStep hk u v).1.label = u.label ∧
      (barrierStep hk u v).2.label = succLabel hk u.label := by
  simp [barrierStep_phase_one hk u v hphase]

theorem barrierStep_phase_one_freshTail {k : Nat} (hk : 0 < k)
    (u v : State k) (hphase : u.phase = true) :
    (barrierStep hk u v).2.phase = false ∧
      (barrierStep hk u v).2.probe = false ∧
      (barrierStep hk u v).2.bullet = false := by
  simp [barrierStep_phase_one hk u v hphase]

/-- Removing the veto without clearing the responder probe would leave a
probe on the new barrier tail.  The actual variant rules out that local fault
definitionally. -/
theorem phase_one_clears_forged_head_probe {k : Nat} (hk : 0 < k)
    (u v : State k) (hphase : u.phase = true) (_hprobe : v.probe = true) :
    (barrierStep hk u v).2.probe = false := by
  simp [barrierStep_phase_one hk u v hphase]

/-- Natural encoding of the renewal phase, used only in proof coordinates. -/
def phaseNat : Bool → Nat
  | false => 0
  | true => 1

/-- Exact doubled-coordinate clock: a phase-zero hit advances the phase on the
old tail, while a phase-one hit advances the physical tail by one edge and
resets the new tail phase.  Either way the lifted coordinate gains one. -/
theorem barrierStep_correctedCoord_tick {k : Nat} (hk : 0 < k)
    (u v : State k) :
    (if u.phase = false then
        phaseNat (barrierStep hk u v).1.phase
      else
        2 + phaseNat (barrierStep hk u v).2.phase) =
      phaseNat u.phase + 1 := by
  cases hphase : u.phase <;> simp [barrierStep, phaseNat, hphase]

/-! ## Connection to charged-barrier algebra -/

/-- In the centered variant every phase-one barrier is ready to advance; the
source protocol's responder-probe veto has been removed. -/
def PairAdvanceReady {k : Nat} (hk : 0 < k) (u v : State k) : Prop :=
  IsBarrier hk u v ∧ u.phase = true

/-- Centered readiness at one physical ring edge. -/
def AdvanceReady {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n) : Prop :=
  PairAdvanceReady hk (C e) (C (ring.rightNeighbor e))

/-- Outside the centered advance branch, both labels are preserved. -/
theorem transition_labels_of_not_pairAdvanceReady {k : Nat} (hk : 0 < k)
    (u v : State k) (hnot : ¬ PairAdvanceReady hk u v) :
    (transition hk u v).1.label = u.label ∧
      (transition hk u v).2.label = v.label := by
  by_cases hbar : IsBarrier hk u v
  · cases hphase : u.phase with
    | false =>
        rw [transition_of_barrier hk u v hbar]
        rw [barrierStep_phase_zero hk u v hphase]
        constructor
        · simp
        · split <;> rfl
    | true =>
        exact (hnot ⟨hbar, hphase⟩).elim
  · rw [transition_of_nonbarrier hk u v hbar]
    cases hv : v.leader <;>
      cases hb : v.bullet <;>
      cases hp : u.probe <;>
      simp [nonBarrierStep, hv, hb, hp]

/-- A non-advancing packaged centered step preserves the full label map. -/
theorem labelsOf_step_eq_self_of_not_ready {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (e : Fin n)
    (hnot : ¬ AdvanceReady hk ring C e) :
    BarrierAlgebra.labelsOf ((protocol k hk).step ring C e) =
      BarrierAlgebra.labelsOf C := by
  have hp := transition_labels_of_not_pairAdvanceReady hk
    (C e) (C (ring.rightNeighbor e)) hnot
  funext i
  by_cases hie : i = e
  · subst i
    simp [BarrierAlgebra.labelsOf, PopulationProtocol.step, protocol, hp.1]
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simp [BarrierAlgebra.labelsOf, PopulationProtocol.step, protocol,
        hie, hp.2]
    · simp [BarrierAlgebra.labelsOf, PopulationProtocol.step, protocol,
        hie, hir]

/-- A ready centered step has exactly the abstract charged advance effect. -/
theorem labelsOf_step_eq_advance_of_ready {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hready : AdvanceReady hk ring C e) :
    BarrierAlgebra.labelsOf ((protocol k hk).step ring C e) =
      BarrierAlgebra.advanceLabels hk ring (BarrierAlgebra.labelsOf C) e := by
  rcases hready with ⟨hbar, hphase⟩
  have hre : ring.rightNeighbor e ≠ e :=
    BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
  have her : e ≠ ring.rightNeighbor e := Ne.symm hre
  have hpair :
      transition hk (C e) (C (ring.rightNeighbor e)) =
        (probeHitsBarrier (C e),
          { C (ring.rightNeighbor e) with
            label := succLabel hk (C e).label
            phase := false
            bullet := false
            probe := false }) := by
    rw [transition_of_barrier hk _ _ hbar]
    exact barrierStep_phase_one hk _ _ hphase
  funext i
  by_cases hie : i = e
  · subst i
    simp [BarrierAlgebra.labelsOf, BarrierAlgebra.advanceLabels,
      PopulationProtocol.step, protocol, hpair, her]
  · by_cases hir : i = ring.rightNeighbor e
    · simp [BarrierAlgebra.labelsOf, BarrierAlgebra.advanceLabels,
        PopulationProtocol.step, protocol, hpair, hir, hre]
    · simp [BarrierAlgebra.labelsOf, BarrierAlgebra.advanceLabels,
        PopulationProtocol.step, protocol, hpair, hie, hir]

/-- Every centered physical step weakly decreases charged-barrier support. -/
theorem protocol_step_barrierCount_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n) :
    BarrierAlgebra.barrierCount hk ring
        (BarrierAlgebra.labelsOf ((protocol k hk).step ring C e)) ≤
      BarrierAlgebra.barrierCount hk ring (BarrierAlgebra.labelsOf C) := by
  by_cases hready : AdvanceReady hk ring C e
  · rw [labelsOf_step_eq_advance_of_ready hk ring hn2 C e hready]
    exact BarrierAlgebra.barrierCount_advance_le hk ring hn2
      (BarrierAlgebra.labelsOf C) e
  · rw [labelsOf_step_eq_self_of_not_ready hk ring C e hready]
    exact Nat.le_refl _

/-- On a nondivisible ring the centered process can never lose its last
barrier, so the exactly-one-barrier slice is transition closed. -/
theorem protocol_step_preserves_oneBarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hndvd : ¬ k ∣ n)
    (hone : BarrierAlgebra.barrierCount hk ring
      (BarrierAlgebra.labelsOf C) = 1) :
    BarrierAlgebra.barrierCount hk ring
        (BarrierAlgebra.labelsOf ((protocol k hk).step ring C e)) = 1 := by
  have hle := protocol_step_barrierCount_le hk ring hn2 C e
  have hpos := BarrierAlgebra.barrierCount_pos_of_not_dvd hk ring
    ((protocol k hk).step ring C e) hndvd
  omega

/-- The carrier is literally unchanged from generalized `P_k`. -/
def states (k : Nat) : ExhaustiveList (State k) :=
  AAFJPK.states k

theorem states_values_length (k : Nat) :
    (states k).values.length = 16 * k := by
  exact AAFJPK.states_values_length k

theorem states_values_nodup (k : Nat) :
    (states k).values.Nodup := by
  exact AAFJPK.states_values_nodup k

theorem mem_states (k : Nat) (q : State k) :
    q ∈ (states k).values := by
  exact (states k).complete q

end CenteredRenewal
end AAFJPK
