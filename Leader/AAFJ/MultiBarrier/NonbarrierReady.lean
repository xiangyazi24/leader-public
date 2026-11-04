import Leader.AAFJ.BarrierAlgebra

set_option autoImplicit false

namespace AAFJPK
namespace OriginalNonbarrierRun

open BarrierAlgebra

private theorem pair_nonbarrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n)
    (hnb : ¬ BarrierAt hk ring (labelsOf C) e) :
    ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
  intro h
  exact hnb ((barrierAt_labelsOf_iff hk ring C e).2 h)

private theorem transition_nonbarrier_phase
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnb : ¬ IsBarrier hk u v) :
    (transition hk u v).1.phase = u.phase ∧
      (transition hk u v).2.phase = v.phase := by
  rw [transition_of_nonbarrier hk u v hnb]
  cases hl : v.leader <;>
    cases hb : v.bullet <;>
      cases hp : u.probe <;>
        simp [nonBarrierStep, hl, hb, hp]

private theorem transition_nonbarrier_source_probe_false
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnb : ¬ IsBarrier hk u v) (hu : u.probe = false) :
    (transition hk u v).1.probe = false := by
  rw [transition_of_nonbarrier hk u v hnb]
  cases hl : v.leader <;>
    cases hb : v.bullet <;>
      simp [nonBarrierStep, hl, hb, hu]

private theorem step_nonbarrier_phase
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e x : Fin n)
    (hnb : ¬ BarrierAt hk ring (labelsOf C) e) :
    (((protocol k hk).step ring C e) x).phase = (C x).phase := by
  have hp := transition_nonbarrier_phase hk
    (C e) (C (ring.rightNeighbor e))
    (pair_nonbarrier hk ring C e hnb)
  by_cases hxe : x = e
  · subst x
    simp [PopulationProtocol.step, protocol, hp.1]
  · by_cases hxr : x = ring.rightNeighbor e
    · subst x
      simp [PopulationProtocol.step, protocol, hxe, hp.2]
    · simp [PopulationProtocol.step, protocol, hxe, hxr]

private theorem step_nonbarrier_head_probe_false
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (barrier e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) barrier)
    (hnb : ¬ BarrierAt hk ring (labelsOf C) e)
    (hp : (C (ring.rightNeighbor barrier)).probe = false) :
    (((protocol k hk).step ring C e)
      (ring.rightNeighbor barrier)).probe = false := by
  have hpair := pair_nonbarrier hk ring C e hnb
  by_cases hs : ring.rightNeighbor barrier = e
  · have hsrc : (C e).probe = false := by simpa [hs] using hp
    have hout := transition_nonbarrier_source_probe_false hk
      (C e) (C (ring.rightNeighbor e)) hpair hsrc
    simpa [PopulationProtocol.step, protocol, hs] using hout
  · by_cases hr :
      ring.rightNeighbor barrier = ring.rightNeighbor e
    · have hbe : barrier = e := rightNeighbor_injective ring hr
      subst e
      exact (hnb hbar).elim
    · simp [PopulationProtocol.step, hs, hr, hp]

theorem step_nonbarrier_preserves_advanceReady
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (barrier e : Fin n)
    (hready : AdvanceReady hk ring C barrier)
    (hnb : ¬ BarrierAt hk ring (labelsOf C) e) :
    AdvanceReady hk ring
      ((protocol k hk).step ring C e) barrier := by
  let D := (protocol k hk).step ring C e
  have hnot : ¬ AdvanceReady hk ring C e := by
    intro h
    exact hnb ((barrierAt_labelsOf_iff hk ring C e).2 h.1)
  have hlabels : labelsOf D = labelsOf C := by
    simpa [D] using
      labelsOf_step_eq_self_of_not_ready hk ring C e hnot
  have hbar : BarrierAt hk ring (labelsOf C) barrier :=
    (barrierAt_labelsOf_iff hk ring C barrier).2 hready.1
  have hbarD : BarrierAt hk ring (labelsOf D) barrier := by
    rw [hlabels]
    exact hbar
  have hphaseD : (D barrier).phase = true := by
    exact (step_nonbarrier_phase hk ring C e barrier hnb).trans
      hready.2.1
  have hprobeD :
      (D (ring.rightNeighbor barrier)).probe = false := by
    exact step_nonbarrier_head_probe_false hk ring C barrier e
      hbar hnb hready.2.2
  exact ⟨(barrierAt_labelsOf_iff hk ring D barrier).1 hbarD,
    hphaseD, hprobeD⟩

/-- Execute a finite physical word using the literal original AAFJ protocol. -/
def run {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) :
    (Fin n → State k) → List (Fin n) → Fin n → State k
  | C, [] => C
  | C, e :: es =>
      run hk ring ((protocol k hk).step ring C e) es

/-- Every chosen edge is nonbarrier in the configuration immediately before
that choice. -/
def AllCurrentNonbarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) :
    (Fin n → State k) → List (Fin n) → Prop
  | _, [] => True
  | C, e :: es =>
      ¬ BarrierAt hk ring (labelsOf C) e ∧
        AllCurrentNonbarrier hk ring
          ((protocol k hk).step ring C e) es

theorem run_nonbarrier_preserves_advanceReady
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (barrier : Fin n) (w : List (Fin n))
    (hready : AdvanceReady hk ring C barrier)
    (hw : AllCurrentNonbarrier hk ring C w) :
    AdvanceReady hk ring (run hk ring C w) barrier := by
  induction w generalizing C with
  | nil =>
      exact hready
  | cons e es ih =>
      rcases hw with ⟨he, hes⟩
      have hstep :=
        step_nonbarrier_preserves_advanceReady
          hk ring C barrier e hready he
      simpa [run] using
        ih ((protocol k hk).step ring C e) hstep hes

#check step_nonbarrier_preserves_advanceReady
#check run_nonbarrier_preserves_advanceReady
#print axioms step_nonbarrier_preserves_advanceReady
#print axioms run_nonbarrier_preserves_advanceReady

end OriginalNonbarrierRun
end AAFJPK
