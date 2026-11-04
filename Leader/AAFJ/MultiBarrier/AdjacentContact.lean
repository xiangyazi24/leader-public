import Leader.AAFJ.MultiBarrier.SupportTransport
import Leader.AAFJ.Centered.CoalescenceFrame

/-!
# Deterministic adjacent-contact service for original AAFJ `P_k`

This file records only literal transition consequences for the original
journal protocol.  It contains no scheduler, probability, or centered-renewal
statement.  The first bridge identifies exactly which ordinary successor hit
clears a blocked barrier-head probe and therefore makes the old barrier ready.
-/

namespace AAFJPK
namespace BarrierAlgebra

set_option autoImplicit false

/-- A blocked phase-one barrier becomes ready after one ordinary successor
service exactly when that successor does not see a leader carrying a bullet.

The result crosses from the literal Protocol-6 transition to the algebraic
`PairAdvanceReady` predicate used by the label-update theorems. -/
theorem pairAdvanceReady_after_successor_service_iff
    {k : Nat} (hk : 0 < k) (u v w : State k)
    (hbar : IsBarrier hk u v)
    (hphase : u.phase = true)
    (hblocked : v.probe = true)
    (hnext : ¬ IsBarrier hk v w) :
    PairAdvanceReady hk u (transition hk v w).1 ↔
      ¬ (w.leader = true ∧ w.bullet = true) := by
  have hbar' : ¬ succLabel hk u.label = v.label := hbar
  rw [transition_of_nonbarrier hk v w hnext]
  cases hleader : w.leader <;>
    cases hbullet : w.bullet <;>
    simp [PairAdvanceReady, IsBarrier, nonBarrierStep,
      hleader, hbullet, hblocked, hbar', hphase]

#check pairAdvanceReady_after_successor_service_iff
#print axioms pairAdvanceReady_after_successor_service_iff

/-- If two adjacent edges are charged and the rear edge is ready, the
original journal step at that rear edge strictly lowers charged-support
count.  The last theorem used here is label-only: no centered transition is
invoked. -/
theorem adjacent_ready_barrierCount_lt
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (a b : Fin n)
    (hab : ring.rightNeighbor a = b)
    (ha : BarrierAt hk ring (labelsOf C) a)
    (hb : BarrierAt hk ring (labelsOf C) b)
    (hphase : (C a).phase = true)
    (hprobe : (C b).probe = false) :
    barrierCount hk ring
        (labelsOf ((AAFJPK.protocol k hk).step ring C a)) <
      barrierCount hk ring (labelsOf C) := by
  have hready : AdvanceReady hk ring C a := by
    refine ⟨(barrierAt_labelsOf_iff hk ring C a).1 ha, hphase, ?_⟩
    simpa [hab] using hprobe
  rw [labelsOf_step_eq_advance_of_ready hk ring hn2 C a hready]
  exact _root_.AAFJPK.CenteredRenewal.CoalescenceFrame.barrierCount_advance_lt_of_source_and_successor_barriers
    hk ring hn2 (labelsOf C) a ha (by simpa [hab] using hb)

#check adjacent_ready_barrierCount_lt
#print axioms adjacent_ready_barrierCount_lt

/-- The original phase-one probe-blocked branch leaves the responder exactly
unchanged and keeps the initiator phase armed. -/
theorem phase_one_probe_blocked_frames
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hbar : IsBarrier hk u v)
    (hphase : u.phase = true)
    (hprobe : v.probe = true) :
    let q := transition hk u v
    q.1.label = u.label ∧ q.1.phase = true ∧ q.2 = v := by
  rw [transition_of_barrier hk u v hbar,
    barrierStep_phase_one_probe_blocked hk u v hphase hprobe]
  simp [hphase]

/-- The original phase-one probe-free barrier branch records the exact local
payload of a front advance.  The pre-existing probe at the tail is included
so that the resulting leader/probe fields are part of the restart witness. -/
theorem front_advance_restart_payload
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hbar : IsBarrier hk u v)
    (hphase : u.phase = true)
    (huProbe : u.probe = true)
    (hvProbe : v.probe = false) :
    let q := transition hk u v
    q.1 = { u with leader := true, probe := false } ∧
      q.2 = { v with
        label := succLabel hk u.label
        phase := false
        bullet := false } := by
  rw [transition_of_barrier hk u v hbar,
    barrierStep_phase_one_probe_free hk u v hphase hvProbe]
  simp [probeHitsBarrier, huProbe]

#check phase_one_probe_blocked_frames
#check front_advance_restart_payload
#print axioms phase_one_probe_blocked_frames
#print axioms front_advance_restart_payload

end BarrierAlgebra
end AAFJPK
