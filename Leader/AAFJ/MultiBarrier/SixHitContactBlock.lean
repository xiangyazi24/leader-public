import Leader.AAFJ.MultiBarrier.AdjacentContact
import Leader.AAFJ.Centered.CoalescenceFrame

/-!
# A fixed six-hit contact block for original AAFJ P_k

This file is a deterministic local layer above the frozen Support and Contact
bridges.  It contains no scheduler or probability statement.  The first
helpers isolate ring geometry and the second three-hit service of a normalized
adjacent pair.
-/

namespace AAFJPK
namespace BarrierAlgebra

set_option autoImplicit false

private theorem rightNeighbor_rightNeighbor_ne_self_of_two_lt
    {n : Nat} (ring : DirectedRing n) (hn3 : 2 < n) (edge : Fin n) :
    ring.rightNeighbor (ring.rightNeighbor edge) ≠ edge := by
  intro hcycle
  have hv := congrArg Fin.val hcycle
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases hfirst : edge.val + 1 < n
  · rw [Nat.mod_eq_of_lt hfirst] at hv
    by_cases hsecond : edge.val + 1 + 1 < n
    · rw [Nat.mod_eq_of_lt hsecond] at hv
      omega
    · have hwrap : edge.val + 1 + 1 = n := by
        omega
      rw [hwrap, Nat.mod_self] at hv
      omega
  · have hwrap : edge.val + 1 = n := by
      omega
    rw [hwrap, Nat.mod_self] at hv
    have hone : 1 < n := by omega
    rw [Nat.mod_eq_of_lt hone] at hv
    omega

theorem exact_two_support_front_free
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 2 < n)
    (L : Labels n k) (a : Fin n)
    (ha : BarrierAt hk ring L a)
    (haNext : BarrierAt hk ring L (ring.rightNeighbor a))
    (hcount : barrierCount hk ring L = 2) :
    ¬ BarrierAt hk ring L
      (ring.rightNeighbor (ring.rightNeighbor a)) := by
  intro haNextNext
  let b : Fin n := ring.rightNeighbor a
  let c : Fin n := ring.rightNeighbor b
  have hn2 : 1 < n := by omega
  have hab : a ≠ b := by
    dsimp [b]
    exact (rightNeighbor_ne_self ring hn2 a).symm
  have hbc : b ≠ c := by
    dsimp [c]
    exact (rightNeighbor_ne_self ring hn2 b).symm
  have hac : a ≠ c := by
    dsimp [b, c]
    exact (rightNeighbor_rightNeighbor_ne_self_of_two_lt ring hn3 a).symm
  have haMem : a ∈ barrierSupport hk ring L :=
    (mem_barrierSupport_iff hk ring L a).2 ha
  have hbMem : b ∈ barrierSupport hk ring L := by
    apply (mem_barrierSupport_iff hk ring L b).2
    simpa [b] using haNext
  have hcMem : c ∈ barrierSupport hk ring L := by
    apply (mem_barrierSupport_iff hk ring L c).2
    simpa [b, c] using haNextNext
  have hthree : [a, b, c].Nodup := by
    simp [hab, hac, hbc]
  have hsubset : [a, b, c] ⊆ barrierSupport hk ring L := by
    intro x hx
    simp at hx
    rcases hx with h | h | h
    · subst x; exact haMem
    · subst x; exact hbMem
    · subst x; exact hcMem
  have hle : 3 ≤ (barrierSupport hk ring L).length := by
    simpa using hthree.length_le_of_subset hsubset
  change (barrierSupport hk ring L).length = 2 at hcount
  omega

theorem original_ready_collision_drops
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hready : AdvanceReady hk ring C e)
    (hnext : BarrierAt hk ring (labelsOf C) (ring.rightNeighbor e)) :
    barrierCount hk ring
        (labelsOf ((AAFJPK.protocol k hk).step ring C e)) <
      barrierCount hk ring (labelsOf C) := by
  exact adjacent_ready_barrierCount_lt hk ring hn2 C e
    (ring.rightNeighbor e) rfl
    ((barrierAt_labelsOf_iff hk ring C e).2 hready.1)
    hnext hready.2.1 hready.2.2

private theorem phase_zero_step_source_controls
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e)
    (hphase : (C e).phase = false) :
    ((AAFJPK.protocol k hk).step ring C e e).probe = false ∧
      ((AAFJPK.protocol k hk).step ring C e e).phase = true := by
  have hjournal :
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
    (barrierAt_labelsOf_iff hk ring C e).1 hbar
  have hlocal :
      (transition hk (C e) (C (ring.rightNeighbor e))).1.probe = false ∧
        (transition hk (C e) (C (ring.rightNeighbor e))).1.phase = true := by
    rw [transition_of_barrier hk (C e) (C (ring.rightNeighbor e)) hjournal]
    rw [barrierStep_phase_zero hk (C e) (C (ring.rightNeighbor e))
      hphase]
    cases hp : (C e).probe <;> simp [probeHitsBarrier, hp]
  simpa [PopulationProtocol.step, protocol] using hlocal

private theorem phase_zero_step_responder_preserves
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e)
    (hphase : (C e).phase = false) :
    ((AAFJPK.protocol k hk).step ring C e
      (ring.rightNeighbor e)).phase =
      (C (ring.rightNeighbor e)).phase := by
  have hjournal :
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
    (barrierAt_labelsOf_iff hk ring C e).1 hbar
  have hlocal :
      (transition hk (C e) (C (ring.rightNeighbor e))).2.phase =
        (C (ring.rightNeighbor e)).phase := by
    rw [transition_of_barrier hk (C e) (C (ring.rightNeighbor e)) hjournal]
    rw [barrierStep_phase_zero hk (C e) (C (ring.rightNeighbor e))
      hphase]
    cases hv : (C (ring.rightNeighbor e)).leader <;> simp [hv]
  simpa [PopulationProtocol.step, protocol,
    rightNeighbor_ne_self ring hn2 e] using hlocal

private theorem phase_zero_step_other_preserves
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e j : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e)
    (hphase : (C e).phase = false)
    (hje : j ≠ e) :
    ((AAFJPK.protocol k hk).step ring C e j).phase = (C j).phase := by
  by_cases hjr : j = ring.rightNeighbor e
  · subst j
    exact phase_zero_step_responder_preserves hk ring hn2 C e hbar hphase
  · have hjournal :
        IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
      (barrierAt_labelsOf_iff hk ring C e).1 hbar
    simp [PopulationProtocol.step, protocol, transition_of_barrier hk
      (C e) (C (ring.rightNeighbor e)) hjournal,
      barrierStep_phase_zero hk (C e) (C (ring.rightNeighbor e)) hphase,
      hje, hjr]

def AdjacentTwoBarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (a b : Fin n) : Prop :=
  ring.rightNeighbor a = b ∧
    ∀ e : Fin n,
      BarrierAt hk ring (labelsOf C) e ↔ e = a ∨ e = b

def NormalizedAdjacentRestart {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (rear front : Fin n) : Prop :=
  AdjacentTwoBarrier hk ring C rear front ∧
    (C rear).phase = false ∧ (C front).phase = false

def contactService3 {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (a b : Fin n) : Fin n → State k :=
  let C1 := (AAFJPK.protocol k hk).step ring C a
  let C2 := (AAFJPK.protocol k hk).step ring C1 b
  (AAFJPK.protocol k hk).step ring C2 a

def contactService6 {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (a b : Fin n) : Fin n → State k :=
  let c := ring.rightNeighbor b
  let C3 := contactService3 hk ring C a b
  contactService3 hk ring C3 b c

/-- Three selections [a,b,a] strictly lower support from a normalized
adjacent pair.  This is the deterministic continuation used after a front
advance; it has no scheduler or probability premise. -/
theorem normalized_adjacent_service3_drops
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (a b : Fin n)
    (hrestart : NormalizedAdjacentRestart hk ring C a b) :
    barrierCount hk ring
        (labelsOf (contactService3 hk ring C a b)) <
      barrierCount hk ring (labelsOf C) := by
  rcases hrestart with ⟨⟨hab, hsupport⟩, hphase_a, hphase_b⟩
  have hBa : BarrierAt hk ring (labelsOf C) a :=
    (hsupport a).2 (Or.inl rfl)
  have hBb : BarrierAt hk ring (labelsOf C) b :=
    (hsupport b).2 (Or.inr rfl)
  have hneab : a ≠ b := by
    intro h
    exact (rightNeighbor_ne_self ring hn2 a) (hab.trans h.symm)
  let C1 := (AAFJPK.protocol k hk).step ring C a
  let C2 := (AAFJPK.protocol k hk).step ring C1 b
  let C3 := (AAFJPK.protocol k hk).step ring C2 a
  have hnot_a : ¬ AdvanceReady hk ring C a := by
    intro h
    exact Bool.noConfusion (hphase_a.symm.trans h.2.1)
  have hlabels1 : labelsOf C1 = labelsOf C := by
    exact labelsOf_step_eq_self_of_not_ready hk ring C a hnot_a
  have hphase1_a : (C1 a).phase = true := by
    exact (phase_zero_step_source_controls hk ring hn2 C a hBa
      hphase_a).2
  have hbar1_b : BarrierAt hk ring (labelsOf C1) b := by
    rw [hlabels1]
    exact hBb
  have hphase1_b : (C1 b).phase = false := by
    have hres :=
      phase_zero_step_responder_preserves hk ring hn2 C a hBa hphase_a
    have hres' : ((AAFJPK.protocol k hk).step ring C a b).phase =
        (C b).phase := by
      simpa [hab] using hres
    simpa [C1] using hres'.trans hphase_b
  have hnot_b : ¬ AdvanceReady hk ring C1 b := by
    intro h
    exact Bool.noConfusion (hphase1_b.symm.trans h.2.1)
  have hlabels2 : labelsOf C2 = labelsOf C1 := by
    exact labelsOf_step_eq_self_of_not_ready hk ring C1 b hnot_b
  have hphase2_a : (C2 a).phase = true := by
    exact
      (phase_zero_step_other_preserves hk ring hn2 C1 b a hbar1_b
        hphase1_b hneab).trans hphase1_a
  have hprobe2_b : (C2 b).probe = false := by
    exact (phase_zero_step_source_controls hk ring hn2 C1 b hbar1_b
      hphase1_b).1
  have hready2 : AdvanceReady hk ring C2 a := by
    refine ⟨?_, hphase2_a, ?_⟩
    · apply (barrierAt_labelsOf_iff hk ring C2 a).1
      rw [hlabels2, hlabels1]
      exact hBa
    · rw [hab]
      exact hprobe2_b
  have hdrop := original_ready_collision_drops hk ring hn2 C2 a hready2 (by
    rw [hlabels2, hlabels1]
    simpa [hab] using hBb)
  rw [hlabels2, hlabels1] at hdrop
  simpa [contactService3, C1, C2, C3] using hdrop

#check exact_two_support_front_free
#check original_ready_collision_drops
#check normalized_adjacent_service3_drops
#print axioms exact_two_support_front_free
#print axioms original_ready_collision_drops
#print axioms normalized_adjacent_service3_drops

end BarrierAlgebra
end AAFJPK



set_option autoImplicit false

namespace AAFJPK.OriginalFull3

open BarrierAlgebra

def C1 {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (a : Fin n) : Fin n → State k :=
  (AAFJPK.protocol k hk).step ring C a

def C2 {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (a b : Fin n) : Fin n → State k :=
  (AAFJPK.protocol k hk).step ring (C1 hk ring C a) b

def C3 {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (a b : Fin n) : Fin n → State k :=
  (AAFJPK.protocol k hk).step ring (C2 hk ring C a b) a

private theorem step_other {n : Nat}
    (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e i : Fin n)
    (hie : i ≠ e) (hir : i ≠ ring.rightNeighbor e) :
    P.step ring C e i = C i := by
  simp [PopulationProtocol.step, hie, hir]

private theorem two_hop_ne {n : Nat}
    (ring : DirectedRing n) (hn3 : 2 < n) (e : Fin n) :
    ring.rightNeighbor (ring.rightNeighbor e) ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases h1 : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt h1] at hv
    by_cases h2 : e.val + 1 + 1 < n
    · rw [Nat.mod_eq_of_lt h2] at hv
      omega
    · have hw : e.val + 1 + 1 = n := by omega
      rw [hw, Nat.mod_self] at hv
      omega
  · have hw : e.val + 1 = n := by omega
    rw [hw, Nat.mod_self] at hv
    have h1 : 1 < n := by omega
    rw [Nat.mod_eq_of_lt h1] at hv
    omega

private theorem ready_head_controls {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hr : AdvanceReady hk ring C e) :
    (((AAFJPK.protocol k hk).step ring C e)
      (ring.rightNeighbor e)).phase = false ∧
    (((AAFJPK.protocol k hk).step ring C e)
      (ring.rightNeighbor e)).probe = false := by
  rcases hr with ⟨hbar, hphase, hprobe⟩
  have hne := rightNeighbor_ne_self ring hn2 e
  simp only [PopulationProtocol.step, AAFJPK.protocol, if_neg hne, if_pos rfl]
  rw [AAFJPK.transition_of_barrier hk _ _ hbar]
  rw [AAFJPK.barrierStep_phase_one_probe_free hk _ _ hphase hprobe]
  simp [hprobe]

private theorem original_transport_pair {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (x e r : Fin n)
    (her : ring.rightNeighbor e = r) (hxe : x ≠ e)
    (hr : AdvanceReady hk ring C e)
    (hfree : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor e))
    (hs : ∀ j, BarrierAt hk ring (labelsOf C) j ↔ j = x ∨ j = e) :
    ∀ j, BarrierAt hk ring
        (labelsOf ((AAFJPK.protocol k hk).step ring C e)) j ↔
      j = x ∨ j = r := by
  intro j
  rw [← mem_barrierSupport_iff hk ring
    (labelsOf ((AAFJPK.protocol k hk).step ring C e)) j]
  rw [protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus
    hk ring hn2 C e hr hfree j]
  constructor
  · rintro ⟨i, hi, hij⟩
    have hib := (mem_barrierSupport_iff hk ring (labelsOf C) i).1 hi
    rcases (hs i).1 hib with rfl | rfl
    · left
      simpa [redirectEdge, hxe] using hij.symm
    · right
      simpa [redirectEdge, her] using hij.symm
  · intro hj
    rcases hj with hjx | hjr
    · refine ⟨x, (mem_barrierSupport_iff hk ring (labelsOf C) x).2
        ((hs x).2 (Or.inl rfl)), ?_⟩
      simpa [redirectEdge, hxe, hjx]
    · refine ⟨e, (mem_barrierSupport_iff hk ring (labelsOf C) e).2
        ((hs e).2 (Or.inr rfl)), ?_⟩
      simpa [redirectEdge, her, hjr]

private theorem barrier_hit_source_controls {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e) :
    ((AAFJPK.protocol k hk).step ring C e e).probe = false ∧
      ((AAFJPK.protocol k hk).step ring C e e).phase = true := by
  have hjournal :
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
    (barrierAt_labelsOf_iff hk ring C e).1 hbar
  have hlocal :
      (transition hk (C e) (C (ring.rightNeighbor e))).1.probe = false ∧
        (transition hk (C e) (C (ring.rightNeighbor e))).1.phase = true := by
    rw [transition_of_barrier hk (C e) (C (ring.rightNeighbor e)) hjournal]
    cases hphase : (C e).phase with
    | false =>
        rw [barrierStep_phase_zero hk (C e) (C (ring.rightNeighbor e))
          hphase]
        cases hp : (C e).probe <;> simp [probeHitsBarrier, hp]
    | true =>
        cases hp : (C (ring.rightNeighbor e)).probe with
        | false =>
            rw [barrierStep_phase_one_probe_free hk (C e)
              (C (ring.rightNeighbor e)) hphase hp]
            cases hu : (C e).probe <;> simp [probeHitsBarrier, hu, hphase]
        | true =>
            rw [barrierStep_phase_one_probe_blocked hk (C e)
              (C (ring.rightNeighbor e)) hphase hp]
            cases hu : (C e).probe <;> simp [probeHitsBarrier, hu, hphase]
  simpa [PopulationProtocol.step, protocol] using hlocal

private theorem nonready_barrier_other_phase
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e j : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e)
    (hnot : ¬ AdvanceReady hk ring C e)
    (hje : j ≠ e) :
    ((AAFJPK.protocol k hk).step ring C e j).phase = (C j).phase := by
  have hjournal :
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
    (barrierAt_labelsOf_iff hk ring C e).1 hbar
  by_cases hphase : (C e).phase = false
  · by_cases hjr : j = ring.rightNeighbor e
    · subst j
      have hlocal :
          (transition hk (C e) (C (ring.rightNeighbor e))).2.phase =
            (C (ring.rightNeighbor e)).phase := by
        rw [transition_of_barrier hk (C e) (C (ring.rightNeighbor e))
          hjournal]
        rw [barrierStep_phase_zero hk (C e) (C (ring.rightNeighbor e))
          hphase]
        cases hv : (C (ring.rightNeighbor e)).leader <;> simp [hv]
      simpa [PopulationProtocol.step, protocol,
        rightNeighbor_ne_self ring hn2 e] using hlocal
    · simp [PopulationProtocol.step, protocol,
        transition_of_barrier hk (C e) (C (ring.rightNeighbor e)) hjournal,
        barrierStep_phase_zero hk (C e) (C (ring.rightNeighbor e)) hphase,
        hje, hjr]
  · have hphase' : (C e).phase = true := by
      cases hp : (C e).phase <;> simp_all
    have hprobe' : (C (ring.rightNeighbor e)).probe = true := by
      by_cases hp : (C (ring.rightNeighbor e)).probe = false
      · exact (hnot ⟨hjournal, hphase', hp⟩).elim
      · cases hv : (C (ring.rightNeighbor e)).probe <;> simp_all
    by_cases hjr : j = ring.rightNeighbor e
    · subst j
      have hlocal :
          (transition hk (C e) (C (ring.rightNeighbor e))).2.phase =
            (C (ring.rightNeighbor e)).phase := by
        rw [transition_of_barrier hk (C e) (C (ring.rightNeighbor e))
          hjournal]
        rw [barrierStep_phase_one_probe_blocked hk
          (C e) (C (ring.rightNeighbor e)) hphase' hprobe']
      simpa [PopulationProtocol.step, protocol,
        rightNeighbor_ne_self ring hn2 e] using hlocal
    · simp [PopulationProtocol.step, protocol,
        transition_of_barrier hk (C e) (C (ring.rightNeighbor e)) hjournal,
        barrierStep_phase_one_probe_blocked hk
          (C e) (C (ring.rightNeighbor e)) hphase' hprobe',
        hje, hjr]

/-- Composition seam for the no-drop [a,b,a] branch.

The four hmid* premises are exactly what the first two original steps must
supply from initial support {a,b} plus the three no-drop hypotheses:
after b advances, support is {a,c}; a is armed; b is probe-free; and the new
tail c is phase/probe false. -/
theorem full3_no_drop_normalized_restart
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (a b c : Fin n)
    (hab : ring.rightNeighbor a = b)
    (hbc : ring.rightNeighbor b = c)
    (hmidSupport :
      ∀ e, BarrierAt hk ring (labelsOf (C2 hk ring C a b)) e ↔
        e = a ∨ e = c)
    (hmidAPhase : (C2 hk ring C a b a).phase = true)
    (hmidBProbe : (C2 hk ring C a b b).probe = false)
    (hmidC :
      (C2 hk ring C a b c).phase = false ∧
      (C2 hk ring C a b c).probe = false) :
    (∀ e, BarrierAt hk ring (labelsOf (C3 hk ring C a b)) e ↔
      e = b ∨ e = c) ∧
    (C3 hk ring C a b b).phase = false ∧
    (C3 hk ring C a b c).phase = false ∧
    (C3 hk ring C a b b).probe = false ∧
    (C3 hk ring C a b c).probe = false := by
  have hn2 : 1 < n := by omega
  have hba : b ≠ a := by
    rw [← hab]
    exact rightNeighbor_ne_self ring hn2 a
  have hcb : c ≠ b := by
    rw [← hbc]
    exact rightNeighbor_ne_self ring hn2 b
  have hca : c ≠ a := by
    rw [← hbc, ← hab]
    exact two_hop_ne ring hn3 a
  have ha :
      BarrierAt hk ring (labelsOf (C2 hk ring C a b)) a :=
    (hmidSupport a).2 (Or.inl rfl)
  have hbFree :
      ¬ BarrierAt hk ring (labelsOf (C2 hk ring C a b)) b := by
    intro h
    rcases (hmidSupport b).1 h with h | h
    · exact hba h
    · exact hcb h.symm
  have hr : AdvanceReady hk ring (C2 hk ring C a b) a :=
    ⟨(barrierAt_labelsOf_iff hk ring (C2 hk ring C a b) a).1 ha,
      hmidAPhase, by simpa [hab] using hmidBProbe⟩
  have hfree :
      ¬ BarrierAt hk ring (labelsOf (C2 hk ring C a b))
        (ring.rightNeighbor a) := by
    simpa [hab] using hbFree
  have hsSwap :
      ∀ e, BarrierAt hk ring (labelsOf (C2 hk ring C a b)) e ↔
        e = c ∨ e = a := by
    intro e
    simpa [or_comm] using hmidSupport e
  have hs3 :
      ∀ e, BarrierAt hk ring (labelsOf (C3 hk ring C a b)) e ↔
        e = b ∨ e = c := by
    intro e
    simpa [C3, or_comm] using
      original_transport_pair hk ring hn2 (C2 hk ring C a b)
        c a b hab hca hr hfree hsSwap e
  have hb3 :
      (C3 hk ring C a b b).phase = false ∧
      (C3 hk ring C a b b).probe = false := by
    simpa [C3, hab] using
      ready_head_controls hk ring hn2 (C2 hk ring C a b) a hr
  have hcKeep : C3 hk ring C a b c = C2 hk ring C a b c := by
    exact step_other (AAFJPK.protocol k hk) ring (C2 hk ring C a b)
      a c hca (by simpa [hab] using hcb)
  refine ⟨hs3, hb3.1, ?_, hb3.2, ?_⟩
  · rw [hcKeep]
    exact hmidC.1
  · rw [hcKeep]
    exact hmidC.2

#print axioms full3_no_drop_normalized_restart

end AAFJPK.OriginalFull3

namespace AAFJPK.OriginalFull3

open BarrierAlgebra
private theorem barrierCount_eq_two_of_exact_support
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (L : Labels n k) (a b : Fin n) (hab : a ≠ b)
    (hsupport :
      ∀ e, BarrierAt hk ring L e ↔ e = a ∨ e = b) :
    barrierCount hk ring L = 2 := by
  have habNodup : [a, b].Nodup := by
    simp [hab]
  have habSubset : [a, b] ⊆ barrierSupport hk ring L := by
    intro x hx
    simp at hx
    rcases hx with h | h
    · subst x
      exact (mem_barrierSupport_iff hk ring L a).2
        ((hsupport a).2 (Or.inl rfl))
    · subst x
      exact (mem_barrierSupport_iff hk ring L b).2
        ((hsupport b).2 (Or.inr rfl))
  have hlow : 2 ≤ (barrierSupport hk ring L).length := by
    simpa using habNodup.length_le_of_subset habSubset
  have hsub : barrierSupport hk ring L ⊆ [a, b] := by
    intro x hx
    have hxbar := (mem_barrierSupport_iff hk ring L x).1 hx
    rcases (hsupport x).1 hxbar with h | h
    · subst x
      simp
    · subst x
      simp
  have hupp :
      (barrierSupport hk ring L).length ≤ [a, b].length :=
    (barrierSupport_nodup hk ring L).length_le_of_subset hsub
  change (barrierSupport hk ring L).length = 2
  simpa using Nat.le_antisymm (by simpa using hupp) hlow



theorem full3_count_unchanged_implies_mid
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (a b c : Fin n)
    (hab : ring.rightNeighbor a = b)
    (hbc : ring.rightNeighbor b = c)
    (hs0 :
      ∀ e, BarrierAt hk ring (labelsOf C) e ↔ e = a ∨ e = b)
    (hcount3 :
      barrierCount hk ring (labelsOf (C3 hk ring C a b)) =
        barrierCount hk ring (labelsOf C)) :
    (∀ e, BarrierAt hk ring (labelsOf (C2 hk ring C a b)) e ↔
      e = a ∨ e = c) ∧
    (C2 hk ring C a b a).phase = true ∧
    (C2 hk ring C a b b).probe = false ∧
    (C2 hk ring C a b c).phase = false ∧
    (C2 hk ring C a b c).probe = false := by
  have hn2 : 1 < n := by omega

  -- Geometry: a,b,c are pairwise distinct.
  have hba : b ≠ a := by
    rw [← hab]
    exact rightNeighbor_ne_self ring hn2 a
  have hcb : c ≠ b := by
    rw [← hbc]
    exact rightNeighbor_ne_self ring hn2 b
  have hca : c ≠ a := by
    rw [← hbc, ← hab]
    exact two_hop_ne ring hn3 a

  have ha0 : BarrierAt hk ring (labelsOf C) a :=
    (hs0 a).2 (Or.inl rfl)
  have hb0 : BarrierAt hk ring (labelsOf C) b :=
    (hs0 b).2 (Or.inr rfl)

  -- Monotonicity + hcount3 forces equality after each of the first 3 steps.
  have hle1 :
      barrierCount hk ring (labelsOf (C1 hk ring C a)) ≤
        barrierCount hk ring (labelsOf C) := by
    simpa [C1] using
      protocol_step_barrierCount_le hk ring hn2 C a
  have hle2 :
      barrierCount hk ring (labelsOf (C2 hk ring C a b)) ≤
        barrierCount hk ring (labelsOf (C1 hk ring C a)) := by
    simpa [C2] using
      protocol_step_barrierCount_le hk ring hn2 (C1 hk ring C a) b
  have hle3 :
      barrierCount hk ring (labelsOf (C3 hk ring C a b)) ≤
        barrierCount hk ring (labelsOf (C2 hk ring C a b)) := by
    simpa [C3] using
      protocol_step_barrierCount_le hk ring hn2 (C2 hk ring C a b) a
  have hcount1 :
      barrierCount hk ring (labelsOf (C1 hk ring C a)) =
        barrierCount hk ring (labelsOf C) := by omega
  have hcount2 :
      barrierCount hk ring (labelsOf (C2 hk ring C a b)) =
        barrierCount hk ring (labelsOf (C1 hk ring C a)) := by omega
  have hcount32 :
      barrierCount hk ring (labelsOf (C3 hk ring C a b)) =
        barrierCount hk ring (labelsOf (C2 hk ring C a b)) := by omega

  -- First a cannot be ready, or it would collide into initial barrier b.
  have hnotA : ¬ AdvanceReady hk ring C a := by
    intro hready
    have hd := original_ready_collision_drops hk ring hn2 C a hready (by
      simpa [hab] using hb0)
    change barrierCount hk ring (labelsOf (C1 hk ring C a)) <
      barrierCount hk ring (labelsOf C) at hd
    omega

  have hlabels1 :
      labelsOf (C1 hk ring C a) = labelsOf C := by
    simpa [C1] using
      labelsOf_step_eq_self_of_not_ready hk ring C a hnotA

  have ha1ctl :=
    barrier_hit_source_controls hk ring C a ha0
  have ha1phase : (C1 hk ring C a a).phase = true := by
    simpa [C1] using ha1ctl.2

  have hs1 :
      ∀ e, BarrierAt hk ring (labelsOf (C1 hk ring C a)) e ↔
        e = a ∨ e = b := by
    intro e
    rw [hlabels1]
    exact hs0 e
  have hb1 :
      BarrierAt hk ring (labelsOf (C1 hk ring C a)) b :=
    (hs1 b).2 (Or.inr rfl)
  have hc1free :
      ¬ BarrierAt hk ring (labelsOf (C1 hk ring C a)) c := by
    intro hc
    rcases (hs1 c).1 hc with h | h
    · exact hca h
    · exact hcb h

  -- Middle b must be ready; otherwise the third a is a forced collision.
  have hreadyB : AdvanceReady hk ring (C1 hk ring C a) b := by
    by_cases hreadyB : AdvanceReady hk ring (C1 hk ring C a) b
    · exact hreadyB
    · exfalso
      have hnotB := hreadyB
      have hlabels2 :
          labelsOf (C2 hk ring C a b) = labelsOf (C1 hk ring C a) := by
        simpa [C2] using
          labelsOf_step_eq_self_of_not_ready hk ring
            (C1 hk ring C a) b hnotB
      have hb2ctl :=
        barrier_hit_source_controls hk ring (C1 hk ring C a) b hb1
      have ha2phase : (C2 hk ring C a b a).phase = true := by
        exact
          (nonready_barrier_other_phase hk ring hn2
            (C1 hk ring C a) b a hb1 hnotB hba.symm).trans ha1phase
      have hb2probe : (C2 hk ring C a b b).probe = false := by
        simpa [C2] using hb2ctl.1
      have ha2 :
          BarrierAt hk ring (labelsOf (C2 hk ring C a b)) a := by
        rw [hlabels2, hlabels1]
        exact ha0
      have hb2 :
          BarrierAt hk ring (labelsOf (C2 hk ring C a b)) b := by
        rw [hlabels2, hlabels1]
        exact hb0
      have hreadyA2 : AdvanceReady hk ring (C2 hk ring C a b) a := by
        refine ⟨(barrierAt_labelsOf_iff hk ring
          (C2 hk ring C a b) a).1 ha2, ha2phase, ?_⟩
        simpa [hab] using hb2probe
      have hd := original_ready_collision_drops hk ring hn2
        (C2 hk ring C a b) a hreadyA2 (by simpa [hab] using hb2)
      change barrierCount hk ring (labelsOf (C3 hk ring C a b)) <
        barrierCount hk ring (labelsOf (C2 hk ring C a b)) at hd
      omega

  -- Ready b advances into free c, so support is exactly {a,c}.
  have hfreeB :
      ¬ BarrierAt hk ring (labelsOf (C1 hk ring C a))
        (ring.rightNeighbor b) := by
    simpa [hbc] using hc1free

  have hmidSupport :
      ∀ e, BarrierAt hk ring (labelsOf (C2 hk ring C a b)) e ↔
        e = a ∨ e = c := by
    intro e
    simpa [C2] using
      original_transport_pair hk ring hn2 (C1 hk ring C a)
        a b c hbc hba.symm hreadyB hfreeB hs1 e

  -- a is outside the ready b interaction.
  have haKeep :
      C2 hk ring C a b a = C1 hk ring C a a := by
    exact step_other (AAFJPK.protocol k hk) ring (C1 hk ring C a)
      b a hba.symm (by simpa [hbc] using hca.symm)
  have hmidAPhase : (C2 hk ring C a b a).phase = true := by
    rw [haKeep]
    exact ha1phase

  have hmidBProbe : (C2 hk ring C a b b).probe = false := by
    simpa [C2] using
      (barrier_hit_source_controls hk ring
        (C1 hk ring C a) b hb1).1

  have hmidC :
      (C2 hk ring C a b c).phase = false ∧
      (C2 hk ring C a b c).probe = false := by
    simpa [C2, hbc] using
      ready_head_controls hk ring hn2 (C1 hk ring C a) b hreadyB

  exact ⟨hmidSupport, hmidAPhase, hmidBProbe, hmidC.1, hmidC.2⟩

/-- Once the first three-hit endpoint has been established and its support
count is known to equal the starting count, the fixed continuation [b,c,b]
strictly lowers support.  The count equality is explicit: this seam does not
pretend to derive the first-prefix no-drop facts. -/
theorem six_hit_drops_of_full3_seam
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (a b c : Fin n)
    (hab : ring.rightNeighbor a = b)
    (hbc : ring.rightNeighbor b = c)
    (hmidSupport :
      ∀ e, BarrierAt hk ring (labelsOf (C2 hk ring C a b)) e ↔
        e = a ∨ e = c)
    (hmidAPhase : (C2 hk ring C a b a).phase = true)
    (hmidBProbe : (C2 hk ring C a b b).probe = false)
    (hmidC :
      (C2 hk ring C a b c).phase = false ∧
      (C2 hk ring C a b c).probe = false)
    (hcount3 :
      barrierCount hk ring (labelsOf (C3 hk ring C a b)) =
        barrierCount hk ring (labelsOf C)) :
    barrierCount hk ring
        (labelsOf (BarrierAlgebra.contactService6 hk ring C a b)) <
      barrierCount hk ring (labelsOf C) := by
  have hn2 : 1 < n := by omega
  have hendpoint := full3_no_drop_normalized_restart hk ring hn3 C a b c
    hab hbc hmidSupport hmidAPhase hmidBProbe hmidC
  have hrestart :
      NormalizedAdjacentRestart hk ring (C3 hk ring C a b) b c := by
    refine ⟨⟨hbc, hendpoint.1⟩, hendpoint.2.1, hendpoint.2.2.1⟩
  have hdrop := normalized_adjacent_service3_drops hk ring hn2
    (C3 hk ring C a b) b c hrestart
  rw [hcount3] at hdrop
  simpa [BarrierAlgebra.contactService6, BarrierAlgebra.contactService3,
    C3, C2, C1, hbc] using hdrop

#check full3_count_unchanged_implies_mid
#print axioms full3_count_unchanged_implies_mid
#check six_hit_drops_of_full3_seam
#print axioms six_hit_drops_of_full3_seam


/-- Exact two-barrier support plus the literal no-drop alternatives force the
fixed six-hit word [a,b,a,b,c,b] to contain a strict support drop.  The
statement is deterministic and makes no scheduler or probability claim. -/
theorem six_hit_drops_of_exact_adjacent
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (a b : Fin n)
    (hab : ring.rightNeighbor a = b)
    (hsupport :
      ∀ e, BarrierAt hk ring (labelsOf C) e ↔
        e = a ∨ e = b) :
    barrierCount hk ring
        (labelsOf (BarrierAlgebra.contactService6 hk ring C a b)) <
      barrierCount hk ring (labelsOf C) := by
  have hn2 : 1 < n := by omega
  let c : Fin n := ring.rightNeighbor b
  have hbc : ring.rightNeighbor b = c := by rfl
  let C3' := C3 hk ring C a b
  let C4' := (AAFJPK.protocol k hk).step ring C3' b
  let C5' := (AAFJPK.protocol k hk).step ring C4' c
  let C6' := (AAFJPK.protocol k hk).step ring C5' b
  have hle1 :
      barrierCount hk ring (labelsOf (C1 hk ring C a)) ≤
        barrierCount hk ring (labelsOf C) := by
    exact protocol_step_barrierCount_le hk ring hn2 C a
  have hle2 :
      barrierCount hk ring (labelsOf (C2 hk ring C a b)) ≤
        barrierCount hk ring (labelsOf (C1 hk ring C a)) := by
    exact protocol_step_barrierCount_le hk ring hn2 (C1 hk ring C a) b
  have hle3 :
      barrierCount hk ring (labelsOf C3') ≤
        barrierCount hk ring (labelsOf (C2 hk ring C a b)) := by
    exact protocol_step_barrierCount_le hk ring hn2 (C2 hk ring C a b) a
  by_cases hdrop3 :
      barrierCount hk ring (labelsOf C3') <
        barrierCount hk ring (labelsOf C)
  · have hle4 :
        barrierCount hk ring (labelsOf C4') ≤
          barrierCount hk ring (labelsOf C3') := by
      exact protocol_step_barrierCount_le hk ring hn2 C3' b
    have hle5 :
        barrierCount hk ring (labelsOf C5') ≤
          barrierCount hk ring (labelsOf C4') := by
      exact protocol_step_barrierCount_le hk ring hn2 C4' c
    have hle6 :
        barrierCount hk ring (labelsOf C6') ≤
          barrierCount hk ring (labelsOf C5') := by
      exact protocol_step_barrierCount_le hk ring hn2 C5' b
    have hfinal :
        barrierCount hk ring (labelsOf C6') <
          barrierCount hk ring (labelsOf C) := by
      omega
    change barrierCount hk ring (labelsOf C6') <
      barrierCount hk ring (labelsOf C)
    exact hfinal
  · have hcount3' :
        barrierCount hk ring (labelsOf C3') =
          barrierCount hk ring (labelsOf C) := by
      omega
    have hcount3 :
        barrierCount hk ring (labelsOf (C3 hk ring C a b)) =
          barrierCount hk ring (labelsOf C) := by
      simpa [C3'] using hcount3'
    have hmid := full3_count_unchanged_implies_mid hk ring hn3 C a b c
      (by simpa [c] using hab) hbc hsupport hcount3
    have hfinal := six_hit_drops_of_full3_seam hk ring hn3 C a b c
      (by simpa [c] using hab) hbc hmid.1 hmid.2.1 hmid.2.2.1
      ⟨hmid.2.2.2.1, hmid.2.2.2.2⟩ hcount3
    simpa [c] using hfinal
#check six_hit_drops_of_exact_adjacent
#print axioms six_hit_drops_of_exact_adjacent

end AAFJPK.OriginalFull3
