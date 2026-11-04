import Leader.AAFJ.MultiBarrier.AdjacentContact
import Leader.AAFJ.MultiBarrier.NonbarrierInterleaving
import Leader.AAFJ.MultiBarrier.GappedThreeHit

set_option autoImplicit false

namespace AAFJPK.OriginalArbitraryRemote

open BarrierAlgebra
open OriginalNonbarrierWord
open OriginalNonbarrierFrame

private theorem gapHit_barrierCount_le
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (word : List (Fin n)) (e : Fin n)
    (hw : CurrentNonbarrierWord hk ring C word) :
    barrierCount hk ring
        (labelsOf (OriginalGappedThree.gapHit hk ring C word e)) ≤
      barrierCount hk ring (labelsOf C) := by
  have hstep := protocol_step_barrierCount_le hk ring hn2
    (rawRun hk ring C word) e
  rw [barrierCount_rawRun_eq hk ring hw] at hstep
  simpa [OriginalGappedThree.gapHit] using hstep

private theorem phase_zero_source_controls
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e)
    (hphase : (C e).phase = false) :
    ((protocol k hk).step ring C e e).probe = false ∧
      ((protocol k hk).step ring C e e).phase = true := by
  have hjournal :
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
    (barrierAt_labelsOf_iff hk ring C e).1 hbar
  have hlocal :
      (transition hk (C e) (C (ring.rightNeighbor e))).1.probe = false ∧
        (transition hk (C e) (C (ring.rightNeighbor e))).1.phase = true := by
    rw [transition_of_barrier hk _ _ hjournal]
    rw [barrierStep_phase_zero hk _ _ hphase]
    cases hp : (C e).probe <;> simp [probeHitsBarrier, hp]
  simpa [PopulationProtocol.step, protocol] using hlocal

private theorem phase_zero_responder_preserves
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e)
    (hphase : (C e).phase = false) :
    ((protocol k hk).step ring C e
      (ring.rightNeighbor e)).phase =
      (C (ring.rightNeighbor e)).phase := by
  have hjournal :
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
    (barrierAt_labelsOf_iff hk ring C e).1 hbar
  have hlocal :
      (transition hk (C e) (C (ring.rightNeighbor e))).2.phase =
        (C (ring.rightNeighbor e)).phase := by
    rw [transition_of_barrier hk _ _ hjournal]
    rw [barrierStep_phase_zero hk _ _ hphase]
    cases hv : (C (ring.rightNeighbor e)).leader <;> simp [hv]
  simpa [PopulationProtocol.step, protocol,
    rightNeighbor_ne_self ring hn2 e] using hlocal

private theorem step_preserves_c_probe
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b c e : Fin n)
    (hbc : ring.rightNeighbor b = c)
    (hnon : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hcBar : BarrierAt hk ring (labelsOf C) c)
    (hb : (C b).probe = false) (hc : (C c).probe = false) :
    (((protocol k hk).step ring C e) c).probe = false := by
  have hec : e ≠ c := by
    intro h
    subst e
    exact hnon ((barrierAt_labelsOf_iff hk ring C c).1 hcBar)
  by_cases hresp : c = ring.rightNeighbor e
  · have heb : e = b := by
      apply rightNeighbor_injective ring
      exact hresp.symm.trans hbc.symm
    subst e
    have hcb : c ≠ b := by
      rw [← hbc]
      exact rightNeighbor_ne_self ring hn2 b
    have hnonbc : ¬ IsBarrier hk (C b) (C c) := by
      simpa [hbc] using hnon
    have hlocal :
        (transition hk (C b) (C c)).2.probe = false := by
      rw [transition_of_nonbarrier hk (C b) (C c) hnonbc]
      cases hl : (C c).leader <;> cases hb' : (C c).bullet <;>
        simp [nonBarrierStep, hb, hc, hl, hb', hcb]
    simpa [PopulationProtocol.step, protocol, hbc, hcb] using hlocal
  · simp [PopulationProtocol.step, protocol, Ne.symm hec, hresp, hc]

private theorem rawRun_preserves_c_probe
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    {C : Fin n → State k} {word : List (Fin n)}
    (a b c : Fin n) (hab : ring.rightNeighbor a = b)
    (hbc : ring.rightNeighbor b = c)
    (haBar : BarrierAt hk ring (labelsOf C) a)
    (hcBar : BarrierAt hk ring (labelsOf C) c)
    (hb : (C b).probe = false) (hc : (C c).probe = false)
    (hw : CurrentNonbarrierWord hk ring C word) :
    (rawRun hk ring C word c).probe = false := by
  induction word generalizing C with
  | nil => exact hc
  | cons e es ih =>
      rcases hw with ⟨hnon, htail⟩
      let D := (protocol k hk).step ring C e
      have hnot := not_advanceReady_of_nonbarrier hk ring C e hnon
      have hlabels : labelsOf D = labelsOf C := by
        simpa [D] using labelsOf_step_eq_self_of_not_ready hk ring C e hnot
      have haD : BarrierAt hk ring (labelsOf D) a := by
        rw [hlabels]
        exact haBar
      have hcD : BarrierAt hk ring (labelsOf D) c := by
        rw [hlabels]
        exact hcBar
      have hbHead : (C (ring.rightNeighbor a)).probe = false := by
        simpa [hab] using hb
      have hbD : (D b).probe = false := by
        have h := nonbarrier_step_preserves_probe_free_barrier_head
          hk ring C e a hnon haBar hbHead
        simpa [D, hab] using h
      have hcDprobe : (D c).probe = false := by
        dsimp [D]
        exact step_preserves_c_probe hk ring hn2 C b c e hbc hnon hcBar hb hc
      change (rawRun hk ring D es c).probe = false
      exact ih haD hcD hbD hcDprobe htail

def gappedService6
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (a b c : Fin n)
    (w0 w1 w2 w3 w4 w5 : List (Fin n)) : Fin n → State k :=
  let C1 := OriginalGappedThree.gapHit hk ring C w0 a
  let C2 := OriginalGappedThree.gapHit hk ring C1 w1 b
  let C3 := OriginalGappedThree.gapHit hk ring C2 w2 a
  let C4 := OriginalGappedThree.gapHit hk ring C3 w3 b
  let C5 := OriginalGappedThree.gapHit hk ring C4 w4 c
  OriginalGappedThree.gapHit hk ring C5 w5 b

private theorem step_other_g {n : Nat}
    (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e i : Fin n)
    (hie : i ≠ e) (hir : i ≠ ring.rightNeighbor e) :
    P.step ring C e i = C i := by
  simp [PopulationProtocol.step, hie, hir]

private theorem two_hop_ne_g {n : Nat}
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
    rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    omega

private theorem cold3_gapped
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (b c : Fin n)
    (w0 w1 w2 : List (Fin n))
    (hbc : ring.rightNeighbor b = c)
    (hb : BarrierAt hk ring (labelsOf C) b)
    (hc : BarrierAt hk ring (labelsOf C) c)
    (hpb : (C b).phase = false) (hpc : (C c).phase = false)
    (hw0 : CurrentNonbarrierWord hk ring C w0)
    (hw1 : CurrentNonbarrierWord hk ring
      (OriginalGappedThree.gapHit hk ring C w0 b) w1)
    (hw2 : CurrentNonbarrierWord hk ring
      (OriginalGappedThree.gapHit hk ring
        (OriginalGappedThree.gapHit hk ring C w0 b) w1 c) w2) :
    barrierCount hk ring
        (labelsOf
          (OriginalGappedThree.gappedService3 hk ring C b c w0 w1 w2)) <
      barrierCount hk ring (labelsOf C) := by
  have hn2 : 1 < n := by omega
  have hcb : c ≠ b := by
    rw [← hbc]
    exact rightNeighbor_ne_self ring hn2 b
  have hcb2 : b ≠ ring.rightNeighbor c := by
    rw [← hbc]
    exact (two_hop_ne_g ring hn3 b).symm
  let D0 := rawRun hk ring C w0
  let E1 := OriginalGappedThree.gapHit hk ring C w0 b
  let D1 := rawRun hk ring E1 w1
  let E2 := OriginalGappedThree.gapHit hk ring E1 w1 c
  let D2 := rawRun hk ring E2 w2
  have hw1' : CurrentNonbarrierWord hk ring E1 w1 := by
    simpa [E1] using hw1
  have hw2' : CurrentNonbarrierWord hk ring E2 w2 := by
    simpa [E2, E1] using hw2
  have hlabelsD1 : labelsOf D1 = labelsOf E1 := by
    simpa [D1] using labelsOf_rawRun_eq hk ring hw1'
  have hbD0 : BarrierAt hk ring (labelsOf D0) b := by
    exact (barrierAt_rawRun_iff hk ring hw0 b).2 hb
  have hcD0 : BarrierAt hk ring (labelsOf D0) c := by
    exact (barrierAt_rawRun_iff hk ring hw0 c).2 hc
  have hpbD0 : (D0 b).phase = false := by
    simpa [D0] using (rawRun_phases_eq hk ring hw0 b).trans hpb
  have hpcD0 : (D0 c).phase = false := by
    simpa [D0] using (rawRun_phases_eq hk ring hw0 c).trans hpc
  have hnotB0 : ¬ AdvanceReady hk ring D0 b := by
    intro h
    exact Bool.noConfusion (hpbD0.symm.trans h.2.1)
  have hlabels1 : labelsOf E1 = labelsOf D0 := by
    simpa [E1, OriginalGappedThree.gapHit] using
      labelsOf_step_eq_self_of_not_ready hk ring D0 b hnotB0
  have hphaseB1 : (E1 b).phase = true := by
    simpa [E1, OriginalGappedThree.gapHit] using
      (phase_zero_source_controls hk ring D0 b hbD0 hpbD0).2
  have hphaseC1 : (E1 c).phase = false := by
    have h := phase_zero_responder_preserves hk ring hn2 D0 b
      hbD0 hpbD0
    have hE1c : (E1 c).phase = (D0 c).phase := by
      simpa [E1, OriginalGappedThree.gapHit, hbc] using h
    exact hE1c.trans hpcD0
  have hbE1 : BarrierAt hk ring (labelsOf E1) b := by
    rw [hlabels1]
    exact hbD0
  have hcE1 : BarrierAt hk ring (labelsOf E1) c := by
    rw [hlabels1]
    exact hcD0
  have hphaseBD1 : (D1 b).phase = true := by
    simpa [D1] using (rawRun_phases_eq hk ring hw1' b).trans hphaseB1
  have hphaseCD1 : (D1 c).phase = false := by
    simpa [D1] using (rawRun_phases_eq hk ring hw1' c).trans hphaseC1
  have hbD1 : BarrierAt hk ring (labelsOf D1) b := by
    simpa [D1] using (barrierAt_rawRun_iff hk ring hw1' b).2 hbE1
  have hcD1 : BarrierAt hk ring (labelsOf D1) c := by
    simpa [D1] using (barrierAt_rawRun_iff hk ring hw1' c).2 hcE1
  have hnotC1 : ¬ AdvanceReady hk ring D1 c := by
    intro h
    exact Bool.noConfusion (hphaseCD1.symm.trans h.2.1)
  have hlabels2 : labelsOf E2 = labelsOf D1 := by
    simpa [E2, OriginalGappedThree.gapHit] using
      labelsOf_step_eq_self_of_not_ready hk ring D1 c hnotC1
  have hphaseC2 : (E2 c).phase = true := by
    simpa [E2, OriginalGappedThree.gapHit] using
      (phase_zero_source_controls hk ring D1 c
        hcD1 hphaseCD1).2
  have hprobeC2 : (E2 c).probe = false := by
    simpa [E2, OriginalGappedThree.gapHit] using
      (phase_zero_source_controls hk ring D1 c
        hcD1 hphaseCD1).1
  have hphaseB2 : (E2 b).phase = true := by
    have h := step_other_g (protocol k hk) ring D1 c b hcb.symm hcb2
    have heq : E2 b = D1 b := by
      change ((protocol k hk).step ring D1 c) b = D1 b
      exact h
    rw [heq]
    exact hphaseBD1
  have hbD2 : BarrierAt hk ring (labelsOf D2) b := by
    have hbE2 : BarrierAt hk ring (labelsOf E2) b := by
      simpa [hlabels2] using hbD1
    exact (barrierAt_rawRun_iff hk ring hw2' b).2
      hbE2
  have hcD2 : BarrierAt hk ring (labelsOf D2) c := by
    have hcE2 : BarrierAt hk ring (labelsOf E2) c := by
      simpa [hlabels2] using hcD1
    exact (barrierAt_rawRun_iff hk ring hw2' c).2
      hcE2
  have hphaseBD2 : (D2 b).phase = true := by
    simpa [D2] using (rawRun_phases_eq hk ring hw2' b).trans hphaseB2
  have hprobeCD2 : (D2 c).probe = false := by
    have hbE2 : BarrierAt hk ring (labelsOf E2) b := by
      simpa [hlabels2] using hbD1
    have h := rawRun_incoming_barrier_head_frame hk ring b c hbc
      hw2' hbE2 hprobeC2
    exact h.2
  have hreadyB2 : AdvanceReady hk ring D2 b :=
    ⟨(barrierAt_labelsOf_iff hk ring D2 b).1 hbD2,
      hphaseBD2, by simpa [hbc] using hprobeCD2⟩
  have hdrop := adjacent_ready_barrierCount_lt hk ring hn2
    D2 b c hbc hbD2 hcD2 hphaseBD2 hprobeCD2
  have hcountD0 : barrierCount hk ring (labelsOf D0) =
      barrierCount hk ring (labelsOf C) := by
    exact barrierCount_rawRun_eq hk ring hw0
  have hcountD1 : barrierCount hk ring (labelsOf D1) =
      barrierCount hk ring (labelsOf E1) := by
    exact barrierCount_rawRun_eq hk ring hw1'
  have hcountD2 : barrierCount hk ring (labelsOf D2) =
      barrierCount hk ring (labelsOf E2) := by
    exact barrierCount_rawRun_eq hk ring hw2'
  have hcountAll : barrierCount hk ring (labelsOf D2) =
      barrierCount hk ring (labelsOf C) := by
    calc
      barrierCount hk ring (labelsOf D2) =
          barrierCount hk ring (labelsOf E2) := hcountD2
      _ = barrierCount hk ring (labelsOf D1) := by rw [hlabels2]
      _ = barrierCount hk ring (labelsOf E1) := hcountD1
      _ = barrierCount hk ring (labelsOf D0) := by rw [hlabels1]
      _ = barrierCount hk ring (labelsOf C) := hcountD0
  rw [hcountAll] at hdrop
  simpa [OriginalGappedThree.gappedService3,
    OriginalGappedThree.gapHit, E1, E2, D0, D1, D2] using hdrop

def C1 {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (a : Fin n) : Fin n → State k :=
  (protocol k hk).step ring C a

def C2 {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (a b : Fin n) : Fin n → State k :=
  (protocol k hk).step ring (C1 hk ring C a) b

def C3 {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (a b : Fin n) : Fin n → State k :=
  (protocol k hk).step ring (C2 hk ring C a b) a

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
    (((protocol k hk).step ring C e)
      (ring.rightNeighbor e)).phase = false ∧
    (((protocol k hk).step ring C e)
      (ring.rightNeighbor e)).probe = false := by
  rcases hr with ⟨hbar, hphase, hprobe⟩
  have hne := rightNeighbor_ne_self ring hn2 e
  simp only [PopulationProtocol.step, AAFJPK.protocol, if_neg hne, if_pos rfl]
  rw [transition_of_barrier hk _ _ hbar]
  rw [barrierStep_phase_one_probe_free hk _ _ hphase hprobe]
  simp [hprobe]

private theorem nonready_barrier_other_phase
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e j : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e)
    (hnot : ¬ AdvanceReady hk ring C e)
    (hje : j ≠ e) :
    ((protocol k hk).step ring C e j).phase = (C j).phase := by
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

private theorem barrier_hit_source_controls
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e) :
    ((protocol k hk).step ring C e e).probe = false ∧
      ((protocol k hk).step ring C e e).phase = true := by
  have hjournal :
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
    (barrierAt_labelsOf_iff hk ring C e).1 hbar
  have hlocal :
      (transition hk (C e) (C (ring.rightNeighbor e))).1.probe = false ∧
        (transition hk (C e) (C (ring.rightNeighbor e))).1.phase = true := by
    rw [transition_of_barrier hk _ _ hjournal]
    cases hphase : (C e).phase with
    | false =>
        rw [barrierStep_phase_zero hk _ _ hphase]
        cases hp : (C e).probe <;> simp [probeHitsBarrier, hp]
    | true =>
        cases hp : (C (ring.rightNeighbor e)).probe with
        | false =>
            rw [barrierStep_phase_one_probe_free hk _ _ hphase hp]
            cases hu : (C e).probe <;>
              simp [probeHitsBarrier, hu, hphase]
        | true =>
            rw [barrierStep_phase_one_probe_blocked hk _ _ hphase hp]
            cases hu : (C e).probe <;>
              simp [probeHitsBarrier, hu, hphase]
  simpa [PopulationProtocol.step, protocol] using hlocal

private theorem moveBar
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e i : Fin n)
    (hr : AdvanceReady hk ring C e)
    (hf : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor e))
    (hi : BarrierAt hk ring (labelsOf C) i) :
    BarrierAt hk ring (labelsOf ((protocol k hk).step ring C e))
      (redirectEdge ring e i) := by
  apply (mem_barrierSupport_iff hk ring _ _).1
  apply (protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus
    hk ring hn2 C e hr hf _).2
  exact ⟨i, (mem_barrierSupport_iff hk ring _ i).2 hi, rfl⟩

private theorem cold3
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (a b : Fin n)
    (hab : ring.rightNeighbor a = b)
    (ha : BarrierAt hk ring (labelsOf C) a)
    (hb : BarrierAt hk ring (labelsOf C) b)
    (hpa : (C a).phase = false) (hpb : (C b).phase = false) :
    barrierCount hk ring (labelsOf (C3 hk ring C a b)) <
      barrierCount hk ring (labelsOf C) := by
  have hn2 : 1 < n := by omega
  have hba : b ≠ a := by
    rw [← hab]; exact rightNeighbor_ne_self ring hn2 a
  have hna : ¬ AdvanceReady hk ring C a := by
    intro h; exact Bool.noConfusion (hpa.symm.trans h.2.1)
  have l1 : labelsOf (C1 hk ring C a) = labelsOf C := by
    simpa [C1] using labelsOf_step_eq_self_of_not_ready hk ring C a hna
  have pa1 : (C1 hk ring C a a).phase = true := by
    simpa [C1] using (barrier_hit_source_controls hk ring C a ha).2
  have hb1 : BarrierAt hk ring (labelsOf (C1 hk ring C a)) b := by
    rw [l1]; exact hb
  have pb1 : (C1 hk ring C a b).phase = false :=
    (nonready_barrier_other_phase hk ring hn2 C a b ha hna hba).trans hpb
  have hnb : ¬ AdvanceReady hk ring (C1 hk ring C a) b := by
    intro h; exact Bool.noConfusion (pb1.symm.trans h.2.1)
  have l2 : labelsOf (C2 hk ring C a b) = labelsOf (C1 hk ring C a) := by
    simpa [C2] using labelsOf_step_eq_self_of_not_ready
      hk ring (C1 hk ring C a) b hnb
  have pa2 : (C2 hk ring C a b a).phase = true :=
    (nonready_barrier_other_phase hk ring hn2
      (C1 hk ring C a) b a hb1 hnb hba.symm).trans pa1
  have pr2 : (C2 hk ring C a b b).probe = false := by
    simpa [C2] using
      (barrier_hit_source_controls hk ring (C1 hk ring C a) b hb1).1
  have ha2 : BarrierAt hk ring (labelsOf (C2 hk ring C a b)) a := by
    rw [l2,l1]; exact ha
  have hb2 : BarrierAt hk ring (labelsOf (C2 hk ring C a b)) b := by
    rw [l2,l1]; exact hb
  have hd := adjacent_ready_barrierCount_lt hk ring hn2
    (C2 hk ring C a b) a b hab ha2 hb2 pa2 pr2
  rw [l2,l1] at hd
  simpa [C3] using hd

theorem adjacent_barriers_bounded_drop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (q : Fin n)
    (hq : BarrierAt hk ring (labelsOf C) q)
    (hb0 : BarrierAt hk ring (labelsOf C) (ring.rightNeighbor q)) :
    ∃ w : List (Fin n), w.length ≤ 6 ∧
      barrierCount hk ring (labelsOf (rawRun hk ring C w)) <
        barrierCount hk ring (labelsOf C) := by
  have hn2 : 1 < n := by omega
  let b := ring.rightNeighbor q
  let c := ring.rightNeighbor b
  have hqb : q ≠ b := by
    dsimp [b]; exact (rightNeighbor_ne_self ring hn2 q).symm
  have hcq : c ≠ q := by dsimp [b,c]; exact two_hop_ne ring hn3 q
  let D1 := C1 hk ring C q
  let D2 := C2 hk ring C q b
  let D3 := C3 hk ring C q b
  by_cases rq : AdvanceReady hk ring C q
  · refine ⟨[q], by simp, ?_⟩
    simpa [rawRun] using adjacent_ready_barrierCount_lt hk ring hn2
      C q b rfl hq (by simpa [b] using hb0) rq.2.1 rq.2.2
  · have l1 : labelsOf D1 = labelsOf C := by
      simpa [D1,C1] using labelsOf_step_eq_self_of_not_ready hk ring C q rq
    have pq1 : (D1 q).phase = true := by
      simpa [D1,C1] using (barrier_hit_source_controls hk ring C q hq).2
    have hq1 : BarrierAt hk ring (labelsOf D1) q := by rw [l1]; exact hq
    have hb1 : BarrierAt hk ring (labelsOf D1) b := by
      rw [l1]; simpa [b] using hb0
    by_cases rb : AdvanceReady hk ring D1 b
    · by_cases hc1 : BarrierAt hk ring (labelsOf D1) c
      · refine ⟨[q,b], by simp, ?_⟩
        have hd := adjacent_ready_barrierCount_lt hk ring hn2
          D1 b c rfl hb1 hc1 rb.2.1 rb.2.2
        rw [l1] at hd
        simpa [rawRun,D1,C1] using hd
      · have hq2 : BarrierAt hk ring (labelsOf D2) q := by
          have h := moveBar hk ring hn2 D1 b q rb
            (by simpa [c] using hc1) hq1
          simpa [D2,C2,redirectEdge,hqb] using h
        have hc2 : BarrierAt hk ring (labelsOf D2) c := by
          have h := moveBar hk ring hn2 D1 b b rb
            (by simpa [c] using hc1) hb1
          simpa [D2,C2,c,redirectEdge] using h
        have hbf : ¬ BarrierAt hk ring (labelsOf D2) b := by
          simpa [D2,C2] using protocol_advance_repairs_edge hk ring hn2 D1 b rb
        have pq2 : (D2 q).phase = true := by
          have h := step_other (protocol k hk) ring D1 b q hqb hcq.symm
          have hD2q : D2 q = D1 q := by
            change ((protocol k hk).step ring D1 b) q = D1 q
            exact h
          rw [hD2q]
          exact pq1
        have pr2 : (D2 b).probe = false := by
          simpa [D2,C2] using (barrier_hit_source_controls hk ring D1 b hb1).1
        have rq2 : AdvanceReady hk ring D2 q := by
          refine ⟨(barrierAt_labelsOf_iff hk ring D2 q).1 hq2, pq2, ?_⟩
          simpa [b] using pr2
        have hb3 : BarrierAt hk ring (labelsOf D3) b := by
          have h := moveBar hk ring hn2 D2 q q rq2
            (by simpa [b] using hbf) hq2
          simpa [D3,C3,b,redirectEdge] using h
        have hc3 : BarrierAt hk ring (labelsOf D3) c := by
          have h := moveBar hk ring hn2 D2 q c rq2
            (by simpa [b] using hbf) hc2
          simpa [D3,C3,redirectEdge,hcq] using h
        have pb3 : (D3 b).phase = false := by
          simpa [D3,C3,b] using (ready_head_controls hk ring hn2 D2 q rq2).1
        have pc2 : (D2 c).phase = false := by
          simpa [D2,C2,c] using (ready_head_controls hk ring hn2 D1 b rb).1
        have pc3 : (D3 c).phase = false := by
          have h := step_other (protocol k hk) ring D2 q c hcq
            (by simpa [b,c] using rightNeighbor_ne_self ring hn2 b)
          have hD3c : D3 c = D2 c := by
            change ((protocol k hk).step ring D2 q) c = D2 c
            exact h
          rw [hD3c]
          exact pc2
        have ht := cold3 hk ring hn3 D3 b c rfl hb3 hc3 pb3 pc3
        have h1 := protocol_step_barrierCount_le hk ring hn2 C q
        have h2 := protocol_step_barrierCount_le hk ring hn2 D1 b
        have h3 := protocol_step_barrierCount_le hk ring hn2 D2 q
        refine ⟨[q,b,q,b,c,b], by simp, ?_⟩
        have hp : barrierCount hk ring (labelsOf D3) ≤
            barrierCount hk ring (labelsOf C) := by
          simpa [D1,D2,D3,C1,C2,C3] using
            Nat.le_trans h3 (Nat.le_trans h2 h1)
        have hf := Nat.lt_of_lt_of_le ht hp
        simpa [rawRun,D1,D2,D3,C1,C2,C3] using hf
    · have l2 : labelsOf D2 = labelsOf D1 := by
        simpa [D2,C2] using labelsOf_step_eq_self_of_not_ready hk ring D1 b rb
      have pq2 : (D2 q).phase = true :=
        (nonready_barrier_other_phase hk ring hn2 D1 b q hb1 rb hqb).trans pq1
      have pr2 : (D2 b).probe = false := by
        simpa [D2,C2] using (barrier_hit_source_controls hk ring D1 b hb1).1
      have hq2 : BarrierAt hk ring (labelsOf D2) q := by rw [l2,l1]; exact hq
      have hb2 : BarrierAt hk ring (labelsOf D2) b := by
        rw [l2,l1]; simpa [b] using hb0
      refine ⟨[q,b,q], by simp, ?_⟩
      have hd := adjacent_ready_barrierCount_lt hk ring hn2
        D2 q b rfl hq2 hb2 pq2 (by simpa [b] using pr2)
      rw [l2,l1] at hd
      simpa [rawRun,D1,D2,C1,C2] using hd

theorem adjacent_barriers_gapped_drop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (a b c : Fin n)
    (hab : ring.rightNeighbor a = b)
    (hbc : ring.rightNeighbor b = c)
    (ha : BarrierAt hk ring (labelsOf C) a)
    (hb : BarrierAt hk ring (labelsOf C) b)
    (w0 w1 w2 w3 w4 w5 : List (Fin n))
    (hw0 : CurrentNonbarrierWord hk ring C w0)
    (hw1 : CurrentNonbarrierWord hk ring
      (OriginalGappedThree.gapHit hk ring C w0 a) w1)
    (hw2 : CurrentNonbarrierWord hk ring
      (OriginalGappedThree.gapHit hk ring
        (OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2)
    (hw3 : CurrentNonbarrierWord hk ring
      (OriginalGappedThree.gapHit hk ring
        (OriginalGappedThree.gapHit hk ring
          (OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2 a) w3)
    (hw4 : CurrentNonbarrierWord hk ring
      (OriginalGappedThree.gapHit hk ring
        (OriginalGappedThree.gapHit hk ring
          (OriginalGappedThree.gapHit hk ring
            (OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2 a) w3 b) w4)
    (hw5 : CurrentNonbarrierWord hk ring
      (OriginalGappedThree.gapHit hk ring
        (OriginalGappedThree.gapHit hk ring
          (OriginalGappedThree.gapHit hk ring
            (OriginalGappedThree.gapHit hk ring
              (OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2 a) w3 b)
        w4 c) w5) :
    barrierCount hk ring
        (labelsOf (gappedService6 hk ring C a b c w0 w1 w2 w3 w4 w5)) <
      barrierCount hk ring (labelsOf C) := by
  have hn2 : 1 < n := by omega
  have hba : b ≠ a := by
    rw [← hab]
    exact rightNeighbor_ne_self ring hn2 a
  have hcb : c ≠ b := by
    rw [← hbc]
    exact rightNeighbor_ne_self ring hn2 b
  have hca : c ≠ a := by
    rw [← hbc, ← hab]
    exact two_hop_ne_g ring hn3 a
  have hbc2 : b ≠ ring.rightNeighbor c := by
    rw [← hbc]
    exact (two_hop_ne_g ring hn3 b).symm
  let D0 := rawRun hk ring C w0
  let E1 := OriginalGappedThree.gapHit hk ring C w0 a
  let D1 := rawRun hk ring E1 w1
  let E2 := OriginalGappedThree.gapHit hk ring E1 w1 b
  let D2 := rawRun hk ring E2 w2
  let E3 := OriginalGappedThree.gapHit hk ring E2 w2 a
  let D3 := rawRun hk ring E3 w3
  let E4 := OriginalGappedThree.gapHit hk ring E3 w3 b
  let D4 := rawRun hk ring E4 w4
  let E5 := OriginalGappedThree.gapHit hk ring E4 w4 c
  let D5 := rawRun hk ring E5 w5
  let E6 := OriginalGappedThree.gapHit hk ring E5 w5 b
  have hw1' : CurrentNonbarrierWord hk ring E1 w1 := by
    simpa [E1] using hw1
  have hw2' : CurrentNonbarrierWord hk ring E2 w2 := by
    simpa [E2, E1] using hw2
  have hw3' : CurrentNonbarrierWord hk ring E3 w3 := by
    simpa [E3, E2, E1] using hw3
  have hw4' : CurrentNonbarrierWord hk ring E4 w4 := by
    simpa [E4, E3, E2, E1] using hw4
  have hw5' : CurrentNonbarrierWord hk ring E5 w5 := by
    simpa [E5, E4, E3, E2, E1] using hw5
  have hle1 : barrierCount hk ring (labelsOf E1) ≤
      barrierCount hk ring (labelsOf C) := by
    simpa [E1] using gapHit_barrierCount_le hk ring hn2 C w0 a hw0
  have hle2 : barrierCount hk ring (labelsOf E2) ≤
      barrierCount hk ring (labelsOf E1) := by
    simpa [E2] using gapHit_barrierCount_le hk ring hn2 E1 w1 b hw1'
  have hle3 : barrierCount hk ring (labelsOf E3) ≤
      barrierCount hk ring (labelsOf E2) := by
    simpa [E3] using gapHit_barrierCount_le hk ring hn2 E2 w2 a hw2'
  have hle4 : barrierCount hk ring (labelsOf E4) ≤
      barrierCount hk ring (labelsOf E3) := by
    simpa [E4] using gapHit_barrierCount_le hk ring hn2 E3 w3 b hw3'
  have hle5 : barrierCount hk ring (labelsOf E5) ≤
      barrierCount hk ring (labelsOf E4) := by
    simpa [E5] using gapHit_barrierCount_le hk ring hn2 E4 w4 c hw4'
  have hle6 : barrierCount hk ring (labelsOf E6) ≤
      barrierCount hk ring (labelsOf E5) := by
    simpa [E6] using gapHit_barrierCount_le hk ring hn2 E5 w5 b hw5'
  have hle6_1 : barrierCount hk ring (labelsOf E6) ≤
      barrierCount hk ring (labelsOf E1) := by
    omega
  have hle6_2 : barrierCount hk ring (labelsOf E6) ≤
      barrierCount hk ring (labelsOf E2) := by
    omega
  have hle6_3 : barrierCount hk ring (labelsOf E6) ≤
      barrierCount hk ring (labelsOf E3) := by
    omega
  have hbarA0 : BarrierAt hk ring (labelsOf D0) a :=
    (barrierAt_rawRun_iff hk ring hw0 a).2 ha
  have hbarB0 : BarrierAt hk ring (labelsOf D0) b :=
    (barrierAt_rawRun_iff hk ring hw0 b).2 hb
  by_cases hra : AdvanceReady hk ring D0 a
  · have hd := adjacent_ready_barrierCount_lt hk ring hn2
      D0 a b hab hbarA0 hbarB0 hra.2.1 (by simpa [hab] using hra.2.2)
    have hdE1 : barrierCount hk ring (labelsOf E1) <
        barrierCount hk ring (labelsOf C) := by
      have hstep : barrierCount hk ring (labelsOf E1) <
          barrierCount hk ring (labelsOf D0) := by
        simpa [E1, D0, OriginalGappedThree.gapHit] using hd
      have hD0eq : barrierCount hk ring (labelsOf D0) =
          barrierCount hk ring (labelsOf C) := by
        simpa [D0] using barrierCount_rawRun_eq hk ring hw0
      calc
        barrierCount hk ring (labelsOf E1) <
            barrierCount hk ring (labelsOf D0) := hstep
        _ = barrierCount hk ring (labelsOf C) := hD0eq
    exact Nat.lt_of_le_of_lt hle6_1 hdE1
  · have hlabels1 : labelsOf E1 = labelsOf D0 := by
      simpa [E1, OriginalGappedThree.gapHit] using
        labelsOf_step_eq_self_of_not_ready hk ring D0 a hra
    have hphaseA1 : (E1 a).phase = true := by
      simpa [E1, OriginalGappedThree.gapHit] using
        (barrier_hit_source_controls hk ring D0 a hbarA0).2
    have hprobeA1 : (E1 a).probe = false := by
      simpa [E1, OriginalGappedThree.gapHit] using
        (barrier_hit_source_controls hk ring D0 a hbarA0).1
    have hbarA1 : BarrierAt hk ring (labelsOf E1) a := by
      rw [hlabels1]
      exact hbarA0
    have hbarB1 : BarrierAt hk ring (labelsOf E1) b := by
      rw [hlabels1]
      exact hbarB0
    have hlabelsD1 : labelsOf D1 = labelsOf E1 := by
      simpa [D1] using labelsOf_rawRun_eq hk ring hw1'
    have hbarA_D1 : BarrierAt hk ring (labelsOf D1) a := by
      simpa [D1] using (barrierAt_rawRun_iff hk ring hw1' a).2 hbarA1
    have hbarB_D1 : BarrierAt hk ring (labelsOf D1) b := by
      simpa [D1] using (barrierAt_rawRun_iff hk ring hw1' b).2 hbarB1
    have hphaseA_D1 : (D1 a).phase = true := by
      simpa [D1] using (rawRun_phases_eq hk ring hw1' a).trans hphaseA1
    by_cases hrb : AdvanceReady hk ring D1 b
    · let cbar := BarrierAt hk ring (labelsOf D1) c
      by_cases hcD1 : BarrierAt hk ring (labelsOf D1) c
      · have hd := adjacent_ready_barrierCount_lt hk ring hn2
          D1 b c hbc hbarB_D1 hcD1 hrb.2.1 (by simpa [hbc] using hrb.2.2)
        have hdE2 : barrierCount hk ring (labelsOf E2) <
            barrierCount hk ring (labelsOf C) := by
          have hstep : barrierCount hk ring (labelsOf E2) <
              barrierCount hk ring (labelsOf D1) := by
            simpa [E2, D1, OriginalGappedThree.gapHit] using hd
          have hD1eq : barrierCount hk ring (labelsOf D1) =
              barrierCount hk ring (labelsOf E1) := by
            simpa [D1] using barrierCount_rawRun_eq hk ring hw1'
          calc
            barrierCount hk ring (labelsOf E2) <
                barrierCount hk ring (labelsOf D1) := hstep
            _ = barrierCount hk ring (labelsOf E1) := hD1eq
            _ ≤ barrierCount hk ring (labelsOf C) := hle1
        exact Nat.lt_of_le_of_lt hle6_2 hdE2
      · have hbarE2A : BarrierAt hk ring (labelsOf E2) a := by
          have h := moveBar hk ring hn2 D1 b a hrb
            (by simpa [hbc] using hcD1) hbarA_D1
          simpa [E2, D1, OriginalGappedThree.gapHit, redirectEdge, hba.symm]
            using h
        have hbarE2C : BarrierAt hk ring (labelsOf E2) c := by
          have h := moveBar hk ring hn2 D1 b b hrb
            (by simpa [hbc] using hcD1) hbarB_D1
          simpa [E2, D1, OriginalGappedThree.gapHit, redirectEdge, hbc]
            using h
        have hfreeE2B : ¬ BarrierAt hk ring (labelsOf E2) b := by
          simpa [E2, OriginalGappedThree.gapHit] using
            protocol_advance_repairs_edge hk ring hn2 D1 b hrb
        have hfreeD2B : ¬ BarrierAt hk ring (labelsOf D2) b := by
          intro h
          exact hfreeE2B ((barrierAt_rawRun_iff hk ring hw2' b).1 h)
        have hphaseE2A : (E2 a).phase = true := by
          have h := step_other_g (protocol k hk) ring D1 b a hba.symm
            (by simpa [hbc] using hca.symm)
          have heq : E2 a = D1 a := by
            change ((protocol k hk).step ring D1 b) a = D1 a
            exact h
          rw [heq]
          exact hphaseA_D1
        have hprobeE2B : (E2 b).probe = false := by
          simpa [E2, OriginalGappedThree.gapHit] using
            (barrier_hit_source_controls hk ring D1 b hbarB_D1).1
        have hphaseE2C_probe :
            (E2 c).phase = false ∧ (E2 c).probe = false := by
          simpa [E2, OriginalGappedThree.gapHit, hbc] using
            ready_head_controls hk ring hn2 D1 b hrb
        have hw2barA : BarrierAt hk ring (labelsOf D2) a := by
          simpa [D2] using (barrierAt_rawRun_iff hk ring hw2' a).2 hbarE2A
        have hw2barC : BarrierAt hk ring (labelsOf D2) c := by
          simpa [D2] using (barrierAt_rawRun_iff hk ring hw2' c).2 hbarE2C
        have hphaseD2A : (D2 a).phase = true := by
          simpa [D2] using (rawRun_phases_eq hk ring hw2' a).trans hphaseE2A
        have hprobeD2B : (D2 b).probe = false := by
          have h := rawRun_incoming_barrier_head_frame hk ring a b hab
            hw2' hbarE2A hprobeE2B
          exact h.2
        have hprobeD2C : (D2 c).probe = false := by
          exact rawRun_preserves_c_probe hk ring hn2 a b c hab hbc
            hbarE2A hbarE2C hprobeE2B hphaseE2C_probe.2 hw2'
        have hreadyD2A : AdvanceReady hk ring D2 a :=
          ⟨(barrierAt_labelsOf_iff hk ring D2 a).1 hw2barA,
            hphaseD2A, by simpa [hab] using hprobeD2B⟩
        have hbarE3B : BarrierAt hk ring (labelsOf E3) b := by
          have hfreeD2Aplus : ¬ BarrierAt hk ring (labelsOf D2)
              (ring.rightNeighbor a) := by
            simpa [hab] using hfreeD2B
          have h := moveBar hk ring hn2 D2 a a hreadyD2A
            hfreeD2Aplus hw2barA
          simpa [E3, D2, OriginalGappedThree.gapHit, redirectEdge, hab]
            using h
        have hbarE3C : BarrierAt hk ring (labelsOf E3) c := by
          have hfreeD2Aplus : ¬ BarrierAt hk ring (labelsOf D2)
              (ring.rightNeighbor a) := by
            simpa [hab] using hfreeD2B
          have h := moveBar hk ring hn2 D2 a c hreadyD2A
            hfreeD2Aplus hw2barC
          simpa [E3, D2, OriginalGappedThree.gapHit, redirectEdge, hab, hca, hcb]
            using h
        have hphaseE3B : (E3 b).phase = false := by
          simpa [E3, OriginalGappedThree.gapHit, hab] using
            (ready_head_controls hk ring hn2 D2 a hreadyD2A).1
        have hphaseE3C : (E3 c).phase = false := by
          have h := step_other_g (protocol k hk) ring D2 a c hca
            (by simpa [hab] using hcb)
          have heq : E3 c = D2 c := by
            change ((protocol k hk).step ring D2 a) c = D2 c
            exact h
          have hphaseD2C : (D2 c).phase = false := by
            have hp := rawRun_phases_eq hk ring hw2' c
            exact hp.trans hphaseE2C_probe.1
          rw [heq]
          exact hphaseD2C
        have htail := cold3_gapped hk ring hn3 E3 b c w3 w4 w5
          hbc hbarE3B hbarE3C hphaseE3B hphaseE3C hw3' hw4' hw5'
        have htail' : barrierCount hk ring (labelsOf E6) <
            barrierCount hk ring (labelsOf E3) := by
          simpa [gappedService6, OriginalGappedThree.gappedService3,
            OriginalGappedThree.gapHit, E3, E4, E5, E6] using htail
        have hE3le : barrierCount hk ring (labelsOf E3) ≤
            barrierCount hk ring (labelsOf C) := by
          omega
        exact Nat.lt_of_lt_of_le htail' hE3le
    · have hlabels2 : labelsOf E2 = labelsOf D1 := by
        simpa [E2, OriginalGappedThree.gapHit] using
          labelsOf_step_eq_self_of_not_ready hk ring D1 b hrb
      have hphaseE2A : (E2 a).phase = true := by
        have h := nonready_barrier_other_phase hk ring hn2 D1 b a
          hbarB_D1 hrb hba.symm
        have heq : E2 a = ((protocol k hk).step ring D1 b) a := by rfl
        rw [heq]
        exact h.trans hphaseA_D1
      have hprobeE2B : (E2 b).probe = false := by
        simpa [E2, OriginalGappedThree.gapHit] using
          (barrier_hit_source_controls hk ring D1 b hbarB_D1).1
      have hbarE2A : BarrierAt hk ring (labelsOf E2) a := by
        rw [hlabels2]
        exact hbarA_D1
      have hbarE2B : BarrierAt hk ring (labelsOf E2) b := by
        rw [hlabels2]
        exact hbarB_D1
      have hw2barA : BarrierAt hk ring (labelsOf D2) a := by
        simpa [D2] using (barrierAt_rawRun_iff hk ring hw2' a).2 hbarE2A
      have hw2barB : BarrierAt hk ring (labelsOf D2) b := by
        simpa [D2] using (barrierAt_rawRun_iff hk ring hw2' b).2 hbarE2B
      have hphaseD2A : (D2 a).phase = true := by
        simpa [D2] using (rawRun_phases_eq hk ring hw2' a).trans hphaseE2A
      have hprobeD2B : (D2 b).probe = false := by
        have h := rawRun_incoming_barrier_head_frame hk ring a b hab
          hw2' hbarE2A hprobeE2B
        exact h.2
      have hreadyD2A : AdvanceReady hk ring D2 a :=
        ⟨(barrierAt_labelsOf_iff hk ring D2 a).1 hw2barA,
          hphaseD2A, by simpa [hab] using hprobeD2B⟩
      have hd := adjacent_ready_barrierCount_lt hk ring hn2
        D2 a b hab hw2barA hw2barB hphaseD2A
        (by simpa [hab] using hprobeD2B)
      have hdE3 : barrierCount hk ring (labelsOf E3) <
          barrierCount hk ring (labelsOf C) := by
        have hstep : barrierCount hk ring (labelsOf E3) <
            barrierCount hk ring (labelsOf D2) := by
          simpa [E3, OriginalGappedThree.gapHit] using hd
        have hD2le : barrierCount hk ring (labelsOf D2) ≤
            barrierCount hk ring (labelsOf E2) := by
          have heq := barrierCount_rawRun_eq hk ring hw2'
          calc
            barrierCount hk ring (labelsOf D2) =
                barrierCount hk ring (labelsOf E2) := by
              simpa [D2] using heq
            _ ≤ barrierCount hk ring (labelsOf E2) := Nat.le_refl _
        have hE2le : barrierCount hk ring (labelsOf E2) ≤
            barrierCount hk ring (labelsOf E1) := hle2
        have hE1le : barrierCount hk ring (labelsOf E1) ≤
            barrierCount hk ring (labelsOf C) := hle1
        omega
      have hE3le : barrierCount hk ring (labelsOf E3) ≤
          barrierCount hk ring (labelsOf C) := by
        omega
      have hfinalle : barrierCount hk ring
          (labelsOf (gappedService6 hk ring C a b c w0 w1 w2 w3 w4 w5)) ≤
          barrierCount hk ring (labelsOf E3) := by
        change barrierCount hk ring (labelsOf E6) ≤
          barrierCount hk ring (labelsOf E3)
        exact hle6_3
      exact Nat.lt_of_le_of_lt hfinalle hdE3

end AAFJPK.OriginalArbitraryRemote
