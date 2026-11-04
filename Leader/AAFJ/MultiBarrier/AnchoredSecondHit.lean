import Leader.AAFJ.MultiBarrier.SixHitContactBlock
import Leader.AAFJ.MultiBarrier.NonbarrierInterleaving


set_option autoImplicit false


namespace AAFJPK.OriginalAnchoredSecond


open BarrierAlgebra
open AAFJPK.OriginalNonbarrierWord


private theorem step_other {n : Nat}
    (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e i : Fin n)
    (hie : i ≠ e) (hir : i ≠ ring.rightNeighbor e) :
    P.step ring C e i = C i := by
  simp [PopulationProtocol.step, hie, hir]


private theorem twoHop_ne {n : Nat} (ring : DirectedRing n)
    (hn3 : 2 < n) (e : Fin n) :
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


private theorem ready_head_controls
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
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


private theorem barrier_hit_source_controls
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n)
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
        rw [barrierStep_phase_zero hk (C e)
          (C (ring.rightNeighbor e)) hphase]
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


private theorem original_transport_pair
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
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


theorem second_hit_stage2
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (D : Fin n → State k) (a b : Fin n) (w1 : List (Fin n))
    (hab : ring.rightNeighbor a = b)
    (hs : ExactTwoBarrierSupport hk ring D a b)
    (haPhase : (D a).phase = true)
    (hw1 : CurrentNonbarrierWord hk ring D w1) :
    let W := rawRun hk ring D w1
    let c := ring.rightNeighbor b
    let E := (AAFJPK.protocol k hk).step ring W b
    AdvanceReady hk ring E a ∧
      (ExactTwoBarrierSupport hk ring E a b ∨
        (ExactTwoBarrierSupport hk ring E a c ∧
          (E c).phase = false ∧ (E c).probe = false)) := by
  let W := rawRun hk ring D w1
  let c := ring.rightNeighbor b
  let E := (AAFJPK.protocol k hk).step ring W b
  change AdvanceReady hk ring E a ∧
    (ExactTwoBarrierSupport hk ring E a b ∨
      (ExactTwoBarrierSupport hk ring E a c ∧
        (E c).phase = false ∧ (E c).probe = false))


  have hn2 : 1 < n := by omega


  have hsW : ExactTwoBarrierSupport hk ring W a b := by
    dsimp [W]
    exact exactTwoBarrierSupport_rawRun hk ring hw1 hs
  have hWa : BarrierAt hk ring (labelsOf W) a :=
    (hsW.2 a).2 (Or.inl rfl)
  have hWb : BarrierAt hk ring (labelsOf W) b :=
    (hsW.2 b).2 (Or.inr rfl)
  have hphaseWa : (W a).phase = true := by
    dsimp [W]
    exact (rawRun_phases_eq hk ring hw1 a).trans haPhase


  have habne : a ≠ b := hsW.1
  have hbc : ring.rightNeighbor b = c := by
    rfl
  have hbcne : b ≠ c := by
    dsimp [c]
    exact (rightNeighbor_ne_self ring hn2 b).symm
  have hac : a ≠ c := by
    intro h
    apply twoHop_ne ring hn3 a
    calc
      ring.rightNeighbor (ring.rightNeighbor a) =
          ring.rightNeighbor b := congrArg ring.rightNeighbor hab
      _ = c := rfl
      _ = a := h.symm
  have harb : a ≠ ring.rightNeighbor b := by
    simpa [c] using hac
  have hcFree : ¬ BarrierAt hk ring (labelsOf W) c := by
    intro hc
    rcases (hsW.2 c).1 hc with h | h
    · exact hac h.symm
    · exact hbcne h.symm


  have hEa : E a = W a := by
    dsimp [E]
    exact step_other (AAFJPK.protocol k hk) ring W b a habne harb
  have hphaseEa : (E a).phase = true := by
    rw [hEa]
    exact hphaseWa
  have hbProbeE : (E b).probe = false := by
    dsimp [E]
    exact (barrier_hit_source_controls hk ring W b hWb).1


  by_cases hrb : AdvanceReady hk ring W b
  · have hsE' :
        ∀ j, BarrierAt hk ring (labelsOf E) j ↔ j = a ∨ j = c := by
      dsimp [E]
      exact original_transport_pair hk ring hn2 W a b c hbc habne hrb
        (by simpa [c] using hcFree) hsW.2
    have hsE : ExactTwoBarrierSupport hk ring E a c := ⟨hac, hsE'⟩
    have hcCtl : (E c).phase = false ∧ (E c).probe = false := by
      dsimp [E]
      simpa [c] using ready_head_controls hk ring hn2 W b hrb
    refine ⟨?_, Or.inr ⟨hsE, hcCtl⟩⟩
    refine ⟨(barrierAt_labelsOf_iff hk ring E a).1
      ((hsE.2 a).2 (Or.inl rfl)), hphaseEa, ?_⟩
    simpa [hab] using hbProbeE


  · have hlabels : labelsOf E = labelsOf W := by
      dsimp [E]
      exact labelsOf_step_eq_self_of_not_ready hk ring W b hrb
    have hsE : ExactTwoBarrierSupport hk ring E a b := by
      refine ⟨habne, ?_⟩
      intro j
      rw [hlabels]
      exact hsW.2 j
    refine ⟨?_, Or.inl hsE⟩
    refine ⟨(barrierAt_labelsOf_iff hk ring E a).1
      ((hsE.2 a).2 (Or.inl rfl)), hphaseEa, ?_⟩
    simpa [hab] using hbProbeE


theorem ready_through_next_nb
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    {E : Fin n → State k} {w : List (Fin n)} (a : Fin n)
    (hr : AdvanceReady hk ring E a)
    (hw : CurrentNonbarrierWord hk ring E w) :
    AdvanceReady hk ring (rawRun hk ring E w) a :=
  rawRun_preserves_advanceReady hk ring a hr hw


#print axioms second_hit_stage2
#print axioms ready_through_next_nb


end AAFJPK.OriginalAnchoredSecond
