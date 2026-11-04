import Leader.AAFJ.MultiBarrier.SixHitContactBlock
import Leader.AAFJ.MultiBarrier.NonbarrierInterleaving


set_option autoImplicit false


namespace AAFJPK.OriginalGappedFirstTriple


open BarrierAlgebra
open OriginalNonbarrierWord
open OriginalNonbarrierFrame


private theorem two_hop_ne {n : Nat}
    (ring : DirectedRing n) (hn3 : 2 < n) (a : Fin n) :
    ring.rightNeighbor (ring.rightNeighbor a) ≠ a := by
  intro h
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases h1 : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt h1] at hv
    by_cases h2 : a.val + 1 + 1 < n
    · rw [Nat.mod_eq_of_lt h2] at hv
      omega
    · have hw : a.val + 1 + 1 = n := by omega
      rw [hw, Nat.mod_self] at hv
      omega
  · have hw : a.val + 1 = n := by omega
    rw [hw, Nat.mod_self] at hv
    rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    omega


private theorem responder_probe_false
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnon : ¬ IsBarrier hk u v)
    (hu : u.probe = false) (hv : v.probe = false) :
    (transition hk u v).2.probe = false := by
  rw [transition_of_nonbarrier hk u v hnon]
  cases hl : v.leader <;> cases hb : v.bullet <;>
    simp [nonBarrierStep, hl, hb, hu, hv]


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
    have hlocal := responder_probe_false hk
      (C b) (C (ring.rightNeighbor b)) hnon hb (by simpa [hbc] using hc)
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
        exact step_preserves_c_probe
          hk ring hn2 C b c e hbc hnon hcBar hb hc
      change (rawRun hk ring D es c).probe = false
      exact ih haD hcD hbD hcDprobe htail


private theorem ready_head_controls
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (a : Fin n)
    (hr : AdvanceReady hk ring C a) :
    (((protocol k hk).step ring C a) (ring.rightNeighbor a)).phase = false ∧
    (((protocol k hk).step ring C a) (ring.rightNeighbor a)).probe = false := by
  rcases hr with ⟨hbar, hphase, hprobe⟩
  simp only [PopulationProtocol.step, protocol,
    if_neg (rightNeighbor_ne_self ring hn2 a)]
  rw [transition_of_barrier hk _ _ hbar,
    barrierStep_phase_one_probe_free hk _ _ hphase hprobe]
  simp [hprobe]


private theorem step_other {n : Nat}
    (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e i : Fin n)
    (hie : i ≠ e) (hir : i ≠ ring.rightNeighbor e) :
    P.step ring C e i = C i := by
  simp [PopulationProtocol.step, hie, hir]


private theorem ready_advance_pair_support
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (a b c : Fin n)
    (hab : ring.rightNeighbor a = b) (hbc : ring.rightNeighbor b = c)
    (hca : c ≠ a)
    (hs : ∀ e, BarrierAt hk ring (labelsOf C) e ↔ e = a ∨ e = c)
    (hr : AdvanceReady hk ring C a) :
    ∀ e, BarrierAt hk ring
        (labelsOf ((protocol k hk).step ring C a)) e ↔ e = b ∨ e = c := by
  have hba : b ≠ a := by
    rw [← hab]
    exact rightNeighbor_ne_self ring hn2 a
  have hcb : c ≠ b := by
    rw [← hbc]
    exact rightNeighbor_ne_self ring hn2 b
  have hbFree : ¬ BarrierAt hk ring (labelsOf C) b := by
    intro h
    rcases (hs b).1 h with h | h
    · exact hba h
    · exact hcb h.symm
  have hnext : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor a) := by
    simpa [hab] using hbFree
  intro j
  have ht := protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus
    hk ring hn2 C a hr hnext j
  constructor
  · intro hj
    have hm := (mem_barrierSupport_iff hk ring
      (labelsOf ((protocol k hk).step ring C a)) j).2 hj
    rcases ht.1 hm with ⟨i, hi, hmap⟩
    have hib := (mem_barrierSupport_iff hk ring (labelsOf C) i).1 hi
    rcases (hs i).1 hib with hia | hic
    · left
      have hmap' := hmap.symm
      rw [hia] at hmap'
      simpa [redirectEdge, hab] using hmap'
    · right
      have hmap' := hmap.symm
      rw [hic] at hmap'
      simpa [redirectEdge, hca] using hmap'
  · intro hj
    apply (mem_barrierSupport_iff hk ring
      (labelsOf ((protocol k hk).step ring C a)) j).1
    apply ht.2
    rcases hj with hjb | hjc
    · refine ⟨a, (mem_barrierSupport_iff hk ring (labelsOf C) a).2
        ((hs a).2 (Or.inl rfl)), ?_⟩
      rw [hjb]
      simp [redirectEdge, hab]
    · refine ⟨c, (mem_barrierSupport_iff hk ring (labelsOf C) c).2
        ((hs c).2 (Or.inr rfl)), ?_⟩
      rw [hjc]
      simp [redirectEdge, hca]


theorem third_hit_restart_or_drop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (a b c : Fin n)
    (hab : ring.rightNeighbor a = b) (hbc : ring.rightNeighbor b = c)
    (hs : ∀ e, BarrierAt hk ring (labelsOf C) e ↔ e = a ∨ e = c)
    (haPhase : (C a).phase = true)
    (hbProbe : (C b).probe = false)
    (hcPhase : (C c).phase = false) (hcProbe : (C c).probe = false)
    (word : List (Fin n))
    (hw : CurrentNonbarrierWord hk ring C word) :
    barrierCount hk ring
        (labelsOf ((protocol k hk).step ring (rawRun hk ring C word) a)) <
      barrierCount hk ring (labelsOf (rawRun hk ring C word)) ∨
    (NormalizedAdjacentRestart hk ring
        ((protocol k hk).step ring (rawRun hk ring C word) a) b c ∧
      (((protocol k hk).step ring (rawRun hk ring C word) a) b).probe = false ∧
      (((protocol k hk).step ring (rawRun hk ring C word) a) c).probe = false) := by
  have hn2 : 1 < n := by omega
  have hcb : c ≠ b := by
    rw [← hbc]
    exact rightNeighbor_ne_self ring hn2 b
  have hca : c ≠ a := by
    rw [← hbc, ← hab]
    exact two_hop_ne ring hn3 a
  let D := rawRun hk ring C word
  let C3 := (protocol k hk).step ring D a
  change barrierCount hk ring (labelsOf C3) < barrierCount hk ring (labelsOf D) ∨
    (NormalizedAdjacentRestart hk ring C3 b c ∧
      (C3 b).probe = false ∧ (C3 c).probe = false)

  have hsD0 := exactTwoBarrierSupport_rawRun hk ring hw
    (⟨hca.symm, hs⟩ : ExactTwoBarrierSupport hk ring C a c)
  have hsD := hsD0.2
  have ha0 : BarrierAt hk ring (labelsOf C) a :=
    (hs a).2 (Or.inl rfl)
  have hc0 : BarrierAt hk ring (labelsOf C) c :=
    (hs c).2 (Or.inr rfl)
  have hhead := rawRun_incoming_barrier_head_frame
    hk ring a b hab hw ha0 hbProbe
  have haD : BarrierAt hk ring (labelsOf D) a := by
    simpa [D] using hhead.1
  have haPhaseD : (D a).phase = true := by
    simpa [D] using (rawRun_phases_eq hk ring hw a).trans haPhase
  have hbProbeD : (D b).probe = false := by
    simpa [D] using hhead.2
  have hcPhaseD : (D c).phase = false := by
    simpa [D] using (rawRun_phases_eq hk ring hw c).trans hcPhase
  have hcProbeD : (D c).probe = false := by
    simpa [D] using rawRun_preserves_c_probe
      hk ring hn2 a b c hab hbc ha0 hc0 hbProbe hcProbe hw
  have hr : AdvanceReady hk ring D a :=
    ⟨(barrierAt_labelsOf_iff hk ring D a).1 haD, haPhaseD,
      by simpa [hab] using hbProbeD⟩
  have hs3 := ready_advance_pair_support
    hk ring hn2 D a b c hab hbc hca hsD hr
  have hb3 := ready_head_controls hk ring hn2 D a hr
  have hbCtl : (C3 b).phase = false ∧ (C3 b).probe = false := by
    simpa [C3, hab] using hb3
  have hcKeep : C3 c = D c := by
    exact step_other (protocol k hk) ring D a c hca
      (by simpa [hab] using hcb)
  have hc3Phase : (C3 c).phase = false := by
    rw [hcKeep]
    exact hcPhaseD
  have hc3Probe : (C3 c).probe = false := by
    rw [hcKeep]
    exact hcProbeD

  right
  exact ⟨⟨⟨hbc, hs3⟩, hbCtl.1, hc3Phase⟩, hbCtl.2, hc3Probe⟩


#print axioms third_hit_restart_or_drop


end AAFJPK.OriginalGappedFirstTriple
