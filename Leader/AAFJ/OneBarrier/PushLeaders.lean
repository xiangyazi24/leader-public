import Leader.AAFJ.OneBarrier.UniqueLeaderCleanup


set_option autoImplicit false


namespace AAFJPK.OriginalOneBarrierPushLeaders


open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord
open OriginalPushOne


private theorem transition_barrier_right_leader
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hbar : IsBarrier hk u v) :
    (transition hk u v).2.leader = v.leader := by
  rw [transition_of_barrier hk u v hbar]
  cases hup : u.probe <;>
    cases huph : u.phase <;>
    cases hvp : v.probe <;>
    cases hvl : v.leader <;>
    simp [barrierStep, probeHitsBarrier, hup, huph, hvp, hvl]


private theorem transition_nonbarrier_left_leader
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnb : ¬ IsBarrier hk u v) :
    (transition hk u v).1.leader = u.leader := by
  rw [transition_of_nonbarrier hk u v hnb]
  cases hvl : v.leader <;>
    cases hvb : v.bullet <;>
    cases hup : u.probe <;>
    simp [nonBarrierStep, hvl, hvb, hup]


private theorem transition_nonbarrier_right_no_birth
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnb : ¬ IsBarrier hk u v) :
    (transition hk u v).2.leader = true → v.leader = true := by
  rw [transition_of_nonbarrier hk u v hnb]
  cases hvl : v.leader <;>
    cases hvb : v.bullet <;>
    cases hup : u.probe <;>
    simp [nonBarrierStep, hvl, hvb, hup]


private theorem step_other_state
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e i : Fin n)
    (hie : i ≠ e) (hir : i ≠ ring.rightNeighbor e) :
    ((protocol k hk).step ring C e) i = C i := by
  simp [PopulationProtocol.step, protocol, hie, hir]


private theorem step_barrier_frame
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (C : Fin n → State k) (e : Fin n)
    (hbar : IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    let D := (protocol k hk).step ring C e
    (D (ring.rightNeighbor e)).leader =
        (C (ring.rightNeighbor e)).leader ∧
      (∀ i : Fin n, (D i).leader = true →
        (C i).leader = true ∨ i = e) := by
  dsimp only
  have hre := rightNeighbor_ne_self ring hn2 e
  have hlocal :=
    transition_barrier_right_leader hk
      (C e) (C (ring.rightNeighbor e)) hbar
  have hright :
      (((protocol k hk).step ring C e) (ring.rightNeighbor e)).leader =
        (C (ring.rightNeighbor e)).leader := by
    simpa [PopulationProtocol.step, protocol, hre] using hlocal
  refine ⟨hright, ?_⟩
  intro i hi
  by_cases hie : i = e
  · exact Or.inr hie
  · by_cases hir : i = ring.rightNeighbor e
    · left
      subst i
      rw [hright] at hi
      exact hi
    · left
      simpa [PopulationProtocol.step, protocol, hie, hir] using hi


private theorem step_nonbarrier_frame
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (C : Fin n → State k) (e : Fin n)
    (hnb : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    let D := (protocol k hk).step ring C e
    (D e).leader = (C e).leader ∧
      (∀ i : Fin n, (D i).leader = true → (C i).leader = true) := by
  dsimp only
  have hre := rightNeighbor_ne_self ring hn2 e
  have hleftLocal :=
    transition_nonbarrier_left_leader hk
      (C e) (C (ring.rightNeighbor e)) hnb
  have hrightLocal :=
    transition_nonbarrier_right_no_birth hk
      (C e) (C (ring.rightNeighbor e)) hnb
  have hleft :
      (((protocol k hk).step ring C e) e).leader = (C e).leader := by
    simpa [PopulationProtocol.step, protocol] using hleftLocal
  refine ⟨hleft, ?_⟩
  intro i hi
  by_cases hie : i = e
  · subst i
    rw [hleft] at hi
    exact hi
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      apply hrightLocal
      simpa [PopulationProtocol.step, protocol, hre] using hi
    · simpa [PopulationProtocol.step, protocol, hie, hir] using hi


theorem pushWord_leader_frame
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b) :
    let h := ring.rightNeighbor b
    let s := ring.rightNeighbor h
    let D := rawRun hk ring C (pushWord hk ring C b)
    (D h).leader = (C h).leader ∧
      (∀ i : Fin n, (D i).leader = true →
        (C i).leader = true ∨ i = b) ∧
      (∀ i : Fin n, i ≠ b → i ≠ h → i ≠ s → D i = C i) := by
  classical
  dsimp only
  let h := ring.rightNeighbor b
  let s := ring.rightNeighbor h
  change
    (rawRun hk ring C (pushWord hk ring C b) h).leader =
        (C h).leader ∧
      (∀ i : Fin n,
        (rawRun hk ring C (pushWord hk ring C b) i).leader = true →
          (C i).leader = true ∨ i = b) ∧
      (∀ i : Fin n, i ≠ b → i ≠ h → i ≠ s →
        rawRun hk ring C (pushWord hk ring C b) i = C i)


  have hn2 : 1 < n := by omega
  have hhb : h ≠ b := by
    simpa [h] using rightNeighbor_ne_self ring hn2 b
  have hbar0 : IsBarrier hk (C b) (C h) := by
    have hb0 : BarrierAt hk ring (labelsOf C) b := (hB b).2 rfl
    simpa [h] using (barrierAt_labelsOf_iff hk ring C b).1 hb0


  by_cases hr : AdvanceReady hk ring C b
  · let C1 := (protocol k hk).step ring C b
    have hf1 := step_barrier_frame hk ring hn2 C b hbar0
    have hh : (C1 h).leader = (C h).leader := by
      simpa [C1, h] using hf1.1
    have hbirth :
        ∀ i : Fin n, (C1 i).leader = true →
          (C i).leader = true ∨ i = b := by
      simpa [C1] using hf1.2
    have hstate :
        ∀ i : Fin n, i ≠ b → i ≠ h → i ≠ s → C1 i = C i := by
      intro i hib hih _his
      apply step_other_state hk ring C b i hib
      simpa [h] using hih
    have hout :=
      And.intro hh (And.intro hbirth hstate)
    have hw : OriginalPushOne.pushWord hk ring C b = [b] := by
      simp [OriginalPushOne.pushWord, hr]
    rw [hw]
    exact hout


  · let C1 := (protocol k hk).step ring C b
    have hf1 := step_barrier_frame hk ring hn2 C b hbar0
    have hB1 : OneBarrierAt hk ring C1 b := by
      simpa [C1, hr] using
        oneBarrierAt_step hk ring hn2 C b b hnd hB


    have hnb1 :
        ¬ IsBarrier hk (C1 h) (C1 (ring.rightNeighbor h)) := by
      intro hbar
      have hbh : BarrierAt hk ring (labelsOf C1) h :=
        (barrierAt_labelsOf_iff hk ring C1 h).2 hbar
      exact hhb ((hB1 h).1 hbh)


    let C2 := (protocol k hk).step ring C1 h
    have hf2 := step_nonbarrier_frame hk ring hn2 C1 h hnb1
    have hnot1 : ¬ AdvanceReady hk ring C1 h :=
      not_advanceReady_of_nonbarrier hk ring C1 h hnb1
    have hB2 : OneBarrierAt hk ring C2 b := by
      simpa [C2, hnot1] using
        oneBarrierAt_step hk ring hn2 C1 b h hnd hB1


    have hnb2 :
        ¬ IsBarrier hk (C2 h) (C2 (ring.rightNeighbor h)) := by
      intro hbar
      have hbh : BarrierAt hk ring (labelsOf C2) h :=
        (barrierAt_labelsOf_iff hk ring C2 h).2 hbar
      exact hhb ((hB2 h).1 hbh)


    let C3 := (protocol k hk).step ring C2 h
    have hf3 := step_nonbarrier_frame hk ring hn2 C2 h hnb2
    have hnot2 : ¬ AdvanceReady hk ring C2 h :=
      not_advanceReady_of_nonbarrier hk ring C2 h hnb2
    have hB3 : OneBarrierAt hk ring C3 b := by
      simpa [C3, hnot2] using
        oneBarrierAt_step hk ring hn2 C2 b h hnd hB2


    have hbar3 : IsBarrier hk (C3 b) (C3 h) := by
      have hb3 : BarrierAt hk ring (labelsOf C3) b := (hB3 b).2 rfl
      simpa [h] using (barrierAt_labelsOf_iff hk ring C3 b).1 hb3


    let C4 := (protocol k hk).step ring C3 b
    have hf4 := step_barrier_frame hk ring hn2 C3 b hbar3


    have hh1 : (C1 h).leader = (C h).leader := by
      simpa [C1, h] using hf1.1
    have hh2 : (C2 h).leader = (C1 h).leader := by
      simpa [C2] using hf2.1
    have hh3 : (C3 h).leader = (C2 h).leader := by
      simpa [C3] using hf3.1
    have hh4 : (C4 h).leader = (C3 h).leader := by
      simpa [C4, h] using hf4.1
    have hh : (C4 h).leader = (C h).leader :=
      hh4.trans (hh3.trans (hh2.trans hh1))


    have hbirth1 :
        ∀ i : Fin n, (C1 i).leader = true →
          (C i).leader = true ∨ i = b := by
      simpa [C1] using hf1.2
    have hbirth2 :
        ∀ i : Fin n, (C2 i).leader = true →
          (C1 i).leader = true := by
      simpa [C2] using hf2.2
    have hbirth3 :
        ∀ i : Fin n, (C3 i).leader = true →
          (C2 i).leader = true := by
      simpa [C3] using hf3.2
    have hbirth4 :
        ∀ i : Fin n, (C4 i).leader = true →
          (C3 i).leader = true ∨ i = b := by
      simpa [C4] using hf4.2
    have hbirth :
        ∀ i : Fin n, (C4 i).leader = true →
          (C i).leader = true ∨ i = b := by
      intro i hi
      rcases hbirth4 i hi with hi3 | hib
      · exact hbirth1 i (hbirth2 i (hbirth3 i hi3))
      · exact Or.inr hib


    have hstate :
        ∀ i : Fin n, i ≠ b → i ≠ h → i ≠ s → C4 i = C i := by
      intro i hib hih his
      have hirB : i ≠ ring.rightNeighbor b := by
        simpa [h] using hih
      have hirH : i ≠ ring.rightNeighbor h := by
        simpa [s] using his
      have h1 : C1 i = C i :=
        step_other_state hk ring C b i hib hirB
      have h2 : C2 i = C1 i :=
        step_other_state hk ring C1 h i hih hirH
      have h3 : C3 i = C2 i :=
        step_other_state hk ring C2 h i hih hirH
      have h4 : C4 i = C3 i :=
        step_other_state hk ring C3 b i hib hirB
      exact h4.trans (h3.trans (h2.trans h1))


    have hout :=
      And.intro hh (And.intro hbirth hstate)
    have hw : OriginalPushOne.pushWord hk ring C b = [b, h, h, b] := by
      simp [OriginalPushOne.pushWord, hr, h]
    rw [hw]
    exact hout


#print axioms pushWord_leader_frame


end AAFJPK.OriginalOneBarrierPushLeaders
