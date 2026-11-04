import Leader.AAFJ.OneBarrier.Sanitation
import Leader.AAFJ.MultiBarrier.PushOne

set_option autoImplicit false

namespace AAFJPK.OriginalUniqueLeaderCleanup

open BarrierAlgebra
open OriginalNonbarrierWord
open SingleBarrierSanitation

def UniqueLeaderAt {n k : Nat}
    (C : Fin n → State k) (l : Fin n) : Prop :=
  (C l).leader = true ∧
    ∀ i : Fin n, (C i).leader = true → i = l

instance instDecidableUniqueLeaderAt
    {n k : Nat} (C : Fin n → State k) (l : Fin n) :
    Decidable (UniqueLeaderAt C l) := by
  unfold UniqueLeaderAt
  infer_instance

/-- Positive while the named unique-leader branch survives; zero otherwise. -/
def terminalRank {n k : Nat}
    (ring : DirectedRing n) (b l : Fin n)
    (C : Fin n → State k) : Nat :=
  if UniqueLeaderAt C l then
    cwDist ring (ring.rightNeighbor b) l + 1
  else
    0

private theorem nonBarrierStep_twice_left_probe_false_local
    {k : Nat} (u v : State k) :
    let p := nonBarrierStep u v
    (nonBarrierStep p.1 p.2).1.probe = false := by
  cases hl : v.leader <;> cases hb : v.bullet <;>
    cases hp : u.probe <;>
    simp [nonBarrierStep, hl, hb, hp]

private theorem transition_nonbarrier_twice_left_probe_false_local
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnon : ¬ IsBarrier hk u v) :
    let p := transition hk u v
    (transition hk p.1 p.2).1.probe = false := by
  let p := transition hk u v
  change (transition hk p.1 p.2).1.probe = false
  have hnot : ¬ PairAdvanceReady hk u v := by
    intro h
    exact hnon h.1
  have hlab :
      p.1.label = u.label ∧ p.2.label = v.label := by
    dsimp [p]
    exact transition_labels_of_not_pairAdvanceReady hk u v hnot
  have hnon2 : ¬ IsBarrier hk p.1 p.2 := by
    intro h
    apply hnon
    unfold IsBarrier at h ⊢
    rw [hlab.1, hlab.2] at h
    exact h
  have hp : p = nonBarrierStep u v := by
    dsimp [p]
    exact transition_of_nonbarrier hk u v hnon
  rw [transition_of_nonbarrier hk p.1 p.2 hnon2, hp]
  simpa using nonBarrierStep_twice_left_probe_false_local u v

private theorem fresh_head_after_ready
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (C : Fin n → State k) (e : Fin n)
    (hr : AdvanceReady hk ring C e) :
    let D := (protocol k hk).step ring C e
    (D (ring.rightNeighbor e)).bullet = false ∧
      (D (ring.rightNeighbor e)).probe = false := by
  rcases hr with ⟨hbar, hphase, hprobe⟩
  have hne := rightNeighbor_ne_self ring hn2 e
  simp only [PopulationProtocol.step, protocol, if_neg hne, if_pos rfl]
  rw [transition_of_barrier hk _ _ hbar]
  rw [barrierStep_phase_one_probe_free hk _ _ hphase hprobe]
  simp [hprobe]

private theorem push_one_barrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b) :
    ∃ w : List (Fin n),
      w.length ≤ 4 ∧
      OneBarrierAt hk ring (rawRun hk ring C w)
        (ring.rightNeighbor b) ∧
      (rawRun hk ring C w (ring.rightNeighbor b)).bullet = false ∧
      (rawRun hk ring C w (ring.rightNeighbor b)).probe = false := by
  have hn2 : 1 < n := by omega
  let s := ring.rightNeighbor b
  by_cases hr : AdvanceReady hk ring C b
  · refine ⟨[b], by simp, ?_, ?_, ?_⟩
    · simpa [rawRun, hr] using
        oneBarrierAt_step hk ring hn2 C b b hnd hB
    · simpa [rawRun] using
        (fresh_head_after_ready hk ring hn2 C b hr).1
    · simpa [rawRun] using
        (fresh_head_after_ready hk ring hn2 C b hr).2
  · let C1 := (protocol k hk).step ring C b
    have hb : BarrierAt hk ring (labelsOf C) b :=
      (hB b).2 rfl
    have hctl :=
      OriginalPushOne.barrier_hit_source_controls_public
        hk ring C b hb
    have hB1 : OneBarrierAt hk ring C1 b := by
      simpa [C1, hr] using
        oneBarrierAt_step hk ring hn2 C b b hnd hB
    have hsb : s ≠ b := by
      simpa [s] using rightNeighbor_ne_self ring hn2 b
    have hnb1 :
        ¬ IsBarrier hk (C1 s) (C1 (ring.rightNeighbor s)) := by
      intro h
      exact hsb
        ((hB1 s).1 ((barrierAt_labelsOf_iff hk ring C1 s).2 h))

    let C2 := (protocol k hk).step ring C1 s
    have hnot1 : ¬ AdvanceReady hk ring C1 s :=
      not_advanceReady_of_nonbarrier hk ring C1 s hnb1
    have hB2 : OneBarrierAt hk ring C2 b := by
      simpa [C2, hnot1] using
        oneBarrierAt_step hk ring hn2 C1 b s hnd hB1
    have hnb2 :
        ¬ IsBarrier hk (C2 s) (C2 (ring.rightNeighbor s)) := by
      intro h
      exact hsb
        ((hB2 s).1 ((barrierAt_labelsOf_iff hk ring C2 s).2 h))

    let C3 := (protocol k hk).step ring C2 s
    have hnot2 : ¬ AdvanceReady hk ring C2 s :=
      not_advanceReady_of_nonbarrier hk ring C2 s hnb2
    have hB3 : OneBarrierAt hk ring C3 b := by
      simpa [C3, hnot2] using
        oneBarrierAt_step hk ring hn2 C2 b s hnd hB2

    have hword : CurrentNonbarrierWord hk ring C1 [s, s] := by
      refine ⟨hnb1, ?_⟩
      refine ⟨?_, trivial⟩
      simpa [C2] using hnb2

    have hphase3 : (C3 b).phase = true := by
      have hp := rawRun_phases_eq hk ring hword b
      have hp' : (C3 b).phase = (C1 b).phase := by
        simpa [C2, C3, rawRun] using hp
      exact hp'.trans (by simpa [C1] using hctl.2)

    have hprobe3 : (C3 s).probe = false := by
      have hre := rightNeighbor_ne_self ring hn2 s
      have hlocal :=
        transition_nonbarrier_twice_left_probe_false_local
          hk (C1 s) (C1 (ring.rightNeighbor s)) hnb1
      simpa [C2, C3, PopulationProtocol.step, protocol,
        hre, Ne.symm hre] using hlocal

    have hr3 : AdvanceReady hk ring C3 b := by
      refine ⟨
        (barrierAt_labelsOf_iff hk ring C3 b).1 ((hB3 b).2 rfl),
        hphase3,
        ?_⟩
      simpa [s] using hprobe3

    let C4 := (protocol k hk).step ring C3 b
    have hB4 : OneBarrierAt hk ring C4 s := by
      simpa [C4, s, hr3] using
        oneBarrierAt_step hk ring hn2 C3 b b hnd hB3
    have hfresh := fresh_head_after_ready hk ring hn2 C3 b hr3

    refine ⟨[b, s, s, b], by simp, ?_, ?_, ?_⟩
    · simpa [rawRun, C1, C2, C3, C4, s] using hB4
    · simpa [rawRun, C1, C2, C3, C4, s] using hfresh.1
    · simpa [rawRun, C1, C2, C3, C4, s] using hfresh.2

private theorem cleanAt_self_of_unique_fresh
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (l : Fin n)
    (hB : OneBarrierAt hk ring C l)
    (hu : UniqueLeaderAt C l)
    (hf : (C l).bullet = false ∧ (C l).probe = false) :
    CleanAt hk ring C l l := by
  refine ⟨hB, ?_⟩
  have hc : cutCoord ring l l = tailCoord ring := by
    apply cutPos_injective ring l
    rw [cutPos_cutCoord, cutPos_tailCoord]
  rw [hc]
  refine ⟨?_, ?_, ?_⟩
  · simpa [cutView] using hu.1
  · intro i hi
    apply cutPos_injective ring l
    rw [cutPos_tailCoord]
    exact hu.2 _ (by simpa [cutView] using hi)
  · intro i hm
    by_cases hit : i = tailCoord ring
    · subst i
      rcases hm with hb | hp
      · have hb' : (C l).bullet = true := by
          simpa [cutView] using hb
        exact False.elim (Bool.noConfusion (hf.1.symm.trans hb'))
      · have hp' : (C l).probe = true := by
          simpa [cutView] using hp
        exact False.elim (Bool.noConfusion (hf.2.symm.trans hp'))
    · change i.val < n - 1
      have hil := i.isLt
      have hine : i.val ≠ n - 1 := by
        intro hval
        apply hit
        apply Fin.ext
        simpa [tailCoord] using hval
      omega

private theorem cwDist_next_left
    {n : Nat} (ring : DirectedRing n) {a z : Fin n}
    (hne : a ≠ z) :
    cwDist ring (ring.rightNeighbor a) z + 1 =
      cwDist ring a z := by
  let d := cwDist ring a z
  have hdlt : d < n := by
    simpa [d] using cwDist_lt ring a z
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd0
    have hz : cwDist ring a z = 0 := by
      simpa [d] using hd0
    have hp := cwPos_cwDist ring a z
    rw [hz, cwPos_zero] at hp
    exact hne hp
  have hpos : cwPos ring a d = z := by
    simpa [d] using cwPos_cwDist ring a z
  have hshift :
      cwPos ring (ring.rightNeighbor a) (d - 1) = z := by
    rw [cwPos_rightNeighbor]
    have heq : d - 1 + 1 = d := by omega
    simpa [heq] using hpos
  have hu :=
    cwPos_bounded_unique ring (ring.rightNeighbor a) z
      (d - 1) (by omega) hshift
  dsimp [d] at hu ⊢
  omega

/-- Public exact-word form of the existing private one-barrier push.
The selected word is the already-public OriginalPushOne.pushWord. -/
theorem pushWord_oneBarrier_fresh
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b) :
    let w := OriginalPushOne.pushWord hk ring C b
    let D := rawRun hk ring C w
    w.length ≤ 4 ∧
      OneBarrierAt hk ring D (ring.rightNeighbor b) ∧
      (D (ring.rightNeighbor b)).bullet = false ∧
      (D (ring.rightNeighbor b)).probe = false := by
  classical
  dsimp only
  have hn2 : 1 < n := by omega
  let s := ring.rightNeighbor b
  by_cases hr : AdvanceReady hk ring C b
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [OriginalPushOne.pushWord, hr]
    · simpa [OriginalPushOne.pushWord, hr, rawRun] using
        oneBarrierAt_step hk ring hn2 C b b hnd hB
    · simpa [OriginalPushOne.pushWord, hr, rawRun] using
        (fresh_head_after_ready hk ring hn2 C b hr).1
    · simpa [OriginalPushOne.pushWord, hr, rawRun] using
        (fresh_head_after_ready hk ring hn2 C b hr).2
  · let C1 := (protocol k hk).step ring C b
    have hb : BarrierAt hk ring (labelsOf C) b :=
      (hB b).2 rfl
    have hctl :=
      OriginalPushOne.barrier_hit_source_controls_public
        hk ring C b hb
    have hB1 : OneBarrierAt hk ring C1 b := by
      simpa [C1, hr] using
        oneBarrierAt_step hk ring hn2 C b b hnd hB
    have hsb : s ≠ b := by
      simpa [s] using rightNeighbor_ne_self ring hn2 b
    have hnb1 :
        ¬ IsBarrier hk (C1 s) (C1 (ring.rightNeighbor s)) := by
      intro h
      exact hsb
        ((hB1 s).1 ((barrierAt_labelsOf_iff hk ring C1 s).2 h))

    let C2 := (protocol k hk).step ring C1 s
    have hnot1 : ¬ AdvanceReady hk ring C1 s :=
      not_advanceReady_of_nonbarrier hk ring C1 s hnb1
    have hB2 : OneBarrierAt hk ring C2 b := by
      simpa [C2, hnot1] using
        oneBarrierAt_step hk ring hn2 C1 b s hnd hB1
    have hnb2 :
        ¬ IsBarrier hk (C2 s) (C2 (ring.rightNeighbor s)) := by
      intro h
      exact hsb
        ((hB2 s).1 ((barrierAt_labelsOf_iff hk ring C2 s).2 h))

    let C3 := (protocol k hk).step ring C2 s
    have hnot2 : ¬ AdvanceReady hk ring C2 s :=
      not_advanceReady_of_nonbarrier hk ring C2 s hnb2
    have hB3 : OneBarrierAt hk ring C3 b := by
      simpa [C3, hnot2] using
        oneBarrierAt_step hk ring hn2 C2 b s hnd hB2

    have hword : CurrentNonbarrierWord hk ring C1 [s, s] := by
      refine ⟨hnb1, ?_⟩
      refine ⟨?_, trivial⟩
      simpa [C2] using hnb2

    have hphase3 : (C3 b).phase = true := by
      have hp := rawRun_phases_eq hk ring hword b
      have hp' : (C3 b).phase = (C1 b).phase := by
        simpa [C2, C3, rawRun] using hp
      exact hp'.trans (by simpa [C1] using hctl.2)

    have hprobe3 : (C3 s).probe = false := by
      have hre := rightNeighbor_ne_self ring hn2 s
      have hlocal :=
        transition_nonbarrier_twice_left_probe_false_local
          hk (C1 s) (C1 (ring.rightNeighbor s)) hnb1
      simpa [C2, C3, PopulationProtocol.step, protocol,
        hre, Ne.symm hre] using hlocal

    have hr3 : AdvanceReady hk ring C3 b := by
      refine ⟨
        (barrierAt_labelsOf_iff hk ring C3 b).1 ((hB3 b).2 rfl),
        hphase3,
        ?_⟩
      simpa [s] using hprobe3

    let C4 := (protocol k hk).step ring C3 b
    have hB4 : OneBarrierAt hk ring C4 s := by
      simpa [C4, s, hr3] using
        oneBarrierAt_step hk ring hn2 C3 b b hnd hB3
    have hfresh :=
      fresh_head_after_ready hk ring hn2 C3 b hr3

    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [OriginalPushOne.pushWord, hr]
    · simpa [OriginalPushOne.pushWord, hr, rawRun,
        C1, C2, C3, C4, s] using hB4
    · simpa [OriginalPushOne.pushWord, hr, rawRun,
        C1, C2, C3, C4, s] using hfresh.1
    · simpa [OriginalPushOne.pushWord, hr, rawRun,
        C1, C2, C3, C4, s] using hfresh.2

#print axioms pushWord_oneBarrier_fresh

theorem uniqueLeader_progress
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b l : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hu : UniqueLeaderAt C l) :
    ∃ w : List (Fin n),
      w.length ≤ 4 ∧
      let D := rawRun hk ring C w
      OneBarrierAt hk ring D (ring.rightNeighbor b) ∧
        (CleanAt hk ring D (ring.rightNeighbor b) l ∨
          terminalRank ring (ring.rightNeighbor b) l D <
            terminalRank ring b l C) := by
  obtain ⟨w, hw, hBD, hbul, hpr⟩ :=
    push_one_barrier hk ring hn3 hnd C b hB
  refine ⟨w, hw, ?_⟩
  let D := rawRun hk ring C w
  change
    OneBarrierAt hk ring D (ring.rightNeighbor b) ∧
      (CleanAt hk ring D (ring.rightNeighbor b) l ∨
        terminalRank ring (ring.rightNeighbor b) l D <
          terminalRank ring b l C)
  refine ⟨by simpa [D] using hBD, ?_⟩

  by_cases huD : UniqueLeaderAt D l
  · by_cases htail : ring.rightNeighbor b = l
    · left
      have hBself : OneBarrierAt hk ring D l := by
        simpa [D, htail] using hBD
      have hfself :
          (D l).bullet = false ∧ (D l).probe = false := by
        constructor
        · simpa [D, htail] using hbul
        · simpa [D, htail] using hpr
      simpa [htail] using
        cleanAt_self_of_unique_fresh hk ring D l hBself huD hfself
    · right
      have hd := cwDist_next_left ring htail
      have hnew :
          terminalRank ring (ring.rightNeighbor b) l D =
            cwDist ring
              (ring.rightNeighbor (ring.rightNeighbor b)) l + 1 := by
        simp [terminalRank, huD]
      have hold :
          terminalRank ring b l C =
            cwDist ring (ring.rightNeighbor b) l + 1 := by
        simp [terminalRank, hu]
      rw [hnew, hold]
      omega
  · right
    have hzero :
        terminalRank ring (ring.rightNeighbor b) l D = 0 := by
      simp [terminalRank, huD]
    rw [hzero]
    simp [terminalRank, hu]

#check uniqueLeader_progress
#print axioms uniqueLeader_progress

end AAFJPK.OriginalUniqueLeaderCleanup
