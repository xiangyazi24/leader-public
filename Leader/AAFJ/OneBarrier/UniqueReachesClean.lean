import Leader.AAFJ.OneBarrier.Sweep
import Leader.AAFJ.OneBarrier.PushLeaders
import Leader.AAFJ.OneBarrier.Leaderless
import Leader.AAFJ.OneBarrier.Reduce
import Leader.AAFJ.OneBarrier.HeadPair

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.OriginalOneBarrierUnique

open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord
open OriginalUniqueLeaderCleanup
open OriginalOneBarrierSweep
open OriginalOneBarrierHeadPair

private theorem cutCoord_self_eq_tailCoord {n : Nat}
    (ring : DirectedRing n) (b : Fin n) :
    cutCoord ring b b = tailCoord ring := by
  apply cutPos_injective ring b
  rw [cutPos_cutCoord, cutPos_tailCoord]

private theorem cutCoord_self_val {n : Nat}
    (ring : DirectedRing n) (b : Fin n) :
    (cutCoord ring b b).val = n - 1 := by
  rw [cutCoord_self_eq_tailCoord]
  rfl

private theorem cutCoord_head_val {n : Nat}
    (ring : DirectedRing n) (b : Fin n) :
    (cutCoord ring b (ring.rightNeighbor b)).val = 0 := by
  have h := cutCoord_cutPos ring b (⟨0, ring.hn⟩ : Fin n)
  rw [cutPos_zero] at h
  exact congrArg Fin.val h

private theorem site_eq_head_of_coord_zero {n : Nat}
    (ring : DirectedRing n) (b i : Fin n)
    (h : (cutCoord ring b i).val = 0) :
    i = ring.rightNeighbor b := by
  have hc :
      cutCoord ring b i = (⟨0, ring.hn⟩ : Fin n) := by
    apply Fin.ext
    exact h
  calc
    i = cutPos ring b (cutCoord ring b i) :=
      (cutPos_cutCoord ring b i).symm
    _ = cutPos ring b (⟨0, ring.hn⟩ : Fin n) := by rw [hc]
    _ = ring.rightNeighbor b := cutPos_zero ring b

private theorem site_eq_tail_of_coord_last {n : Nat}
    (ring : DirectedRing n) (b i : Fin n)
    (h : (cutCoord ring b i).val = n - 1) :
    i = b := by
  have hc :
      cutCoord ring b i = tailCoord ring := by
    apply Fin.ext
    simpa [tailCoord] using h
  calc
    i = cutPos ring b (cutCoord ring b i) :=
      (cutPos_cutCoord ring b i).symm
    _ = cutPos ring b (tailCoord ring) := by rw [hc]
    _ = b := cutPos_tailCoord ring b

private theorem site_eq_of_cutCoord_val_eq {n : Nat}
    (ring : DirectedRing n) (b i j : Fin n)
    (h : (cutCoord ring b i).val = (cutCoord ring b j).val) :
    i = j := by
  have hc : cutCoord ring b i = cutCoord ring b j := by
    apply Fin.ext
    exact h
  have hp := congrArg (cutPos ring b) hc
  simpa using hp

private theorem cutCoord_after_advance_val_of_pos {n : Nat}
    (ring : DirectedRing n) (b i : Fin n)
    (hpos : 0 < (cutCoord ring b i).val) :
    (cutCoord ring (ring.rightNeighbor b) i).val =
      (cutCoord ring b i).val - 1 := by
  rw [cutCoord_nextBarrier]
  exact leftNeighbor_val_of_pos ring (cutCoord ring b i) hpos

private theorem old_tail_after_advance_val {n : Nat}
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (b : Fin n) :
    (cutCoord ring (ring.rightNeighbor b) b).val = n - 2 := by
  rw [cutCoord_nextBarrier, cutCoord_self_eq_tailCoord]
  have hpos : 0 < (tailCoord ring).val := by
    change 0 < n - 1
    omega
  have hleft := leftNeighbor_val_of_pos ring (tailCoord ring) hpos
  rw [hleft]
  change n - 1 - 1 = n - 2
  omega

private theorem follower_leader_false_of_unique
    {n k : Nat} {C : Fin n → State k} {l i : Fin n}
    (hu : UniqueLeaderAt C l) (hi : i ≠ l) :
    (C i).leader = false := by
  cases hbit : (C i).leader with
  | false => rfl
  | true =>
      exact False.elim (hi (hu.2 i hbit))

private theorem uniqueLeaderAt_of_leaders_eq
    {n k : Nat} {C D : Fin n → State k} {l : Fin n}
    (hu : UniqueLeaderAt C l)
    (h : ∀ i : Fin n, (D i).leader = (C i).leader) :
    UniqueLeaderAt D l := by
  refine ⟨?_, ?_⟩
  · rw [h l]
    exact hu.1
  · intro i hi
    apply hu.2 i
    rw [← h i]
    exact hi

private theorem cleanAt_of_unique_upper_clear
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b l : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hu : UniqueLeaderAt C l)
    (hfree : ∀ i : Fin n,
      (cutCoord ring b l).val ≤ (cutCoord ring b i).val →
        (C i).bullet = false ∧ (C i).probe = false) :
    CleanAt hk ring C b l := by
  refine ⟨hB, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [cutView] using hu.1
  · intro j hj
    have hphys :
        (C (cutPos ring b j)).leader = true := by
      simpa [cutView] using hj
    have heq : cutPos ring b j = l := hu.2 _ hphys
    have hc := congrArg (cutCoord ring b) heq
    simpa using hc
  · intro j hm
    refine Classical.byContradiction (fun hnot => ?_)
    have hge :
        (cutCoord ring b l).val ≤ j.val := by
      omega
    have hf := hfree (cutPos ring b j) (by
      simpa using hge)
    rcases hm with hb | hp
    · have hb' :
          (C (cutPos ring b j)).bullet = true := by
        simpa [cutView] using hb
      exact Bool.noConfusion (hf.1.symm.trans hb')
    · have hp' :
          (C (cutPos ring b j)).probe = true := by
        simpa [cutView] using hp
      exact Bool.noConfusion (hf.2.symm.trans hp')

private theorem clean_of_cleanAt
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b l : Fin n)
    (h : CleanAt hk ring C b l) :
    Clean hk ring C := by
  exact ⟨l, b, h⟩

private theorem bullet_sweep_leaderless
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b l q : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hu : UniqueLeaderAt C l)
    (hlow : 1 ≤ (cutCoord ring b l).val)
    (hqge :
      (cutCoord ring b l).val ≤ (cutCoord ring b q).val)
    (hq : (C q).bullet = true) :
    ∃ w : List (Fin n),
      ∀ i : Fin n, (rawRun hk ring C w i).leader = false := by
  let m := (cutCoord ring b q).val
  have hm : m < n := (cutCoord ring b q).isLt
  have hqpos :
      q = cutPos ring b (⟨m, hm⟩ : Fin n) := by
    rw [← cutPos_cutCoord ring b q]
  have hbul :
      (C (cutPos ring b (⟨m, hm⟩ : Fin n))).bullet = true := by
    rw [← hqpos]
    exact hq
  let D := rawRun hk ring C (sweepWord ring b m)
  have hs := sweep_spec hk ring hn3 C b hB m hm hbul
  dsimp only at hs
  change
    CurrentNonbarrierWord hk ring C (sweepWord ring b m) ∧
      OneBarrierAt hk ring D b ∧
      (∀ i : Fin n,
        1 ≤ (cutCoord ring b i).val →
        (cutCoord ring b i).val ≤ m →
        (D i).leader = false) ∧
      (∀ i : Fin n,
        ((cutCoord ring b i).val = 0 ∨
          m < (cutCoord ring b i).val) →
        (D i).leader = (C i).leader) ∧
      (∀ i : Fin n,
        m < (cutCoord ring b i).val →
        D i = C i) ∧
      (D (ring.rightNeighbor b)).bullet = true at hs
  rcases hs with ⟨_, _, hclear, _, _, _⟩
  have hmono :=
    sweep_leaderCount_le hk ring hn3 C b hB m hm hbul
  dsimp only at hmono
  change leaderCount D ≤ leaderCount C ∧
    (∀ i : Fin n, (D i).leader = true → (C i).leader = true) at hmono
  refine ⟨sweepWord ring b m, ?_⟩
  intro i
  cases hi : (D i).leader with
  | false => rfl
  | true =>
      have hCi : (C i).leader = true := hmono.2 i hi
      have hil : i = l := hu.2 i hCi
      subst i
      have hkilled :
          (D l).leader = false :=
        hclear l hlow (by
          change (cutCoord ring b l).val ≤ m
          exact hqge)
      exact False.elim
        (Bool.noConfusion (hkilled.symm.trans hi))

private theorem incoming_sanitizes_tail_probe_unique
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b l : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hu : UniqueLeaderAt C l)
    (hlb : l ≠ b)
    (hprobe : (C b).probe = true) :
    let a := ring.leftNeighbor b
    let D := (protocol k hk).step ring C a
    OneBarrierAt hk ring D b ∧
      UniqueLeaderAt D l ∧
      (D b).bullet = false ∧
      (D b).probe = true := by
  let a := ring.leftNeighbor b
  let D := (protocol k hk).step ring C a
  have har : ring.rightNeighbor a = b := by
    simpa [a] using rightNeighbor_leftNeighbor_clean ring b
  have hab : a ≠ b := by
    intro h
    have hs : ring.rightNeighbor b = b := by
      have h' := har
      rw [h] at h'
      exact h'
    exact (rightNeighbor_ne_self ring hn2 b) hs
  have hnb :
      ¬ IsBarrier hk (C a) (C (ring.rightNeighbor a)) := by
    intro hbarr
    have hp : BarrierAt hk ring (labelsOf C) a :=
      (barrierAt_labelsOf_iff hk ring C a).2 hbarr
    exact hab ((hB a).1 hp)
  have hnot : ¬ AdvanceReady hk ring C a :=
    not_advanceReady_of_nonbarrier hk ring C a hnb
  have hCbLeader : (C b).leader = false :=
    follower_leader_false_of_unique hu (Ne.symm hlb)
  have hrespLeader :
      (C (ring.rightNeighbor a)).leader = false := by
    rw [har]
    exact hCbLeader
  have hrespProbe :
      (C (ring.rightNeighbor a)).probe = true := by
    rw [har]
    exact hprobe
  have hlocal :
      (transition hk (C a) (C (ring.rightNeighbor a))).1.leader =
          (C a).leader ∧
      (transition hk (C a) (C (ring.rightNeighbor a))).2.leader =
          (C (ring.rightNeighbor a)).leader ∧
      (transition hk (C a) (C (ring.rightNeighbor a))).2.bullet = false ∧
      (transition hk (C a) (C (ring.rightNeighbor a))).2.probe = true := by
    rw [transition_of_nonbarrier hk _ _ hnb]
    cases hb : (C (ring.rightNeighbor a)).bullet <;>
      cases hp : (C a).probe <;>
      simp [nonBarrierStep, hrespLeader, hrespProbe, hb, hp]
  have hleaders :
      ∀ i : Fin n, (D i).leader = (C i).leader := by
    intro i
    simpa [D] using
      step_leaders_eq_of_local hk ring hn2 C a hlocal.1 hlocal.2.1 i
  have hBD : OneBarrierAt hk ring D b := by
    simpa [D, hnot] using
      oneBarrierAt_step hk ring hn2 C b a hnd hB
  have huD : UniqueLeaderAt D l :=
    uniqueLeaderAt_of_leaders_eq hu hleaders
  have hne := rightNeighbor_ne_self ring hn2 a
  have hDbBullet : (D b).bullet = false := by
    have hx :
        (D (ring.rightNeighbor a)).bullet = false := by
      simpa [D, PopulationProtocol.step, protocol, hne] using
        hlocal.2.2.1
    simpa [har] using hx
  have hDbProbe : (D b).probe = true := by
    have hx :
        (D (ring.rightNeighbor a)).probe = true := by
      simpa [D, PopulationProtocol.step, protocol, hne] using
        hlocal.2.2.2
    simpa [har] using hx
  exact ⟨hBD, huD, hDbBullet, hDbProbe⟩

private theorem barrier_tail_probe_frame
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b l : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hu : UniqueLeaderAt C l)
    (hlb : l ≠ b)
    (hlh : l ≠ ring.rightNeighbor b)
    (hprobe : (C b).probe = true)
    (hbullet : (C b).bullet = false) :
    let h := ring.rightNeighbor b
    let D := (protocol k hk).step ring C b
    OneBarrierAt hk ring D
        (if AdvanceReady hk ring C b then h else b) ∧
      (D b).leader = true ∧
      (D b).bullet = false ∧
      (D b).probe = false ∧
      (D l).leader = true ∧
      (∀ i : Fin n, (D i).leader = true → i = l ∨ i = b) ∧
      (AdvanceReady hk ring C b →
        (D h).bullet = false ∧ (D h).probe = false) := by
  let h := ring.rightNeighbor b
  let D := (protocol k hk).step ring C b
  have hne : h ≠ b := by
    simpa [h] using rightNeighbor_ne_self ring hn2 b
  have hbar : IsBarrier hk (C b) (C h) := by
    have hb : BarrierAt hk ring (labelsOf C) b := (hB b).2 rfl
    simpa [h] using (barrierAt_labelsOf_iff hk ring C b).1 hb
  have hCbLeader : (C b).leader = false :=
    follower_leader_false_of_unique hu (Ne.symm hlb)
  have hChLeader : (C h).leader = false := by
    apply follower_leader_false_of_unique hu
    simpa [h] using Ne.symm hlh
  have hlocal :
      (transition hk (C b) (C h)).1.leader = true ∧
      (transition hk (C b) (C h)).1.bullet = false ∧
      (transition hk (C b) (C h)).1.probe = false ∧
      (transition hk (C b) (C h)).2.leader = false := by
    rw [transition_of_barrier hk _ _ hbar]
    cases hphase : (C b).phase <;>
      cases hheadProbe : (C h).probe <;>
      simp [barrierStep, probeHitsBarrier, hprobe, hbullet,
        hCbLeader, hChLeader, hphase, hheadProbe]
  have hDbLeader : (D b).leader = true := by
    simpa [D, PopulationProtocol.step, protocol] using hlocal.1
  have hDbBullet : (D b).bullet = false := by
    simpa [D, PopulationProtocol.step, protocol] using hlocal.2.1
  have hDbProbe : (D b).probe = false := by
    simpa [D, PopulationProtocol.step, protocol] using hlocal.2.2.1
  have hDhLeader : (D h).leader = false := by
    simpa [D, h, PopulationProtocol.step, protocol, hne] using
      hlocal.2.2.2
  have hDlLeader : (D l).leader = true := by
    simpa [D, PopulationProtocol.step, protocol, hlb, hlh] using hu.1
  have honly :
      ∀ i : Fin n, (D i).leader = true → i = l ∨ i = b := by
    intro i hi
    by_cases hib : i = b
    · exact Or.inr hib
    by_cases hih : i = h
    · subst i
      rw [hDhLeader] at hi
      contradiction
    · left
      apply hu.2 i
      simpa [D, h, PopulationProtocol.step, protocol, hib, hih] using hi
  have hBD :
      OneBarrierAt hk ring D
        (if AdvanceReady hk ring C b then h else b) := by
    simpa [D, h] using
      oneBarrierAt_step hk ring hn2 C b b hnd hB
  have hfresh :
      AdvanceReady hk ring C b →
        (D h).bullet = false ∧ (D h).probe = false := by
    intro hr
    rcases hr with ⟨_, hphase, hheadProbe⟩
    constructor
    · simp only [D, h, PopulationProtocol.step, protocol,
        if_neg hne, if_pos rfl]
      rw [transition_of_barrier hk _ _ hbar]
      rw [barrierStep_phase_one_probe_free hk _ _ hphase hheadProbe]
      simp
    · simp only [D, h, PopulationProtocol.step, protocol,
        if_neg hne, if_pos rfl]
      rw [transition_of_barrier hk _ _ hbar]
      rw [barrierStep_phase_one_probe_free hk _ _ hphase hheadProbe]
      simp [hheadProbe]
  exact ⟨hBD, hDbLeader, hDbBullet, hDbProbe,
    hDlLeader, honly, hfresh⟩

private theorem tail_unique_probe_reaches_clean
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hu : UniqueLeaderAt C b)
    (hprobe : (C b).probe = true)
    (hbullet : (C b).bullet = false) :
    Clean hk ring ((protocol k hk).step ring C b) := by
  let D := (protocol k hk).step ring C b
  have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).1 ((hB b).2 rfl)
  have hne := rightNeighbor_ne_self ring hn2 b
  have hheadLeader :
      (C (ring.rightNeighbor b)).leader = false :=
    follower_leader_false_of_unique hu hne
  have hlocal :
      (transition hk (C b) (C (ring.rightNeighbor b))).1.leader = true ∧
      (transition hk (C b) (C (ring.rightNeighbor b))).1.bullet = false ∧
      (transition hk (C b) (C (ring.rightNeighbor b))).1.probe = false ∧
      (transition hk (C b) (C (ring.rightNeighbor b))).2.leader = false := by
    rw [transition_of_barrier hk _ _ hbar]
    cases hphase : (C b).phase <;>
      cases hheadProbe : (C (ring.rightNeighbor b)).probe <;>
      simp [barrierStep, probeHitsBarrier, hprobe, hbullet,
        hphase, hheadProbe, hheadLeader]
  have hDbLeader : (D b).leader = true := by
    simpa [D, PopulationProtocol.step, protocol] using hlocal.1
  have hDbBullet : (D b).bullet = false := by
    simpa [D, PopulationProtocol.step, protocol] using hlocal.2.1
  have hDbProbe : (D b).probe = false := by
    simpa [D, PopulationProtocol.step, protocol] using hlocal.2.2.1
  have hDheadLeader :
      (D (ring.rightNeighbor b)).leader = false := by
    simpa [D, PopulationProtocol.step, protocol, hne] using
      hlocal.2.2.2
  have huD : UniqueLeaderAt D b := by
    refine ⟨hDbLeader, ?_⟩
    intro i hi
    by_cases hib : i = b
    · exact hib
    by_cases hih : i = ring.rightNeighbor b
    · subst i
      rw [hDheadLeader] at hi
      contradiction
    · have hCi : (C i).leader = true := by
        simpa [D, PopulationProtocol.step, protocol, hib, hih] using hi
      exact hu.2 i hCi
  have hdataOld :
      CleanData (cutView ring b D) (tailCoord ring) :=
    OriginalOneBarrierLeaderless.cleanData_tail_of_unique_fresh
      ring D b huD ⟨hDbBullet, hDbProbe⟩
  have hc : cutCoord ring b b = tailCoord ring :=
    cutCoord_self_eq_tailCoord ring b
  have hstep := oneBarrierAt_step hk ring hn2 C b b hnd hB
  by_cases hready : AdvanceReady hk ring C b
  · have hBD :
        OneBarrierAt hk ring D (ring.rightNeighbor b) := by
      simpa [D, hready] using hstep
    rcases hready with ⟨_, hphase, hheadProbe⟩
    have hheadFresh :
        (D (ring.rightNeighbor b)).bullet = false ∧
        (D (ring.rightNeighbor b)).probe = false := by
      simp only [D, PopulationProtocol.step, protocol,
        if_neg hne, if_pos rfl]
      rw [transition_of_barrier hk _ _ hbar]
      rw [barrierStep_phase_one_probe_free
        hk _ _ hphase hheadProbe]
      simp [hheadProbe]
    have hheadFreshCut :
        ((cutView ring b D) ⟨0, ring.hn⟩).bullet = false ∧
        ((cutView ring b D) ⟨0, ring.hn⟩).probe = false := by
      have hheadPos :
          cutPos ring b ⟨0, ring.hn⟩ = ring.rightNeighbor b :=
        cutPos_zero ring b
      simpa [cutView, hheadPos] using hheadFresh
    have hrot := cleanData_rotateCut ring (cutView ring b D)
      (tailCoord ring) hdataOld hheadFreshCut
    have hdataNext :
        CleanData (cutView ring (ring.rightNeighbor b) D)
          (cutCoord ring (ring.rightNeighbor b) b) := by
      rw [cutCoord_nextBarrier ring b b]
      rw [cutView_nextBarrier ring b D]
      rw [hc]
      exact hrot
    exact ⟨b, ring.rightNeighbor b, hBD, hdataNext⟩
  · have hBD : OneBarrierAt hk ring D b := by
      simpa [D, hready] using hstep
    have hcleanAt :=
      OriginalOneBarrierLeaderless.cleanAt_self_of_unique_fresh
        hk ring D b hBD huD ⟨hDbBullet, hDbProbe⟩
    exact ⟨b, b, hcleanAt⟩

theorem unique_head_case
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b l : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hl : (C l).leader = true)
    (honly : ∀ i : Fin n, (C i).leader = true → i = l)
    (hell : (cutCoord ring b l).val = 0) :
    ∃ w : List (Fin n),
      Clean hk ring (rawRun hk ring C w) ∨
        ∀ i : Fin n, (rawRun hk ring C w i).leader = false := by
  classical
  have hlh : l = ring.rightNeighbor b :=
    site_eq_head_of_coord_zero ring b l hell
  let h := ring.rightNeighbor b
  let u := OriginalPushOne.pushWord hk ring C b
  let P := rawRun hk ring C u
  have hfresh :=
    OriginalUniqueLeaderCleanup.pushWord_oneBarrier_fresh
      hk ring hn3 hnd C b hB
  dsimp only at hfresh
  change
    u.length ≤ 4 ∧
      OneBarrierAt hk ring P h ∧
      (P h).bullet = false ∧
      (P h).probe = false at hfresh
  rcases hfresh with ⟨_, hBP, hPbullet, hPprobe⟩
  have hframe :=
    OriginalOneBarrierPushLeaders.pushWord_leader_frame
      hk ring hn3 hnd C b hB
  dsimp only at hframe
  change
    (P h).leader = (C h).leader ∧
      (∀ i : Fin n, (P i).leader = true →
        (C i).leader = true ∨ i = b) ∧
      (∀ i : Fin n, i ≠ b → i ≠ h →
        i ≠ ring.rightNeighbor h → P i = C i) at hframe
  have hPleader : (P h).leader = true := by
    rw [hframe.1]
    simpa [hlh] using hl
  have hpos : 1 ≤ (cutCoord ring h h).val := by
    rw [cutCoord_self_val]
    omega
  let v :=
    [ring.leftNeighbor h] ++
      sweepWord ring h ((cutCoord ring h h).val - 1)
  let D := rawRun hk ring P v
  have ht :=
    topShoot_pinned
      hk ring hn3 P h h hBP hpos hPleader hPbullet
  dsimp only at ht
  change
    OneBarrierAt hk ring D h ∧
      D h = P h ∧
      (∀ i, 1 ≤ (cutCoord ring h i).val →
        (cutCoord ring h i).val < (cutCoord ring h h).val →
        (D i).leader = false) ∧
      (∀ i, (cutCoord ring h h).val <
        (cutCoord ring h i).val → D i = P i) ∧
      (D (ring.rightNeighbor h)).leader =
        (P (ring.rightNeighbor h)).leader ∧
      (∀ i, (D i).leader = true → (P i).leader = true) at ht
  rcases ht with ⟨hBD, hDh, hclear, _, _, hnoBirth⟩
  have hcb :
      (cutCoord ring h b).val = n - 2 := by
    simpa [h] using old_tail_after_advance_val ring hn3 b
  have hch :
      (cutCoord ring h h).val = n - 1 :=
    cutCoord_self_val ring h
  have huD : UniqueLeaderAt D h := by
    refine ⟨?_, ?_⟩
    · rw [hDh]
      exact hPleader
    · intro i hi
      have hPi := hnoBirth i hi
      rcases hframe.2.1 i hPi with hCi | hib
      · have hil : i = l := honly i hCi
        simpa [h, hlh] using hil
      · subst i
        have hkilled :
            (D b).leader = false :=
          hclear b (by rw [hcb]; omega) (by rw [hcb, hch]; omega)
        exact False.elim
          (Bool.noConfusion (hkilled.symm.trans hi))
  have hDfresh :
      (D h).bullet = false ∧ (D h).probe = false := by
    constructor
    · rw [hDh]
      exact hPbullet
    · rw [hDh]
      exact hPprobe
  have hcleanAt :=
    OriginalOneBarrierLeaderless.cleanAt_self_of_unique_fresh
      hk ring D h hBD huD hDfresh
  have hclean : Clean hk ring D :=
    clean_of_cleanAt hk ring D h h hcleanAt
  refine ⟨u ++ v, Or.inl ?_⟩
  rw [OriginalOneBarrierLeaderless.rawRun_append]
  simpa [P, D] using hclean

theorem unique_tail_case
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b l : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hl : (C l).leader = true)
    (honly : ∀ i : Fin n, (C i).leader = true → i = l)
    (hell : (cutCoord ring b l).val = n - 1) :
    ∃ w : List (Fin n),
      Clean hk ring (rawRun hk ring C w) ∨
        ∀ i : Fin n, (rawRun hk ring C w i).leader = false := by
  have hlb : l = b := site_eq_tail_of_coord_last ring b l hell
  subst l
  have hu : UniqueLeaderAt C b := ⟨hl, honly⟩
  by_cases hbullet : (C b).bullet = true
  · have hlow : 1 ≤ (cutCoord ring b b).val := by
      rw [cutCoord_self_val]
      omega
    obtain ⟨w, hzero⟩ :=
      bullet_sweep_leaderless hk ring hn3 C b b b
        hB hu hlow (Nat.le_refl _) hbullet
    exact ⟨w, Or.inr hzero⟩
  · have hbullet0 : (C b).bullet = false := by
      cases hb : (C b).bullet
      · rfl
      · exact False.elim (hbullet hb)
    by_cases hprobe : (C b).probe = true
    · have hclean :=
        tail_unique_probe_reaches_clean
          hk ring (by omega) hnd C b hB hu hprobe hbullet0
      refine ⟨[b], Or.inl ?_⟩
      simpa [rawRun] using hclean
    · have hprobe0 : (C b).probe = false := by
        cases hp : (C b).probe
        · rfl
        · exact False.elim (hprobe hp)
      have hcleanAt :=
        OriginalOneBarrierLeaderless.cleanAt_self_of_unique_fresh
          hk ring C b hB hu ⟨hbullet0, hprobe0⟩
      have hclean : Clean hk ring C :=
        clean_of_cleanAt hk ring C b b hcleanAt
      exact ⟨[], Or.inl (by simpa [rawRun] using hclean)⟩

theorem unique_middle_case
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b l : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hl : (C l).leader = true)
    (honly : ∀ i : Fin n, (C i).leader = true → i = l)
    (hlow : 1 ≤ (cutCoord ring b l).val)
    (hhigh : (cutCoord ring b l).val ≤ n - 2) :
    ∃ w : List (Fin n),
      Clean hk ring (rawRun hk ring C w) ∨
        ∀ i : Fin n, (rawRun hk ring C w i).leader = false := by
  classical
  have hn2 : 1 < n := by omega
  have hu : UniqueLeaderAt C l := ⟨hl, honly⟩
  have hlb : l ≠ b := by
    intro h
    subst l
    rw [cutCoord_self_val] at hhigh
    omega
  have hlh : l ≠ ring.rightNeighbor b := by
    intro h
    subst l
    rw [cutCoord_head_val] at hlow
    omega
  by_cases hbulEx :
      ∃ q : Fin n,
        (cutCoord ring b l).val ≤ (cutCoord ring b q).val ∧
          (C q).bullet = true
  · obtain ⟨q, hqge, hqb⟩ := hbulEx
    obtain ⟨w, hzero⟩ :=
      bullet_sweep_leaderless hk ring hn3 C b l q
        hB hu hlow hqge hqb
    exact ⟨w, Or.inr hzero⟩
  · have hbulFree :
        ∀ i : Fin n,
          (cutCoord ring b l).val ≤ (cutCoord ring b i).val →
            (C i).bullet = false := by
      intro i hi
      cases hb : (C i).bullet with
      | false => rfl
      | true => exact False.elim (hbulEx ⟨i, hi, hb⟩)
    by_cases hprobeEx :
        ∃ q : Fin n,
          (cutCoord ring b l).val ≤ (cutCoord ring b q).val ∧
            (C q).probe = true
    · obtain ⟨q, hqge, hqp⟩ := hprobeEx
      let p := cutCoord ring b q
      let m := n - 1 - p.val
      let W :=
        OriginalDangerousProbeChase.walkWord ring
          (cutPos ring b p) m
      let E := rawRun hk ring C W
      have hp :
          (cutView ring b C p).probe = true := by
        simpa [p, cutView] using hqp
      have hs : ¬ Shielded (cutView ring b C) p := by
        rintro ⟨a, hpa, ha⟩
        have hphys :
            (C (cutPos ring b a)).leader = true := by
          simpa [cutView] using ha
        have heq : cutPos ring b a = l := hu.2 _ hphys
        have hc := congrArg (cutCoord ring b) heq
        have haval :
            a.val = (cutCoord ring b l).val := by
          simpa using congrArg Fin.val hc
        change (cutCoord ring b q).val < a.val at hpa
        omega
      have hm : p.val + m = n - 1 := by
        dsimp [m]
        have hpLt := p.isLt
        omega
      have hprep :=
        OriginalDangerousProbeChase.chase_prefix
          hk ring hn2 b m C p hB hp hs hm
      change
        CurrentNonbarrierWord hk ring C W ∧
          OneBarrierAt hk ring E b ∧
          (∀ i : Fin n, (E i).leader = (C i).leader) ∧
          (E b).probe = true at hprep
      rcases hprep with ⟨_, hBE, hleadersE, hEprobe⟩
      have huE : UniqueLeaderAt E l :=
        uniqueLeaderAt_of_leaders_eq hu hleadersE
      let a := ring.leftNeighbor b
      let F := (protocol k hk).step ring E a
      have hsan :=
        incoming_sanitizes_tail_probe_unique
          hk ring hn2 hnd E b l hBE huE hlb hEprobe
      change
        OneBarrierAt hk ring F b ∧
          UniqueLeaderAt F l ∧
          (F b).bullet = false ∧
          (F b).probe = true at hsan
      rcases hsan with ⟨hBF, huF, hFbullet, hFprobe⟩
      let h := ring.rightNeighbor b
      let G := (protocol k hk).step ring F b
      have hbirth :=
        barrier_tail_probe_frame
          hk ring hn2 hnd F b l hBF huF hlb hlh hFprobe hFbullet
      dsimp only at hbirth
      rcases hbirth with
        ⟨hBG0, hGbLeader, hGbBullet, hGbProbe,
          hGlLeader, honlyG, hheadFresh⟩
      have hpre :
          rawRun hk ring C (W ++ [a, b]) = G := by
        rw [OriginalOneBarrierLeaderless.rawRun_append]
        rfl
      by_cases hready : AdvanceReady hk ring F b
      · have hBG : OneBarrierAt hk ring G h := by
          simpa [hready] using hBG0
        have hHfresh : (G h).bullet = false ∧ (G h).probe = false :=
          hheadFresh hready
        have hlNew :
            (cutCoord ring h l).val =
              (cutCoord ring b l).val - 1 := by
          simpa [h] using
            cutCoord_after_advance_val_of_pos
              ring b l (by omega)
        have hbNew :
            (cutCoord ring h b).val = n - 2 := by
          simpa [h] using old_tail_after_advance_val ring hn3 b
        by_cases hell1 : (cutCoord ring b l).val = 1
        · have hlzero : (cutCoord ring h l).val = 0 := by
            omega
          have hls : l = ring.rightNeighbor h :=
            site_eq_head_of_coord_zero ring h l hlzero
          have hph : b ≠ ring.rightNeighbor h := by
            intro hbhead
            apply hlb
            exact hls.trans hbhead.symm
          have hh :
              (G (ring.rightNeighbor h)).leader = true := by
            rw [← hls]
            exact hGlLeader
          have hpairOnly :
              ∀ i : Fin n, (G i).leader = true →
                i = b ∨ i = ring.rightNeighbor h := by
            intro i hi
            rcases honlyG i hi with hil | hib
            · exact Or.inr (hil.trans hls)
            · exact Or.inl hib
          obtain ⟨v, hclean⟩ :=
            OriginalOneBarrierHeadPair.headPair_reaches_clean
              hk ring hn3 hnd G h hBG b hph hGbLeader hh hpairOnly
          refine ⟨(W ++ [a, b]) ++ v, Or.inl ?_⟩
          rw [OriginalOneBarrierLeaderless.rawRun_append, hpre]
          exact hclean
        · have hlNewPos : 1 ≤ (cutCoord ring h l).val := by
            omega
          have hlNewLt :
              (cutCoord ring h l).val < (cutCoord ring h b).val := by
            rw [hbNew]
            omega
          have hbPos : 1 ≤ (cutCoord ring h b).val := by
            rw [hbNew]
            omega
          let v :=
            [ring.leftNeighbor b] ++
              sweepWord ring h ((cutCoord ring h b).val - 1)
          let D := rawRun hk ring G v
          have ht :=
            topShoot_pinned
              hk ring hn3 G h b hBG hbPos hGbLeader hGbBullet
          dsimp only at ht
          change
            OneBarrierAt hk ring D h ∧
              D b = G b ∧
              (∀ i, 1 ≤ (cutCoord ring h i).val →
                (cutCoord ring h i).val < (cutCoord ring h b).val →
                (D i).leader = false) ∧
              (∀ i, (cutCoord ring h b).val <
                (cutCoord ring h i).val → D i = G i) ∧
              (D (ring.rightNeighbor h)).leader =
                (G (ring.rightNeighbor h)).leader ∧
              (∀ i, (D i).leader = true → (G i).leader = true) at ht
          rcases ht with ⟨hBD, hDb, hclear, habove, _, hnoBirth⟩
          have huD : UniqueLeaderAt D b := by
            refine ⟨?_, ?_⟩
            · rw [hDb]
              exact hGbLeader
            · intro i hi
              rcases honlyG i (hnoBirth i hi) with hil | hib
              · subst i
                have hkilled :
                    (D l).leader = false :=
                  hclear l hlNewPos hlNewLt
                exact False.elim
                  (Bool.noConfusion (hkilled.symm.trans hi))
              · exact hib
          have hDbFresh :
              (D b).bullet = false ∧ (D b).probe = false := by
            constructor
            · rw [hDb]
              exact hGbBullet
            · rw [hDb]
              exact hGbProbe
          have hhSelf :
              (cutCoord ring h h).val = n - 1 :=
            cutCoord_self_val ring h
          have hDh :
              D h = G h :=
            habove h (by rw [hbNew, hhSelf]; omega)
          have hDhFresh :
              (D h).bullet = false ∧ (D h).probe = false := by
            rw [hDh]
            exact hHfresh
          have hfree :
              ∀ i : Fin n,
                (cutCoord ring h b).val ≤
                    (cutCoord ring h i).val →
                  (D i).bullet = false ∧ (D i).probe = false := by
            intro i hi
            have hilimit := (cutCoord ring h i).isLt
            have hcases :
                (cutCoord ring h i).val = n - 2 ∨
                  (cutCoord ring h i).val = n - 1 := by
              rw [hbNew] at hi
              omega
            rcases hcases with hcase | hcase
            · have hib : i = b := by
                apply site_eq_of_cutCoord_val_eq ring h
                rw [hcase, hbNew]
              subst i
              exact hDbFresh
            · have hih : i = h :=
                site_eq_tail_of_coord_last ring h i hcase
              subst i
              exact hDhFresh
          have hcleanAt :=
            cleanAt_of_unique_upper_clear
              hk ring D h b hBD huD hfree
          have hclean : Clean hk ring D :=
            clean_of_cleanAt hk ring D h b hcleanAt
          refine ⟨(W ++ [a, b]) ++ v, Or.inl ?_⟩
          rw [OriginalOneBarrierLeaderless.rawRun_append, hpre]
          simpa [D] using hclean
      · have hBG : OneBarrierAt hk ring G b := by
          simpa [hready] using hBG0
        have hbPos : 1 ≤ (cutCoord ring b b).val := by
          rw [cutCoord_self_val]
          omega
        let v :=
          [ring.leftNeighbor b] ++
            sweepWord ring b ((cutCoord ring b b).val - 1)
        let D := rawRun hk ring G v
        have ht :=
          topShoot_pinned
            hk ring hn3 G b b hBG hbPos hGbLeader hGbBullet
        dsimp only at ht
        change
          OneBarrierAt hk ring D b ∧
            D b = G b ∧
            (∀ i, 1 ≤ (cutCoord ring b i).val →
              (cutCoord ring b i).val < (cutCoord ring b b).val →
              (D i).leader = false) ∧
            (∀ i, (cutCoord ring b b).val <
              (cutCoord ring b i).val → D i = G i) ∧
            (D (ring.rightNeighbor b)).leader =
              (G (ring.rightNeighbor b)).leader ∧
            (∀ i, (D i).leader = true → (G i).leader = true) at ht
        rcases ht with ⟨hBD, hDb, hclear, _, _, hnoBirth⟩
        have hlLt :
            (cutCoord ring b l).val < (cutCoord ring b b).val := by
          rw [cutCoord_self_val]
          omega
        have huD : UniqueLeaderAt D b := by
          refine ⟨?_, ?_⟩
          · rw [hDb]
            exact hGbLeader
          · intro i hi
            rcases honlyG i (hnoBirth i hi) with hil | hib
            · subst i
              have hkilled :
                  (D l).leader = false :=
                hclear l hlow hlLt
              exact False.elim
                (Bool.noConfusion (hkilled.symm.trans hi))
            · exact hib
        have hDfresh :
            (D b).bullet = false ∧ (D b).probe = false := by
          constructor
          · rw [hDb]
            exact hGbBullet
          · rw [hDb]
            exact hGbProbe
        have hcleanAt :=
          OriginalOneBarrierLeaderless.cleanAt_self_of_unique_fresh
            hk ring D b hBD huD hDfresh
        have hclean : Clean hk ring D :=
          clean_of_cleanAt hk ring D b b hcleanAt
        refine ⟨(W ++ [a, b]) ++ v, Or.inl ?_⟩
        rw [OriginalOneBarrierLeaderless.rawRun_append, hpre]
        simpa [D] using hclean
    · have hprobeFree :
          ∀ i : Fin n,
            (cutCoord ring b l).val ≤ (cutCoord ring b i).val →
              (C i).probe = false := by
        intro i hi
        cases hp : (C i).probe with
        | false => rfl
        | true => exact False.elim (hprobeEx ⟨i, hi, hp⟩)
      have hfree :
          ∀ i : Fin n,
            (cutCoord ring b l).val ≤ (cutCoord ring b i).val →
              (C i).bullet = false ∧ (C i).probe = false := by
        intro i hi
        exact ⟨hbulFree i hi, hprobeFree i hi⟩
      have hcleanAt :=
        cleanAt_of_unique_upper_clear
          hk ring C b l hB hu hfree
      have hclean : Clean hk ring C :=
        clean_of_cleanAt hk ring C b l hcleanAt
      exact ⟨[], Or.inl (by simpa [rawRun] using hclean)⟩

theorem unique_reaches_clean_or_leaderless
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (l : Fin n)
    (hl : (C l).leader = true)
    (honly : ∀ i, (C i).leader = true → i = l) :
    ∃ w : List (Fin n),
      Clean hk ring (rawRun hk ring C w) ∨
        ∀ i, (rawRun hk ring C w i).leader = false := by
  let ell := (cutCoord ring b l).val
  by_cases hzero : ell = 0
  · exact unique_head_case
      hk ring hn3 hnd C b l hB hl honly
        (by simpa [ell] using hzero)
  · by_cases htail : ell = n - 1
    · exact unique_tail_case
        hk ring hn3 hnd C b l hB hl honly
          (by simpa [ell] using htail)
    · have hellLt : ell < n := (cutCoord ring b l).isLt
      have hlow : 1 ≤ ell := by omega
      have hhigh : ell ≤ n - 2 := by omega
      exact unique_middle_case
        hk ring hn3 hnd C b l hB hl honly
          (by simpa [ell] using hlow)
          (by simpa [ell] using hhigh)

end AAFJPK.OriginalOneBarrierUnique

#print axioms AAFJPK.OriginalOneBarrierUnique.unique_head_case
#print axioms AAFJPK.OriginalOneBarrierUnique.unique_tail_case
#print axioms AAFJPK.OriginalOneBarrierUnique.unique_middle_case
#print axioms AAFJPK.OriginalOneBarrierUnique.unique_reaches_clean_or_leaderless
