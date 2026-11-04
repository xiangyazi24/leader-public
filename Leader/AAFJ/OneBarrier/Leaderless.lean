import Leader.AAFJ.OneBarrier.UniqueLeaderCleanup
import Leader.AAFJ.OneBarrier.DangerousProbeChase


set_option autoImplicit false
set_option Elab.async false


namespace AAFJPK.OriginalOneBarrierLeaderless


open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord
open OriginalUniqueLeaderCleanup


/-- Raw execution composes over list append. -/
theorem rawRun_append {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (u v : List (Fin n)) :
    rawRun hk ring C (u ++ v) =
      rawRun hk ring (rawRun hk ring C u) v := by
  induction u generalizing C with
  | nil => rfl
  | cons e es ih =>
      simpa only [List.cons_append, rawRun] using
        ih ((protocol k hk).step ring C e)


/-- A unique leader at the cut tail with no local marks already has CleanData. -/
theorem cleanData_tail_of_unique_fresh {n k : Nat}
    (ring : DirectedRing n) (C : Fin n → State k) (b : Fin n)
    (hu : UniqueLeaderAt C b)
    (hf : (C b).bullet = false ∧ (C b).probe = false) :
    CleanData (cutView ring b C) (tailCoord ring) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [cutView] using hu.1
  · intro i hi
    apply cutPos_injective ring b
    rw [cutPos_tailCoord]
    exact hu.2 _ (by simpa [cutView] using hi)
  · intro i hm
    by_cases hit : i = tailCoord ring
    · subst i
      rcases hm with hb | hp
      · have hb' : (C b).bullet = true := by
          simpa [cutView] using hb
        exact False.elim (Bool.noConfusion (hf.1.symm.trans hb'))
      · have hp' : (C b).probe = true := by
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


/-- Public version of the private cleanup leaf needed by this file. -/
theorem cleanAt_self_of_unique_fresh {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hu : UniqueLeaderAt C b)
    (hf : (C b).bullet = false ∧ (C b).probe = false) :
    CleanAt hk ring C b b := by
  refine ⟨hB, ?_⟩
  have hc : cutCoord ring b b = tailCoord ring := by
    apply cutPos_injective ring b
    rw [cutPos_cutCoord, cutPos_tailCoord]
  rw [hc]
  exact cleanData_tail_of_unique_fresh ring C b hu hf


/-- In a leaderless one-barrier state, a phase-zero barrier hit seeds a probe
at the current head and creates no leader. -/
theorem phase_zero_seed_probe {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (h0 : ∀ i : Fin n, (C i).leader = false)
    (htailProbe : (C b).probe = false)
    (hphase : (C b).phase = false) :
    let D := (protocol k hk).step ring C b
    OneBarrierAt hk ring D b ∧
      (∀ i : Fin n, (D i).leader = false) ∧
      (D b).phase = true ∧
      (D (ring.rightNeighbor b)).probe = true := by
  let D := (protocol k hk).step ring C b
  have hb : BarrierAt hk ring (labelsOf C) b := (hB b).2 rfl
  have hi : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).1 hb
  have hnot : ¬ AdvanceReady hk ring C b := by
    simp [AdvanceReady, PairAdvanceReady, hphase]
  have hBD : OneBarrierAt hk ring D b := by
    simpa [D, hnot] using
      oneBarrierAt_step hk ring hn2 C b b hnd hB
  have ht :
      transition hk (C b) (C (ring.rightNeighbor b)) =
        ({ probeHitsBarrier (C b) with phase := true },
          { C (ring.rightNeighbor b) with probe := true }) := by
    rw [transition_of_barrier hk _ _ hi,
      barrierStep_phase_zero hk _ _ hphase]
    simp [h0 (ring.rightNeighbor b)]
  have heq := step_leaders_eq_of_local hk ring hn2 C b
    (by simp [ht, probeHitsBarrier, htailProbe, h0 b])
    (by simp [ht, h0 (ring.rightNeighbor b)])
  have h0D : ∀ i : Fin n, (D i).leader = false := by
    intro i
    change (((protocol k hk).step ring C b) i).leader = false
    rw [heq i, h0 i]
  have hphaseD : (D b).phase = true := by
    simp [D, PopulationProtocol.step, protocol, ht]
  have hre := rightNeighbor_ne_self ring hn2 b
  have hprobeD : (D (ring.rightNeighbor b)).probe = true := by
    simp [D, PopulationProtocol.step, protocol, ht, hre]
  exact ⟨hBD, h0D, hphaseD, hprobeD⟩


/-- A leaderless phase-one barrier with a probe-free head advances once.
The new barrier tail is phase zero and probe free. -/
theorem phase_one_advance_probe_free {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (h0 : ∀ i : Fin n, (C i).leader = false)
    (htailProbe : (C b).probe = false)
    (hphase : (C b).phase = true)
    (hheadProbe : (C (ring.rightNeighbor b)).probe = false) :
    let s := ring.rightNeighbor b
    let D := (protocol k hk).step ring C b
    OneBarrierAt hk ring D s ∧
      (∀ i : Fin n, (D i).leader = false) ∧
      (D s).phase = false ∧
      (D s).probe = false := by
  let s := ring.rightNeighbor b
  let D := (protocol k hk).step ring C b
  have hb : BarrierAt hk ring (labelsOf C) b := (hB b).2 rfl
  have hi : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).1 hb
  have hr : AdvanceReady hk ring C b := ⟨hi, hphase, hheadProbe⟩
  have hBD : OneBarrierAt hk ring D s := by
    change OneBarrierAt hk ring ((protocol k hk).step ring C b) s
    simpa [s, hr] using
      oneBarrierAt_step hk ring hn2 C b b hnd hB
  have ht := barrierStep_phase_one_probe_free
    hk (C b) (C (ring.rightNeighbor b)) hphase hheadProbe
  have heq := step_leaders_eq_of_local hk ring hn2 C b
    (by simp [transition, hi, ht, probeHitsBarrier, htailProbe, h0 b])
    (by simp [transition, hi, ht, h0 (ring.rightNeighbor b)])
  have h0D : ∀ i : Fin n, (D i).leader = false := by
    intro i
    change (((protocol k hk).step ring C b) i).leader = false
    rw [heq i, h0 i]
  have hre := rightNeighbor_ne_self ring hn2 b
  have hphaseD : (D s).phase = false := by
    simp [D, s, PopulationProtocol.step, protocol,
      transition_of_barrier hk _ _ hi, ht, hre, hheadProbe]
  have hprobeD : (D s).probe = false := by
    simp [D, s, PopulationProtocol.step, protocol,
      transition_of_barrier hk _ _ hi, ht, hre, hheadProbe]
  exact ⟨hBD, h0D, hphaseD, hprobeD⟩


/-- One service of the edge entering a leaderless barrier tail preserves a
tail probe and clears the tail bullet. -/
theorem incoming_sanitizes_tail_probe {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (h0 : ∀ i : Fin n, (C i).leader = false)
    (hprobe : (C b).probe = true) :
    let p := ring.leftNeighbor b
    let D := (protocol k hk).step ring C p
    OneBarrierAt hk ring D b ∧
      (∀ i : Fin n, (D i).leader = false) ∧
      (D b).bullet = false ∧
      (D b).probe = true := by
  let p := ring.leftNeighbor b
  let D := (protocol k hk).step ring C p
  have hr : ring.rightNeighbor p = b := by
    simpa [p] using rightNeighbor_leftNeighbor_clean ring b
  have hpne : p ≠ b := by
    intro h
    have hright : ring.rightNeighbor p = b := hr
    rw [h] at hright
    exact (rightNeighbor_ne_self ring hn2 b) hright
  have hnb :
      ¬ IsBarrier hk (C p) (C (ring.rightNeighbor p)) := by
    intro hbar
    have hphys : BarrierAt hk ring (labelsOf C) p :=
      (barrierAt_labelsOf_iff hk ring C p).2 hbar
    exact hpne ((hB p).1 hphys)
  have hnot : ¬ AdvanceReady hk ring C p :=
    not_advanceReady_of_nonbarrier hk ring C p hnb
  have hBD : OneBarrierAt hk ring D b := by
    simpa [D, hnot] using
      oneBarrierAt_step hk ring hn2 C b p hnd hB
  have hrespLeader :
      (C (ring.rightNeighbor p)).leader = false := by
    rw [hr]
    exact h0 b
  have hrespProbe :
      (C (ring.rightNeighbor p)).probe = true := by
    rw [hr]
    exact hprobe
  have hlocal :
      (transition hk (C p) (C (ring.rightNeighbor p))).1.leader = false ∧
      (transition hk (C p) (C (ring.rightNeighbor p))).2.leader = false ∧
      (transition hk (C p) (C (ring.rightNeighbor p))).2.bullet = false ∧
      (transition hk (C p) (C (ring.rightNeighbor p))).2.probe = true := by
    rw [transition_of_nonbarrier hk _ _ hnb]
    cases hb : (C (ring.rightNeighbor p)).bullet <;>
      cases hp : (C p).probe <;>
      simp [nonBarrierStep, hrespLeader, hrespProbe, h0 p, hb, hp]
  have hleaders := step_leaders_eq_of_local hk ring hn2 C p
    (by rw [hlocal.1, h0 p])
    (by rw [hlocal.2.1, hrespLeader])
  have h0D : ∀ i : Fin n, (D i).leader = false := by
    intro i
    change (((protocol k hk).step ring C p) i).leader = false
    rw [hleaders i, h0 i]
  have hre := rightNeighbor_ne_self ring hn2 p
  have hDrespBullet :
      (D (ring.rightNeighbor p)).bullet = false := by
    simpa [D, PopulationProtocol.step, protocol, hre] using
      hlocal.2.2.1
  have hDrespProbe :
      (D (ring.rightNeighbor p)).probe = true := by
    simpa [D, PopulationProtocol.step, protocol, hre] using
      hlocal.2.2.2
  refine ⟨hBD, h0D, ?_, ?_⟩
  · simpa [hr] using hDrespBullet
  · simpa [hr] using hDrespProbe


/-- A fresh tail probe in a leaderless one-barrier state becomes a unique
fresh leader after the barrier service, and the result is Clean whether or
not that service also advances the barrier. -/
theorem tail_probe_reaches_clean {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (h0 : ∀ i : Fin n, (C i).leader = false)
    (hprobe : (C b).probe = true)
    (hbullet : (C b).bullet = false) :
    Clean hk ring ((protocol k hk).step ring C b) := by
  let D := (protocol k hk).step ring C b
  have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).1 ((hB b).2 rfl)
  have hlocal :
      (transition hk (C b) (C (ring.rightNeighbor b))).1.leader = true ∧
      (transition hk (C b) (C (ring.rightNeighbor b))).1.bullet = false ∧
      (transition hk (C b) (C (ring.rightNeighbor b))).1.probe = false ∧
      (transition hk (C b) (C (ring.rightNeighbor b))).2.leader = false := by
    rw [transition_of_barrier hk _ _ hbar]
    cases hphase : (C b).phase <;>
      cases hheadProbe : (C (ring.rightNeighbor b)).probe <;>
      simp [barrierStep, probeHitsBarrier, hprobe, hbullet,
        hphase, hheadProbe, h0 (ring.rightNeighbor b)]
  have hDbLeader : (D b).leader = true := by
    simpa [D, PopulationProtocol.step, protocol] using hlocal.1
  have hDbBullet : (D b).bullet = false := by
    simpa [D, PopulationProtocol.step, protocol] using hlocal.2.1
  have hDbProbe : (D b).probe = false := by
    simpa [D, PopulationProtocol.step, protocol] using hlocal.2.2.1
  have hne := rightNeighbor_ne_self ring hn2 b
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
      rw [h0 i] at hCi
      contradiction
  have hdataOld :
      CleanData (cutView ring b D) (tailCoord ring) :=
    cleanData_tail_of_unique_fresh ring D b huD
      ⟨hDbBullet, hDbProbe⟩
  have hc : cutCoord ring b b = tailCoord ring := by
    apply cutPos_injective ring b
    rw [cutPos_cutCoord, cutPos_tailCoord]
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
    refine ⟨b, ?_⟩
    refine ⟨ring.rightNeighbor b, ?_⟩
    exact ⟨hBD, hdataNext⟩
  · have hBD : OneBarrierAt hk ring D b := by
      simpa [D, hready] using hstep
    have hcleanAt :
        CleanAt hk ring D b b :=
      cleanAt_self_of_unique_fresh hk ring D b hBD huD
        ⟨hDbBullet, hDbProbe⟩
    refine ⟨b, ?_⟩
    exact ⟨b, hcleanAt⟩


/-- If a leaderless one-barrier state already contains a probe, an explicit
finite word reaches Clean. -/
theorem probe_present_reaches_clean {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (h0 : ∀ i : Fin n, (C i).leader = false)
    (hex : ∃ x : Fin n, (C x).probe = true) :
    ∃ w : List (Fin n), Clean hk ring (rawRun hk ring C w) := by
  obtain ⟨x, hx⟩ := hex
  let p := cutCoord ring b x
  let m := n - 1 - p.val
  let W :=
    OriginalDangerousProbeChase.walkWord ring
      (cutPos ring b p) m
  let E := rawRun hk ring C W
  have hp : (cutView ring b C p).probe = true := by
    simpa [p, cutView] using hx
  have hs : ¬ Shielded (cutView ring b C) p := by
    rintro ⟨ell, _, hell⟩
    have hphys :
        (C (cutPos ring b ell)).leader = true := by
      simpa [cutView] using hell
    rw [h0 (cutPos ring b ell)] at hphys
    contradiction
  have hm : p.val + m = n - 1 := by
    dsimp [m]
    have hpLt := p.isLt
    omega
  have hprep :=
    OriginalDangerousProbeChase.chase_prefix hk ring hn2 b m
      C p hB hp hs hm
  change
    CurrentNonbarrierWord hk ring C W ∧
      OneBarrierAt hk ring E b ∧
      (∀ i : Fin n, (E i).leader = (C i).leader) ∧
      (E b).probe = true at hprep
  obtain ⟨_, hBE, hleaders, hPE⟩ := hprep
  have h0E : ∀ i : Fin n, (E i).leader = false := by
    intro i
    rw [hleaders i, h0 i]
  let a := ring.leftNeighbor b
  let F := (protocol k hk).step ring E a
  have hsan :=
    incoming_sanitizes_tail_probe hk ring hn2 hnd
      E b hBE h0E hPE
  change
    OneBarrierAt hk ring F b ∧
      (∀ i : Fin n, (F i).leader = false) ∧
      (F b).bullet = false ∧
      (F b).probe = true at hsan
  have hclean :=
    tail_probe_reaches_clean hk ring hn2 hnd
      F b hsan.1 hsan.2.1 hsan.2.2.2 hsan.2.2.1
  refine ⟨W ++ [a, b], ?_⟩
  rw [rawRun_append hk ring C W [a, b]]
  simpa [E, F, a, rawRun] using hclean


/-- From a probe-free leaderless one-barrier state, one or two barrier hits
produce a probe while preserving leaderlessness and a unique barrier. -/
theorem probe_free_reaches_probe {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (h0 : ∀ i : Fin n, (C i).leader = false)
    (hprobe0 : ∀ i : Fin n, (C i).probe = false) :
    ∃ w : List (Fin n), ∃ b' : Fin n,
      w.length ≤ 2 ∧
      OneBarrierAt hk ring (rawRun hk ring C w) b' ∧
      (∀ i : Fin n, (rawRun hk ring C w i).leader = false) ∧
      ∃ i : Fin n, (rawRun hk ring C w i).probe = true := by
  cases hphase : (C b).phase with
  | false =>
      let D := (protocol k hk).step ring C b
      have hseed :=
        phase_zero_seed_probe hk ring hn2 hnd C b hB h0
          (hprobe0 b) hphase
      change
        OneBarrierAt hk ring D b ∧
          (∀ i : Fin n, (D i).leader = false) ∧
          (D b).phase = true ∧
          (D (ring.rightNeighbor b)).probe = true at hseed
      refine ⟨[b], b, by simp, ?_, ?_, ?_⟩
      · simpa [rawRun, D] using hseed.1
      · intro i
        simpa [rawRun, D] using hseed.2.1 i
      · refine ⟨ring.rightNeighbor b, ?_⟩
        simpa [rawRun, D] using hseed.2.2.2
  | true =>
      let s := ring.rightNeighbor b
      let D := (protocol k hk).step ring C b
      have hadv :=
        phase_one_advance_probe_free hk ring hn2 hnd
          C b hB h0 (hprobe0 b) hphase (hprobe0 s)
      change
        OneBarrierAt hk ring D s ∧
          (∀ i : Fin n, (D i).leader = false) ∧
          (D s).phase = false ∧
          (D s).probe = false at hadv
      let E := (protocol k hk).step ring D s
      have hseed :=
        phase_zero_seed_probe hk ring hn2 hnd D s
          hadv.1 hadv.2.1 hadv.2.2.2 hadv.2.2.1
      change
        OneBarrierAt hk ring E s ∧
          (∀ i : Fin n, (E i).leader = false) ∧
          (E s).phase = true ∧
          (E (ring.rightNeighbor s)).probe = true at hseed
      refine ⟨[b, s], s, by simp, ?_, ?_, ?_⟩
      · simpa [rawRun, D, E, s] using hseed.1
      · intro i
        simpa [rawRun, D, E, s] using hseed.2.1 i
      · refine ⟨ring.rightNeighbor s, ?_⟩
        simpa [rawRun, D, E, s] using hseed.2.2.2


theorem leaderless_reaches_clean {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (hnd : ¬ k ∣ n) (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (h0 : ∀ i : Fin n, (C i).leader = false) :
    ∃ w : List (Fin n), Clean hk ring (rawRun hk ring C w) := by
  have hn2 : 1 < n := by omega
  by_cases hex : ∃ i : Fin n, (C i).probe = true
  · exact probe_present_reaches_clean
      hk ring hn2 hnd C b hB h0 hex
  · have hprobe0 : ∀ i : Fin n, (C i).probe = false := by
      intro i
      cases hp : (C i).probe with
      | false => rfl
      | true => exact False.elim (hex ⟨i, hp⟩)
    obtain ⟨u, b', _, hB', h0', hex'⟩ :=
      probe_free_reaches_probe
        hk ring hn2 hnd C b hB h0 hprobe0
    obtain ⟨v, hclean⟩ :=
      probe_present_reaches_clean hk ring hn2 hnd
        (rawRun hk ring C u) b' hB' h0' hex'
    refine ⟨u ++ v, ?_⟩
    rw [rawRun_append hk ring C u v]
    exact hclean


end AAFJPK.OriginalOneBarrierLeaderless


#print axioms AAFJPK.OriginalOneBarrierLeaderless.rawRun_append
#print axioms AAFJPK.OriginalOneBarrierLeaderless.cleanData_tail_of_unique_fresh
#print axioms AAFJPK.OriginalOneBarrierLeaderless.cleanAt_self_of_unique_fresh
#print axioms AAFJPK.OriginalOneBarrierLeaderless.phase_zero_seed_probe
#print axioms AAFJPK.OriginalOneBarrierLeaderless.phase_one_advance_probe_free
#print axioms AAFJPK.OriginalOneBarrierLeaderless.incoming_sanitizes_tail_probe
#print axioms AAFJPK.OriginalOneBarrierLeaderless.tail_probe_reaches_clean
#print axioms AAFJPK.OriginalOneBarrierLeaderless.probe_present_reaches_clean
#print axioms AAFJPK.OriginalOneBarrierLeaderless.probe_free_reaches_probe
#print axioms AAFJPK.OriginalOneBarrierLeaderless.leaderless_reaches_clean
