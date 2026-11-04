import Leader.AAFJ.OneBarrier.Sanitation
import Leader.AAFJ.NonbarrierWord


set_option autoImplicit false
namespace AAFJPK.ZeroLeaderBirth


open BarrierAlgebra SingleBarrierSanitation OriginalNonbarrierWord


private abbrev NL {n k : Nat} (C : Fin n -> State k) : Prop :=
  forall i, (C i).leader = false


variable {n k : Nat} (hk : 0 < k) (R : DirectedRing n)


private def st (C : Fin n -> State k) (e : Fin n) :=
  (protocol k hk).step R C e


private theorem nonbarrier_probe_push
    (hn2 : 1 < n) (C : Fin n -> State k) (e : Fin n)
    (hnb : ¬ (BarrierAt hk R (labelsOf C) e))
    (hz : NL C) (hp : (C e).probe = true) :
    NL (st hk R C e) ∧
      ((st hk R C e) (R.rightNeighbor e)).probe = true := by
  have hi : ¬ (IsBarrier hk (C e) (C (R.rightNeighbor e))) := by
    intro h
    exact hnb ((barrierAt_labelsOf_iff hk R C e).2 h)
  have hloc :
      (transition hk (C e) (C (R.rightNeighbor e))).1.leader = false ∧
      (transition hk (C e) (C (R.rightNeighbor e))).2.leader = false ∧
      (transition hk (C e) (C (R.rightNeighbor e))).2.probe = true := by
    rw [transition_of_nonbarrier hk _ _ hi]
    cases hb : (C (R.rightNeighbor e)).bullet with
    | false =>
        rw [nonBarrierStep_follower_probe_only _ _ (hz _) hb hp]
        simp [hz]
    | true =>
        rw [nonBarrierStep_follower_bullet_probe _ _ (hz _) hb hp]
        simp [hz]
  have heq := step_leaders_eq_of_local hk R hn2 C e
    (by rw [hloc.1, hz e])
    (by rw [hloc.2.1, hz (R.rightNeighbor e)])
  refine ⟨?_, ?_⟩
  · intro i
    change (((protocol k hk).step R C e) i).leader = false
    rw [heq i, hz i]
  · have hre := rightNeighbor_ne_self R hn2 e
    simpa [st, PopulationProtocol.step, protocol, hre] using hloc.2.2


private theorem seed
    (hn2 : 1 < n) (hnd : ¬ (k ∣ n))
    (C : Fin n -> State k) (b : Fin n)
    (ho : OneBarrierAt hk R C b) (hz : NL C)
    (hp : (C b).probe = false) (hph : (C b).phase = false) :
    let D := st hk R C b
    OneBarrierAt hk R D b ∧ NL D ∧
      (D b).phase = true ∧ (D (R.rightNeighbor b)).probe = true := by
  let D := st hk R C b
  have hb := (ho b).2 rfl
  have hi := (barrierAt_labelsOf_iff hk R C b).1 hb
  have hnot : ¬ (AdvanceReady hk R C b) := by
    simp [AdvanceReady, PairAdvanceReady, hph]
  have h1 : OneBarrierAt hk R D b := by
    change OneBarrierAt hk R ((protocol k hk).step R C b) b
    simpa [hnot] using oneBarrierAt_step hk R hn2 C b b hnd ho
  have ht : transition hk (C b) (C (R.rightNeighbor b)) =
      ({probeHitsBarrier (C b) with phase := true},
       {C (R.rightNeighbor b) with probe := true}) := by
    rw [transition_of_barrier hk _ _ hi, barrierStep_phase_zero hk _ _ hph]
    simp [hz (R.rightNeighbor b)]
  have heq := step_leaders_eq_of_local hk R hn2 C b
    (by simp [ht, probeHitsBarrier, hp, hz b])
    (by simp [ht, hz (R.rightNeighbor b)])
  have hre := rightNeighbor_ne_self R hn2 b
  refine ⟨h1, ?_, ?_, ?_⟩
  · intro i
    change (((protocol k hk).step R C b) i).leader = false
    rw [heq i, hz i]
  · simp [D, st, PopulationProtocol.step, protocol, ht]
  · simp [D, st, PopulationProtocol.step, protocol, ht, hre]


private theorem advance
    (hn2 : 1 < n) (hnd : ¬ (k ∣ n))
    (C : Fin n -> State k) (b : Fin n)
    (ho : OneBarrierAt hk R C b) (hz : NL C)
    (hp : (C b).probe = false) (hph : (C b).phase = true)
    (hh : (C (R.rightNeighbor b)).probe = false) :
    let h := R.rightNeighbor b
    let D := st hk R C b
    OneBarrierAt hk R D h ∧ NL D ∧
      (D h).phase = false ∧ (D h).probe = false := by
  let h := R.rightNeighbor b
  let D := st hk R C b
  have hb := (ho b).2 rfl
  have hi := (barrierAt_labelsOf_iff hk R C b).1 hb
  have hr : AdvanceReady hk R C b := ⟨hi, hph, hh⟩
  have h1 : OneBarrierAt hk R D h := by
    change OneBarrierAt hk R ((protocol k hk).step R C b) h
    simpa [h, hr] using oneBarrierAt_step hk R hn2 C b b hnd ho
  have ht := barrierStep_phase_one_probe_free hk
    (C b) (C (R.rightNeighbor b)) hph hh
  have heq := step_leaders_eq_of_local hk R hn2 C b
    (by simp [transition, hi, ht, probeHitsBarrier, hp])
    (by simp [transition, hi, ht])
  have hre := rightNeighbor_ne_self R hn2 b
  refine ⟨h1, ?_, ?_, ?_⟩
  · intro i
    change (((protocol k hk).step R C b) i).leader = false
    rw [heq i, hz i]
  · simp [D, st, h, PopulationProtocol.step, protocol,
      transition_of_barrier hk _ _ hi, ht, hre, hh]
  · simp [D, st, h, PopulationProtocol.step, protocol,
      transition_of_barrier hk _ _ hi, ht, hre, hh]


private theorem birth
    (hn2 : 1 < n) (hnd : ¬ (k ∣ n))
    (C : Fin n -> State k) (b : Fin n)
    (ho : OneBarrierAt hk R C b) (hp : (C b).probe = true) :
    exists b', OneBarrierAt hk R (rawRun hk R C [b]) b' ∧
      (rawRun hk R C [b] b).leader = true := by
  have hb := (ho b).2 rfl
  have hi := (barrierAt_labelsOf_iff hk R C b).1 hb
  have h1 := oneBarrierAt_step hk R hn2 C b b hnd ho
  have hl : (transition hk (C b) (C (R.rightNeighbor b))).1.leader = true := by
    cases hph : (C b).phase <;>
      cases hh : (C (R.rightNeighbor b)).probe <;>
      simp [transition, hi, barrierStep, probeHitsBarrier, hp, hph, hh]
  refine ⟨if AdvanceReady hk R C b then R.rightNeighbor b else b, ?_, ?_⟩
  · simpa [rawRun] using h1
  · simpa [rawRun, PopulationProtocol.step, protocol] using hl


private def chase (R : DirectedRing n) (p b : Fin n) : Nat -> List (Fin n)
  | 0 => [b]
  | d + 1 => p :: chase R (R.rightNeighbor p) b d


@[simp] private theorem chase_length
    (R : DirectedRing n) (p b : Fin n) (d : Nat) :
    (chase R p b d).length = d + 1 := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih => simp [chase, ih, Nat.succ_eq_add_one]


private theorem dist_self (p : Fin n) : cwDist R p p = 0 :=
  (cwPos_bounded_unique R p p 0 R.hn (cwPos_zero R p)).symm


private theorem chase_birth
    (hn2 : 1 < n) (hnd : ¬ (k ∣ n))
    (C : Fin n -> State k) (p b : Fin n)
    (d : Nat) (hd : d < n) (hpos : cwPos R p d = b)
    (ho : OneBarrierAt hk R C b) (hz : NL C) (hp : (C p).probe = true) :
    exists b', OneBarrierAt hk R (rawRun hk R C (chase R p b d)) b' ∧
      (rawRun hk R C (chase R p b d) b).leader = true := by
  induction d generalizing C p with
  | zero =>
      rw [cwPos_zero] at hpos
      subst p
      simpa [chase] using birth hk R hn2 hnd C b ho hp
  | succ d ih =>
      have hne : p ≠ b := by
        intro h
        have hpos_succ : cwPos R p (d + 1) = p := hpos.trans h.symm
        have hz0 := cwPos_bounded_unique R p p (d + 1) (by omega)
          hpos_succ
        rw [dist_self R p] at hz0
        omega
      have hnb : ¬ (BarrierAt hk R (labelsOf C) p) := by
        intro h
        exact hne ((ho p).1 h)
      let D := st hk R C p
      have hnot : ¬ (AdvanceReady hk R C p) := by
        intro h
        exact hnb ((barrierAt_labelsOf_iff hk R C p).2 h.1)
      have h1 : OneBarrierAt hk R D b := by
        change OneBarrierAt hk R ((protocol k hk).step R C p) b
        simpa [hnot] using oneBarrierAt_step hk R hn2 C b p hnd ho
      have hm := nonbarrier_probe_push hk R hn2 C p hnb hz hp
      have hzD : NL D := by simpa [D, st] using hm.1
      have hpD : (D (R.rightNeighbor p)).probe = true := by
        simpa [D, st] using hm.2
      have hpos' : cwPos R (R.rightNeighbor p) d = b := by
        rw [cwPos_rightNeighbor]
        simpa [Nat.succ_eq_add_one] using hpos
      obtain ⟨b', hb', hl⟩ := ih (C := D) (p := R.rightNeighbor p)
        (by omega) hpos' h1 hzD hpD
      refine ⟨b', ?_, ?_⟩
      · simpa [chase, rawRun, D, st] using hb'
      · simpa [chase, rawRun, D, st] using hl


theorem zeroLeader_oneBarrierAt_birth_word
    (hn2 : 1 < n) (hnd : ¬ (k ∣ n))
    (C : Fin n -> State k) (b : Fin n)
    (ho : OneBarrierAt hk R C b) (hz : forall i, (C i).leader = false) :
    exists w b', w.length <= n + 2 ∧
      OneBarrierAt hk R (rawRun hk R C w) b' ∧
      exists i, (rawRun hk R C w i).leader = true := by
  let h := R.rightNeighbor b
  let d := cwDist R h b
  have hd : d < n := cwDist_lt R h b
  have hpos : cwPos R h d = b := cwPos_cwDist R h b
  cases htp : (C b).probe with
  | true =>
      obtain ⟨b', hb', hl⟩ := birth hk R hn2 hnd C b ho htp
      refine ⟨[b], b', ?_, hb', ⟨b, hl⟩⟩
      simp only [List.length_cons, List.length_nil]
      omega
  | false =>
    cases hph : (C b).phase with
    | false =>
      let D := st hk R C b
      obtain ⟨hD, hzD, _, hpD⟩ := seed hk R hn2 hnd C b ho hz htp hph
      obtain ⟨b', hb', hl⟩ :=
        chase_birth hk R hn2 hnd D h b d hd hpos hD hzD hpD
      refine ⟨b :: chase R h b d, b', ?_, ?_, ⟨b, ?_⟩⟩
      · simp only [List.length_cons, chase_length]
        omega
      · simpa [rawRun, D, st] using hb'
      · simpa [rawRun, D, st] using hl
    | true =>
      cases hhp : (C h).probe with
      | true =>
        obtain ⟨b', hb', hl⟩ :=
          chase_birth hk R hn2 hnd C h b d hd hpos ho hz hhp
        refine ⟨chase R h b d, b', ?_, hb', ⟨b, hl⟩⟩
        simp only [chase_length]
        omega
      | false =>
        let D := st hk R C b
        obtain ⟨hD, hzD, hphD, hpD⟩ :=
          advance hk R hn2 hnd C b ho hz htp hph hhp
        let E := st hk R D h
        obtain ⟨hE, hzE, _, hpE⟩ :=
          seed hk R hn2 hnd D h hD hzD hpD hphD
        let h2 := R.rightNeighbor h
        let d2 := cwDist R h2 h
        have hd2 : d2 < n := cwDist_lt R h2 h
        have hpos2 : cwPos R h2 d2 = h := cwPos_cwDist R h2 h
        obtain ⟨b', hb', hl⟩ :=
          chase_birth hk R hn2 hnd E h2 h d2 hd2 hpos2 hE hzE hpE
        refine ⟨b :: h :: chase R h2 h d2, b', ?_, ?_, ⟨h, ?_⟩⟩
        · simp only [List.length_cons, chase_length]
          omega
        · simpa [rawRun, D, E, st] using hb'
        · simpa [rawRun, D, E, st] using hl


end AAFJPK.ZeroLeaderBirth

#print axioms AAFJPK.ZeroLeaderBirth.zeroLeader_oneBarrierAt_birth_word
