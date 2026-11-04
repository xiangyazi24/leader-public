import Leader.AAFJ.OneBarrier.MultipleLeaderProgress
import Leader.AAFJ.OneBarrier.UniqueLeaderCleanup

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.SelectedMultipleUniqueSafe

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.SingleBarrierSanitation
open AAFJPK.OriginalNonbarrierWord
open AAFJPK.OriginalUniqueLeaderCleanup
open AAFJPK.OriginalMultipleLeaderOneBarrier
open AAFJPK.CenteredRenewal.OneBarrierCleanup

private theorem packaged_step_eq_of_local
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n)
    (hlocal :
      AAFJPK.transition hk (C e) (C (ring.rightNeighbor e)) =
        CenteredRenewal.transition hk
          (C e) (C (ring.rightNeighbor e))) :
    (AAFJPK.protocol k hk).step ring C e =
      CenteredRenewal.OneBarrierCleanup.step hk ring C e := by
  funext i
  simp [CenteredRenewal.OneBarrierCleanup.step,
    PopulationProtocol.step, AAFJPK.protocol, CenteredRenewal.protocol,
    hlocal]

private theorem original_step_eq_centered_of_nonbarrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n)
    (hnb : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    (AAFJPK.protocol k hk).step ring C e =
      CenteredRenewal.OneBarrierCleanup.step hk ring C e := by
  apply packaged_step_eq_of_local hk ring C e
  rw [AAFJPK.transition_of_nonbarrier hk _ _ hnb,
    CenteredRenewal.transition_of_nonbarrier hk _ _ hnb]

private theorem original_run_eq_centered_of_avoids_barrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n) (w : List (Fin n))
    (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (havoid : ∀ e ∈ w, e ≠ b) :
    rawRun hk ring C w =
      CenteredRenewal.OneBarrierCleanup.runWord hk ring C w := by
  induction w generalizing C with
  | nil => rfl
  | cons e es ih =>
      have he : e ≠ b := havoid e (by simp)
      have hnb :
          ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro hb
        apply he
        exact (hone e).1
          ((barrierAt_labelsOf_iff hk ring C e).2 hb)
      have hnot : ¬ AdvanceReady hk ring C e := by
        intro hr
        exact hnb hr.1
      let D := (AAFJPK.protocol k hk).step ring C e
      have honeD : OneBarrierAt hk ring D b := by
        have h :=
          SingleBarrierSanitation.oneBarrierAt_step
            hk ring hn2 C b e hndvd hone
        simpa [D, hnot] using h
      have htail : ∀ f ∈ es, f ≠ b := by
        intro f hf
        exact havoid f (by simp [hf])
      have hstep :=
        original_step_eq_centered_of_nonbarrier hk ring C e hnb
      change
        rawRun hk ring D es =
          CenteredRenewal.OneBarrierCleanup.runWord hk ring
            (CenteredRenewal.OneBarrierCleanup.step hk ring C e) es
      rw [← hstep]
      exact ih D honeD htail

private theorem parkedSweepWord_avoids_barrier
    {n : Nat} (ring : DirectedRing n) (b : Fin n) :
    ∀ e ∈ parkedSweepWord ring b, e ≠ b := by
  intro e he
  simp only [parkedSweepWord, List.mem_append] at he
  rcases he with he | he
  · have hp : e ∈ cutPathEdges ring b :=
      (mem_duplicateEdges_iff e (cutPathEdges ring b)).1 he
    exact mem_cutPathEdges_ne_barrier ring b e hp
  · have hpR : e ∈ (cutPathEdges ring b).reverse :=
      (mem_duplicateEdges_iff e (cutPathEdges ring b).reverse).1 he
    have hp : e ∈ cutPathEdges ring b := by simpa using hpR
    exact mem_cutPathEdges_ne_barrier ring b e hp

theorem parked_sweep_original_sterile
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b) :
    let S := rawRun hk ring C (parkedSweepWord ring b)
    OneBarrierAt hk ring S b ∧ EndpointSterile ring S b := by
  let w := parkedSweepWord ring b
  let S := rawRun hk ring C w
  have heq : S =
      CenteredRenewal.OneBarrierCleanup.runWord hk ring C w := by
    dsimp [S]
    exact original_run_eq_centered_of_avoids_barrier
      hk ring hn2 C b w hndvd hone
      (parkedSweepWord_avoids_barrier ring b)
  have hc :=
    CenteredRenewal.OneBarrierCleanup.parkedSweepWord_endpointSterile
      hk ring hn2 C b hndvd hone
  refine ⟨?_, ?_⟩
  · change OneBarrierAt hk ring S b
    rw [heq]
    simpa [w] using hc.1
  · change EndpointSterile ring S b
    rw [heq]
    simpa [w] using hc.2

/-!
This is the source-level endpoint bridge needed before strengthening the
Multiple producer.  It deliberately takes the actual endpoint-discharge
construction, rather than an arbitrary endpoint mode or a public reduction
disjunct.  The parked-sweep theorem supplies `hsterile`; the theorem below
checks the original Protocol-6 discharge itself.
-/

theorem endpoint_discharge_unique_safe
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (S : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring S b)
    (hsterile : EndpointSterile ring S b) :
    (∃ ell, UniqueLeaderAt
      (rawRun hk ring S (endpointDischargeWord S b)) ell) →
      ¬ Dangerous (cutView ring (endpointDischargeBarrier ring S b)
        (rawRun hk ring S (endpointDischargeWord S b))) := by
  let wd := endpointDischargeWord S b
  let b' := endpointDischargeBarrier ring S b
  let D := rawRun hk ring S wd
  intro hunique
  change ¬ Dangerous (cutView ring b' D)
  cases hprobe : (S b).probe with
  | false =>
      have hD : D = S := by
        simp [D, wd, endpointDischargeWord, hprobe, rawRun]
      have hb' : b' = b := by
        simp [b', endpointDischargeBarrier, hprobe]
      rw [hD, hb']
      rw [not_dangerous_iff]
      intro p hp
      have hphys := hp
      simp only [cutView] at hphys
      by_cases hpb : cutPos ring b p = b
      · have hf : False := by
          rw [hpb, hprobe] at hphys
          cases hphys
        exact hf.elim
      · have hf : False := by
          rw [hsterile.1 _ hpb] at hphys
          cases hphys
        exact hf.elim
  | true =>
      cases hphase : (S b).phase with
      | false =>
          have hbar : IsBarrier hk (S b) (S (ring.rightNeighbor b)) :=
            (barrierAt_labelsOf_iff hk ring S b).mp
              ((hone b).2 rfl)
          have htrans :
              transition hk (S b) (S (ring.rightNeighbor b)) =
                barrierStep hk (S b) (S (ring.rightNeighbor b)) :=
            transition_of_barrier hk _ _ hbar
          have hstep :
              (protocol k hk).step ring S b =
                fun i => if i = b then
                  (barrierStep hk (S b) (S (ring.rightNeighbor b))).1
                else if i = ring.rightNeighbor b then
                  (barrierStep hk (S b) (S (ring.rightNeighbor b))).2
                else S i := by
            funext i
            simp [PopulationProtocol.step, protocol, htrans]
          have htailLeader :
              ((protocol k hk).step ring S b b).leader = true := by
            rw [hstep]
            simp [barrierStep, probeHitsBarrier, hprobe, hphase]
          have htailProbe :
              ((protocol k hk).step ring S b b).probe = false := by
            rw [hstep]
            simp [barrierStep, probeHitsBarrier, hprobe, hphase]
          have hD : D = (protocol k hk).step ring S b := by
            simp [D, wd, endpointDischargeWord, hprobe, rawRun]
            rfl
          have hb' : b' = b := by
            simp [b', endpointDischargeBarrier, hprobe, hphase]
          rw [hD, hb']
          apply not_dangerous_of_tail_leader ring
          · simpa [cutView] using htailLeader
          · simpa [cutView] using htailProbe
      | true =>
          have hbar : IsBarrier hk (S b) (S (ring.rightNeighbor b)) :=
            (barrierAt_labelsOf_iff hk ring S b).mp
              ((hone b).2 rfl)
          have htrans :
              transition hk (S b) (S (ring.rightNeighbor b)) =
                barrierStep hk (S b) (S (ring.rightNeighbor b)) :=
            transition_of_barrier hk _ _ hbar
          have hstep :
              (protocol k hk).step ring S b =
                fun i => if i = b then
                  (barrierStep hk (S b) (S (ring.rightNeighbor b))).1
                else if i = ring.rightNeighbor b then
                  (barrierStep hk (S b) (S (ring.rightNeighbor b))).2
                else S i := by
            funext i
            simp [PopulationProtocol.step, protocol, htrans]
          have hD : D = (protocol k hk).step ring S b := by
            simp [D, wd, endpointDischargeWord, hprobe, rawRun]
            rfl
          have hb' : b' = ring.rightNeighbor b := by
            simp [b', endpointDischargeBarrier, hprobe, hphase]
          rw [hD, hb']
          rw [not_dangerous_iff]
          intro p hp
          have hphys :
              (((protocol k hk).step ring S b)
                (cutPos ring (ring.rightNeighbor b) p)).probe = true := by
            simpa [cutView] using hp
          by_cases hqb : cutPos ring (ring.rightNeighbor b) p = b
          · have hf : False := by
              rw [hqb, hstep] at hphys
              cases hh : (S (ring.rightNeighbor b)).probe <;>
                simp [barrierStep, probeHitsBarrier, hprobe, hphase, hh] at hphys
            exact hf.elim
          · by_cases hqh :
                cutPos ring (ring.rightNeighbor b) p = ring.rightNeighbor b
            · have hf : False := by
                rw [hqh, hstep] at hphys
                have hne : ring.rightNeighbor b ≠ b :=
                  rightNeighbor_ne_self ring hn2 b
                have hheadProbe :
                    (S (ring.rightNeighbor b)).probe = false :=
                  hsterile.1 _ hne
                cases hh : (S (ring.rightNeighbor b)).probe with
                | false =>
                    simp [barrierStep, probeHitsBarrier, hprobe, hphase, hh,
                      hne] at hphys
                | true =>
                    have hf : False := by simpa [hheadProbe] using hh
                    exact hf.elim
              exact hf.elim
            · have hSprobe :
                  (S (cutPos ring (ring.rightNeighbor b) p)).probe = false := by
                apply hsterile.1 _
                exact hqb
              have hf : False := by
                rw [hstep] at hphys
                simp [hqb, hqh, hSprobe] at hphys
              exact hf.elim

private theorem bitCount_false {n : Nat} :
    bitCount (fun _ : Fin n => false) = 0 := by
  induction n with
  | zero => simp [bitCount]
  | succ n ih =>
      rw [bitCount_succ]
      simp [ih]

private theorem one_le_bitCount_of_true {n : Nat}
    (bits : Fin n → Bool) (i : Fin n) (hi : bits i = true) :
    1 ≤ bitCount bits := by
  let after : Fin n → Bool := fun j => if j = i then false else bits j
  have hdrop := bitCount_single_drop bits after i hi (by simp [after]) (by
    intro j hji
    simp [after, hji])
  omega

private theorem two_le_bitCount_of_two_true {n : Nat}
    (bits : Fin n → Bool) (i j : Fin n) (hi : bits i = true)
    (hj : bits j = true) (hne : j ≠ i) :
    2 ≤ bitCount bits := by
  let after : Fin n → Bool := fun x => if x = i then false else bits x
  have hafterJ : after j = true := by simp [after, hne, hj]
  have hone := one_le_bitCount_of_true after j hafterJ
  have hdrop := bitCount_single_drop bits after i hi (by simp [after]) (by
    intro x hxi
    simp [after, hxi])
  omega

private theorem leaderCount_eq_one_of_unique
    {n k : Nat} (X : Fin n → State k) (ell : Fin n)
    (hell : (X ell).leader = true)
    (hunique : ∀ i : Fin n, (X i).leader = true → i = ell) :
    leaderCount X = 1 := by
  let before : Fin n → Bool := fun _ => false
  let after : Fin n → Bool := fun i => (X i).leader
  have hbefore : before ell = false := by rfl
  have hafter : after ell = true := by simpa [after] using hell
  have hother : ∀ i, i ≠ ell → after i = before i := by
    intro i hne
    by_cases hi : (X i).leader = false
    · simp [after, before, hi]
    · have hit : (X i).leader = true := by cases h : (X i).leader <;> simp_all
      exact False.elim (hne (hunique i hit))
  have h := bitCount_single_birth before after ell hbefore hafter hother
  have hzero : bitCount before = 0 := by
    simpa [before] using (bitCount_false (n := n))
  unfold leaderCount
  change bitCount after = 1
  simpa [hzero] using h

theorem endpoint_discharge_unique_phi_one
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (S : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring S b)
    (hsterile : EndpointSterile ring S b) :
    (∃ ell, UniqueLeaderAt
      (rawRun hk ring S (endpointDischargeWord S b)) ell) →
      PhiAt ring (endpointDischargeBarrier ring S b)
        (rawRun hk ring S (endpointDischargeWord S b)) = 1 := by
  intro hunique
  have hsafe := endpoint_discharge_unique_safe hk ring hn2 S b
    hone hsterile hunique
  obtain ⟨ell, hell, huniq⟩ := hunique
  have hcutLeader :
      ((cutView ring (endpointDischargeBarrier ring S b)
        (rawRun hk ring S (endpointDischargeWord S b)))
        (cutCoord ring (endpointDischargeBarrier ring S b) ell)).leader = true := by
    simpa [cutView] using hell
  have hcutUnique :
      ∀ i : Fin n,
        ((cutView ring (endpointDischargeBarrier ring S b)
          (rawRun hk ring S (endpointDischargeWord S b))) i).leader = true →
          i = cutCoord ring (endpointDischargeBarrier ring S b) ell := by
    intro i hi
    have hphys :
        (rawRun hk ring S (endpointDischargeWord S b)
          (cutPos ring (endpointDischargeBarrier ring S b) i)).leader = true := by
      simpa [cutView] using hi
    have hsame := huniq _ hphys
    have hcoord := congrArg
      (cutCoord ring (endpointDischargeBarrier ring S b)) hsame
    simpa using hcoord
  have hcount :
      leaderCount (cutView ring (endpointDischargeBarrier ring S b)
        (rawRun hk ring S (endpointDischargeWord S b))) = 1 := by
    exact leaderCount_eq_one_of_unique _ _ hcutLeader hcutUnique
  unfold PhiAt Phi
  rw [hcount]
  simp [dangerBit, hsafe]

theorem multiple_selected_unique_endpoint_safe
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hmulti : MultipleLeaders C) :
    let ws := parkedSweepWord ring b
    let S := rawRun hk ring C ws
    let wd := endpointDischargeWord S b
    let b' := endpointDischargeBarrier ring S b
    let D := rawRun hk ring S wd
    ∀ (hunique : ∃ ell, UniqueLeaderAt D ell),
      ¬ Dangerous (cutView ring b' D) ∧ PhiAt ring b' D = 1 := by
  let ws := parkedSweepWord ring b
  let S := rawRun hk ring C ws
  let wd := endpointDischargeWord S b
  let b' := endpointDischargeBarrier ring S b
  let D := rawRun hk ring S wd
  change ∀ (hunique : ∃ ell, UniqueLeaderAt D ell),
    ¬ Dangerous (cutView ring b' D) ∧ PhiAt ring b' D = 1
  intro hunique
  have hS := parked_sweep_original_sterile hk ring (by omega) C b
    hndvd hone
  have hsafe := endpoint_discharge_unique_safe hk ring (by omega) S b
    hS.1 hS.2 hunique
  have hphi := endpoint_discharge_unique_phi_one hk ring (by omega) S b
    hS.1 hS.2 hunique
  exact ⟨hsafe, hphi⟩

theorem multiple_selected_unique_endpoint_phi_drop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hmulti : MultipleLeaders C) :
    let ws := parkedSweepWord ring b
    let S := rawRun hk ring C ws
    let wd := endpointDischargeWord S b
    let b' := endpointDischargeBarrier ring S b
    let D := rawRun hk ring S wd
    ∀ (hunique : ∃ ell, UniqueLeaderAt D ell),
      PhiAt ring b' D < PhiAt ring b C := by
  let ws := parkedSweepWord ring b
  let S := rawRun hk ring C ws
  let wd := endpointDischargeWord S b
  let b' := endpointDischargeBarrier ring S b
  let D := rawRun hk ring S wd
  change ∀ (hunique : ∃ ell, UniqueLeaderAt D ell),
    PhiAt ring b' D < PhiAt ring b C
  intro hunique
  have hsafePhi := multiple_selected_unique_endpoint_safe hk ring (by omega)
    hndvd C b hone hmulti hunique
  have hphi := hsafePhi.2
  have htwo : 2 ≤ leaderCount (cutView ring b C) := by
    rcases hmulti with ⟨i, j, hij, hi, hj⟩
    have hci :
        ((cutView ring b C) (cutCoord ring b i)).leader = true := by
      simpa [cutView] using hi
    have hcj :
        ((cutView ring b C) (cutCoord ring b j)).leader = true := by
      simpa [cutView] using hj
    have hcoord : cutCoord ring b j ≠ cutCoord ring b i := by
      intro heq
      apply hij
      simpa using (congrArg (cutPos ring b) heq).symm
    exact two_le_bitCount_of_two_true
      (fun q => ((cutView ring b C) q).leader)
      (cutCoord ring b i) (cutCoord ring b j) hci hcj hcoord
  have hparent : 2 ≤ PhiAt ring b C := by
    unfold PhiAt Phi
    exact Nat.le_trans (by omega) (Nat.le_max_right _ _)
  calc
    PhiAt ring b' D = 1 := hphi
    _ < 2 := by omega
    _ ≤ PhiAt ring b C := hparent

end AAFJPK.SelectedMultipleUniqueSafe
