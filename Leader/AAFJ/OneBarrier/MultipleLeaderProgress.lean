import Leader.AAFJ.Centered.OneBarrierCleanup
import Leader.AAFJ.NonbarrierWord

set_option autoImplicit false

namespace AAFJPK.OriginalMultipleLeaderOneBarrier

open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord
open CenteredRenewal.OneBarrierCleanup

/-- Two distinct physical leaders. -/
def MultipleLeaders {n k : Nat} (C : Fin n → State k) : Prop :=
  ∃ i j : Fin n,
    i ≠ j ∧ (C i).leader = true ∧ (C j).leader = true

/-- Exactly one physical leader, with its witness exposed. -/
def UniqueLeader {n k : Nat} (C : Fin n → State k) : Prop :=
  ∃ ell : Fin n,
    (C ell).leader = true ∧
      ∀ i : Fin n, (C i).leader = true → i = ell

/-- Controlled plateau coordinate.  It is not asserted to be one-step
monotone; it is consumed only at the endpoint of the macro below. -/
noncomputable def multiLeaderBit {n k : Nat} (C : Fin n → State k) : Nat := by
  classical
  exact if MultipleLeaders C then 1 else 0

/-- Strict lexicographic decrease of (PhiAt,multiLeaderBit), written without
depending on a library product-order API. -/
def StrictLexDrop {n k : Nat} (ring : DirectedRing n)
    (b : Fin n) (C : Fin n → State k)
    (b' : Fin n) (D : Fin n → State k) : Prop :=
  PhiAt ring b' D < PhiAt ring b C ∨
    (PhiAt ring b' D = PhiAt ring b C ∧
      multiLeaderBit D < multiLeaderBit C)

private theorem rawRun_append
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (u v : List (Fin n)) :
    rawRun hk ring C (u ++ v) =
      rawRun hk ring (rawRun hk ring C u) v := by
  induction u generalizing C with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, rawRun]
      exact ih ((AAFJPK.protocol k hk).step ring C e)

/-! ## Original/centered equality on rows where they are actually equal -/

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

private theorem original_step_eq_centered_of_barrier_phase_zero
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hphase : (C e).phase = false) :
    (AAFJPK.protocol k hk).step ring C e =
      CenteredRenewal.OneBarrierCleanup.step hk ring C e := by
  apply packaged_step_eq_of_local hk ring C e
  rw [AAFJPK.transition_of_barrier hk _ _ hbar,
    CenteredRenewal.transition_of_barrier hk _ _ hbar]
  rw [AAFJPK.barrierStep_phase_zero hk _ _ hphase,
    CenteredRenewal.barrierStep_phase_zero hk _ _ hphase]

private theorem original_step_eq_centered_of_barrier_phase_one_probe_free
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hphase : (C e).phase = true)
    (hprobe : (C (ring.rightNeighbor e)).probe = false) :
    (AAFJPK.protocol k hk).step ring C e =
      CenteredRenewal.OneBarrierCleanup.step hk ring C e := by
  apply packaged_step_eq_of_local hk ring C e
  rw [AAFJPK.transition_of_barrier hk _ _ hbar,
    CenteredRenewal.transition_of_barrier hk _ _ hbar]
  rw [AAFJPK.barrierStep_phase_one_probe_free hk _ _ hphase hprobe,
    CenteredRenewal.barrierStep_phase_one hk _ _ hphase]
  simp [hprobe]

/-- Any ordinary word avoiding the parked unique barrier has literally the
same endpoint under original Protocol 6 and the centered helper semantics. -/
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

/-! ## Pathwise OneBarrier/Phi bookkeeping for the actual original run -/

/-- Every finite original word stays in the exactly-one-barrier slice and
weakly decreases Phi when the cut witness is updated after each step. -/
theorem rawRun_oneBarrier_phi_le
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (w : List (Fin n)) :
    ∃ b' : Fin n,
      OneBarrierAt hk ring (rawRun hk ring C w) b' ∧
        PhiAt ring b' (rawRun hk ring C w) ≤ PhiAt ring b C := by
  induction w generalizing C b with
  | nil =>
      exact ⟨b, by simpa [rawRun] using hone, Nat.le_refl _⟩
  | cons e es ih =>
      let D := (AAFJPK.protocol k hk).step ring C e
      let b1 :=
        if AdvanceReady hk ring C e then ring.rightNeighbor b else b
      have hs :
          OneBarrierAt hk ring D b1 ∧
            PhiAt ring b1 D ≤ PhiAt ring b C := by
        simpa [D, b1] using
          SingleBarrierSanitation.oneBarrier_phi_step_le
            hk ring hn3 C b e hndvd hone
      obtain ⟨b2, hb2, hp2⟩ := ih D b1 hs.1
      change
        ∃ b' : Fin n,
          OneBarrierAt hk ring (rawRun hk ring D es) b' ∧
            PhiAt ring b' (rawRun hk ring D es) ≤ PhiAt ring b C
      exact ⟨b2, hb2, Nat.le_trans hp2 hs.2⟩

theorem rawRun_preserves_oneBarrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (w : List (Fin n)) :
    ∃ b' : Fin n, OneBarrierAt hk ring (rawRun hk ring C w) b' := by
  obtain ⟨b', hb', _⟩ :=
    rawRun_oneBarrier_phi_le hk ring hn3 C b hndvd hone w
  exact ⟨b', hb'⟩

/-! ## Geometry: the three inherited ordinary words really avoid the barrier -/

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

private theorem corridorAWord_avoids_barrier
    {n : Nat} (ring : DirectedRing n) (b R : Fin n)
    (hnonhead : R ≠ ring.rightNeighbor b) :
    ∀ e ∈ corridorAWord ring b R, e ≠ b := by
  let r := (cutCoord ring b R).val
  let e0 := ring.leftNeighbor R
  let backStart := ring.leftNeighbor e0
  let back := backwardEdgeWalk ring backStart (r - 1)
  have he0 : e0 ≠ b := by
    intro heb
    apply hnonhead
    have heb' : ring.leftNeighbor R = b := by simpa [e0] using heb
    rw [← rightNeighbor_leftNeighbor_clean ring R, heb']
  have hgeom := corridorA_back_geometry ring b R hnonhead
  have hord : ∀ q ∈ back, q ≠ b := by
    simpa [back, backStart, e0, r] using hgeom.2.2.1
  intro q hq
  simp only [corridorAWord, List.mem_cons, mem_duplicateEdges_iff] at hq
  rcases hq with hq | hq
  · simpa [e0] using hq ▸ he0
  · exact hord q (by simpa [back, backStart, e0, r] using hq)

private theorem finalCorridorWord_avoids_barrier
    {n : Nat} (ring : DirectedRing n) (hn3 : 3 ≤ n) (b : Fin n) :
    ∀ e ∈ finalCorridorWord ring b, e ≠ b := by
  have hn2 : 1 < n := by omega
  let e0 := ring.leftNeighbor b
  let back := backwardEdgeWalk ring (ring.leftNeighbor e0) (n - 2)
  have he0 : e0 ≠ b := by
    intro h
    have hr := congrArg ring.rightNeighbor h
    rw [rightNeighbor_leftNeighbor_clean] at hr
    exact (rightNeighbor_ne_self ring hn2 b) hr.symm
  have hgeom := finalCorridor_back_geometry ring hn3 b
  have hord : ∀ q ∈ back, q ≠ b := by
    simpa [back, e0] using hgeom.2.2.2
  intro q hq
  simp only [finalCorridorWord, List.mem_cons, mem_duplicateEdges_iff] at hq
  rcases hq with hq | hq
  · simpa [e0] using hq ▸ he0
  · exact hord q (by simpa [back, e0] using hq)

/-! ## Original parked preparation -/

private theorem original_parkedSweep_endpointSterile
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b) :
    let w := parkedSweepWord ring b
    let S := rawRun hk ring C w
    w.length = 4 * (n - 1) ∧
      OneBarrierAt hk ring S b ∧ EndpointSterile ring S b := by
  let w := parkedSweepWord ring b
  let S := rawRun hk ring C w
  have heq :
      S = CenteredRenewal.OneBarrierCleanup.runWord hk ring C w := by
    dsimp [S]
    exact original_run_eq_centered_of_avoids_barrier
      hk ring hn2 C b w hndvd hone
      (by simpa [w] using parkedSweepWord_avoids_barrier ring b)
  have hc :=
    CenteredRenewal.OneBarrierCleanup.parkedSweepWord_endpointSterile
      hk ring hn2 C b hndvd hone
  refine ⟨?_, ?_, ?_⟩
  · simpa [w] using
      CenteredRenewal.OneBarrierCleanup.parkedSweepWord_length ring b
  · change OneBarrierAt hk ring S b
    rw [heq]
    simpa [w] using hc.1
  · change EndpointSterile ring S b
    rw [heq]
    simpa [w] using hc.2

private theorem original_endpointDischarge_eq_centered
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hsterile : EndpointSterile ring C b) :
    rawRun hk ring C (endpointDischargeWord C b) =
      CenteredRenewal.OneBarrierCleanup.runWord
        hk ring C (endpointDischargeWord C b) := by
  have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).1
      (SingleBarrierSanitation.oneBarrierAt_barrier hk ring C b hone)
  have hheadProbe :
      (C (ring.rightNeighbor b)).probe = false :=
    hsterile.1 (ring.rightNeighbor b)
      (rightNeighbor_ne_self ring hn2 b)
  cases hprobe : (C b).probe with
  | false =>
      simp [endpointDischargeWord, hprobe, rawRun,
        CenteredRenewal.OneBarrierCleanup.runWord]
  | true =>
      cases hphase : (C b).phase with
      | false =>
          have heq :=
            original_step_eq_centered_of_barrier_phase_zero
              hk ring C b hbar hphase
          have heq' :
              (AAFJPK.protocol k hk).step ring C b =
                CenteredRenewal.OneBarrierCleanup.step hk ring C b := heq
          simpa [PopulationProtocol.Configuration, AAFJPK.protocol,
            CenteredRenewal.protocol, endpointDischargeWord, hprobe, rawRun,
            CenteredRenewal.OneBarrierCleanup.runWord] using heq'
      | true =>
          have heq :=
            original_step_eq_centered_of_barrier_phase_one_probe_free
              hk ring C b hbar hphase hheadProbe
          have heq' :
              (AAFJPK.protocol k hk).step ring C b =
                CenteredRenewal.OneBarrierCleanup.step hk ring C b := heq
          simpa [PopulationProtocol.Configuration, AAFJPK.protocol,
            CenteredRenewal.protocol, endpointDischargeWord, hprobe, rawRun,
            CenteredRenewal.OneBarrierCleanup.runWord] using heq'

private theorem original_endpointSterile_discharge
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b)
    (hsterile : EndpointSterile ring C b) :
    let w := endpointDischargeWord C b
    let b' := endpointDischargeBarrier ring C b
    let D := rawRun hk ring C w
    w.length ≤ 1 ∧
      OneBarrierAt hk ring D b' ∧
      PreparedAt ring D b' ∧
      ((C b).probe = true → (D b).leader = true) := by
  let w := endpointDischargeWord C b
  let b' := endpointDischargeBarrier ring C b
  let D := rawRun hk ring C w
  have heq :
      D = CenteredRenewal.OneBarrierCleanup.runWord hk ring C w := by
    dsimp [D]
    simpa [w] using
      original_endpointDischarge_eq_centered
        hk ring hn2 C b hone hsterile
  have hc :
      w.length ≤ 1 ∧
        OneBarrierAt hk ring
          (CenteredRenewal.OneBarrierCleanup.runWord hk ring C w) b' ∧
        PreparedAt ring
          (CenteredRenewal.OneBarrierCleanup.runWord hk ring C w) b' ∧
        ((C b).probe = true →
          (CenteredRenewal.OneBarrierCleanup.runWord hk ring C w b).leader =
            true) := by
    simpa [w, b'] using
      CenteredRenewal.OneBarrierCleanup.endpointSterile_discharge
        hk ring hn2 C b hndvd hone hsterile
  refine ⟨hc.1, ?_, ?_, ?_⟩
  · change OneBarrierAt hk ring D b'
    rw [heq]
    exact hc.2.1
  · change PreparedAt ring D b'
    rw [heq]
    exact hc.2.2.1
  · intro hp
    change (D b).leader = true
    rw [heq]
    exact hc.2.2.2 hp

/-! ## Actual original barrier crossing after sanitizing the head -/

private structure HeadAdvanceResult
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C D : Fin n → State k) (h : Fin n) : Prop where
  barrier : OneBarrierAt hk ring D h
  tailLeader : (D h).leader = true
  tailFresh : MarkFree (D h)
  leadersEq : ∀ i : Fin n, (D i).leader = (C i).leader

private structure ArmHeadResult
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C D : Fin n → State k) (b h : Fin n) : Prop where
  barrier : OneBarrierAt hk ring D b
  tailPhase : (D b).phase = true
  tailProbe : (D b).probe = false
  headLeader : (D h).leader = true
  headProbe : (D h).probe = (C h).probe
  leadersEq : ∀ i : Fin n, (D i).leader = (C i).leader

private theorem original_phase_one_over_probeFree_head_leader
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hphase : (C b).phase = true)
    (htailProbe : (C b).probe = false)
    (hheadProbe : (C (ring.rightNeighbor b)).probe = false)
    (hheadLeader : (C (ring.rightNeighbor b)).leader = true) :
    HeadAdvanceResult hk ring C
      ((AAFJPK.protocol k hk).step ring C b)
      (ring.rightNeighbor b) := by
  let h := ring.rightNeighbor b
  let D := (AAFJPK.protocol k hk).step ring C b
  have hbar : IsBarrier hk (C b) (C h) := by
    simpa [h] using
      (barrierAt_labelsOf_iff hk ring C b).1
        (SingleBarrierSanitation.oneBarrierAt_barrier hk ring C b hone)
  have hready : AdvanceReady hk ring C b := by
    exact ⟨hbar, hphase, by simpa [h] using hheadProbe⟩
  have honeD0 :=
    SingleBarrierSanitation.oneBarrierAt_step
      hk ring hn2 C b b hndvd hone
  have honeD : OneBarrierAt hk ring D h := by
    simpa [D, h, hready] using honeD0
  have htrans :
      AAFJPK.transition hk (C b) (C h) =
        (probeHitsBarrier (C b),
          { C h with
            label := succLabel hk (C b).label
            phase := false
            bullet := false }) := by
    rw [AAFJPK.transition_of_barrier hk _ _ hbar]
    simpa [h] using
      AAFJPK.barrierStep_phase_one_probe_free hk
        (C b) (C h) hphase (by simpa [h] using hheadProbe)
  have hl :
      (AAFJPK.transition hk (C b) (C h)).1.leader =
        (C b).leader := by
    rw [htrans]
    simp [probeHitsBarrier, htailProbe]
  have hr :
      (AAFJPK.transition hk (C b) (C h)).2.leader =
        (C h).leader := by
    rw [htrans]
  have hleaders :
      ∀ i : Fin n, (D i).leader = (C i).leader := by
    simpa [D, h] using
      SingleBarrierSanitation.step_leaders_eq_of_local
        hk ring hn2 C b hl (by simpa [h] using hr)
  have hne : h ≠ b := by
    simpa [h] using rightNeighbor_ne_self ring hn2 b
  have hDh :
      D h =
        { C h with
          label := succLabel hk (C b).label
          phase := false
          bullet := false } := by
    simp [D, h, PopulationProtocol.step, AAFJPK.protocol,
      htrans, hne]
  refine ⟨honeD, ?_, ?_, hleaders⟩
  · rw [hleaders h]
    simpa [h] using hheadLeader
  · change MarkFree (D h)
    rw [hDh]
    simp [MarkFree, hheadProbe, h]

private theorem original_phase_zero_over_head_leader
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hphase : (C b).phase = false)
    (htailProbe : (C b).probe = false)
    (hheadLeader : (C (ring.rightNeighbor b)).leader = true) :
    ArmHeadResult hk ring C
      ((AAFJPK.protocol k hk).step ring C b)
      b (ring.rightNeighbor b) := by
  let h := ring.rightNeighbor b
  let D := (AAFJPK.protocol k hk).step ring C b
  have hbar : IsBarrier hk (C b) (C h) := by
    simpa [h] using
      (barrierAt_labelsOf_iff hk ring C b).1
        (SingleBarrierSanitation.oneBarrierAt_barrier hk ring C b hone)
  have hnot : ¬ AdvanceReady hk ring C b := by
    intro hr
    exact Bool.noConfusion (hphase.symm.trans hr.2.1)
  have htrans :
      AAFJPK.transition hk (C b) (C h) =
        ({ probeHitsBarrier (C b) with phase := true }, C h) := by
    rw [AAFJPK.transition_of_barrier hk _ _ hbar]
    rw [AAFJPK.barrierStep_phase_zero hk _ _ hphase]
    have hheadLeader' : (C h).leader = true := by
      simpa [h] using hheadLeader
    simp [hheadLeader']
  have honeD0 :=
    SingleBarrierSanitation.oneBarrierAt_step
      hk ring hn2 C b b hndvd hone
  have honeD : OneBarrierAt hk ring D b := by
    simpa [D, hnot] using honeD0
  have hl :
      (AAFJPK.transition hk (C b) (C h)).1.leader =
        (C b).leader := by
    rw [htrans]
    simp [probeHitsBarrier, htailProbe]
  have hr :
      (AAFJPK.transition hk (C b) (C h)).2.leader =
        (C h).leader := by
    rw [htrans]
  have hleaders :
      ∀ i : Fin n, (D i).leader = (C i).leader := by
    simpa [D, h] using
      SingleBarrierSanitation.step_leaders_eq_of_local
        hk ring hn2 C b hl (by simpa [h] using hr)
  have hne : h ≠ b := by
    simpa [h] using rightNeighbor_ne_self ring hn2 b
  have hbState :
      D b = { probeHitsBarrier (C b) with phase := true } := by
    simp [D, h, PopulationProtocol.step, AAFJPK.protocol, htrans]
  have hhState : D h = C h := by
    simp [D, h, PopulationProtocol.step, AAFJPK.protocol, htrans, hne]
  refine ⟨honeD, ?_, ?_, ?_, ?_, hleaders⟩
  · change (D b).phase = true
    rw [hbState]
  · change (D b).probe = false
    rw [hbState]
    simp [probeHitsBarrier, htailProbe]
  · change (D h).leader = true
    rw [hhState]
    simpa [h] using hheadLeader
  · change (D h).probe = (C h).probe
    rw [hhState]

/-- Once both tail and head probes are clear, the actual original barrier
crossing needs one hit when armed and two when phase-zero. -/
private theorem original_advance_probeFree_head_leader
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (htailProbe : (C b).probe = false)
    (hheadProbe : (C (ring.rightNeighbor b)).probe = false)
    (hheadLeader : (C (ring.rightNeighbor b)).leader = true) :
    (advanceOverHeadLeaderWord C b).length ≤ 2 ∧
      HeadAdvanceResult hk ring C
        (rawRun hk ring C (advanceOverHeadLeaderWord C b))
        (ring.rightNeighbor b) := by
  cases hphase : (C b).phase with
  | true =>
      refine ⟨?_, ?_⟩
      · simp [advanceOverHeadLeaderWord, hphase]
      · simpa [advanceOverHeadLeaderWord, hphase, rawRun] using
          original_phase_one_over_probeFree_head_leader
            hk ring hn2 C b hndvd hone hphase htailProbe
              hheadProbe hheadLeader
  | false =>
      let C1 := (AAFJPK.protocol k hk).step ring C b
      have h0 :=
        original_phase_zero_over_head_leader
          hk ring hn2 C b hndvd hone hphase htailProbe hheadLeader
      have hheadProbe1 : (C1 (ring.rightNeighbor b)).probe = false := by
        have hh := h0.headProbe.trans hheadProbe
        simpa [C1] using hh
      have h1 :=
        original_phase_one_over_probeFree_head_leader
          hk ring hn2 C1 b hndvd h0.barrier h0.tailPhase h0.tailProbe
            hheadProbe1 h0.headLeader
      refine ⟨?_, ?_⟩
      · simp [advanceOverHeadLeaderWord, hphase]
      · simp only [advanceOverHeadLeaderWord, hphase, rawRun]
        change
          HeadAdvanceResult hk ring C
            ((AAFJPK.protocol k hk).step ring C1 b)
            (ring.rightNeighbor b)
        refine
          ⟨h1.barrier, h1.tailLeader, h1.tailFresh, ?_⟩
        intro i
        exact (h1.leadersEq i).trans (h0.leadersEq i)

private theorem nonBarrierStep_left_leader_eq
    {k : Nat} (u v : State k) :
    (nonBarrierStep u v).1.leader = u.leader := by
  cases hl : v.leader <;>
    cases hb : v.bullet <;>
    cases hp : u.probe <;>
    simp [nonBarrierStep, hl, hb, hp]

private theorem centered_doubleHit_initiator_leader_eq_of_nonbarrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hnb : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e))) :
    (doubleHit hk ring C e e).leader = (C e).leader := by
  have hp := doubleHit_pair_of_nonbarrier hk ring hn2 C e hnb
  have h :=
    congrArg (fun z : State k × State k => z.1.leader) hp
  simpa only [nonBarrierStep_left_leader_eq] using h

private structure CrossResult
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C D : Fin n → State k) (h : Fin n) : Prop where
  barrier : OneBarrierAt hk ring D h
  tailLeader : (D h).leader = true
  tailFresh : MarkFree (D h)
  noLeaderBirth :
    ∀ i : Fin n, (D i).leader = true → (C i).leader = true

/-- Original Protocol-6 replacement for the centered head crossing.

The first two letters are ordinary services of the old head edge.  They force
the old head probe false.  The remaining one/two letters are actual barrier
services, so the original phase-one responder-probe veto is discharged rather
than ignored. -/
theorem original_cross_head_leader
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (htailFresh : MarkFree (C b))
    (hhead : (C (ring.rightNeighbor b)).leader = true) :
    ∃ w : List (Fin n),
      w.length ≤ 4 ∧
        CrossResult hk ring C (rawRun hk ring C w)
          (ring.rightNeighbor b) := by
  have hn2 : 1 < n := by omega
  let h := ring.rightNeighbor b
  have hhne : h ≠ b := by
    simpa [h] using rightNeighbor_ne_self ring hn2 b
  have hnb :
      ¬ IsBarrier hk (C h) (C (ring.rightNeighbor h)) := by
    intro hb
    apply hhne
    exact (hone h).1
      ((barrierAt_labelsOf_iff hk ring C h).2 hb)
  have hav : ∀ e ∈ [h, h], e ≠ b := by
    intro e he
    have heh : e = h := by simpa using he
    subst e
    exact hhne
  let P := rawRun hk ring C [h, h]
  have hEqP :
      P = doubleHit hk ring C h := by
    have heq :=
      original_run_eq_centered_of_avoids_barrier
        hk ring hn2 C b [h, h] hndvd hone hav
    simpa [P, doubleHit] using heq
  have honeP : OneBarrierAt hk ring P b := by
    have hc :=
      doubleHit_parks_unique_barrier
        hk ring hn2 C b h hndvd hone hhne
    rw [← hEqP] at hc
    exact hc
  have hheadProbeP : (P h).probe = false := by
    have hc :=
      doubleHit_probe_clear_of_nonbarrier hk ring hn2 C h hnb
    rw [← hEqP] at hc
    exact hc
  have hheadLeaderP : (P h).leader = true := by
    have hc :=
      centered_doubleHit_initiator_leader_eq_of_nonbarrier
        hk ring hn2 C h hnb
    rw [← hEqP] at hc
    rw [hc]
    simpa [h] using hhead
  have hbhn :
      b ≠ ring.rightNeighbor h := by
    simpa [h] using (rightNeighbor_sq_ne_self ring hn3 b).symm
  have htailFrame : P b = C b := by
    have hc := doubleHit_frame hk ring C h b (Ne.symm hhne) hbhn
    rw [← hEqP] at hc
    exact hc
  have htailFreshP : MarkFree (P b) := by
    rw [htailFrame]
    exact htailFresh
  have hnoBirthP :
      ∀ i : Fin n, (P i).leader = true → (C i).leader = true := by
    have hc :=
      doubleHit_no_leader_birth_of_nonbarrier
        hk ring hn2 C h hnb
    intro i hi
    apply hc i
    rw [← hEqP]
    exact hi
  let w2 := advanceOverHeadLeaderWord P b
  have hadv :=
    original_advance_probeFree_head_leader
      hk ring hn2 P b hndvd honeP htailFreshP.2
        hheadProbeP hheadLeaderP
  refine ⟨[h, h] ++ w2, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    have hw2 : w2.length ≤ 2 := by simpa [w2] using hadv.1
    omega
  · rw [rawRun_append]
    change
      CrossResult hk ring C
        (rawRun hk ring P w2) (ring.rightNeighbor b)
    have ha :
        HeadAdvanceResult hk ring P
          (rawRun hk ring P w2) (ring.rightNeighbor b) := by
      simpa [w2] using hadv.2
    refine
      ⟨ha.barrier, ha.tailLeader, ha.tailFresh, ?_⟩
    intro i hi
    apply hnoBirthP i
    rw [← ha.leadersEq i]
    exact hi

/-! ## Original wrappers around the two purely ordinary corridors -/

private theorem original_corridorA_reaches_result
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b R : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hprepared : PreparedAt ring C b)
    (hR : RightmostLeader ring C b R)
    (hnonhead : R ≠ ring.rightNeighbor b) :
    let w := corridorAWord ring b R
    w.length ≤ 2 * n - 3 ∧
      CorridorAResult hk ring (rawRun hk ring C w) b R := by
  have hn2 : 1 < n := by omega
  let w := corridorAWord ring b R
  have heq :
      rawRun hk ring C w =
        CenteredRenewal.OneBarrierCleanup.runWord hk ring C w := by
    apply original_run_eq_centered_of_avoids_barrier
      hk ring hn2 C b w hndvd hone
    simpa [w] using corridorAWord_avoids_barrier ring b R hnonhead
  have hc :=
    CenteredRenewal.OneBarrierCleanup.corridorA_reaches_result
      hk ring hn3 C b R hndvd hone hprepared hR hnonhead
  refine ⟨?_, ?_⟩
  · simpa [w] using hc.1
  · rw [heq]
    simpa [w] using hc.2

private theorem original_finalCorridor_reaches_clean
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hready : FinalCorridorReady hk ring C b) :
    let w := finalCorridorWord ring b
    w.length = 2 * n - 3 ∧
      Clean hk ring (rawRun hk ring C w) := by
  have hn2 : 1 < n := by omega
  let w := finalCorridorWord ring b
  have heq :
      rawRun hk ring C w =
        CenteredRenewal.OneBarrierCleanup.runWord hk ring C w := by
    apply original_run_eq_centered_of_avoids_barrier
      hk ring hn2 C b w hndvd hready.barrier
    simpa [w] using finalCorridorWord_avoids_barrier ring hn3 b
  have hc :=
    CenteredRenewal.OneBarrierCleanup.finalCorridor_reaches_clean
      hk ring hn3 C b hndvd hready
  refine ⟨?_, ?_⟩
  · simpa [w] using hc.1
  · rw [heq]
    simpa [w] using hc.2

/-! ## At most two original head crossings after Corridor A -/

private theorem original_corridorA_head_leader_reaches_ready
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b R : Fin n) (hndvd : ¬ k ∣ n)
    (hA : CorridorAResult hk ring C b R)
    (hhead : (C (ring.rightNeighbor b)).leader = true) :
    ∃ w : List (Fin n), ∃ b' : Fin n,
      w.length ≤ 8 ∧
        FinalCorridorReady hk ring (rawRun hk ring C w) b' := by
  have hn2 : 1 < n := by omega
  have htailFresh : MarkFree (C b) := by
    exact hA.suffixFresh b (by
      have hr := (cutCoord ring b R).isLt
      simp [tailCoord]
      omega)
  obtain ⟨w1, hw1, hc1⟩ :=
    original_cross_head_leader
      hk ring hn3 C b hndvd hA.barrier htailFresh hhead
  let b1 := ring.rightNeighbor b
  let D1 := rawRun hk ring C w1
  have hc1' : CrossResult hk ring C D1 b1 := by
    simpa [D1, b1] using hc1
  by_cases hnext : (D1 (ring.rightNeighbor b1)).leader = false
  · exact ⟨w1, b1, by omega,
      ⟨hc1'.barrier, hc1'.tailLeader, hc1'.tailFresh, hnext⟩⟩
  · have hnextTrue :
        (D1 (ring.rightNeighbor b1)).leader = true := by
      cases hv : (D1 (ring.rightNeighbor b1)).leader with
      | false => exact False.elim (hnext hv)
      | true => rfl
    have hnextC :
        (C (ring.rightNeighbor b1)).leader = true :=
      hc1'.noLeaderBirth _ hnextTrue
    have hRnext : R = ring.rightNeighbor b1 := by
      rcases hA.leaders _ hnextC with hR | hb1
      · exact hR.symm
      · exact False.elim ((rightNeighbor_ne_self ring hn2 b1) hb1)
    obtain ⟨w2, hw2, hc2⟩ :=
      original_cross_head_leader
        hk ring hn3 D1 b1 hndvd hc1'.barrier
          hc1'.tailFresh hnextTrue
    let b2 := ring.rightNeighbor b1
    let D2 := rawRun hk ring D1 w2
    have hc2' : CrossResult hk ring D1 D2 b2 := by
      simpa [D2, b2] using hc2
    have hfinalHead :
        (D2 (ring.rightNeighbor b2)).leader = false := by
      cases hv : (D2 (ring.rightNeighbor b2)).leader with
      | false => rfl
      | true =>
          have hD1 :
              (D1 (ring.rightNeighbor b2)).leader = true :=
            hc2'.noLeaderBirth _ hv
          have hC :
              (C (ring.rightNeighbor b2)).leader = true :=
            hc1'.noLeaderBirth _ hD1
          rcases hA.leaders _ hC with hR | hb1
          · rw [hRnext] at hR
            exact False.elim
              ((rightNeighbor_ne_self ring hn2
                (ring.rightNeighbor b1)) (by simpa [b2] using hR))
          · exact False.elim
              ((rightNeighbor_sq_ne_self ring hn3 b1)
                (by simpa [b2] using hb1))
    refine ⟨w1 ++ w2, b2, ?_, ?_⟩
    · rw [List.length_append]
      omega
    · rw [rawRun_append]
      exact
        ⟨hc2'.barrier, hc2'.tailLeader,
          hc2'.tailFresh, hfinalHead⟩

/-! ## Prepared multiple leaders always clean up -/

theorem prepared_multipleLeaders_reaches_clean
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hprepared : PreparedAt ring C b)
    (hmulti : MultipleLeaders C) :
    ∃ w : List (Fin n),
      w.length ≤ 4 * n + 2 ∧
        Clean hk ring (rawRun hk ring C w) := by
  classical
  rcases hmulti with ⟨i0, j0, hij, hi0, hj0⟩
  have hHas : ∃ i : Fin n, (C i).leader = true := ⟨i0, hi0⟩
  obtain ⟨R, hR⟩ := exists_rightmostLeader ring C b hHas
  have hnonhead : R ≠ ring.rightNeighbor b := by
    intro h
    subst R
    have hu := rightmost_head_is_unique ring C b hR
    have hi := hu i0 hi0
    have hj := hu j0 hj0
    exact hij (hi.trans hj.symm)
  let wA := corridorAWord ring b R
  let A := rawRun hk ring C wA
  have hA :=
    original_corridorA_reaches_result
      hk ring hn3 C b R hndvd hone hprepared hR hnonhead
  have hA' : CorridorAResult hk ring A b R := by
    simpa [A, wA] using hA.2
  by_cases hhead : (A (ring.rightNeighbor b)).leader = false
  · refine ⟨wA, ?_, ?_⟩
    · have hwA : wA.length ≤ 2 * n - 3 := by
        simpa [wA] using hA.1
      omega
    · exact corridorA_clean_of_head_follower hk ring A b R hA' hhead
  · have hheadTrue :
        (A (ring.rightNeighbor b)).leader = true := by
      cases hv : (A (ring.rightNeighbor b)).leader with
      | false => exact False.elim (hhead hv)
      | true => rfl
    obtain ⟨wm, b', hwm, hready⟩ :=
      original_corridorA_head_leader_reaches_ready
        hk ring hn3 A b R hndvd hA' hheadTrue
    have hfinal :=
      original_finalCorridor_reaches_clean
        hk ring hn3 (rawRun hk ring A wm) b' hndvd hready
    let wf := finalCorridorWord ring b'
    refine ⟨wA ++ wm ++ wf, ?_, ?_⟩
    · simp only [List.length_append]
      have hwA : wA.length ≤ 2 * n - 3 := by
        simpa [wA] using hA.1
      have hwf : wf.length = 2 * n - 3 := by
        simpa [wf] using hfinal.1
      omega
    · rw [rawRun_append, rawRun_append]
      simpa [A, wf] using hfinal.2

/-! ## Global multiple-leader progress -/

/-- From an arbitrary original one-barrier state with at least two leaders,
there is one bounded literal macro.  Every prefix remains in the one-barrier
slice by rawRun_preserves_oneBarrier.  The endpoint either is Clean, has a
genuine unique physical leader, or strictly lowers the controlled lexicographic
rank (PhiAt,multiLeaderBit). -/
theorem multipleLeader_oneBarrier_progress
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b : Fin n) (hndvd : ¬ k ∣ n)
    (hone : OneBarrierAt hk ring C b)
    (hmulti : MultipleLeaders C) :
    ∃ w : List (Fin n), ∃ b' : Fin n,
      w.length ≤ 8 * n - 1 ∧
      OneBarrierAt hk ring (rawRun hk ring C w) b' ∧
      (Clean hk ring (rawRun hk ring C w) ∨
        UniqueLeader (rawRun hk ring C w) ∨
        StrictLexDrop ring b C b' (rawRun hk ring C w)) := by
  classical
  have hn2 : 1 < n := by omega
  let ws := parkedSweepWord ring b
  let S := rawRun hk ring C ws
  have hsweep :=
    original_parkedSweep_endpointSterile
      hk ring hn2 C b hndvd hone
  have hws : ws.length = 4 * (n - 1) := by
    simpa [ws] using hsweep.1
  have honeS : OneBarrierAt hk ring S b := by
    simpa [S, ws] using hsweep.2.1
  have hsterileS : EndpointSterile ring S b := by
    simpa [S, ws] using hsweep.2.2
  let wd := endpointDischargeWord S b
  let b' := endpointDischargeBarrier ring S b
  let D := rawRun hk ring S wd
  have hdis :=
    original_endpointSterile_discharge
      hk ring hn2 S b hndvd honeS hsterileS
  have hwd : wd.length ≤ 1 := by
    simpa [wd] using hdis.1
  have honeD : OneBarrierAt hk ring D b' := by
    simpa [D, b', wd] using hdis.2.1
  have hpreparedD : PreparedAt ring D b' := by
    simpa [D, b', wd] using hdis.2.2.1
  have hprepRun :
      rawRun hk ring C (ws ++ wd) = D := by
    simpa [S, D] using rawRun_append hk ring C ws wd
  by_cases hmultiD : MultipleLeaders D
  · obtain ⟨wt, hwt, hclean⟩ :=
      prepared_multipleLeaders_reaches_clean
        hk ring hn3 D b' hndvd honeD hpreparedD hmultiD
    let w := ws ++ wd ++ wt
    have hrun :
        rawRun hk ring C w = rawRun hk ring D wt := by
      dsimp [w]
      rw [rawRun_append, rawRun_append]
    have hcleanFinal : Clean hk ring (rawRun hk ring C w) := by
      rw [hrun]
      exact hclean
    obtain ⟨bout, hbout⟩ :=
      rawRun_preserves_oneBarrier
        hk ring hn3 C b hndvd hone w
    refine ⟨w, bout, ?_, hbout, Or.inl hcleanFinal⟩
    dsimp [w]
    simp only [List.length_append]
    omega
  · by_cases hHasD : ∃ ell : Fin n, (D ell).leader = true
    · obtain ⟨ell, hell⟩ := hHasD
      have hUniqueD : UniqueLeader D := by
        refine ⟨ell, hell, ?_⟩
        intro i hi
        by_cases hie : i = ell
        · exact hie
        · exact False.elim (hmultiD ⟨i, ell, hie, hi, hell⟩)
      have honeFinal :
          OneBarrierAt hk ring (rawRun hk ring C (ws ++ wd)) b' := by
        rw [hprepRun]
        exact honeD
      have hUniqueFinal :
          UniqueLeader (rawRun hk ring C (ws ++ wd)) := by
        rw [hprepRun]
        exact hUniqueD
      refine ⟨ws ++ wd, b', ?_, honeFinal,
        Or.inr (Or.inl hUniqueFinal)⟩
      rw [List.length_append]
      omega
    · have hzeroD : ∀ i : Fin n, (D i).leader = false := by
        intro i
        cases hi : (D i).leader with
        | false => rfl
        | true => exact False.elim (hHasD ⟨i, hi⟩)
      have hmono0 :=
        rawRun_oneBarrier_phi_le
          hk ring hn3 C b hndvd hone (ws ++ wd)
      obtain ⟨bm, hbm, hphi⟩ := hmono0
      rw [hprepRun] at hbm hphi
      have hbmEq : bm = b' := by
        apply (honeD bm).1
        exact SingleBarrierSanitation.oneBarrierAt_barrier
          hk ring D bm hbm
      subst bm
      have hlexD : StrictLexDrop ring b C b' D := by
        by_cases hlt : PhiAt ring b' D < PhiAt ring b C
        · exact Or.inl hlt
        · refine Or.inr ⟨by omega, ?_⟩
          simp [multiLeaderBit, hmulti, hmultiD]
      have honeFinal :
          OneBarrierAt hk ring (rawRun hk ring C (ws ++ wd)) b' := by
        rw [hprepRun]
        exact honeD
      have hlexFinal :
          StrictLexDrop ring b C b'
            (rawRun hk ring C (ws ++ wd)) := by
        rw [hprepRun]
        exact hlexD
      refine ⟨ws ++ wd, b', ?_, honeFinal,
        Or.inr (Or.inr hlexFinal)⟩
      rw [List.length_append]
      omega

#print axioms rawRun_oneBarrier_phi_le
#print axioms original_cross_head_leader
#print axioms prepared_multipleLeaders_reaches_clean
#print axioms multipleLeader_oneBarrier_progress

end AAFJPK.OriginalMultipleLeaderOneBarrier
