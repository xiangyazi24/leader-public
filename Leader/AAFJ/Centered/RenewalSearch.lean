import Leader.AAFJ.Centered.RankMonotone
import Leader.AAFJ.Centered.OneBarrierCleanup
import Leader.AAFJ.Centered.NoDropLaterShield
import Leader.Core.PredictableTargetCounterFiniteTree
import Leader.Core.PayloadFiniteStoppingTree

/-!
# Deterministic renewal search above the one-barrier rank floor

This file proves the literal covered/debt protocol laws used above the
one-barrier rank floor.  The main search state accepts arbitrary scheduler
interactions and counts only genuine centered barrier advances.  It separates
the first-leg bare ahead witness from the second-leg swept-origin witness.

An earlier controlled barrier-only circuit is retained as a local deterministic
brick.  Its word is an explicit consecutive schedule and is not used as a
stochastic or arbitrary-interleaving runtime theorem.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace RenewalSearch

open FiniteUniformStoppingTree
open PredictableTargetCounterFiniteTree
open PayloadFiniteStoppingTree

open BarrierAlgebra
open SingleBarrierSanitation
open OneBarrierCleanup
open NoDropLaterShield

set_option autoImplicit false

/-- One actual barrier advance: an unarmed tail is first armed, then the same
physical barrier is hit again. -/
def barrierAdvanceWord {n k : Nat} (C : Fin n -> State k) (b : Fin n) :
    List (Fin n) :=
  if (C b).phase then [b] else [b, b]

def barrierAdvanceConfig {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (b : Fin n) :
    Fin n -> State k :=
  runWord hk ring C (barrierAdvanceWord C b)

@[simp] theorem barrierAdvanceWord_length_le_two {n k : Nat}
    (C : Fin n -> State k) (b : Fin n) :
    (barrierAdvanceWord C b).length <= 2 := by
  cases hphase : (C b).phase <;> simp [barrierAdvanceWord, hphase]

/-- Neither centered barrier phase deletes an already present leader. -/
theorem barrier_hit_preserves_leaders {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (b : Fin n)
    (hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b))) :
    forall i : Fin n, (C i).leader = true ->
      (step hk ring C b i).leader = true := by
  intro i hi
  have htrans : CenteredRenewal.transition hk (C b)
      (C (ring.rightNeighbor b)) =
      CenteredRenewal.barrierStep hk (C b) (C (ring.rightNeighbor b)) :=
    CenteredRenewal.transition_of_barrier hk _ _ hbar
  have hre := rightNeighbor_ne_self ring hn2 b
  by_cases hib : i = b
  · subst i
    cases hphase : (C b).phase <;>
      cases hprobe : (C b).probe <;>
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
        CenteredRenewal.barrierStep, hphase, probeHitsBarrier, hprobe] <;>
      exact hi
  · by_cases hih : i = ring.rightNeighbor b
    · subst i
      cases hphase : (C b).phase <;>
        simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
          CenteredRenewal.barrierStep, hphase, hre, hi]
    · simpa [step, PopulationProtocol.step, CenteredRenewal.protocol, hib,
        hih] using hi

/-- A phase-zero hit arms the old barrier tail. -/
theorem barrier_phase_zero_arms_tail {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (_hn2 : 1 < n)
    (C : Fin n -> State k) (b : Fin n)
    (hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)))
    (hphase : (C b).phase = false) :
    (step hk ring C b b).phase = true := by
  have htrans : CenteredRenewal.transition hk (C b)
      (C (ring.rightNeighbor b)) =
      CenteredRenewal.barrierStep hk (C b) (C (ring.rightNeighbor b)) :=
    CenteredRenewal.transition_of_barrier hk _ _ hbar
  simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
    CenteredRenewal.barrierStep, hphase]

/-- A barrier hit cannot introduce a mobile mark away from its responder. -/
theorem barrier_hit_preserves_markFree_of_ne_head {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (_hn2 : 1 < n)
    (C : Fin n -> State k) (b i : Fin n)
    (hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)))
    (hihead : i ≠ ring.rightNeighbor b) (hfree : MarkFree (C i)) :
    MarkFree (step hk ring C b i) := by
  have htrans : CenteredRenewal.transition hk (C b)
      (C (ring.rightNeighbor b)) =
      CenteredRenewal.barrierStep hk (C b) (C (ring.rightNeighbor b)) :=
    CenteredRenewal.transition_of_barrier hk _ _ hbar
  by_cases hib : i = b
  · subst i
    rcases hfree with ⟨hbullet, hprobe⟩
    cases hphase : (C b).phase <;>
      simp [MarkFree, step, PopulationProtocol.step,
        CenteredRenewal.protocol, htrans, CenteredRenewal.barrierStep, hphase,
        probeHitsBarrier, hbullet, hprobe]
  · unfold step PopulationProtocol.step
    simp [hib, hihead, hfree]

/-- Literal one-macro package: exact successor barrier, sanitized new tail,
leader persistence, and pathwise rank monotonicity. -/
theorem barrierAdvance_spec {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b) :
    let D := barrierAdvanceConfig hk ring C b
    OneBarrierAt hk ring D (ring.rightNeighbor b) /\
      MarkFree (D (ring.rightNeighbor b)) /\
      (forall i : Fin n, (C i).leader = true -> (D i).leader = true) /\
      PhiAt ring (ring.rightNeighbor b) D <= PhiAt ring b C := by
  have hn2 : 1 < n := by omega
  have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).mp ((hone b).2 rfl)
  cases hphase : (C b).phase with
  | true =>
      have honeD := barrier_phase_one_advances_unique_barrier hk ring hn2 C b
        hndvd hone hphase
      have hfresh := advance_sanitizes_new_tail hk ring hn2 C b hone hphase
      have hleaders := barrier_hit_preserves_leaders hk ring hn2 C b hbar
      have hrank := Rank.oneBarrier_phi_step_le hk ring hn3 C b b hndvd hone
      have hready : CenteredRenewal.AdvanceReady hk ring C b :=
        ⟨hbar, hphase⟩
      simp only [barrierAdvanceConfig, barrierAdvanceWord, hphase,
        ↓reduceIte, runWord_cons, runWord_nil]
      refine ⟨honeD, ⟨hfresh.2.1, hfresh.2.2⟩, hleaders, ?_⟩
      simpa [hready, step] using hrank.2
  | false =>
      let C1 := step hk ring C b
      have hone1 := barrier_phase_zero_keeps_unique_barrier hk ring hn2 C b
        hndvd hone hphase
      have hphase1 : (C1 b).phase = true :=
        barrier_phase_zero_arms_tail hk ring hn2 C b hbar hphase
      have hbar1 : IsBarrier hk (C1 b) (C1 (ring.rightNeighbor b)) :=
        (barrierAt_labelsOf_iff hk ring C1 b).mp ((hone1 b).2 rfl)
      have honeD := barrier_phase_one_advances_unique_barrier hk ring hn2 C1 b
        hndvd hone1 hphase1
      have hfresh := advance_sanitizes_new_tail hk ring hn2 C1 b hone1 hphase1
      have hleaders0 := barrier_hit_preserves_leaders hk ring hn2 C b hbar
      have hleaders1 := barrier_hit_preserves_leaders hk ring hn2 C1 b hbar1
      have hrank0 := Rank.oneBarrier_phi_step_le hk ring hn3 C b b hndvd hone
      have hrank1 := Rank.oneBarrier_phi_step_le hk ring hn3 C1 b b hndvd hone1
      simp only [barrierAdvanceConfig, barrierAdvanceWord, hphase,
        Bool.false_eq_true, ↓reduceIte, runWord_cons, runWord_nil]
      refine ⟨honeD, ⟨hfresh.2.1, hfresh.2.2⟩, ?_, ?_⟩
      · intro i hi
        exact hleaders1 i (hleaders0 i hi)
      · have hready0 : ¬ CenteredRenewal.AdvanceReady hk ring C b := by
          intro h
          exact Bool.noConfusion (h.2.symm.trans hphase)
        have hready1 : CenteredRenewal.AdvanceReady hk ring C1 b := by
          exact ⟨hbar1, hphase1⟩
        have h0 : PhiAt ring b C1 <= PhiAt ring b C := by
          simpa [hready0, C1, step] using hrank0.2
        have h1 : PhiAt ring (ring.rightNeighbor b) (step hk ring C1 b) <=
            PhiAt ring b C1 := by
          simpa [hready1, step] using hrank1.2
        exact Nat.le_trans h1 h0

/-- A complete advance macro preserves every pre-existing mark-free vertex.
The only temporary mark which phase zero may create is on the responder, and
the mandatory phase-one hit immediately sanitizes that same vertex. -/
theorem barrierAdvance_preserves_markFree {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (b i : Fin n)
    (hone : OneBarrierAt hk ring C b) (hfree : MarkFree (C i)) :
    MarkFree (barrierAdvanceConfig hk ring C b i) := by
  have hn2 : 1 < n := by omega
  have hbar : IsBarrier hk (C b) (C (ring.rightNeighbor b)) :=
    (barrierAt_labelsOf_iff hk ring C b).mp ((hone b).2 rfl)
  by_cases hihead : i = ring.rightNeighbor b
  · subst i
    exact (barrierAdvance_spec hk ring hn3 hndvd C b hone).2.1
  · cases hphase : (C b).phase with
    | true =>
        simpa [barrierAdvanceConfig, barrierAdvanceWord, hphase] using
          barrier_hit_preserves_markFree_of_ne_head hk ring hn2 C b i hbar
            hihead hfree
    | false =>
        let C1 := step hk ring C b
        have hone1 := barrier_phase_zero_keeps_unique_barrier hk ring hn2 C b
          hndvd hone hphase
        have hbar1 : IsBarrier hk (C1 b) (C1 (ring.rightNeighbor b)) :=
          (barrierAt_labelsOf_iff hk ring C1 b).mp ((hone1 b).2 rfl)
        have hfree1 : MarkFree (C1 i) :=
          barrier_hit_preserves_markFree_of_ne_head hk ring hn2 C b i hbar
            hihead hfree
        have hfree2 := barrier_hit_preserves_markFree_of_ne_head hk ring hn2
          C1 b i hbar1 hihead hfree1
        simpa [barrierAdvanceConfig, barrierAdvanceWord, hphase, C1] using hfree2

/-! ## Adaptive complete barrier circuit -/

/-- Execute `fuel` successive physical barrier advances.  The word depends on
the phase seen at each successive tail, but every letter is a literal protocol
interaction. -/
def barrierCircuitWord {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) :
    (Fin n -> State k) -> Fin n -> Nat -> List (Fin n)
  | _, _, 0 => []
  | C, b, fuel + 1 =>
      let first := barrierAdvanceWord C b
      let D := runWord hk ring C first
      first ++ barrierCircuitWord hk ring D (ring.rightNeighbor b) fuel

def barrierCircuitConfig {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (b : Fin n)
    (fuel : Nat) : Fin n -> State k :=
  runWord hk ring C (barrierCircuitWord hk ring C b fuel)

/-- Physical barrier after a given number of genuine advances. -/
def barrierAfter {n : Nat} (ring : DirectedRing n) : Fin n -> Nat -> Fin n
  | b, 0 => b
  | b, fuel + 1 => barrierAfter ring (ring.rightNeighbor b) fuel

@[simp] theorem barrierAfter_zero {n : Nat} (ring : DirectedRing n)
    (b : Fin n) : barrierAfter ring b 0 = b := rfl

@[simp] theorem barrierAfter_succ {n : Nat} (ring : DirectedRing n)
    (b : Fin n) (fuel : Nat) :
    barrierAfter ring b (fuel + 1) =
      barrierAfter ring (ring.rightNeighbor b) fuel := rfl

theorem barrierAfter_eq_cwPos {n : Nat} (ring : DirectedRing n)
    (b : Fin n) : forall fuel,
    barrierAfter ring b fuel = cwPos ring b fuel := by
  intro fuel
  induction fuel generalizing b with
  | zero =>
      apply Fin.ext
      simp [barrierAfter, cwPos, Nat.mod_eq_of_lt b.isLt]
  | succ fuel ih =>
      rw [barrierAfter_succ, ih, cwPos_rightNeighbor]

@[simp] theorem barrierAfter_period {n : Nat} (ring : DirectedRing n)
    (b : Fin n) : barrierAfter ring b n = b := by
  rw [barrierAfter_eq_cwPos, cwPos_period]

/-- During one complete circuit every physical vertex is a new barrier tail. -/
theorem exists_barrierAfter_eq {n : Nat} (ring : DirectedRing n)
    (b i : Fin n) :
    exists t, 1 <= t /\ t <= n /\ barrierAfter ring b t = i := by
  let d := cwDist ring b i
  by_cases hd : d = 0
  · refine ⟨n, ring.hn, Nat.le_refl _, ?_⟩
    rw [barrierAfter_period]
    have hpos := cwPos_cwDist ring b i
    change cwDist ring b i = 0 at hd
    rw [hd] at hpos
    have hzero : cwPos ring b 0 = b := by
      apply Fin.ext
      simp [cwPos, Nat.mod_eq_of_lt b.isLt]
    rw [hzero] at hpos
    exact hpos
  · refine ⟨d, Nat.pos_of_ne_zero hd, Nat.le_of_lt (cwDist_lt ring b i), ?_⟩
    rw [barrierAfter_eq_cwPos]
    exact cwPos_cwDist ring b i

/-- The vertices which have already served as sanitized new barrier tails. -/
def VisitedFresh {n k : Nat} (ring : DirectedRing n)
    (C : Fin n -> State k) (start : Fin n) (fuel : Nat) : Prop :=
  forall t, 1 <= t -> t <= fuel -> MarkFree (C (barrierAfter ring start t))

@[simp] theorem barrierCircuitWord_zero {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (b : Fin n) :
    barrierCircuitWord hk ring C b 0 = [] := rfl

theorem barrierCircuitWord_length_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (b : Fin n) :
    forall fuel,
      (barrierCircuitWord hk ring C b fuel).length <= 2 * fuel := by
  intro fuel
  induction fuel generalizing C b with
  | zero => simp
  | succ fuel ih =>
      simp only [barrierCircuitWord, List.length_append]
      have hfirst := barrierAdvanceWord_length_le_two C b
      have htail := ih
        (runWord hk ring C (barrierAdvanceWord C b))
        (ring.rightNeighbor b)
      omega

theorem barrierCircuitConfig_succ {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (b : Fin n)
    (fuel : Nat) :
    barrierCircuitConfig hk ring C b (fuel + 1) =
      barrierCircuitConfig hk ring (barrierAdvanceConfig hk ring C b)
        (ring.rightNeighbor b) fuel := by
  unfold barrierCircuitConfig barrierAdvanceConfig
  simp only [barrierCircuitWord, runWord_append]

/-- Complete inductive circuit package. -/
theorem barrierCircuit_spec {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (b : Fin n) (hone : OneBarrierAt hk ring C b) :
    forall fuel,
      let D := barrierCircuitConfig hk ring C b fuel
      OneBarrierAt hk ring D (barrierAfter ring b fuel) /\
        (forall i : Fin n, (C i).leader = true -> (D i).leader = true) /\
        PhiAt ring (barrierAfter ring b fuel) D <= PhiAt ring b C /\
        (forall i : Fin n, MarkFree (C i) -> MarkFree (D i)) /\
        VisitedFresh ring D b fuel := by
  intro fuel
  induction fuel generalizing C b with
  | zero =>
      refine ⟨hone, fun _ h => h, Nat.le_refl _, fun _ h => h, ?_⟩
      intro t ht hzero
      omega
  | succ fuel ih =>
      let C1 := barrierAdvanceConfig hk ring C b
      have hfirst := barrierAdvance_spec hk ring hn3 hndvd C b hone
      have htail := ih C1 (ring.rightNeighbor b) hfirst.1
      rw [barrierCircuitConfig_succ]
      refine ⟨htail.1, ?_, ?_, ?_, ?_⟩
      · intro i hi
        exact htail.2.1 i (hfirst.2.2.1 i hi)
      · exact Nat.le_trans htail.2.2.1 hfirst.2.2.2
      · intro i hi
        exact htail.2.2.2.1 i
          (barrierAdvance_preserves_markFree hk ring hn3 hndvd C b i hone hi)
      · intro t htpos htle
        cases t with
        | zero => omega
        | succ t =>
            cases t with
            | zero =>
                change MarkFree
                  (barrierCircuitConfig hk ring C1 (ring.rightNeighbor b) fuel
                    (ring.rightNeighbor b))
                exact htail.2.2.2.1 (ring.rightNeighbor b) hfirst.2.1
            | succ t =>
                change MarkFree
                  (barrierCircuitConfig hk ring C1 (ring.rightNeighbor b) fuel
                    (barrierAfter ring (ring.rightNeighbor b) (t + 1)))
                exact htail.2.2.2.2 (t + 1) (by omega) (by omega)

/-- One complete physical barrier circuit makes every vertex mark-free. -/
theorem fullCircuit_all_markFree {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (b : Fin n) (hone : OneBarrierAt hk ring C b) :
    forall i : Fin n,
      MarkFree (barrierCircuitConfig hk ring C b n i) := by
  intro i
  obtain ⟨t, htpos, htle, ht⟩ := exists_barrierAfter_eq ring b i
  have hspec := barrierCircuit_spec hk ring hn3 hndvd C b hone n
  rw [← ht]
  exact hspec.2.2.2.2 t htpos htle

/-- The complete circuit returns the literal barrier to its starting edge. -/
theorem fullCircuit_oneBarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (b : Fin n) (hone : OneBarrierAt hk ring C b) :
    OneBarrierAt hk ring (barrierCircuitConfig hk ring C b n) b := by
  simpa using (barrierCircuit_spec hk ring hn3 hndvd C b hone n).1

/-! ## Arbitrary-interleaving advance traces -/

/-- Physical unique-barrier witness after one arbitrary scheduler step. -/
def postStepBarrier {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n -> State k) (b selected : Fin n) : Fin n :=
  if CenteredRenewal.AdvanceReady hk ring C selected then
    ring.rightNeighbor b else b

/-- A trace contains arbitrary literal centered interactions and counts only
genuine phase-one barrier advances. -/
inductive AdvanceTrace {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) :
    (Fin n -> State k) -> Fin n -> (Fin n -> State k) -> Fin n -> Nat -> Prop
  | refl (C : Fin n -> State k) (b : Fin n) :
      AdvanceTrace hk ring C b C b 0
  | step {C D : Fin n -> State k} {b d : Fin n} {a : Nat}
      (trace : AdvanceTrace hk ring C b D d a) (selected : Fin n) :
      AdvanceTrace hk ring C b (step hk ring D selected)
        (postStepBarrier hk ring D d selected)
        (a + if CenteredRenewal.AdvanceReady hk ring D selected then 1 else 0)

/-- Every arbitrary-interleaving trace retains the literal one-barrier witness
and is pathwise rank-nonincreasing. -/
theorem AdvanceTrace.oneBarrier_rank_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {C D : Fin n -> State k} {b d : Fin n} {a : Nat}
    (trace : AdvanceTrace hk ring C b D d a)
    (hone : OneBarrierAt hk ring C b) :
    OneBarrierAt hk ring D d /\ PhiAt ring d D <= PhiAt ring b C := by
  induction trace with
  | refl => exact ⟨hone, Nat.le_refl _⟩
  | step trace selected ih =>
      have hprev := ih hone
      have hnext := Rank.oneBarrier_phi_step_le hk ring hn3 _ _ selected
        hndvd hprev.1
      refine ⟨?_, Nat.le_trans hnext.2 hprev.2⟩
      simpa [postStepBarrier, OneBarrierCleanup.step] using hnext.1

/-- Exact arithmetic shape of any rank plateau above the floor. -/
theorem plateau_shape {n k r : Nat} (X : Fin n -> State k)
    (hr : Phi X = r) (hr1 : 1 < r) :
    (¬ Dangerous X /\ leaderCount X = r) \/
      (Dangerous X /\ leaderCount X + 1 = r) := by
  by_cases hd : Dangerous X
  · right
    refine ⟨hd, ?_⟩
    simp [Phi, dangerBit, hd] at hr
    omega
  · left
    refine ⟨hd, ?_⟩
    simp [Phi, dangerBit, hd] at hr
    omega

theorem plateau_shape_at {n k r : Nat} (ring : DirectedRing n)
    (C : Fin n -> State k) (tail : Fin n)
    (hr : PhiAt ring tail C = r) (hr1 : 1 < r) :
    (¬ Dangerous (cutView ring tail C) /\
        leaderCount (cutView ring tail C) = r) \/
      (Dangerous (cutView ring tail C) /\
        leaderCount (cutView ring tail C) + 1 = r) :=
  plateau_shape (cutView ring tail C) hr hr1

/-- Pure rank arithmetic for two states on the same plateau.  The only
possible shape changes are one unit of leader debt (`D : 0 -> 1`) or one unit
of compensating leader birth (`D : 1 -> 0`). -/
theorem plateau_transition_shapes {n k r : Nat}
    (before after : Fin n -> State k)
    (hbefore : Phi before = r) (hafter : Phi after = r) (hr1 : 1 < r) :
    ((Dangerous before <-> Dangerous after) /\
        leaderCount after = leaderCount before) \/
      (¬ Dangerous before /\ Dangerous after /\
        leaderCount after + 1 = leaderCount before) \/
      (Dangerous before /\ ¬ Dangerous after /\
        leaderCount after = leaderCount before + 1) := by
  have hb := plateau_shape before hbefore hr1
  have ha := plateau_shape after hafter hr1
  rcases hb with hb | hb <;> rcases ha with ha | ha
  · left
    refine ⟨⟨fun h => False.elim (hb.1 h), fun h => False.elim (ha.1 h)⟩,
      ?_⟩
    omega
  · right; left
    exact ⟨hb.1, ha.1, by omega⟩
  · right; right
    exact ⟨hb.1, ha.1, by omega⟩
  · left
    refine ⟨⟨fun _ => ha.1, fun _ => hb.1⟩, ?_⟩
    omega

/-- Pointwise inclusion of true bits gives count monotonicity. -/
theorem bitCount_le_of_true_imp {n : Nat} (a b : Fin n -> Bool)
    (himp : forall i, b i = true -> a i = true) :
    bitCount b <= bitCount a := by
  induction n with
  | zero => simp [bitCount]
  | succ n ih =>
      rw [bitCount_succ, bitCount_succ]
      have htail := ih (fun i : Fin n => a i.succ)
        (fun i : Fin n => b i.succ) (fun i => himp i.succ)
      cases ha : a 0 <;> cases hb : b 0
      · simpa [ha, hb] using htail
      · have hfalse := himp 0 (by simp [hb])
        simp [ha] at hfalse
      · simpa [ha, hb, Nat.add_comm] using
          Nat.le_trans htail (Nat.le_succ _)
      · simpa [ha, hb] using Nat.succ_le_succ htail

theorem exists_true_of_bitCount_pos {n : Nat} (bits : Fin n -> Bool)
    (hpos : 0 < bitCount bits) : exists i : Fin n, bits i = true := by
  induction n with
  | zero => simp [bitCount] at hpos
  | succ n ih =>
      rw [bitCount_succ] at hpos
      cases hhead : bits 0
      · have htail : 0 < bitCount (fun i : Fin n => bits i.succ) := by
          simp [hhead] at hpos
          exact hpos
        obtain ⟨i, hi⟩ := ih (fun i : Fin n => bits i.succ) htail
        exact ⟨i.succ, hi⟩
      · exact ⟨0, hhead⟩

theorem exists_two_true_of_two_le_bitCount {n : Nat} (bits : Fin n -> Bool)
    (htwo : 2 <= bitCount bits) :
    exists i j : Fin n, i ≠ j /\ bits i = true /\ bits j = true := by
  induction n with
  | zero => simp [bitCount] at htwo
  | succ n ih =>
      rw [bitCount_succ] at htwo
      cases hhead : bits 0
      · have htail : 2 <= bitCount (fun i : Fin n => bits i.succ) := by
          simp [hhead] at htwo
          exact htwo
        obtain ⟨i, j, hne, hi, hj⟩ := ih
          (fun i : Fin n => bits i.succ) htail
        exact ⟨i.succ, j.succ, fun h => hne (Fin.succ_inj.mp h), hi, hj⟩
      · have htail : 0 < bitCount (fun i : Fin n => bits i.succ) := by
          simp [hhead] at htwo
          omega
        obtain ⟨i, hi⟩ := exists_true_of_bitCount_pos
          (fun i : Fin n => bits i.succ) htail
        exact ⟨0, i.succ, (Fin.succ_ne_zero i).symm, hhead, hi⟩

/-- A nonbarrier centered interaction cannot increase the physical leader
count. -/
theorem nonbarrier_step_leaderCount_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (selected : Fin n)
    (hbar : ¬ IsBarrier hk (C selected)
      (C (ring.rightNeighbor selected))) :
    leaderCount (step hk ring C selected) <= leaderCount C := by
  apply bitCount_le_of_true_imp
  intro i hi
  exact step_no_leader_birth_of_nonbarrier hk ring hn2 C selected hbar i hi

/-- Exact physical payload of a compensating plateau birth. -/
structure CompensatingTailBirth {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (before after : Fin n -> State k)
    (tail selected : Fin n) : Prop where
  selected_tail : selected = tail
  tail_probe : (before tail).probe = true
  tail_follower : (before tail).leader = false
  tail_born : (after tail).leader = true
  tail_probe_cleared : (after tail).probe = false
  other_leaders : forall i : Fin n, i ≠ tail ->
    (after i).leader = (before i).leader

theorem barrier_hit_other_leaders_eq {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (tail i : Fin n)
    (hbar : IsBarrier hk (C tail) (C (ring.rightNeighbor tail)))
    (hitail : i ≠ tail) :
    (step hk ring C tail i).leader = (C i).leader := by
  have htrans : CenteredRenewal.transition hk (C tail)
      (C (ring.rightNeighbor tail)) =
      CenteredRenewal.barrierStep hk (C tail)
        (C (ring.rightNeighbor tail)) :=
    CenteredRenewal.transition_of_barrier hk _ _ hbar
  by_cases hihead : i = ring.rightNeighbor tail
  · subst i
    have hre := rightNeighbor_ne_self ring hn2 tail
    cases hphase : (C tail).phase <;>
      cases hleader : (C (ring.rightNeighbor tail)).leader <;>
      simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
        CenteredRenewal.barrierStep, hphase, hleader, hre]
  · simp [step, PopulationProtocol.step, CenteredRenewal.protocol, hitail,
      hihead]

theorem barrier_hit_tail_leader_eq {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (tail : Fin n)
    (hbar : IsBarrier hk (C tail) (C (ring.rightNeighbor tail))) :
    (step hk ring C tail tail).leader =
      (if (C tail).probe then true else (C tail).leader) := by
  have htrans : CenteredRenewal.transition hk (C tail)
      (C (ring.rightNeighbor tail)) =
      CenteredRenewal.barrierStep hk (C tail)
        (C (ring.rightNeighbor tail)) :=
    CenteredRenewal.transition_of_barrier hk _ _ hbar
  cases hphase : (C tail).phase <;> cases hprobe : (C tail).probe <;>
    simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      CenteredRenewal.barrierStep, hphase, probeHitsBarrier, hprobe]

theorem barrier_hit_tail_probe_false_of_probe {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (tail : Fin n)
    (hbar : IsBarrier hk (C tail) (C (ring.rightNeighbor tail)))
    (hprobe : (C tail).probe = true) :
    (step hk ring C tail tail).probe = false := by
  have htrans : CenteredRenewal.transition hk (C tail)
      (C (ring.rightNeighbor tail)) =
      CenteredRenewal.barrierStep hk (C tail)
        (C (ring.rightNeighbor tail)) :=
    CenteredRenewal.transition_of_barrier hk _ _ hbar
  cases hphase : (C tail).phase <;>
    simp [step, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      CenteredRenewal.barrierStep, hphase, probeHitsBarrier, hprobe]

/-- Any literal one-step increase of the leader count in a one-barrier state
is exactly a current-tail probe conversion. -/
theorem leaderCount_birth_is_compensating_tail_birth {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (C : Fin n -> State k) (tail selected : Fin n)
    (hone : OneBarrierAt hk ring C tail)
    (hbirth : leaderCount (step hk ring C selected) = leaderCount C + 1) :
    CompensatingTailBirth hk ring C (step hk ring C selected) tail selected := by
  have hn2 : 1 < n := by omega
  have hselected : selected = tail := by
    by_cases heq : selected = tail
    · exact heq
    · have hnot : ¬ IsBarrier hk (C selected)
          (C (ring.rightNeighbor selected)) := by
        intro hbar
        have hphysical : BarrierAt hk ring (labelsOf C) selected :=
          (barrierAt_labelsOf_iff hk ring C selected).2 hbar
        exact heq ((hone selected).1 hphysical)
      have hle := nonbarrier_step_leaderCount_le hk ring hn2 C selected hnot
      omega
  subst selected
  have hbar : IsBarrier hk (C tail) (C (ring.rightNeighbor tail)) :=
    (barrierAt_labelsOf_iff hk ring C tail).mp ((hone tail).2 rfl)
  have hother : forall i : Fin n, i ≠ tail ->
      (step hk ring C tail i).leader = (C i).leader := by
    intro i hi
    exact barrier_hit_other_leaders_eq hk ring hn2 C tail i hbar hi
  have htail := barrier_hit_tail_leader_eq hk ring C tail hbar
  have hbefore : (C tail).leader = false := by
    cases hb : (C tail).leader with
    | false => rfl
    | true =>
        have heq : (fun i => (step hk ring C tail i).leader) =
            fun i => (C i).leader := by
          funext i
          by_cases hi : i = tail
          · subst i
            simpa [hb] using htail
          · exact hother i hi
        have hc : leaderCount (step hk ring C tail) = leaderCount C := by
          unfold leaderCount
          exact bitCount_congr (fun i => congrFun heq i)
        omega
  have hafter : (step hk ring C tail tail).leader = true := by
    cases ha : (step hk ring C tail tail).leader with
    | true => rfl
    | false =>
        have heq : (fun i => (step hk ring C tail i).leader) =
            fun i => (C i).leader := by
          funext i
          by_cases hi : i = tail
          · subst i
            rw [ha, hbefore]
          · exact hother i hi
        have hc : leaderCount (step hk ring C tail) = leaderCount C := by
          unfold leaderCount
          exact bitCount_congr (fun i => congrFun heq i)
        omega
  have hprobe : (C tail).probe = true := by
    cases hp : (C tail).probe with
    | true => rfl
    | false =>
        rw [hp, hbefore] at htail
        rw [hafter] at htail
        simp at htail
  exact {
    selected_tail := rfl
    tail_probe := hprobe
    tail_follower := hbefore
    tail_born := hafter
    tail_probe_cleared :=
      barrier_hit_tail_probe_false_of_probe hk ring C tail hbar hprobe
    other_leaders := hother }

/-- Pointwise form of the same classification.  This is the useful form for
the debt-to-covered branch: rank arithmetic first produces some newly born
leader, then literal dynamics identifies it with the current barrier tail. -/
theorem leader_birth_point_is_compensating_tail_birth {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (C : Fin n -> State k) (tail selected born : Fin n)
    (hone : OneBarrierAt hk ring C tail)
    (hbefore : (C born).leader = false)
    (hafter : (step hk ring C selected born).leader = true) :
    CompensatingTailBirth hk ring C (step hk ring C selected) tail selected := by
  have hn2 : 1 < n := by omega
  have hselected : selected = tail := by
    by_cases heq : selected = tail
    · exact heq
    · have hnot : ¬ IsBarrier hk (C selected)
          (C (ring.rightNeighbor selected)) := by
        intro hbar
        have hphysical : BarrierAt hk ring (labelsOf C) selected :=
          (barrierAt_labelsOf_iff hk ring C selected).2 hbar
        exact heq ((hone selected).1 hphysical)
      have hold := step_no_leader_birth_of_nonbarrier hk ring hn2 C selected
        hnot born hafter
      rw [hbefore] at hold
      contradiction
  subst selected
  have hbar : IsBarrier hk (C tail) (C (ring.rightNeighbor tail)) :=
    (barrierAt_labelsOf_iff hk ring C tail).mp ((hone tail).2 rfl)
  have hother : forall i : Fin n, i ≠ tail ->
      (step hk ring C tail i).leader = (C i).leader := by
    intro i hi
    exact barrier_hit_other_leaders_eq hk ring hn2 C tail i hbar hi
  have hborn : born = tail := by
    by_cases heq : born = tail
    · exact heq
    · have heqLeader := hother born heq
      rw [hafter, hbefore] at heqLeader
      contradiction
  subst born
  have htail := barrier_hit_tail_leader_eq hk ring C tail hbar
  have hprobe : (C tail).probe = true := by
    cases hp : (C tail).probe
    · rw [hp, hbefore] at htail
      rw [hafter] at htail
      simp at htail
    · rfl
  exact {
    selected_tail := rfl
    tail_probe := hprobe
    tail_follower := hbefore
    tail_born := hafter
    tail_probe_cleared :=
      barrier_hit_tail_probe_false_of_probe hk ring C tail hbar hprobe
    other_leaders := hother }

/-- Exact single-leader deletion is invariant under passing to the physical
barrier cut.  This is the reindexing bridge used by the arbitrary-interleaving
shield argument below. -/
theorem deletesOnlyLeaderAt_cutView {n k : Nat} (ring : DirectedRing n)
    (tail target : Fin n) (before after : Fin n -> State k)
    (hdelete : DeletesOnlyLeaderAt target before after) :
    DeletesOnlyLeaderAt (cutCoord ring tail target)
      (cutView ring tail before) (cutView ring tail after) := by
  refine {
    before_leader := ?_
    after_leader := ?_
    other_leaders := ?_
    probes := ?_
  }
  · simpa [cutView] using hdelete.before_leader
  · simpa [cutView] using hdelete.after_leader
  · intro i hi
    have hphys : cutPos ring tail i ≠ target := by
      intro h
      apply hi
      apply cutPos_injective ring tail
      rw [h, cutPos_cutCoord]
    simpa [cutView] using hdelete.other_leaders (cutPos ring tail i) hphys
  · intro i
    simpa [cutView] using hdelete.probes (cutPos ring tail i)

/-- A protected physical target cannot die during an arbitrary ordinary
interaction on a positive `PhiAt` plateau.  The witness need not be fixed or
mark-free: if the target is the deleted responder, the strictly later leader
survives that same literal transition and forces a strict rank drop. -/
theorem protected_target_survives_plateau_step {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (C : Fin n -> State k) (tail selected target witness : Fin n)
    (_hone : OneBarrierAt hk ring C tail)
    (htarget : (C target).leader = true)
    (hlater : (cutCoord ring tail target).val <
      (cutCoord ring tail witness).val)
    (hwitness : (C witness).leader = true)
    (hpositive : 1 < PhiAt ring tail C)
    (hplateau : PhiAt ring tail (step hk ring C selected) =
      PhiAt ring tail C) :
    (step hk ring C selected target).leader = true := by
  have hn2 : 1 < n := by omega
  by_cases hbarrier : IsBarrier hk (C selected)
      (C (ring.rightNeighbor selected))
  · exact centered_barrier_step_preserves_leader hk ring hn2 C target
      selected hbarrier htarget
  · cases hdead : (step hk ring C selected target).leader with
    | true => rfl
    | false =>
        obtain ⟨htargetResp, hbullet⟩ :=
          centered_nonbarrier_target_death hk ring hn2 C target selected
            hbarrier htarget hdead
        have hdelete := centered_nonbarrier_leader_hit_deletes_only hk ring
          hn2 C selected hbarrier (by simpa [← htargetResp] using htarget)
            (by simpa [← htargetResp] using hbullet)
        have hdeleteTarget : DeletesOnlyLeaderAt target C
            (step hk ring C selected) := by
          rw [htargetResp]
          simpa [OneBarrierCleanup.step] using hdelete
        have hdeleteCut := deletesOnlyLeaderAt_cutView ring tail target C
          (step hk ring C selected) hdeleteTarget
        have hwne : witness ≠ target := by
          intro h
          subst witness
          exact Nat.lt_irrefl _ hlater
        have hwitnessAfter :
            (step hk ring C selected witness).leader = true := by
          rw [hdeleteTarget.other_leaders witness hwne]
          exact hwitness
        have hlaterCut : exists w : Fin n,
            (cutCoord ring tail target).val < w.val /\
              ((cutView ring tail (step hk ring C selected)) w).leader =
                true := by
          refine ⟨cutCoord ring tail witness, hlater, ?_⟩
          simpa [cutView] using hwitnessAfter
        have hstrict := phi_lt_after_delete_with_later
          (cutView ring tail C)
          (cutView ring tail (step hk ring C selected))
          (cutCoord ring tail target) hdeleteCut hlaterCut hpositive
        exact False.elim ((Nat.ne_of_lt hstrict) hplateau)

/-- Exact debt discharge on an arbitrary plateau step.  If the old physical
cut is dangerous and the successor cut is safe without lowering `PhiAt`,
some leader must have been born.  Literal centered dynamics then identifies
that birth with the probed current barrier tail.  This statement allows a
genuine barrier advance and therefore applies with arbitrary ordinary steps
between counted advances. -/
theorem danger_to_safe_plateau_is_compensating_tail_birth {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (C : Fin n -> State k) (tail selected : Fin n)
    (hone : OneBarrierAt hk ring C tail)
    (holdDanger : Dangerous (cutView ring tail C))
    (hnewSafe : ¬ Dangerous
      (cutView ring (postStepBarrier hk ring C tail selected)
        (step hk ring C selected)))
    (hpositive : 1 < PhiAt ring tail C)
    (hplateau :
      PhiAt ring (postStepBarrier hk ring C tail selected)
          (step hk ring C selected) = PhiAt ring tail C) :
    CompensatingTailBirth hk ring C (step hk ring C selected) tail selected := by
  let D := step hk ring C selected
  let newTail := postStepBarrier hk ring C tail selected
  by_cases hborn : exists born : Fin n,
      (C born).leader = false /\ (D born).leader = true
  · obtain ⟨born, hbefore, hafter⟩ := hborn
    exact leader_birth_point_is_compensating_tail_birth hk ring hn3 C tail
      selected born hone hbefore hafter
  · have himp : forall i : Fin n, (D i).leader = true ->
        (C i).leader = true := by
      intro i hi
      cases hold : (C i).leader
      · exact False.elim (hborn ⟨i, hold, hi⟩)
      · rfl
    have hcountRaw : leaderCount (cutView ring tail D) <=
        leaderCount (cutView ring tail C) := by
      apply bitCount_le_of_true_imp
      intro i hi
      change (D (cutPos ring tail i)).leader = true at hi
      change (C (cutPos ring tail i)).leader = true
      exact himp (cutPos ring tail i) hi
    have hcount : leaderCount (cutView ring newTail D) <=
        leaderCount (cutView ring tail C) := by
      by_cases hready : CenteredRenewal.AdvanceReady hk ring C selected
      · have htail : newTail = ring.rightNeighbor tail := by
          simp [newTail, postStepBarrier, hready]
        rw [htail, cutView_nextBarrier, leaderCount_rotateCut]
        exact hcountRaw
      · have htail : newTail = tail := by
          simp [newTail, postStepBarrier, hready]
        simpa [htail] using hcountRaw
    change Phi (cutView ring newTail D) = Phi (cutView ring tail C) at hplateau
    change 1 < Phi (cutView ring tail C) at hpositive
    change ¬ Dangerous (cutView ring newTail D) at hnewSafe
    have hcountTwo : 2 <= leaderCount (cutView ring newTail D) := by
      by_cases hle : leaderCount (cutView ring newTail D) <= 1
      · have hphi : Phi (cutView ring newTail D) = 1 := by
          simp [Phi, dangerBit, hnewSafe, Nat.max_eq_left hle]
        omega
      · omega
    have hnewPhi : Phi (cutView ring newTail D) =
        leaderCount (cutView ring newTail D) := by
      simp [Phi, dangerBit, hnewSafe,
        Nat.max_eq_right (by omega : 1 <=
          leaderCount (cutView ring newTail D))]
    have holdPhi : Phi (cutView ring tail C) =
        leaderCount (cutView ring tail C) + 1 := by
      simp [Phi, dangerBit, holdDanger,
        Nat.max_eq_right (by omega : 1 <=
          leaderCount (cutView ring tail C) + 1)]
    rw [hnewPhi, holdPhi] at hplateau
    omega

/-- Fixed-cut plateau preservation for any leader when dangerousness cannot
be newly introduced.  It covers both safe-to-safe continuation and the
vacuous dangerous-old debt case. -/
theorem fixed_cut_leader_survives_plateau_step {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (C : Fin n -> State k) (tail selected target : Fin n)
    (htarget : (C target).leader = true)
    (hpositive : 1 < PhiAt ring tail C)
    (hsafe : ¬ Dangerous (cutView ring tail C) ->
      ¬ Dangerous (cutView ring tail (step hk ring C selected)))
    (hplateau : PhiAt ring tail (step hk ring C selected) =
      PhiAt ring tail C) :
    (step hk ring C selected target).leader = true := by
  have hn2 : 1 < n := by omega
  by_cases hbarrier : IsBarrier hk (C selected)
      (C (ring.rightNeighbor selected))
  · exact centered_barrier_step_preserves_leader hk ring hn2 C target
      selected hbarrier htarget
  · cases hdead : (step hk ring C selected target).leader with
    | true => rfl
    | false =>
        obtain ⟨htargetResp, hbullet⟩ :=
          centered_nonbarrier_target_death hk ring hn2 C target selected
            hbarrier htarget hdead
        have hdelete := centered_nonbarrier_leader_hit_deletes_only hk ring
          hn2 C selected hbarrier (by simpa [← htargetResp] using htarget)
            (by simpa [← htargetResp] using hbullet)
        have hdeleteTarget : DeletesOnlyLeaderAt target C
            (step hk ring C selected) := by
          rw [htargetResp]
          simpa [OneBarrierCleanup.step] using hdelete
        have hdeleteCut := deletesOnlyLeaderAt_cutView ring tail target C
          (step hk ring C selected) hdeleteTarget
        have hdrop : leaderCount
              (cutView ring tail (step hk ring C selected)) + 1 =
            leaderCount (cutView ring tail C) := by
          unfold leaderCount
          exact bitCount_single_drop _ _ (cutCoord ring tail target)
            hdeleteCut.before_leader hdeleteCut.after_leader
            hdeleteCut.other_leaders
        have hstrict := phi_lt_of_single_delete
          (cutView ring tail C)
          (cutView ring tail (step hk ring C selected)) hdrop hpositive hsafe
        exact False.elim ((Nat.ne_of_lt hstrict) hplateau)

/-- Literal fixed-target crossing.  A phase-one barrier advance across a
leader head preserves that physical leader and makes it the fresh new tail. -/
theorem crosses_leader_head_fresh {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail)
    (hphase : (C tail).phase = true)
    (hleader : (C (ring.rightNeighbor tail)).leader = true) :
    let target := ring.rightNeighbor tail
    let D := step hk ring C tail
    OneBarrierAt hk ring D target /\
      (D target).leader = true /\ (D target).phase = false /\
      MarkFree (D target) /\
      PhiAt ring target D <= PhiAt ring tail C := by
  have hn2 : 1 < n := by omega
  have honeD := barrier_phase_one_advances_unique_barrier hk ring hn2 C tail
    hndvd hone hphase
  have hfresh := advance_sanitizes_new_tail hk ring hn2 C tail hone hphase
  have hbar : IsBarrier hk (C tail) (C (ring.rightNeighbor tail)) :=
    (barrierAt_labelsOf_iff hk ring C tail).mp ((hone tail).2 rfl)
  have hleaders := barrier_hit_preserves_leaders hk ring hn2 C tail hbar
  have hrank := Rank.oneBarrier_phi_step_le hk ring hn3 C tail tail hndvd hone
  have hready : CenteredRenewal.AdvanceReady hk ring C tail :=
    ⟨hbar, hphase⟩
  refine ⟨honeD, hleaders _ hleader, hfresh.1,
    ⟨hfresh.2.1, hfresh.2.2⟩, ?_⟩
  simpa [hready, OneBarrierCleanup.step] using hrank.2

/-- A fresh renewal tail and a nearest counterclockwise predecessor whose
clockwise gap is at most half the ring. -/
structure GoodFreshRenewal {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (tail : Fin n) : Type where
  barrier : OneBarrierAt hk ring C tail
  tailLeader : (C tail).leader = true
  tailPhase : (C tail).phase = false
  tailFresh : MarkFree (C tail)
  predecessor : Fin n
  predecessor_ne : predecessor ≠ tail
  predecessorLeader : (C predecessor).leader = true
  gap_pos : 0 < cwDist ring predecessor tail
  gap_le_half : cwDist ring predecessor tail <= n / 2
  nearest : forall other : Fin n,
    other ≠ tail -> (C other).leader = true ->
      cwDist ring predecessor tail <= cwDist ring other tail

def predecessorCandidates {n k : Nat} (C : Fin n -> State k)
    (tail : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun i => i ≠ tail && (C i).leader

@[simp] theorem mem_predecessorCandidates_iff {n k : Nat}
    (C : Fin n -> State k) (tail i : Fin n) :
    i ∈ predecessorCandidates C tail ↔
      i ≠ tail /\ (C i).leader = true := by
  simp [predecessorCandidates]

/-- Finite minimum bridge from any live predecessor to the nearest one stored
by `GoodFreshRenewal`; minimization can only shorten the certified gap. -/
theorem exists_nearest_predecessor_le {n k : Nat} (ring : DirectedRing n)
    (C : Fin n -> State k) (tail p : Fin n)
    (hpne : p ≠ tail) (hp : (C p).leader = true) :
    exists a : Fin n,
      a ≠ tail /\ (C a).leader = true /\
      0 < cwDist ring a tail /\
      cwDist ring a tail <= cwDist ring p tail /\
      forall other : Fin n, other ≠ tail -> (C other).leader = true ->
        cwDist ring a tail <= cwDist ring other tail := by
  classical
  have hnonempty : predecessorCandidates C tail ≠ [] := by
    intro hempty
    have hm : p ∈ predecessorCandidates C tail :=
      (mem_predecessorCandidates_iff C tail p).2 ⟨hpne, hp⟩
    rw [hempty] at hm
    simp at hm
  let a : Fin n := List.minOn (fun i => cwDist ring i tail)
    (predecessorCandidates C tail) hnonempty
  have haMem : a ∈ predecessorCandidates C tail :=
    List.minOn_mem (f := fun i => cwDist ring i tail)
  have ha := (mem_predecessorCandidates_iff C tail a).1 haMem
  have hamin (x : Fin n) (hx : x ∈ predecessorCandidates C tail) :
      cwDist ring a tail <= cwDist ring x tail := by
    exact List.apply_minOn_le_of_mem (f := fun i => cwDist ring i tail) hx
  refine ⟨a, ha.1, ha.2, ?_, hamin p
    ((mem_predecessorCandidates_iff C tail p).2 ⟨hpne, hp⟩), ?_⟩
  · by_cases hzero : cwDist ring a tail = 0
    · have hreach := cwPos_cwDist ring a tail
      rw [hzero] at hreach
      have haeq : a = tail := by
        have hz : cwPos ring a 0 = a := by
          apply Fin.ext
          simp [cwPos, Nat.mod_eq_of_lt a.isLt]
        exact hz.symm.trans hreach
      exact False.elim (ha.1 haeq)
    · omega
  · intro other hone hleader
    exact hamin other
      ((mem_predecessorCandidates_iff C tail other).2 ⟨hone, hleader⟩)

/-- Physical post-step payload retained at a renewal boundary.  It is not an
absorbing flag: consumers receive the literal configuration and may bind the
next fire stage immediately. -/
structure FreshWithPredecessor {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (tail : Fin n) : Type where
  barrier : OneBarrierAt hk ring C tail
  tailLeader : (C tail).leader = true
  tailPhase : (C tail).phase = false
  tailFresh : MarkFree (C tail)
  predecessor : Fin n
  predecessor_ne : predecessor ≠ tail
  predecessorLeader : (C predecessor).leader = true

theorem FreshWithPredecessor.toGood {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n -> State k} {tail : Fin n}
    (fresh : FreshWithPredecessor hk ring C tail)
    (hgap : cwDist ring fresh.predecessor tail <= n / 2) :
    Nonempty (GoodFreshRenewal hk ring C tail) := by
  obtain ⟨a, hane, haleader, hagap, hale, hnearest⟩ :=
    exists_nearest_predecessor_le ring C tail fresh.predecessor
      fresh.predecessor_ne fresh.predecessorLeader
  exact ⟨{
    barrier := fresh.barrier
    tailLeader := fresh.tailLeader
    tailPhase := fresh.tailPhase
    tailFresh := fresh.tailFresh
    predecessor := a
    predecessor_ne := hane
    predecessorLeader := haleader
    gap_pos := hagap
    gap_le_half := Nat.le_trans hale hgap
    nearest := hnearest }⟩

/-- Existential compatibility surface.  The timed-service layer must consume
the universal prefix form below, not this weaker proposition. -/
def HasBoundedRenewalSearch {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (b : Fin n) : Prop :=
  exists D : Fin n -> State k, exists d : Fin n, exists advances : Nat,
    AdvanceTrace hk ring C b D d advances /\ advances <= 2 * n /\
      (PhiAt ring d D < PhiAt ring b C \/
        Nonempty (GoodFreshRenewal hk ring D d))

/-- Legacy unbound trace surface retained only to record why an existential
trace endpoint is insufficient: its conclusion is not tied to the supplied
proof object.  The actual consumer uses the total same-word machine below. -/
def LegacyUnboundTraceSearch {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (b : Fin n) : Prop :=
  forall D : Fin n -> State k, forall d : Fin n, forall advances : Nat,
    AdvanceTrace hk ring C b D d advances -> 2 * n <= advances ->
      exists E : Fin n -> State k, exists e : Fin n, exists used : Nat,
        AdvanceTrace hk ring C b E e used /\ used <= 2 * n /\
          (PhiAt ring e E < PhiAt ring b C \/
            Nonempty (GoodFreshRenewal hk ring E e))

/-! ## Covered/debt sweep surface -/

/-- Strict order in the moving physical barrier cut. -/
def LaterAt {n : Nat} (ring : DirectedRing n)
    (tail earlier later : Fin n) : Prop :=
  (cutCoord ring tail earlier).val < (cutCoord ring tail later).val

theorem cwPos_add_search {n : Nat} (ring : DirectedRing n)
    (start : Fin n) (a b : Nat) :
    cwPos ring (cwPos ring start a) b = cwPos ring start (a + b) := by
  apply Fin.ext
  unfold cwPos
  dsimp only
  rw [Nat.mod_add_mod]
  congr 1
  omega

theorem cwDist_add_reverse_of_ne {n : Nat} (ring : DirectedRing n)
    (i j : Fin n) (hne : i ≠ j) :
    cwDist ring i j + cwDist ring j i = n := by
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  unfold cwDist
  by_cases hij : i.val < j.val
  · have hfirst : (j.val + n - i.val) % n = j.val - i.val := by
      have heq : j.val + n - i.val = n + (j.val - i.val) := by omega
      have hdiff : j.val - i.val < n := by
        have hjlt := j.isLt
        omega
      rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add]
      simpa [Nat.mod_mod] using Nat.mod_eq_of_lt hdiff
    have hsecond : (i.val + n - j.val) % n = i.val + n - j.val := by
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hfirst, hsecond]
    omega
  · have hji : j.val < i.val := by omega
    have hfirst : (j.val + n - i.val) % n = j.val + n - i.val := by
      rw [Nat.mod_eq_of_lt (by omega)]
    have hsecond : (i.val + n - j.val) % n = i.val - j.val := by
      have heq : i.val + n - j.val = n + (i.val - j.val) := by omega
      have hdiff : i.val - j.val < n := by
        have hilt := i.isLt
        omega
      rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add]
      simpa [Nat.mod_mod] using Nat.mod_eq_of_lt hdiff
    rw [hfirst, hsecond]
    omega

/-- Lifted progress toward one fixed physical leader target.  The lifted
advance counter distinguishes a full lap from modular equality. -/
structure SweepFrame {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n -> State k) (currentTail : Fin n) : Type where
  startTail : Fin n
  target : Fin n
  targetSteps : Nat
  advances : Nat
  targetSteps_pos : 0 < targetSteps
  targetSteps_le : targetSteps <= n
  target_phys : cwPos ring startTail targetSteps = target
  before_target : advances < targetSteps
  tail_phys : currentTail = cwPos ring startTail advances
  unique_barrier : OneBarrierAt hk ring C currentTail
  target_leader : (C target).leader = true

/-- Mutable covered-mode predecessor.  The physical witness may be replaced
by a tail-born leader after a non-strict death/debt interval. -/
structure SweptPredecessor {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n -> State k} {tail : Fin n}
    (frame : SweepFrame hk ring C tail) : Type where
  index : Nat
  index_le : index <= frame.advances
  index_lt_target : index < frame.targetSteps
  predecessor : Fin n
  predecessor_phys : predecessor = cwPos ring frame.startTail index
  predecessor_leader : (C predecessor).leader = true
  predecessor_later : LaterAt ring tail frame.target predecessor

/-- A swept-origin predecessor reaches the fixed target within the frame
span.  The strict-span premise is exactly the short second-leg condition. -/
theorem SweptPredecessor.gap_le_targetSteps {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n -> State k} {tail : Fin n}
    {frame : SweepFrame hk ring C tail} (pred : SweptPredecessor frame)
    (hspan : frame.targetSteps < n) :
    cwDist ring pred.predecessor frame.target <= frame.targetSteps := by
  have hindex : pred.index <= frame.targetSteps :=
    Nat.le_trans pred.index_le (Nat.le_of_lt frame.before_target)
  let d := frame.targetSteps - pred.index
  have hdlt : d < n := by omega
  have hreach : cwPos ring pred.predecessor d = frame.target := by
    rw [pred.predecessor_phys, cwPos_add_search]
    change cwPos ring frame.startTail (pred.index +
      (frame.targetSteps - pred.index)) = frame.target
    rw [Nat.add_sub_of_le hindex, frame.target_phys]
  have hdEq := cwPos_bounded_unique ring pred.predecessor frame.target d
    hdlt hreach
  omega

/-- Plateau mode.  Covered states carry a mutable later leader in the swept
arc; debt states assert dangerousness and deliberately carry no fake witness. -/
inductive CoverOrDebt {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n -> State k} {tail : Fin n}
    (frame : SweepFrame hk ring C tail) : Type where
  | covered (danger_free : ¬ Dangerous (cutView ring tail C))
      (predecessor : SweptPredecessor frame) : CoverOrDebt frame
  | debt (dangerous : Dangerous (cutView ring tail C)) : CoverOrDebt frame

/-- Full state needed for the arbitrary-interleaving induction at plateau
rank `r`. -/
structure SweptCover {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (tail : Fin n) : Type where
  rank_eq : PhiAt ring tail C = r
  rank_gt_one : 1 < r
  frame : SweepFrame hk ring C tail
  mode : CoverOrDebt frame

/-- Actual post-renewal seed for the short second leg. -/
structure BadFreshSecondSeed {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (tail : Fin n) : Type where
  state : SweptCover (r := r) hk ring C tail
  span_le_half : state.frame.targetSteps <= n / 2
  initial_advances : state.frame.advances = 0

/-- If a fresh predecessor is not already short, walking from the fresh tail
back to that predecessor is the complementary short arc.  The literal
post-step configuration is retained and seeds swept index zero at the fresh
tail. -/
theorem badFresh_secondSeed {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (tail : Fin n)
    (fresh : FreshWithPredecessor hk ring C tail)
    (hrank : PhiAt ring tail C = r) (hr1 : 1 < r)
    (hbad : ¬ Nonempty (GoodFreshRenewal hk ring C tail)) :
    Nonempty (BadFreshSecondSeed (r := r) hk ring C tail) := by
  let span := cwDist ring tail fresh.predecessor
  have hbadGap : n / 2 < cwDist ring fresh.predecessor tail := by
    by_cases hle : cwDist ring fresh.predecessor tail <= n / 2
    · exact False.elim (hbad (fresh.toGood hle))
    · omega
  have hsum := cwDist_add_reverse_of_ne ring fresh.predecessor tail
    fresh.predecessor_ne
  have hspanPos : 0 < span := by
    by_cases hzero : span = 0
    · have hreach := cwPos_cwDist ring tail fresh.predecessor
      rw [show cwDist ring tail fresh.predecessor = span by rfl, hzero,
        cwPos_zero] at hreach
      exact False.elim (fresh.predecessor_ne hreach.symm)
    · omega
  have hspanLt : span < n := cwDist_lt ring tail fresh.predecessor
  have hspanHalf : span <= n / 2 := by
    change cwDist ring tail fresh.predecessor <= n / 2
    omega
  have hsafe : ¬ Dangerous (cutView ring tail C) := by
    apply not_dangerous_of_tail_leader ring
    · change (C (cutPos ring tail (tailCoord ring))).leader = true
      rw [cutPos_tailCoord]
      exact fresh.tailLeader
    · change (C (cutPos ring tail (tailCoord ring))).probe = false
      rw [cutPos_tailCoord]
      exact fresh.tailFresh.2
  let frame : SweepFrame hk ring C tail := {
    startTail := tail
    target := fresh.predecessor
    targetSteps := span
    advances := 0
    targetSteps_pos := hspanPos
    targetSteps_le := Nat.le_of_lt hspanLt
    target_phys := cwPos_cwDist ring tail fresh.predecessor
    before_target := hspanPos
    tail_phys := (cwPos_zero ring tail).symm
    unique_barrier := fresh.barrier
    target_leader := fresh.predecessorLeader
  }
  have hlater : LaterAt ring tail fresh.predecessor tail := by
    simpa [LaterAt, StrictlyLaterAt] using strictlyLater_tail_of_ne ring
      fresh.predecessor tail fresh.predecessor_ne
  let pred : SweptPredecessor frame := {
    index := 0
    index_le := Nat.zero_le _
    index_lt_target := hspanPos
    predecessor := tail
    predecessor_phys := (cwPos_zero ring tail).symm
    predecessor_leader := fresh.tailLeader
    predecessor_later := hlater
  }
  let state : SweptCover (r := r) hk ring C tail := {
    rank_eq := hrank
    rank_gt_one := hr1
    frame := frame
    mode := .covered hsafe pred
  }
  exact ⟨⟨state, hspanHalf, rfl⟩⟩

/-- Strict cut order is stable when the barrier advances, provided the first
point has not been reached by the new head. -/
theorem laterAt_nextBarrier {n : Nat} (ring : DirectedRing n)
    (tail target witness : Fin n)
    (hlater : LaterAt ring tail target witness)
    (htargetPos : 0 < (cutCoord ring tail target).val) :
    LaterAt ring (ring.rightNeighbor tail) target witness := by
  have hwitnessPos : 0 < (cutCoord ring tail witness).val := by
    unfold LaterAt at hlater
    omega
  unfold LaterAt
  rw [cutCoord_nextBarrier, cutCoord_nextBarrier]
  have ht := leftNeighbor_val_of_pos ring (cutCoord ring tail target)
    htargetPos
  have hw := leftNeighbor_val_of_pos ring (cutCoord ring tail witness)
    hwitnessPos
  rw [ht, hw]
  exact Nat.sub_lt_sub_right (by omega) hlater

/-- After an advance, the old tail is strictly later than every old vertex
which was neither the head nor the tail.  This is the geometric placement of
a debt-discharging tail birth. -/
theorem laterAt_oldTail_after_advance {n : Nat} (ring : DirectedRing n)
    (hn3 : 3 <= n) (tail target : Fin n)
    (htargetPos : 0 < (cutCoord ring tail target).val)
    (htargetNeTail : target ≠ tail) :
    LaterAt ring (ring.rightNeighbor tail) target tail := by
  have htargetNotLast : (cutCoord ring tail target).val ≠ n - 1 := by
    intro hval
    apply htargetNeTail
    have hcoord : cutCoord ring tail target = tailCoord ring := by
      apply Fin.ext
      exact hval
    calc
      target = cutPos ring tail (cutCoord ring tail target) :=
        (cutPos_cutCoord ring tail target).symm
      _ = cutPos ring tail (tailCoord ring) := by rw [hcoord]
      _ = tail := cutPos_tailCoord ring tail
  have htargetLe : (cutCoord ring tail target).val <= n - 2 := by
    have hlt := (cutCoord ring tail target).isLt
    omega
  unfold LaterAt
  rw [cutCoord_nextBarrier, cutCoord_nextBarrier]
  have ht := leftNeighbor_val_of_pos ring (cutCoord ring tail target)
    htargetPos
  have htailCoord : cutCoord ring tail tail = tailCoord ring :=
    cutCoord_self ring tail
  have htailPos : 0 < (cutCoord ring tail tail).val := by
    rw [htailCoord]
    change 0 < n - 1
    omega
  have hb := leftNeighbor_val_of_pos ring (cutCoord ring tail tail) htailPos
  rw [ht, hb, htailCoord]
  change (cutCoord ring tail target).val - 1 < (n - 1) - 1
  omega

/-- Before the lifted crossing count is reached, the fixed physical target
is not the current barrier head.  The `targetSteps = n` full-lap case is
handled separately, so modular equality cannot erase progress. -/
theorem SweepFrame.target_not_next_head {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n -> State k} {tail : Fin n}
    (frame : SweepFrame hk ring C tail)
    (hnext : frame.advances + 1 < frame.targetSteps) :
    frame.target ≠ ring.rightNeighbor tail := by
  intro heq
  have hwalk : cwPos ring frame.startTail frame.targetSteps =
      cwPos ring frame.startTail (frame.advances + 1) := by
    calc
      cwPos ring frame.startTail frame.targetSteps = frame.target :=
        frame.target_phys
      _ = ring.rightNeighbor tail := heq
      _ = ring.rightNeighbor
          (cwPos ring frame.startTail frame.advances) :=
        congrArg ring.rightNeighbor frame.tail_phys
      _ = cwPos ring frame.startTail (frame.advances + 1) :=
        (cwPos_succ ring frame.startTail frame.advances).symm
  have haLt : frame.advances + 1 < n :=
    Nat.lt_of_lt_of_le hnext frame.targetSteps_le
  by_cases htLt : frame.targetSteps < n
  · have ha := cwPos_bounded_unique ring frame.startTail
      (cwPos ring frame.startTail (frame.advances + 1))
      (frame.advances + 1) haLt rfl
    have ht := cwPos_bounded_unique ring frame.startTail
      (cwPos ring frame.startTail (frame.advances + 1))
      frame.targetSteps htLt hwalk
    omega
  · have htEq : frame.targetSteps = n :=
      Nat.le_antisymm frame.targetSteps_le (Nat.le_of_not_gt htLt)
    rw [htEq, cwPos_period] at hwalk
    have ha := cwPos_bounded_unique ring frame.startTail frame.startTail
      (frame.advances + 1) haLt hwalk.symm
    have hself : cwDist ring frame.startTail frame.startTail = 0 := by
      simp [cwDist]
    rw [hself] at ha
    omega

theorem SweepFrame.target_cutCoord_pos_before_next {n k : Nat}
    {hk : 0 < k} {ring : DirectedRing n}
    {C : Fin n -> State k} {tail : Fin n}
    (frame : SweepFrame hk ring C tail)
    (hnext : frame.advances + 1 < frame.targetSteps) :
    0 < (cutCoord ring tail frame.target).val := by
  by_cases hzero : (cutCoord ring tail frame.target).val = 0
  · have hcoord : cutCoord ring tail frame.target =
        (⟨0, ring.hn⟩ : Fin n) := by
      apply Fin.ext
      exact hzero
    have hhead : frame.target = ring.rightNeighbor tail := by
      calc
        frame.target = cutPos ring tail (cutCoord ring tail frame.target) :=
          (cutPos_cutCoord ring tail frame.target).symm
        _ = cutPos ring tail (⟨0, ring.hn⟩ : Fin n) := by rw [hcoord]
        _ = ring.rightNeighbor tail := cutPos_zero ring tail
    exact False.elim (frame.target_not_next_head hnext hhead)
  · omega

/-- The exact terminal/continuation surface required from one arbitrary
literal interaction.  Proving that centered dynamics instantiate this
surface is the remaining protocol-side seam before timed service can consume
`HasBoundedRenewalSearch`. -/
inductive SweptCoverStepResult {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (oldC newC : Fin n -> State k)
    (oldTail newTail : Fin n) : Type where
  | rankDrop (drop : PhiAt ring newTail newC < PhiAt ring oldTail oldC)
  | continue (next : SweptCover (r := r) hk ring newC newTail)
  | crossedFresh (target : Fin n) (predecessor : Fin n)
      (barrier : OneBarrierAt hk ring newC target)
      (tail_eq : newTail = target)
      (target_leader : (newC target).leader = true)
      (target_phase : (newC target).phase = false)
      (target_fresh : MarkFree (newC target))
      (predecessor_ne : predecessor ≠ target)
      (predecessor_leader : (newC predecessor).leader = true)
      (gap_le : cwDist ring predecessor target <= n) :
      SweptCoverStepResult hk ring oldC newC oldTail newTail

/-- Non-crossing literal steps cannot report a fresh endpoint.  Keeping this
fact in the result type makes the total scheduler-edge interpreter exhaustive
without an unreachable fallback branch. -/
inductive SweptCoverActiveStepResult {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (oldC newC : Fin n -> State k)
    (oldTail newTail : Fin n) (expectedAdvances expectedTargetSteps : Nat) :
    Type where
  | rankDrop (drop : PhiAt ring newTail newC < PhiAt ring oldTail oldC)
  | continue (next : SweptCover (r := r) hk ring newC newTail)
      (advances_eq : next.frame.advances = expectedAdvances)
      (targetSteps_eq : next.frame.targetSteps = expectedTargetSteps)

def SweptCoverActiveStepResult.toStepResult {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {oldC newC : Fin n -> State k}
    {oldTail newTail : Fin n} {expectedAdvances expectedTargetSteps : Nat}
    (result : SweptCoverActiveStepResult (r := r) hk ring oldC newC
      oldTail newTail expectedAdvances expectedTargetSteps) :
    SweptCoverStepResult (r := r) hk ring oldC newC oldTail newTail :=
  match result with
  | .rankDrop drop => .rankDrop drop
  | .continue next _ _ => .continue next

/-- Every non-advancing literal interaction closes the covered/debt
invariant.  This is the arbitrary-ordinary-interleaving part of the sweep:
the scheduler may take any number of such steps between counted advances. -/
def sweptCover_step_of_not_ready {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail selected : Fin n)
    (old : SweptCover (r := r) hk ring C tail)
    (hnotready : ¬ CenteredRenewal.AdvanceReady hk ring C selected) :
    SweptCoverActiveStepResult (r := r) hk ring C (step hk ring C selected)
      tail tail old.frame.advances old.frame.targetSteps := by
  let D := step hk ring C selected
  have hrank := Rank.oneBarrier_phi_step_le hk ring hn3 C tail selected
    hndvd old.frame.unique_barrier
  have honeD : OneBarrierAt hk ring D tail := by
    simpa [D, hnotready, OneBarrierCleanup.step] using hrank.1
  have hle : PhiAt ring tail D <= PhiAt ring tail C := by
    simpa [D, hnotready, OneBarrierCleanup.step] using hrank.2
  by_cases hdrop : PhiAt ring tail D < PhiAt ring tail C
  · exact .rankDrop hdrop
  · have hplateau : PhiAt ring tail D = PhiAt ring tail C := by omega
    have hrankD : PhiAt ring tail D = r := hplateau.trans old.rank_eq
    have htargetD : (D old.frame.target).leader = true := by
      cases old.mode with
      | covered hsafe predecessor =>
          exact protected_target_survives_plateau_step hk ring hn3 C tail
            selected old.frame.target predecessor.predecessor
            old.frame.unique_barrier old.frame.target_leader
            predecessor.predecessor_later predecessor.predecessor_leader
            (by rw [old.rank_eq]; exact old.rank_gt_one) hplateau
      | debt hdanger =>
          exact fixed_cut_leader_survives_plateau_step hk ring hn3 C tail
            selected old.frame.target old.frame.target_leader
            (by rw [old.rank_eq]; exact old.rank_gt_one)
            (fun hsafe => False.elim (hsafe hdanger)) hplateau
    let nextFrame : SweepFrame hk ring D tail := {
      startTail := old.frame.startTail
      target := old.frame.target
      targetSteps := old.frame.targetSteps
      advances := old.frame.advances
      targetSteps_pos := old.frame.targetSteps_pos
      targetSteps_le := old.frame.targetSteps_le
      target_phys := old.frame.target_phys
      before_target := old.frame.before_target
      tail_phys := old.frame.tail_phys
      unique_barrier := honeD
      target_leader := htargetD
    }
    have hpositive : 1 < PhiAt ring tail C := by
      rw [old.rank_eq]
      exact old.rank_gt_one
    by_cases hnewDanger : Dangerous (cutView ring tail D)
    · exact .continue {
        rank_eq := hrankD
        rank_gt_one := old.rank_gt_one
        frame := nextFrame
        mode := .debt hnewDanger } rfl rfl
    · cases old.mode with
      | covered holdSafe predecessor =>
          have hpredD : (D predecessor.predecessor).leader = true :=
            fixed_cut_leader_survives_plateau_step hk ring hn3 C tail
              selected predecessor.predecessor
              predecessor.predecessor_leader hpositive
              (fun _ => hnewDanger) hplateau
          let nextPred : SweptPredecessor nextFrame := {
            index := predecessor.index
            index_le := predecessor.index_le
            index_lt_target := predecessor.index_lt_target
            predecessor := predecessor.predecessor
            predecessor_phys := predecessor.predecessor_phys
            predecessor_leader := hpredD
            predecessor_later := predecessor.predecessor_later
          }
          exact .continue {
            rank_eq := hrankD
            rank_gt_one := old.rank_gt_one
            frame := nextFrame
            mode := .covered hnewDanger nextPred } rfl rfl
      | debt holdDanger =>
          have hbirth := danger_to_safe_plateau_is_compensating_tail_birth
            hk ring hn3 C tail selected old.frame.unique_barrier holdDanger
            (by simpa [D, postStepBarrier, hnotready] using hnewDanger)
            hpositive (by simpa [D, postStepBarrier, hnotready] using hplateau)
          have htargetNeTail : old.frame.target ≠ tail := by
            intro heq
            have ht := old.frame.target_leader
            rw [heq] at ht
            have hf := hbirth.tail_follower
            rw [ht] at hf
            contradiction
          have hlater : LaterAt ring tail old.frame.target tail := by
            simpa [LaterAt, StrictlyLaterAt] using
              strictlyLater_tail_of_ne ring old.frame.target tail
                htargetNeTail
          let nextPred : SweptPredecessor nextFrame := {
            index := old.frame.advances
            index_le := Nat.le_refl _
            index_lt_target := old.frame.before_target
            predecessor := tail
            predecessor_phys := old.frame.tail_phys
            predecessor_leader := hbirth.tail_born
            predecessor_later := hlater
          }
          exact .continue {
            rank_eq := hrankD
            rank_gt_one := old.rank_gt_one
            frame := nextFrame
            mode := .covered hnewDanger nextPred } rfl rfl

/-- A genuine advance which is still strictly before the fixed target also
closes the covered/debt invariant.  The lifted counter is incremented, old
covered witnesses rotate coherently, and a debt discharge is re-seeded at
the literal old-tail birth. -/
def sweptCover_step_of_ready_before_target {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail selected : Fin n)
    (old : SweptCover (r := r) hk ring C tail)
    (hready : CenteredRenewal.AdvanceReady hk ring C selected)
    (hbefore : old.frame.advances + 1 < old.frame.targetSteps) :
    SweptCoverActiveStepResult (r := r) hk ring C (step hk ring C selected)
      tail (ring.rightNeighbor tail) (old.frame.advances + 1)
      old.frame.targetSteps := by
  have hselected : selected = tail := by
    have hphysical : BarrierAt hk ring (labelsOf C) selected :=
      (barrierAt_labelsOf_iff hk ring C selected).2 hready.1
    exact (old.frame.unique_barrier selected).1 hphysical
  subst selected
  let D := step hk ring C tail
  let newTail := ring.rightNeighbor tail
  have hrank := Rank.oneBarrier_phi_step_le hk ring hn3 C tail tail hndvd
    old.frame.unique_barrier
  have honeD : OneBarrierAt hk ring D newTail := by
    simpa [D, newTail, hready, OneBarrierCleanup.step] using hrank.1
  have hle : PhiAt ring newTail D <= PhiAt ring tail C := by
    simpa [D, newTail, hready, OneBarrierCleanup.step] using hrank.2
  by_cases hdrop : PhiAt ring newTail D < PhiAt ring tail C
  · exact .rankDrop hdrop
  · have hplateau : PhiAt ring newTail D = PhiAt ring tail C := by omega
    have hrankD : PhiAt ring newTail D = r := hplateau.trans old.rank_eq
    have hn2 : 1 < n := by omega
    have htargetD : (D old.frame.target).leader = true :=
      centered_barrier_step_preserves_leader hk ring hn2 C old.frame.target
        tail hready.1 old.frame.target_leader
    have htailPhys : newTail =
        cwPos ring old.frame.startTail (old.frame.advances + 1) := by
      calc
        newTail = ring.rightNeighbor tail := rfl
        _ = ring.rightNeighbor
            (cwPos ring old.frame.startTail old.frame.advances) :=
          congrArg ring.rightNeighbor old.frame.tail_phys
        _ = cwPos ring old.frame.startTail (old.frame.advances + 1) :=
          (cwPos_succ ring old.frame.startTail old.frame.advances).symm
    let nextFrame : SweepFrame hk ring D newTail := {
      startTail := old.frame.startTail
      target := old.frame.target
      targetSteps := old.frame.targetSteps
      advances := old.frame.advances + 1
      targetSteps_pos := old.frame.targetSteps_pos
      targetSteps_le := old.frame.targetSteps_le
      target_phys := old.frame.target_phys
      before_target := hbefore
      tail_phys := htailPhys
      unique_barrier := honeD
      target_leader := htargetD
    }
    have hpositive : 1 < PhiAt ring tail C := by
      rw [old.rank_eq]
      exact old.rank_gt_one
    have htargetPos := old.frame.target_cutCoord_pos_before_next hbefore
    by_cases hnewDanger : Dangerous (cutView ring newTail D)
    · exact .continue {
        rank_eq := hrankD
        rank_gt_one := old.rank_gt_one
        frame := nextFrame
        mode := .debt hnewDanger } rfl rfl
    · cases old.mode with
      | covered holdSafe predecessor =>
          have hpredD : (D predecessor.predecessor).leader = true :=
            centered_barrier_step_preserves_leader hk ring hn2 C
              predecessor.predecessor tail hready.1
              predecessor.predecessor_leader
          have hlater := laterAt_nextBarrier ring tail old.frame.target
            predecessor.predecessor predecessor.predecessor_later htargetPos
          let nextPred : SweptPredecessor nextFrame := {
            index := predecessor.index
            index_le := Nat.le_trans predecessor.index_le
              (Nat.le_succ old.frame.advances)
            index_lt_target := predecessor.index_lt_target
            predecessor := predecessor.predecessor
            predecessor_phys := predecessor.predecessor_phys
            predecessor_leader := hpredD
            predecessor_later := hlater
          }
          exact .continue {
            rank_eq := hrankD
            rank_gt_one := old.rank_gt_one
            frame := nextFrame
            mode := .covered hnewDanger nextPred } rfl rfl

      | debt holdDanger =>
          have hbirth := danger_to_safe_plateau_is_compensating_tail_birth
            hk ring hn3 C tail tail old.frame.unique_barrier holdDanger
            (by simpa [D, newTail, postStepBarrier, hready] using hnewDanger)
            hpositive
            (by simpa [D, newTail, postStepBarrier, hready] using hplateau)
          have htargetNeTail : old.frame.target ≠ tail := by
            intro heq
            have ht := old.frame.target_leader
            rw [heq] at ht
            have hf := hbirth.tail_follower
            rw [ht] at hf
            contradiction
          have hlater : LaterAt ring newTail old.frame.target tail :=
            laterAt_oldTail_after_advance ring hn3 tail old.frame.target
              htargetPos htargetNeTail
          let nextPred : SweptPredecessor nextFrame := {
            index := old.frame.advances
            index_le := Nat.le_succ _
            index_lt_target := old.frame.before_target
            predecessor := tail
            predecessor_phys := old.frame.tail_phys
            predecessor_leader := hbirth.tail_born
            predecessor_later := hlater
          }
          exact .continue {
            rank_eq := hrankD
            rank_gt_one := old.rank_gt_one
            frame := nextFrame
            mode := .covered hnewDanger nextPred } rfl rfl

/-- The counted advance which reaches the fixed target is terminal: either
the rank strictly drops, or the centered responder assignment yields a
phase-zero, mark-free leader tail with a live predecessor. -/
def sweptCover_step_of_ready_crossing {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail selected : Fin n)
    (old : SweptCover (r := r) hk ring C tail)
    (hready : CenteredRenewal.AdvanceReady hk ring C selected)
    (hcrossing : old.frame.advances + 1 = old.frame.targetSteps) :
    SweptCoverStepResult (r := r) hk ring C (step hk ring C selected)
      tail (ring.rightNeighbor tail) := by
  have hselected : selected = tail := by
    have hphysical : BarrierAt hk ring (labelsOf C) selected :=
      (barrierAt_labelsOf_iff hk ring C selected).2 hready.1
    exact (old.frame.unique_barrier selected).1 hphysical
  subst selected
  have htargetEq : old.frame.target = ring.rightNeighbor tail := by
    calc
      old.frame.target =
          cwPos ring old.frame.startTail old.frame.targetSteps :=
        old.frame.target_phys.symm
      _ = cwPos ring old.frame.startTail (old.frame.advances + 1) := by
        rw [hcrossing]
      _ = ring.rightNeighbor
          (cwPos ring old.frame.startTail old.frame.advances) :=
        cwPos_succ ring old.frame.startTail old.frame.advances
      _ = ring.rightNeighbor tail :=
        congrArg ring.rightNeighbor old.frame.tail_phys.symm
  let D := step hk ring C tail
  let newTail := ring.rightNeighbor tail
  have hheadLeader : (C (ring.rightNeighbor tail)).leader = true := by
    simpa [← htargetEq] using old.frame.target_leader
  have hterminal := crosses_leader_head_fresh hk ring hn3 hndvd C tail
    old.frame.unique_barrier hready.2 hheadLeader
  have honeD : OneBarrierAt hk ring D newTail := by
    simpa [D, newTail] using hterminal.1
  have htailLeader : (D newTail).leader = true := by
    simpa [D, newTail] using hterminal.2.1
  have htailPhase : (D newTail).phase = false := by
    simpa [D, newTail] using hterminal.2.2.1
  have htailFresh : MarkFree (D newTail) := by
    simpa [D, newTail] using hterminal.2.2.2.1
  have hle : PhiAt ring newTail D <= PhiAt ring tail C := by
    simpa [D, newTail] using hterminal.2.2.2.2
  by_cases hdrop : PhiAt ring newTail D < PhiAt ring tail C
  · exact .rankDrop hdrop
  · have hplateau : PhiAt ring newTail D = PhiAt ring tail C := by omega
    have hrankD : PhiAt ring newTail D = r := hplateau.trans old.rank_eq
    have hpositive : 1 < PhiAt ring tail C := by
      rw [old.rank_eq]
      exact old.rank_gt_one
    have hnewSafe : ¬ Dangerous (cutView ring newTail D) := by
      apply not_dangerous_of_tail_leader ring
      · change (D (cutPos ring newTail (tailCoord ring))).leader = true
        rw [cutPos_tailCoord]
        exact htailLeader
      · change (D (cutPos ring newTail (tailCoord ring))).probe = false
        rw [cutPos_tailCoord]
        exact htailFresh.2
    have honeTarget : OneBarrierAt hk ring D old.frame.target := by
      simpa [newTail, htargetEq] using honeD
    cases old.mode with
    | covered holdSafe predecessor =>
        have hn2 : 1 < n := by omega
        have hpredD : (D predecessor.predecessor).leader = true :=
          centered_barrier_step_preserves_leader hk ring hn2 C
            predecessor.predecessor tail hready.1
            predecessor.predecessor_leader
        have hpneq : predecessor.predecessor ≠ old.frame.target := by
          intro heq
          have hlater := predecessor.predecessor_later
          rw [heq] at hlater
          exact Nat.lt_irrefl _ hlater
        exact .crossedFresh old.frame.target predecessor.predecessor
          (by simpa [D] using honeTarget)
          htargetEq.symm (by simpa [htargetEq] using htailLeader)
          (by simpa [htargetEq] using htailPhase)
          (by simpa [htargetEq] using htailFresh) hpneq hpredD
          (Nat.le_of_lt (cwDist_lt ring predecessor.predecessor
            old.frame.target))
    | debt holdDanger =>
        have hbirth := danger_to_safe_plateau_is_compensating_tail_birth
          hk ring hn3 C tail tail old.frame.unique_barrier holdDanger
          (by simpa [D, newTail, postStepBarrier, hready] using hnewSafe)
          hpositive
          (by simpa [D, newTail, postStepBarrier, hready] using hplateau)
        have htailNeTarget : tail ≠ old.frame.target := by
          rw [htargetEq]
          exact Ne.symm (rightNeighbor_ne_self ring (by omega) tail)
        exact .crossedFresh old.frame.target tail
          (by simpa [D] using honeTarget) htargetEq.symm
          (by simpa [htargetEq] using htailLeader)
          (by simpa [htargetEq] using htailPhase)
          (by simpa [htargetEq] using htailFresh) htailNeTarget
          hbirth.tail_born
          (Nat.le_of_lt (cwDist_lt ring tail old.frame.target))

inductive SweptBoundedCrossingResult {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (oldC newC : Fin n -> State k)
    (oldTail newTail : Fin n) : Type where
  | rankDrop (drop : PhiAt ring newTail newC < PhiAt ring oldTail oldC)
  | good (certificate : Nonempty (GoodFreshRenewal hk ring newC newTail))

/-- Short-leg crossing closes directly to an actual GoodFreshRenewal payload;
the swept provenance supplies the half-gap bound. -/
def sweptCover_ready_crossing_good {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail selected : Fin n)
    (old : SweptCover (r := r) hk ring C tail)
    (hready : CenteredRenewal.AdvanceReady hk ring C selected)
    (hcrossing : old.frame.advances + 1 = old.frame.targetSteps)
    (hspanHalf : old.frame.targetSteps <= n / 2) :
    SweptBoundedCrossingResult (r := r) hk ring C
      (step hk ring C selected) tail (ring.rightNeighbor tail) := by
  have hselected : selected = tail := by
    have hphysical : BarrierAt hk ring (labelsOf C) selected :=
      (barrierAt_labelsOf_iff hk ring C selected).2 hready.1
    exact (old.frame.unique_barrier selected).1 hphysical
  subst selected
  have htargetEq : old.frame.target = ring.rightNeighbor tail := by
    calc
      old.frame.target =
          cwPos ring old.frame.startTail old.frame.targetSteps :=
        old.frame.target_phys.symm
      _ = cwPos ring old.frame.startTail (old.frame.advances + 1) := by
        rw [hcrossing]
      _ = ring.rightNeighbor
          (cwPos ring old.frame.startTail old.frame.advances) :=
        cwPos_succ ring old.frame.startTail old.frame.advances
      _ = ring.rightNeighbor tail :=
        congrArg ring.rightNeighbor old.frame.tail_phys.symm
  let D := step hk ring C tail
  let newTail := ring.rightNeighbor tail
  have hheadLeader : (C (ring.rightNeighbor tail)).leader = true := by
    simpa [← htargetEq] using old.frame.target_leader
  have hterminal := crosses_leader_head_fresh hk ring hn3 hndvd C tail
    old.frame.unique_barrier hready.2 hheadLeader
  have honeD : OneBarrierAt hk ring D newTail := by
    simpa [D, newTail] using hterminal.1
  have htailLeader : (D newTail).leader = true := by
    simpa [D, newTail] using hterminal.2.1
  have htailPhase : (D newTail).phase = false := by
    simpa [D, newTail] using hterminal.2.2.1
  have htailFresh : MarkFree (D newTail) := by
    simpa [D, newTail] using hterminal.2.2.2.1
  have hle : PhiAt ring newTail D <= PhiAt ring tail C := by
    simpa [D, newTail] using hterminal.2.2.2.2
  by_cases hdrop : PhiAt ring newTail D < PhiAt ring tail C
  · exact .rankDrop hdrop
  · have hplateau : PhiAt ring newTail D = PhiAt ring tail C := by omega
    have hrankD : PhiAt ring newTail D = r := hplateau.trans old.rank_eq
    have hpositive : 1 < PhiAt ring tail C := by
      rw [old.rank_eq]
      exact old.rank_gt_one
    have hnewSafe : ¬ Dangerous (cutView ring newTail D) := by
      apply not_dangerous_of_tail_leader ring
      · change (D (cutPos ring newTail (tailCoord ring))).leader = true
        rw [cutPos_tailCoord]
        exact htailLeader
      · change (D (cutPos ring newTail (tailCoord ring))).probe = false
        rw [cutPos_tailCoord]
        exact htailFresh.2
    cases old.mode with
    | covered holdSafe predecessor =>
        have hn2 : 1 < n := by omega
        have hpredD : (D predecessor.predecessor).leader = true :=
          centered_barrier_step_preserves_leader hk ring hn2 C
            predecessor.predecessor tail hready.1
            predecessor.predecessor_leader
        have hpneq : predecessor.predecessor ≠ newTail := by
          intro heq
          have hlater := predecessor.predecessor_later
          have hsame : predecessor.predecessor = old.frame.target :=
            heq.trans htargetEq.symm
          rw [hsame] at hlater
          exact (Nat.lt_irrefl _ hlater)
        have hspanLt : old.frame.targetSteps < n := by
          have hhalfLt : n / 2 < n := by omega
          omega
        have hgapSpan := predecessor.gap_le_targetSteps hspanLt
        let fresh : FreshWithPredecessor hk ring D newTail := {
          barrier := honeD
          tailLeader := htailLeader
          tailPhase := htailPhase
          tailFresh := htailFresh
          predecessor := predecessor.predecessor
          predecessor_ne := hpneq
          predecessorLeader := hpredD
        }
        have hgapFresh : cwDist ring fresh.predecessor newTail <= n / 2 := by
          dsimp [fresh]
          have hnewTarget : newTail = old.frame.target := by
            exact htargetEq.symm
          rw [hnewTarget]
          exact Nat.le_trans hgapSpan hspanHalf
        exact SweptBoundedCrossingResult.good (fresh.toGood hgapFresh)
    | debt holdDanger =>
        have hbirth := danger_to_safe_plateau_is_compensating_tail_birth
          hk ring hn3 C tail tail old.frame.unique_barrier holdDanger
          (by simpa [D, newTail, postStepBarrier, hready] using hnewSafe)
          hpositive
          (by simpa [D, newTail, postStepBarrier, hready] using hplateau)
        have hne : tail ≠ newTail :=
          Ne.symm (rightNeighbor_ne_self ring (by omega) tail)
        have hgapOne : cwDist ring tail newTail = 1 := by
          exact (cwPos_bounded_unique ring tail newTail 1 (by omega)
            (by simp [newTail])).symm
        have honeHalf : cwDist ring tail newTail <= n / 2 := by
          rw [hgapOne]
          omega
        let fresh : FreshWithPredecessor hk ring D newTail := {
          barrier := honeD
          tailLeader := htailLeader
          tailPhase := htailPhase
          tailFresh := htailFresh
          predecessor := tail
          predecessor_ne := hne
          predecessorLeader := hbirth.tail_born
        }
        exact .good (fresh.toGood honeHalf)

/-- Branch-complete literal protocol law for the covered/debt search.  It
accepts an arbitrary scheduler edge: non-advancing interactions preserve the
lifted counter, genuine advances either continue before the target or report
the exact fresh crossing terminal. -/
def sweptCover_literal_step {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail selected : Fin n)
    (old : SweptCover (r := r) hk ring C tail) :
    SweptCoverStepResult (r := r) hk ring C (step hk ring C selected) tail
      (postStepBarrier hk ring C tail selected) := by
  by_cases hready : CenteredRenewal.AdvanceReady hk ring C selected
  · by_cases hbefore : old.frame.advances + 1 < old.frame.targetSteps
    · simpa [postStepBarrier, hready] using
        (sweptCover_step_of_ready_before_target hk ring hn3 hndvd C tail
          selected old hready hbefore).toStepResult
    · have hcrossing : old.frame.advances + 1 =
          old.frame.targetSteps := by
        have hold := old.frame.before_target
        omega
      simpa [postStepBarrier, hready] using
        sweptCover_step_of_ready_crossing hk ring hn3 hndvd C tail selected
          old hready hcrossing
  · simpa [postStepBarrier, hready] using
      (sweptCover_step_of_not_ready hk ring hn3 hndvd C tail selected old
        hready).toStepResult

/-! ## First-leg ahead cover

The first target uses the same lifted crossing frame but deliberately carries
no swept-origin claim for its mutable witness.  This separation prevents the
false initialization `index <= advances = 0` for an arbitrary later leader. -/

abbrev CrossingFrame {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n -> State k) (tail : Fin n) : Type :=
  SweepFrame hk ring C tail

inductive AheadCover {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n -> State k} {tail : Fin n}
    (frame : CrossingFrame hk ring C tail) : Type where
  | covered (danger_free : ¬ Dangerous (cutView ring tail C))
      (witness : Fin n) (witness_leader : (C witness).leader = true)
      (witness_later : LaterAt ring tail frame.target witness) :
      AheadCover frame
  | debt (dangerous : Dangerous (cutView ring tail C)) : AheadCover frame

structure AheadState {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k) (tail : Fin n) : Type where
  rank_eq : PhiAt ring tail C = r
  rank_gt_one : 1 < r
  frame : CrossingFrame hk ring C tail
  mode : AheadCover frame

inductive AheadStepResult {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (oldC newC : Fin n -> State k)
    (oldTail newTail : Fin n) : Type where
  | rankDrop (drop : PhiAt ring newTail newC < PhiAt ring oldTail oldC)
  | continue (next : AheadState (r := r) hk ring newC newTail)
  | crossedFresh (target predecessor : Fin n)
      (barrier : OneBarrierAt hk ring newC target)
      (tail_eq : newTail = target)
      (rank_eq : PhiAt ring newTail newC = r)
      (target_leader : (newC target).leader = true)
      (target_phase : (newC target).phase = false)
      (target_fresh : MarkFree (newC target))
      (predecessor_ne : predecessor ≠ target)
      (predecessor_leader : (newC predecessor).leader = true) :
      AheadStepResult hk ring oldC newC oldTail newTail

/-- First-leg steps which have not reached the fixed target have only the
rank-drop and continuation outcomes. -/
inductive AheadActiveStepResult {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (oldC newC : Fin n -> State k)
    (oldTail newTail : Fin n) (expectedAdvances : Nat) : Type where
  | rankDrop (drop : PhiAt ring newTail newC < PhiAt ring oldTail oldC)
  | continue (next : AheadState (r := r) hk ring newC newTail)
      (advances_eq : next.frame.advances = expectedAdvances)

def AheadActiveStepResult.toStepResult {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {oldC newC : Fin n -> State k}
    {oldTail newTail : Fin n} {expectedAdvances : Nat}
    (result : AheadActiveStepResult (r := r) hk ring oldC newC
      oldTail newTail expectedAdvances) :
    AheadStepResult (r := r) hk ring oldC newC oldTail newTail :=
  match result with
  | .rankDrop drop => .rankDrop drop
  | .continue next _ => .continue next

/-- Reaching the first fixed target cannot continue the same leg. -/
inductive AheadCrossingResult {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (oldC newC : Fin n -> State k)
    (oldTail newTail : Fin n) : Type where
  | rankDrop (drop : PhiAt ring newTail newC < PhiAt ring oldTail oldC)
  | crossedFresh (target predecessor : Fin n)
      (barrier : OneBarrierAt hk ring newC target)
      (tail_eq : newTail = target)
      (rank_eq : PhiAt ring newTail newC = r)
      (target_leader : (newC target).leader = true)
      (target_phase : (newC target).phase = false)
      (target_fresh : MarkFree (newC target))
      (predecessor_ne : predecessor ≠ target)
      (predecessor_leader : (newC predecessor).leader = true) :
      AheadCrossingResult hk ring oldC newC oldTail newTail

def AheadCrossingResult.toStepResult {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {oldC newC : Fin n -> State k}
    {oldTail newTail : Fin n}
    (result : AheadCrossingResult (r := r) hk ring oldC newC oldTail
      newTail) : AheadStepResult (r := r) hk ring oldC newC oldTail newTail :=
  match result with
  | .rankDrop drop => .rankDrop drop
  | .crossedFresh target predecessor barrier tail_eq rank_eq target_leader
      target_phase target_fresh predecessor_ne predecessor_leader =>
    .crossedFresh target predecessor barrier tail_eq rank_eq target_leader
      target_phase target_fresh predecessor_ne predecessor_leader

def aheadCover_step_of_not_ready {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail selected : Fin n)
    (old : AheadState (r := r) hk ring C tail)
    (hnotready : ¬ CenteredRenewal.AdvanceReady hk ring C selected) :
    AheadActiveStepResult (r := r) hk ring C (step hk ring C selected)
      tail tail old.frame.advances := by
  let D := step hk ring C selected
  have hrank := Rank.oneBarrier_phi_step_le hk ring hn3 C tail selected
    hndvd old.frame.unique_barrier
  have honeD : OneBarrierAt hk ring D tail := by
    simpa [D, hnotready, OneBarrierCleanup.step] using hrank.1
  have hle : PhiAt ring tail D <= PhiAt ring tail C := by
    simpa [D, hnotready, OneBarrierCleanup.step] using hrank.2
  by_cases hdrop : PhiAt ring tail D < PhiAt ring tail C
  · exact .rankDrop hdrop
  · have hplateau : PhiAt ring tail D = PhiAt ring tail C := by omega
    have hrankD : PhiAt ring tail D = r := hplateau.trans old.rank_eq
    have hpositive : 1 < PhiAt ring tail C := by
      rw [old.rank_eq]
      exact old.rank_gt_one
    have htargetD : (D old.frame.target).leader = true := by
      cases old.mode with
      | covered hsafe witness hwitness hlater =>
          exact protected_target_survives_plateau_step hk ring hn3 C tail
            selected old.frame.target witness old.frame.unique_barrier
            old.frame.target_leader hlater hwitness hpositive hplateau
      | debt hdanger =>
          exact fixed_cut_leader_survives_plateau_step hk ring hn3 C tail
            selected old.frame.target old.frame.target_leader hpositive
            (fun hsafe => False.elim (hsafe hdanger)) hplateau
    let nextFrame : CrossingFrame hk ring D tail := {
      startTail := old.frame.startTail
      target := old.frame.target
      targetSteps := old.frame.targetSteps
      advances := old.frame.advances
      targetSteps_pos := old.frame.targetSteps_pos
      targetSteps_le := old.frame.targetSteps_le
      target_phys := old.frame.target_phys
      before_target := old.frame.before_target
      tail_phys := old.frame.tail_phys
      unique_barrier := honeD
      target_leader := htargetD
    }
    by_cases hnewDanger : Dangerous (cutView ring tail D)
    · exact .continue {
        rank_eq := hrankD
        rank_gt_one := old.rank_gt_one
        frame := nextFrame
        mode := .debt hnewDanger } rfl
    · cases old.mode with
      | covered holdSafe witness hwitness hlater =>
          have hwitnessD : (D witness).leader = true :=
            fixed_cut_leader_survives_plateau_step hk ring hn3 C tail
              selected witness hwitness hpositive (fun _ => hnewDanger)
              hplateau
          exact .continue {
            rank_eq := hrankD
            rank_gt_one := old.rank_gt_one
            frame := nextFrame
            mode := .covered hnewDanger witness hwitnessD hlater } rfl
      | debt holdDanger =>
          have hbirth := danger_to_safe_plateau_is_compensating_tail_birth
            hk ring hn3 C tail selected old.frame.unique_barrier holdDanger
            (by simpa [D, postStepBarrier, hnotready] using hnewDanger)
            hpositive (by simpa [D, postStepBarrier, hnotready] using hplateau)
          have htargetNeTail : old.frame.target ≠ tail := by
            intro heq
            have ht := old.frame.target_leader
            rw [heq] at ht
            have hf := hbirth.tail_follower
            rw [ht] at hf
            contradiction
          have hlater : LaterAt ring tail old.frame.target tail := by
            simpa [LaterAt, StrictlyLaterAt] using
              strictlyLater_tail_of_ne ring old.frame.target tail
                htargetNeTail
          exact .continue {
            rank_eq := hrankD
            rank_gt_one := old.rank_gt_one
            frame := nextFrame
            mode := .covered hnewDanger tail hbirth.tail_born hlater } rfl

def aheadCover_step_of_ready_before_target {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail selected : Fin n)
    (old : AheadState (r := r) hk ring C tail)
    (hready : CenteredRenewal.AdvanceReady hk ring C selected)
    (hbefore : old.frame.advances + 1 < old.frame.targetSteps) :
    AheadActiveStepResult (r := r) hk ring C (step hk ring C selected) tail
      (ring.rightNeighbor tail) (old.frame.advances + 1) := by
  have hselected : selected = tail := by
    have hphysical : BarrierAt hk ring (labelsOf C) selected :=
      (barrierAt_labelsOf_iff hk ring C selected).2 hready.1
    exact (old.frame.unique_barrier selected).1 hphysical
  subst selected
  let D := step hk ring C tail
  let newTail := ring.rightNeighbor tail
  have hrank := Rank.oneBarrier_phi_step_le hk ring hn3 C tail tail hndvd
    old.frame.unique_barrier
  have honeD : OneBarrierAt hk ring D newTail := by
    simpa [D, newTail, hready, OneBarrierCleanup.step] using hrank.1
  have hle : PhiAt ring newTail D <= PhiAt ring tail C := by
    simpa [D, newTail, hready, OneBarrierCleanup.step] using hrank.2
  by_cases hdrop : PhiAt ring newTail D < PhiAt ring tail C
  · exact .rankDrop hdrop
  · have hplateau : PhiAt ring newTail D = PhiAt ring tail C := by omega
    have hrankD : PhiAt ring newTail D = r := hplateau.trans old.rank_eq
    have hn2 : 1 < n := by omega
    have htargetD : (D old.frame.target).leader = true :=
      centered_barrier_step_preserves_leader hk ring hn2 C old.frame.target
        tail hready.1 old.frame.target_leader
    have htailPhys : newTail =
        cwPos ring old.frame.startTail (old.frame.advances + 1) := by
      calc
        newTail = ring.rightNeighbor tail := rfl
        _ = ring.rightNeighbor
            (cwPos ring old.frame.startTail old.frame.advances) :=
          congrArg ring.rightNeighbor old.frame.tail_phys
        _ = cwPos ring old.frame.startTail (old.frame.advances + 1) :=
          (cwPos_succ ring old.frame.startTail old.frame.advances).symm
    let nextFrame : CrossingFrame hk ring D newTail := {
      startTail := old.frame.startTail
      target := old.frame.target
      targetSteps := old.frame.targetSteps
      advances := old.frame.advances + 1
      targetSteps_pos := old.frame.targetSteps_pos
      targetSteps_le := old.frame.targetSteps_le
      target_phys := old.frame.target_phys
      before_target := hbefore
      tail_phys := htailPhys
      unique_barrier := honeD
      target_leader := htargetD
    }
    have hpositive : 1 < PhiAt ring tail C := by
      rw [old.rank_eq]
      exact old.rank_gt_one
    have htargetPos := old.frame.target_cutCoord_pos_before_next hbefore
    by_cases hnewDanger : Dangerous (cutView ring newTail D)
    · exact .continue {
        rank_eq := hrankD
        rank_gt_one := old.rank_gt_one
        frame := nextFrame
        mode := .debt hnewDanger } rfl
    · cases old.mode with
      | covered holdSafe witness hwitness hlater =>
          have hwitnessD : (D witness).leader = true :=
            centered_barrier_step_preserves_leader hk ring hn2 C witness tail
              hready.1 hwitness
          have hlaterD := laterAt_nextBarrier ring tail old.frame.target
            witness hlater htargetPos
          exact .continue {
            rank_eq := hrankD
            rank_gt_one := old.rank_gt_one
            frame := nextFrame
            mode := .covered hnewDanger witness hwitnessD hlaterD } rfl
      | debt holdDanger =>
          have hbirth := danger_to_safe_plateau_is_compensating_tail_birth
            hk ring hn3 C tail tail old.frame.unique_barrier holdDanger
            (by simpa [D, newTail, postStepBarrier, hready] using hnewDanger)
            hpositive
            (by simpa [D, newTail, postStepBarrier, hready] using hplateau)
          have htargetNeTail : old.frame.target ≠ tail := by
            intro heq
            have ht := old.frame.target_leader
            rw [heq] at ht
            have hf := hbirth.tail_follower
            rw [ht] at hf
            contradiction
          have hlaterD : LaterAt ring newTail old.frame.target tail :=
            laterAt_oldTail_after_advance ring hn3 tail old.frame.target
              htargetPos htargetNeTail
          exact .continue {
            rank_eq := hrankD
            rank_gt_one := old.rank_gt_one
            frame := nextFrame
            mode := .covered hnewDanger tail hbirth.tail_born hlaterD } rfl

def aheadCover_step_of_ready_crossing {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail selected : Fin n)
    (old : AheadState (r := r) hk ring C tail)
    (hready : CenteredRenewal.AdvanceReady hk ring C selected)
    (hcrossing : old.frame.advances + 1 = old.frame.targetSteps) :
    AheadCrossingResult (r := r) hk ring C (step hk ring C selected) tail
      (ring.rightNeighbor tail) := by
  have hselected : selected = tail := by
    have hphysical : BarrierAt hk ring (labelsOf C) selected :=
      (barrierAt_labelsOf_iff hk ring C selected).2 hready.1
    exact (old.frame.unique_barrier selected).1 hphysical
  subst selected
  have htargetEq : old.frame.target = ring.rightNeighbor tail := by
    calc
      old.frame.target =
          cwPos ring old.frame.startTail old.frame.targetSteps :=
        old.frame.target_phys.symm
      _ = cwPos ring old.frame.startTail (old.frame.advances + 1) := by
        rw [hcrossing]
      _ = ring.rightNeighbor
          (cwPos ring old.frame.startTail old.frame.advances) :=
        cwPos_succ ring old.frame.startTail old.frame.advances
      _ = ring.rightNeighbor tail :=
        congrArg ring.rightNeighbor old.frame.tail_phys.symm
  let D := step hk ring C tail
  let newTail := ring.rightNeighbor tail
  have hheadLeader : (C (ring.rightNeighbor tail)).leader = true := by
    simpa [← htargetEq] using old.frame.target_leader
  have hterminal := crosses_leader_head_fresh hk ring hn3 hndvd C tail
    old.frame.unique_barrier hready.2 hheadLeader
  have honeD : OneBarrierAt hk ring D newTail := by
    simpa [D, newTail] using hterminal.1
  have htailLeader : (D newTail).leader = true := by
    simpa [D, newTail] using hterminal.2.1
  have htailPhase : (D newTail).phase = false := by
    simpa [D, newTail] using hterminal.2.2.1
  have htailFresh : MarkFree (D newTail) := by
    simpa [D, newTail] using hterminal.2.2.2.1
  have hle : PhiAt ring newTail D <= PhiAt ring tail C := by
    simpa [D, newTail] using hterminal.2.2.2.2
  by_cases hdrop : PhiAt ring newTail D < PhiAt ring tail C
  · exact .rankDrop hdrop
  · have hplateau : PhiAt ring newTail D = PhiAt ring tail C := by omega
    have hrankD : PhiAt ring newTail D = r := hplateau.trans old.rank_eq
    have hpositive : 1 < PhiAt ring tail C := by
      rw [old.rank_eq]
      exact old.rank_gt_one
    have hnewSafe : ¬ Dangerous (cutView ring newTail D) := by
      apply not_dangerous_of_tail_leader ring
      · change (D (cutPos ring newTail (tailCoord ring))).leader = true
        rw [cutPos_tailCoord]
        exact htailLeader
      · change (D (cutPos ring newTail (tailCoord ring))).probe = false
        rw [cutPos_tailCoord]
        exact htailFresh.2
    have honeTarget : OneBarrierAt hk ring D old.frame.target := by
      simpa [newTail, htargetEq] using honeD
    cases old.mode with
    | covered holdSafe witness hwitness hlater =>
        have hn2 : 1 < n := by omega
        have hwitnessD : (D witness).leader = true :=
          centered_barrier_step_preserves_leader hk ring hn2 C witness tail
            hready.1 hwitness
        have hwneq : witness ≠ old.frame.target := by
          intro heq
          rw [heq] at hlater
          exact Nat.lt_irrefl _ hlater
        exact .crossedFresh old.frame.target witness
          (by simpa [D] using honeTarget) htargetEq.symm hrankD
          (by simpa [htargetEq] using htailLeader)
          (by simpa [htargetEq] using htailPhase)
          (by simpa [htargetEq] using htailFresh) hwneq hwitnessD
    | debt holdDanger =>
        have hbirth := danger_to_safe_plateau_is_compensating_tail_birth
          hk ring hn3 C tail tail old.frame.unique_barrier holdDanger
          (by simpa [D, newTail, postStepBarrier, hready] using hnewSafe)
          hpositive
          (by simpa [D, newTail, postStepBarrier, hready] using hplateau)
        have htailNeTarget : tail ≠ old.frame.target := by
          rw [htargetEq]
          exact Ne.symm (rightNeighbor_ne_self ring (by omega) tail)
        exact .crossedFresh old.frame.target tail
          (by simpa [D] using honeTarget) htargetEq.symm hrankD
          (by simpa [htargetEq] using htailLeader)
          (by simpa [htargetEq] using htailPhase)
          (by simpa [htargetEq] using htailFresh) htailNeTarget
          hbirth.tail_born

def aheadCover_literal_step {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail selected : Fin n)
    (old : AheadState (r := r) hk ring C tail) :
    AheadStepResult (r := r) hk ring C (step hk ring C selected) tail
      (postStepBarrier hk ring C tail selected) := by
  by_cases hready : CenteredRenewal.AdvanceReady hk ring C selected
  · by_cases hbefore : old.frame.advances + 1 < old.frame.targetSteps
    · simpa [postStepBarrier, hready] using
        (aheadCover_step_of_ready_before_target hk ring hn3 hndvd C tail
          selected old hready hbefore).toStepResult
    · have hold := old.frame.before_target
      have hcrossing : old.frame.advances + 1 =
          old.frame.targetSteps := by omega
      simpa [postStepBarrier, hready] using
        (aheadCover_step_of_ready_crossing hk ring hn3 hndvd C tail selected
          old hready hcrossing).toStepResult
  · simpa [postStepBarrier, hready] using
      (aheadCover_step_of_not_ready hk ring hn3 hndvd C tail selected old
        hready).toStepResult

/-- Every positive-rank one-barrier plateau has a valid first-leg seed.  In
safe mode two leaders are selected and ordered in the current cut; the earlier
one is the fixed target and the later one is the bare cover witness.  In debt
mode any existing leader is a target and no false witness is asserted. -/
theorem exists_initialAheadState {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (C : Fin n -> State k)
    (tail : Fin n) (hone : OneBarrierAt hk ring C tail)
    (hrank : PhiAt ring tail C = r) (hr1 : 1 < r) :
    Nonempty (AheadState (r := r) hk ring C tail) := by
  let X := cutView ring tail C
  have hshape := plateau_shape X hrank hr1
  rcases hshape with hsafe | hdanger
  · have htwo : 2 <= leaderCount X := by omega
    obtain ⟨i, j, hij, hi, hj⟩ := exists_two_true_of_two_le_bitCount
      (fun q => (X q).leader) htwo
    have horder : i.val < j.val ∨ j.val < i.val := by
      have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      omega
    rcases horder with hijlt | hjilt
    · let target := cutPos ring tail i
      let witness := cutPos ring tail j
      obtain ⟨span, hspanPos, hspanLe, hspanPhys⟩ :=
        exists_barrierAfter_eq ring tail target
      have htarget : (C target).leader = true := by
        simpa [X, cutView, target] using hi
      have hwitness : (C witness).leader = true := by
        simpa [X, cutView, witness] using hj
      have hlater : LaterAt ring tail target witness := by
        unfold LaterAt target witness
        rw [cutCoord_cutPos, cutCoord_cutPos]
        exact hijlt
      let frame : CrossingFrame hk ring C tail := {
        startTail := tail
        target := target
        targetSteps := span
        advances := 0
        targetSteps_pos := hspanPos
        targetSteps_le := hspanLe
        target_phys := by
          rw [← barrierAfter_eq_cwPos]
          exact hspanPhys
        before_target := hspanPos
        tail_phys := by
          simp
        unique_barrier := hone
        target_leader := htarget
      }
      exact ⟨{
        rank_eq := hrank
        rank_gt_one := hr1
        frame := frame
        mode := .covered hsafe.1 witness hwitness hlater }⟩
    · let target := cutPos ring tail j
      let witness := cutPos ring tail i
      obtain ⟨span, hspanPos, hspanLe, hspanPhys⟩ :=
        exists_barrierAfter_eq ring tail target
      have htarget : (C target).leader = true := by
        simpa [X, cutView, target] using hj
      have hwitness : (C witness).leader = true := by
        simpa [X, cutView, witness] using hi
      have hlater : LaterAt ring tail target witness := by
        unfold LaterAt target witness
        rw [cutCoord_cutPos, cutCoord_cutPos]
        exact hjilt
      let frame : CrossingFrame hk ring C tail := {
        startTail := tail
        target := target
        targetSteps := span
        advances := 0
        targetSteps_pos := hspanPos
        targetSteps_le := hspanLe
        target_phys := by
          rw [← barrierAfter_eq_cwPos]
          exact hspanPhys
        before_target := hspanPos
        tail_phys := by
          simp
        unique_barrier := hone
        target_leader := htarget
      }
      exact ⟨{
        rank_eq := hrank
        rank_gt_one := hr1
        frame := frame
        mode := .covered hsafe.1 witness hwitness hlater }⟩
  · have hpos : 0 < leaderCount X := by omega
    obtain ⟨i, hi⟩ := exists_true_of_bitCount_pos
      (fun q => (X q).leader) hpos
    let target := cutPos ring tail i
    obtain ⟨span, hspanPos, hspanLe, hspanPhys⟩ :=
      exists_barrierAfter_eq ring tail target
    have htarget : (C target).leader = true := by
      simpa [X, cutView, target] using hi
    let frame : CrossingFrame hk ring C tail := {
      startTail := tail
      target := target
      targetSteps := span
      advances := 0
      targetSteps_pos := hspanPos
      targetSteps_le := hspanLe
      target_phys := by
        rw [← barrierAfter_eq_cwPos]
        exact hspanPhys
      before_target := hspanPos
      tail_phys := by
        simp
      unique_barrier := hone
      target_leader := htarget
    }
    exact ⟨{
      rank_eq := hrank
      rank_gt_one := hr1
      frame := frame
      mode := .debt hdanger.1 }⟩

/-! ## Total pathwise search machine -/

/-- Proof state driven by the scheduler's literal selected edge.  Terminal
constructors retain the exact post-step physical configuration.  The second
leg stores the first crossing count and its fixed half-ring span. -/
inductive RenewalProofState {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) : Type where
  | first {C : Fin n -> State k} {tail : Fin n}
      (state : AheadState (r := r) hk ring C tail)
  | second {C : Fin n -> State k} {tail : Fin n}
      (firstUsed : Nat) (firstUsed_le : firstUsed <= n)
      (state : SweptCover (r := r) hk ring C tail)
      (span_le_half : state.frame.targetSteps <= n / 2)
  | good {C : Fin n -> State k} {tail : Fin n}
      (used : Nat) (certificate : Nonempty (GoodFreshRenewal hk ring C tail))
  | dropped {C : Fin n -> State k} {tail : Fin n}
      (used : Nat) (drop : PhiAt ring tail C < r)

def RenewalProofState.config {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (state : RenewalProofState (r := r) hk ring) :
    Fin n -> State k :=
  match state with
  | .first (C := C) _ => C
  | .second (C := C) _ _ _ _ => C
  | .good (C := C) _ _ => C
  | .dropped (C := C) _ _ => C

def RenewalProofState.tail {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (state : RenewalProofState (r := r) hk ring) :
    Fin n :=
  match state with
  | .first (tail := tail) _ => tail
  | .second (tail := tail) _ _ _ _ => tail
  | .good (tail := tail) _ _ => tail
  | .dropped (tail := tail) _ _ => tail

/-- Count of genuine phase-one barrier advances already consumed. -/
def RenewalProofState.advances {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (state : RenewalProofState (r := r) hk ring) :
    Nat :=
  match state with
  | .first active => active.frame.advances
  | .second firstUsed _ active _ => firstUsed + active.frame.advances
  | .good used _ => used
  | .dropped used _ => used

def RenewalProofState.IsTerminal {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (state : RenewalProofState (r := r) hk ring) :
    Prop :=
  match state with
  | .good _ _ => True
  | .dropped _ _ => True
  | .first _ => False
  | .second _ _ _ _ => False

/-- Canonical first-leg seed from the actual one-barrier plateau. -/
noncomputable def initialRenewalProofState {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (C : Fin n -> State k)
    (tail : Fin n) (hone : OneBarrierAt hk ring C tail)
    (hrank : PhiAt ring tail C = r) (hr1 : 1 < r) :
    RenewalProofState (r := r) hk ring :=
  .first (Classical.choice
    (exists_initialAheadState hk ring C tail hone hrank hr1))

/-- Every active proof state is strictly below the exact `n+n/2` advance
budget.  Equality is therefore allowed only at a terminal reached by the
last counted advance. -/
theorem RenewalProofState.active_advances_lt {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n)
    (state : RenewalProofState (r := r) hk ring)
    (hactive : ¬ state.IsTerminal) :
    state.advances < n + n / 2 := by
  cases state with
  | first active =>
      simp [RenewalProofState.advances]
      have hlt := active.frame.before_target
      have hle := active.frame.targetSteps_le
      have hhalf : 0 < n / 2 := by omega
      omega
  | second firstUsed hfirst active hspan =>
      simp [RenewalProofState.advances]
      have hlt := active.frame.before_target
      omega
  | good used certificate =>
      simp [RenewalProofState.IsTerminal] at hactive
  | dropped used drop =>
      simp [RenewalProofState.IsTerminal] at hactive

noncomputable def aheadActiveToProofState {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (old : AheadState (r := r) hk ring C tail) (nextUsed : Nat)
    (result : AheadActiveStepResult (r := r) hk ring C D tail d
      nextUsed) : RenewalProofState (r := r) hk ring := by
  cases result with
  | rankDrop drop =>
      rw [old.rank_eq] at drop
      exact .dropped nextUsed drop
  | «continue» next advances_eq => exact .first next

/-- Convert the actual first crossing without changing its physical endpoint.
A short fresh gap terminates immediately; a bad fresh gap seeds the
complementary half-ring leg at that same endpoint. -/
noncomputable def aheadCrossingToProofState {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (old : AheadState (r := r) hk ring C tail) (nextUsed : Nat)
    (hused : nextUsed <= n)
    (result : AheadCrossingResult (r := r) hk ring C D tail d) :
    RenewalProofState (r := r) hk ring := by
  cases result with
  | rankDrop drop =>
      rw [old.rank_eq] at drop
      exact .dropped nextUsed drop
  | crossedFresh target predecessor barrier tail_eq rank_eq target_leader
      target_phase target_fresh predecessor_ne predecessor_leader =>
      let fresh : FreshWithPredecessor hk ring D d := {
        barrier := by simpa [tail_eq] using barrier
        tailLeader := by simpa [tail_eq] using target_leader
        tailPhase := by simpa [tail_eq] using target_phase
        tailFresh := by simpa [tail_eq] using target_fresh
        predecessor := predecessor
        predecessor_ne := by
          intro heq
          exact predecessor_ne (heq.trans tail_eq)
        predecessorLeader := predecessor_leader
      }
      by_cases hgood : Nonempty (GoodFreshRenewal hk ring D d)
      · exact .good nextUsed hgood
      · let seed := Classical.choice
            (badFresh_secondSeed hk ring D d fresh rank_eq
              old.rank_gt_one hgood)
        exact .second nextUsed hused seed.state seed.span_le_half

noncomputable def sweptActiveToProofState {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (firstUsed : Nat) (hfirst : firstUsed <= n)
    (old : SweptCover (r := r) hk ring C tail)
    (hspan : old.frame.targetSteps <= n / 2)
    {expectedAdvances : Nat}
    (result : SweptCoverActiveStepResult (r := r) hk ring C D tail d
      expectedAdvances old.frame.targetSteps) :
    RenewalProofState (r := r) hk ring := by
  cases result with
  | rankDrop drop =>
      rw [old.rank_eq] at drop
      exact .dropped (firstUsed + expectedAdvances) drop
  | «continue» next advances_eq targetSteps_eq =>
      have hspanNext : next.frame.targetSteps <= n / 2 := by
        rw [targetSteps_eq]
        exact hspan
      exact .second firstUsed hfirst next hspanNext

def sweptCrossingToProofState {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (old : SweptCover (r := r) hk ring C tail) (nextUsed : Nat)
    (result : SweptBoundedCrossingResult (r := r) hk ring C D tail d) :
    RenewalProofState (r := r) hk ring := by
  cases result with
  | rankDrop drop =>
      rw [old.rank_eq] at drop
      exact .dropped nextUsed drop
  | good certificate => exact .good nextUsed certificate

/-- Total scheduler-edge interpreter.  Active states take the literal centered
step on `selected`; terminal states are absorbing because the timed tree binds
their physical payload immediately rather than padding it. -/
noncomputable def renewalProofNext {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : RenewalProofState (r := r) hk ring) (selected : Fin n) :
    RenewalProofState (r := r) hk ring := by
  cases state with
  | @first C tail old =>
      by_cases hready : CenteredRenewal.AdvanceReady hk ring C selected
      · by_cases hbefore : old.frame.advances + 1 < old.frame.targetSteps
        · exact aheadActiveToProofState hk ring old
            (old.frame.advances + 1)
            (aheadCover_step_of_ready_before_target hk ring hn3 hndvd C tail
              selected old hready hbefore)
        · have hcrossing : old.frame.advances + 1 =
              old.frame.targetSteps := by
            have hold := old.frame.before_target
            omega
          have hused : old.frame.advances + 1 <= n := by
            rw [hcrossing]
            exact old.frame.targetSteps_le
          exact aheadCrossingToProofState hk ring old
            (old.frame.advances + 1) hused
            (aheadCover_step_of_ready_crossing hk ring hn3 hndvd C tail
              selected old hready hcrossing)
      · exact aheadActiveToProofState hk ring old old.frame.advances
          (aheadCover_step_of_not_ready hk ring hn3 hndvd C tail selected old
            hready)
  | @second C tail firstUsed hfirst old hspan =>
      by_cases hready : CenteredRenewal.AdvanceReady hk ring C selected
      · by_cases hbefore : old.frame.advances + 1 < old.frame.targetSteps
        · exact sweptActiveToProofState hk ring firstUsed hfirst old hspan
            (sweptCover_step_of_ready_before_target hk ring hn3 hndvd C tail
              selected old hready hbefore)
        · have hcrossing : old.frame.advances + 1 =
              old.frame.targetSteps := by
            have hold := old.frame.before_target
            omega
          exact sweptCrossingToProofState hk ring old
            (firstUsed + (old.frame.advances + 1))
            (sweptCover_ready_crossing_good hk ring hn3 hndvd C tail selected
              old hready hcrossing hspan)
      · exact sweptActiveToProofState hk ring firstUsed hfirst old hspan
          (sweptCover_step_of_not_ready hk ring hn3 hndvd C tail selected old
            hready)
  | good used certificate => exact .good used certificate
  | dropped used drop => exact .dropped used drop

@[simp] theorem aheadActiveToProofState_config {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (old : AheadState (r := r) hk ring C tail) (nextUsed : Nat)
    (result : AheadActiveStepResult (r := r) hk ring C D tail d nextUsed) :
    (aheadActiveToProofState hk ring old nextUsed result).config = D := by
  cases result <;> rfl

@[simp] theorem aheadActiveToProofState_tail {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (old : AheadState (r := r) hk ring C tail) (nextUsed : Nat)
    (result : AheadActiveStepResult (r := r) hk ring C D tail d nextUsed) :
    (aheadActiveToProofState hk ring old nextUsed result).tail = d := by
  cases result <;> rfl

@[simp] theorem aheadActiveToProofState_advances {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (old : AheadState (r := r) hk ring C tail) (nextUsed : Nat)
    (result : AheadActiveStepResult (r := r) hk ring C D tail d nextUsed) :
    (aheadActiveToProofState hk ring old nextUsed result).advances = nextUsed := by
  cases result with
  | rankDrop drop => rfl
  | «continue» next advances_eq =>
      simp [aheadActiveToProofState, RenewalProofState.advances, advances_eq]

@[simp] theorem aheadCrossingToProofState_config {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (old : AheadState (r := r) hk ring C tail) (nextUsed : Nat)
    (hused : nextUsed <= n)
    (result : AheadCrossingResult (r := r) hk ring C D tail d) :
    (aheadCrossingToProofState hk ring old nextUsed hused result).config = D := by
  cases result with
  | rankDrop drop => rfl
  | crossedFresh target predecessor barrier tail_eq rank_eq target_leader
      target_phase target_fresh predecessor_ne predecessor_leader =>
      simp only [aheadCrossingToProofState]
      split <;> rfl

@[simp] theorem aheadCrossingToProofState_tail {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (old : AheadState (r := r) hk ring C tail) (nextUsed : Nat)
    (hused : nextUsed <= n)
    (result : AheadCrossingResult (r := r) hk ring C D tail d) :
    (aheadCrossingToProofState hk ring old nextUsed hused result).tail = d := by
  cases result with
  | rankDrop drop => rfl
  | crossedFresh target predecessor barrier tail_eq rank_eq target_leader
      target_phase target_fresh predecessor_ne predecessor_leader =>
      simp only [aheadCrossingToProofState]
      split <;> rfl

@[simp] theorem aheadCrossingToProofState_advances {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) {C D : Fin n -> State k}
    {tail d : Fin n} (old : AheadState (r := r) hk ring C tail)
    (nextUsed : Nat) (hused : nextUsed <= n)
    (result : AheadCrossingResult (r := r) hk ring C D tail d) :
    (aheadCrossingToProofState hk ring old nextUsed hused result).advances =
      nextUsed := by
  cases result with
  | rankDrop drop => rfl
  | crossedFresh target predecessor barrier tail_eq rank_eq target_leader
      target_phase target_fresh predecessor_ne predecessor_leader =>
      simp only [aheadCrossingToProofState]
      split
      · rfl
      · simp only [RenewalProofState.advances]
        rw [(Classical.choice
          (badFresh_secondSeed hk ring D d
            { barrier := by simpa [tail_eq] using barrier
              tailLeader := by simpa [tail_eq] using target_leader
              tailPhase := by simpa [tail_eq] using target_phase
              tailFresh := by simpa [tail_eq] using target_fresh
              predecessor := predecessor
              predecessor_ne := by
                intro heq
                exact predecessor_ne (heq.trans tail_eq)
              predecessorLeader := predecessor_leader }
            rank_eq old.rank_gt_one (by assumption))).initial_advances]
        omega

@[simp] theorem sweptActiveToProofState_config {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (firstUsed : Nat) (hfirst : firstUsed <= n)
    (old : SweptCover (r := r) hk ring C tail)
    (hspan : old.frame.targetSteps <= n / 2) {expectedAdvances : Nat}
    (result : SweptCoverActiveStepResult (r := r) hk ring C D tail d
      expectedAdvances old.frame.targetSteps) :
    (sweptActiveToProofState hk ring firstUsed hfirst old hspan result).config =
      D := by
  cases result <;> rfl

@[simp] theorem sweptActiveToProofState_tail {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (firstUsed : Nat) (hfirst : firstUsed <= n)
    (old : SweptCover (r := r) hk ring C tail)
    (hspan : old.frame.targetSteps <= n / 2) {expectedAdvances : Nat}
    (result : SweptCoverActiveStepResult (r := r) hk ring C D tail d
      expectedAdvances old.frame.targetSteps) :
    (sweptActiveToProofState hk ring firstUsed hfirst old hspan result).tail =
      d := by
  cases result <;> rfl

@[simp] theorem sweptActiveToProofState_advances {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) {C D : Fin n -> State k}
    {tail d : Fin n} (firstUsed : Nat) (hfirst : firstUsed <= n)
    (old : SweptCover (r := r) hk ring C tail)
    (hspan : old.frame.targetSteps <= n / 2) {expectedAdvances : Nat}
    (result : SweptCoverActiveStepResult (r := r) hk ring C D tail d
      expectedAdvances old.frame.targetSteps) :
    (sweptActiveToProofState hk ring firstUsed hfirst old hspan result).advances =
      firstUsed + expectedAdvances := by
  cases result with
  | rankDrop drop => rfl
  | «continue» next advances_eq targetSteps_eq =>
      simp [sweptActiveToProofState, RenewalProofState.advances, advances_eq]

@[simp] theorem sweptCrossingToProofState_config {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (old : SweptCover (r := r) hk ring C tail) (nextUsed : Nat)
    (result : SweptBoundedCrossingResult (r := r) hk ring C D tail d) :
    (sweptCrossingToProofState hk ring old nextUsed result).config = D := by
  cases result <;> rfl

@[simp] theorem sweptCrossingToProofState_tail {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) {C D : Fin n -> State k} {tail d : Fin n}
    (old : SweptCover (r := r) hk ring C tail) (nextUsed : Nat)
    (result : SweptBoundedCrossingResult (r := r) hk ring C D tail d) :
    (sweptCrossingToProofState hk ring old nextUsed result).tail = d := by
  cases result <;> rfl

@[simp] theorem sweptCrossingToProofState_advances {n k r : Nat}
    (hk : 0 < k) (ring : DirectedRing n) {C D : Fin n -> State k}
    {tail d : Fin n} (old : SweptCover (r := r) hk ring C tail)
    (nextUsed : Nat)
    (result : SweptBoundedCrossingResult (r := r) hk ring C D tail d) :
    (sweptCrossingToProofState hk ring old nextUsed result).advances =
      nextUsed := by
  cases result <;> rfl

/-- On every active proof state, the total interpreter projects to the exact
literal centered configuration step. -/
theorem renewalProofNext_configuration {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : RenewalProofState (r := r) hk ring) (selected : Fin n)
    (hactive : ¬ state.IsTerminal) :
    (renewalProofNext hk ring hn3 hndvd state selected).config =
      step hk ring state.config selected := by
  cases state with
  | @first C tail old =>
      change (renewalProofNext hk ring hn3 hndvd (.first old) selected).config =
        step hk ring C selected
      by_cases hready : CenteredRenewal.AdvanceReady hk ring C selected
      · by_cases hbefore : old.frame.advances + 1 < old.frame.targetSteps
        · simp [renewalProofNext, hready, hbefore]
        · simp [renewalProofNext, hready, hbefore]
      · simp [renewalProofNext, hready]
  | @second C tail firstUsed hfirst old hspan =>
      change (renewalProofNext hk ring hn3 hndvd
        (.second firstUsed hfirst old hspan) selected).config =
          step hk ring C selected
      by_cases hready : CenteredRenewal.AdvanceReady hk ring C selected
      · by_cases hbefore : old.frame.advances + 1 < old.frame.targetSteps
        · simp [renewalProofNext, hready, hbefore]
        · simp [renewalProofNext, hready, hbefore]
      · simp [renewalProofNext, hready]
  | good used certificate =>
      simp [RenewalProofState.IsTerminal] at hactive
  | dropped used drop =>
      simp [RenewalProofState.IsTerminal] at hactive

/-- The barrier pointer projection is the literal `postStepBarrier`; in
particular only phase-one barrier hits count and move it. -/
theorem renewalProofNext_tail {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : RenewalProofState (r := r) hk ring) (selected : Fin n)
    (hactive : ¬ state.IsTerminal) :
    (renewalProofNext hk ring hn3 hndvd state selected).tail =
      postStepBarrier hk ring state.config state.tail selected := by
  cases state with
  | @first C tail old =>
      change (renewalProofNext hk ring hn3 hndvd (.first old) selected).tail =
        postStepBarrier hk ring C tail selected
      by_cases hready : CenteredRenewal.AdvanceReady hk ring C selected
      · by_cases hbefore : old.frame.advances + 1 < old.frame.targetSteps
        · simp [renewalProofNext, postStepBarrier, hready, hbefore]
        · simp [renewalProofNext, postStepBarrier, hready, hbefore]
      · simp [renewalProofNext, postStepBarrier, hready]
  | @second C tail firstUsed hfirst old hspan =>
      change (renewalProofNext hk ring hn3 hndvd
        (.second firstUsed hfirst old hspan) selected).tail =
          postStepBarrier hk ring C tail selected
      by_cases hready : CenteredRenewal.AdvanceReady hk ring C selected
      · by_cases hbefore : old.frame.advances + 1 < old.frame.targetSteps
        · simp [renewalProofNext, postStepBarrier, hready, hbefore]
        · simp [renewalProofNext, postStepBarrier, hready, hbefore]
      · simp [renewalProofNext, postStepBarrier, hready]
  | good used certificate =>
      simp [RenewalProofState.IsTerminal] at hactive
  | dropped used drop =>
      simp [RenewalProofState.IsTerminal] at hactive

/-- Exact genuine-advance counter update along the same scheduler edge. -/
theorem renewalProofNext_advances {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : RenewalProofState (r := r) hk ring) (selected : Fin n)
    (hactive : ¬ state.IsTerminal) :
    (renewalProofNext hk ring hn3 hndvd state selected).advances =
      state.advances +
        if CenteredRenewal.AdvanceReady hk ring state.config selected then 1
        else 0 := by
  cases state with
  | @first C tail old =>
      change (renewalProofNext hk ring hn3 hndvd (.first old) selected).advances =
        old.frame.advances +
          if CenteredRenewal.AdvanceReady hk ring C selected then 1 else 0
      by_cases hready : CenteredRenewal.AdvanceReady hk ring C selected
      · by_cases hbefore : old.frame.advances + 1 < old.frame.targetSteps
        · simp [renewalProofNext, hready, hbefore]
        · simp [renewalProofNext, hready, hbefore]
      · simp [renewalProofNext, hready]
  | @second C tail firstUsed hfirst old hspan =>
      change (renewalProofNext hk ring hn3 hndvd
        (.second firstUsed hfirst old hspan) selected).advances =
          (firstUsed + old.frame.advances) +
            if CenteredRenewal.AdvanceReady hk ring C selected then 1 else 0
      by_cases hready : CenteredRenewal.AdvanceReady hk ring C selected
      · by_cases hbefore : old.frame.advances + 1 < old.frame.targetSteps
        · simp [renewalProofNext, hready, hbefore]
          omega
        · simp [renewalProofNext, hready, hbefore]
          omega
      · simp [renewalProofNext, hready]
  | good used certificate =>
      simp [RenewalProofState.IsTerminal] at hactive
  | dropped used drop =>
      simp [RenewalProofState.IsTerminal] at hactive

theorem RenewalProofState.active_oneBarrier {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (state : RenewalProofState (r := r) hk ring)
    (hactive : ¬ state.IsTerminal) :
    OneBarrierAt hk ring state.config state.tail := by
  cases state with
  | first active => exact active.frame.unique_barrier
  | second firstUsed hfirst active hspan => exact active.frame.unique_barrier
  | good used certificate =>
      simp [RenewalProofState.IsTerminal] at hactive
  | dropped used drop =>
      simp [RenewalProofState.IsTerminal] at hactive

theorem renewalProofNext_terminal_self {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : RenewalProofState (r := r) hk ring) (selected : Fin n)
    (hterminal : state.IsTerminal) :
    renewalProofNext hk ring hn3 hndvd state selected = state := by
  cases state <;> simp [RenewalProofState.IsTerminal] at hterminal
  all_goals rfl

/-- Twice the counted advances plus the current barrier phase.  Each adaptive
selection of the current barrier edge adds exactly one while the search stays
active; every other scheduler edge adds zero. -/
def RenewalProofState.hitClock {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (state : RenewalProofState (r := r) hk ring) : Nat :=
  2 * state.advances + phaseNat ((state.config state.tail).phase)

theorem renewalProofNext_hitClock {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : RenewalProofState (r := r) hk ring) (selected : Fin n)
    (hactive : ¬ state.IsTerminal)
    (hnextActive : ¬ (renewalProofNext hk ring hn3 hndvd state selected).IsTerminal) :
    (renewalProofNext hk ring hn3 hndvd state selected).hitClock =
      state.hitClock + if selected = state.tail then 1 else 0 := by
  let next := renewalProofNext hk ring hn3 hndvd state selected
  have hconfig := renewalProofNext_configuration hk ring hn3 hndvd state
    selected hactive
  have htail := renewalProofNext_tail hk ring hn3 hndvd state selected hactive
  have hadv := renewalProofNext_advances hk ring hn3 hndvd state selected hactive
  have hone := state.active_oneBarrier hactive
  by_cases htarget : selected = state.tail
  · subst selected
    rw [if_pos rfl]
    change next.hitClock = state.hitClock + 1
    have hbar : IsBarrier hk (state.config state.tail)
        (state.config (ring.rightNeighbor state.tail)) :=
      (barrierAt_labelsOf_iff hk ring state.config state.tail).1
        ((hone state.tail).2 rfl)
    cases hphase : (state.config state.tail).phase with
    | false =>
        have hnotready : ¬ CenteredRenewal.AdvanceReady hk ring state.config
            state.tail := by
          intro h
          simp [CenteredRenewal.AdvanceReady,
            CenteredRenewal.PairAdvanceReady, hphase] at h
        have harm := barrier_phase_zero_arms_tail hk ring (by omega)
          state.config state.tail hbar hphase
        have htailSame : next.tail = state.tail := by
          simpa [next, postStepBarrier, hnotready] using htail
        have hphaseNext : (next.config next.tail).phase = true := by
          rw [htailSame, hconfig]
          exact harm
        have hadvEq : next.advances = state.advances := by
          simpa [next, hnotready] using hadv
        simp [RenewalProofState.hitClock, hphase, hphaseNext, hadvEq,
          phaseNat]
    | true =>
        have hready : CenteredRenewal.AdvanceReady hk ring state.config
            state.tail := ⟨hbar, hphase⟩
        have hfresh := CenteredRenewal.barrierStep_phase_one_freshTail hk
          (state.config state.tail)
          (state.config (ring.rightNeighbor state.tail)) hphase
        have htailNext : next.tail = ring.rightNeighbor state.tail := by
          simpa [next, postStepBarrier, hready] using htail
        have hphaseNext : (next.config next.tail).phase = false := by
          rw [htailNext, hconfig]
          have hre : ring.rightNeighbor state.tail ≠ state.tail :=
            rightNeighbor_ne_self ring (by omega) state.tail
          have htrans : CenteredRenewal.transition hk
              (state.config state.tail)
              (state.config (ring.rightNeighbor state.tail)) =
              CenteredRenewal.barrierStep hk (state.config state.tail)
                (state.config (ring.rightNeighbor state.tail)) :=
            CenteredRenewal.transition_of_barrier hk _ _ hbar
          simpa [step, PopulationProtocol.step, CenteredRenewal.protocol,
            htrans, hre] using hfresh.1
        have hadvEq : next.advances = state.advances + 1 := by
          simpa [next, hready] using hadv
        simp [RenewalProofState.hitClock, hphase, hphaseNext, hadvEq,
          phaseNat]
        omega
  · have hphysical : ¬ IsBarrier hk (state.config selected)
        (state.config (ring.rightNeighbor selected)) := by
      intro hb
      exact htarget ((hone selected).1
        ((barrierAt_labelsOf_iff hk ring state.config selected).2 hb))
    have hnotready : ¬ CenteredRenewal.AdvanceReady hk ring state.config
        selected := fun h => hphysical h.1
    have htailSame : next.tail = state.tail := by
      simpa [next, postStepBarrier, hnotready] using htail
    have hphaseSame := step_phases_eq_of_nonbarrier hk ring state.config
      selected hphysical state.tail
    have hphaseNext : (next.config next.tail).phase =
        (state.config state.tail).phase := by
      rw [htailSame, hconfig]
      exact hphaseSame
    rw [if_neg htarget, Nat.add_zero]
    change next.hitClock = state.hitClock
    have hadvEq : next.advances = state.advances := by
      simpa [next, hnotready] using hadv
    simp [RenewalProofState.hitClock, hphaseNext, hadvEq]

noncomputable def renewalProofRun {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    RenewalProofState (r := r) hk ring -> List (Fin n) ->
      RenewalProofState (r := r) hk ring
  | state, [] => state
  | state, selected :: word =>
      renewalProofRun hk ring hn3 hndvd
        (renewalProofNext hk ring hn3 hndvd state selected) word

/-- Number of adaptive current-barrier targets in the same scheduler word. -/
noncomputable def renewalTargetHits {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    RenewalProofState (r := r) hk ring -> List (Fin n) -> Nat
  | _, [] => 0
  | state, selected :: word =>
      (if selected = state.tail then 1 else 0) +
        renewalTargetHits hk ring hn3 hndvd
          (renewalProofNext hk ring hn3 hndvd state selected) word

theorem renewalProofRun_terminal_self {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : RenewalProofState (r := r) hk ring) (word : List (Fin n))
    (hterminal : state.IsTerminal) :
    renewalProofRun hk ring hn3 hndvd state word = state := by
  induction word generalizing state with
  | nil => rfl
  | cons selected word ih =>
      rw [renewalProofRun, renewalProofNext_terminal_self hk ring hn3 hndvd
        state selected hterminal]
      exact ih state hterminal

theorem RenewalProofState.active_hitClock_lt_four_mul {n k r : Nat}
    {hk : 0 < k} {ring : DirectedRing n} (hn3 : 3 <= n)
    (state : RenewalProofState (r := r) hk ring)
    (hactive : ¬ state.IsTerminal) : state.hitClock < 4 * n := by
  have hadv := state.active_advances_lt hn3 hactive
  cases hphase : (state.config state.tail).phase <;>
    simp [RenewalProofState.hitClock, phaseNat, hphase] <;> omega

/-- Exact pathwise accounting along one and the same scheduler word.  If the
endpoint remains active, every prefix remained active (terminal states are
absorbing), so the adaptive target-hit count equals the increase of the
doubled phase clock. -/
theorem renewalProofRun_hitClock {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : RenewalProofState (r := r) hk ring) (word : List (Fin n))
    (hstart : ¬ state.IsTerminal)
    (hend : ¬ (renewalProofRun hk ring hn3 hndvd state word).IsTerminal) :
    (renewalProofRun hk ring hn3 hndvd state word).hitClock =
      state.hitClock + renewalTargetHits hk ring hn3 hndvd state word := by
  induction word generalizing state with
  | nil => simp [renewalProofRun, renewalTargetHits]
  | cons selected word ih =>
      let next := renewalProofNext hk ring hn3 hndvd state selected
      have hnext : ¬ next.IsTerminal := by
        intro hterminal
        have hrun := renewalProofRun_terminal_self hk ring hn3 hndvd next word
          hterminal
        apply hend
        simpa [renewalProofRun, next, hrun] using hterminal
      have hstep := renewalProofNext_hitClock hk ring hn3 hndvd state selected
        hstart hnext
      have htail := ih next hnext (by simpa [renewalProofRun, next] using hend)
      change (renewalProofRun hk ring hn3 hndvd next word).hitClock =
        state.hitClock + ((if selected = state.tail then 1 else 0) +
          renewalTargetHits hk ring hn3 hndvd next word)
      rw [htail, hstep]
      omega

/-- Universal same-word terminal theorem.  Four `n` adaptive selections of
the live barrier edge cannot coexist with an active endpoint; the terminal
state is the first actual Good/RankDrop payload and is then preserved exactly. -/
theorem renewalProofRun_terminal_of_four_mul_hits {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : RenewalProofState (r := r) hk ring) (word : List (Fin n))
    (hstart : ¬ state.IsTerminal)
    (hhits : 4 * n <= renewalTargetHits hk ring hn3 hndvd state word) :
    (renewalProofRun hk ring hn3 hndvd state word).IsTerminal := by
  by_cases hend :
      (renewalProofRun hk ring hn3 hndvd state word).IsTerminal
  · exact hend
  · have hclock := renewalProofRun_hitClock hk ring hn3 hndvd state word
      hstart hend
    have hbound := RenewalProofState.active_hitClock_lt_four_mul hn3
      (renewalProofRun hk ring hn3 hndvd state word) hend
    omega

/-- A terminal proof state exposes the actual physical endpoint certificate. -/
theorem RenewalProofState.terminal_payload {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (state : RenewalProofState (r := r) hk ring)
    (hterminal : state.IsTerminal) :
    Or (Nonempty (GoodFreshRenewal hk ring state.config state.tail))
      (PhiAt ring state.tail state.config < r) := by
  cases state with
  | first active => simp [RenewalProofState.IsTerminal] at hterminal
  | second firstUsed hfirst active hspan =>
      simp [RenewalProofState.IsTerminal] at hterminal
  | good used certificate => exact Or.inl certificate
  | dropped used drop => exact Or.inr drop

/-- Payload-retaining first-terminal search tree.  Both rank drop and good
renewal are successful local outcomes; there is no failure constructor used. -/
noncomputable def renewalSearchStep {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : RenewalProofState (r := r) hk ring) (selected : Fin n) :
    PayloadNode (RenewalProofState (r := r) hk ring)
      (RenewalProofState (r := r) hk ring)
      (RenewalProofState (r := r) hk ring) := by
  classical
  let next := renewalProofNext hk ring hn3 hndvd state selected
  exact if next.IsTerminal then .success next else .active next

@[simp] theorem renewalSearchStep_of_terminal {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : RenewalProofState (r := r) hk ring) (selected : Fin n)
    (hterminal : state.IsTerminal) :
    renewalSearchStep hk ring hn3 hndvd state selected = .success state := by
  classical
  simp [renewalSearchStep,
    renewalProofNext_terminal_self hk ring hn3 hndvd state selected hterminal,
    hterminal]

theorem renewalSearchStep_eq_success_iff {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state endpoint : RenewalProofState (r := r) hk ring) (selected : Fin n) :
    renewalSearchStep hk ring hn3 hndvd state selected = .success endpoint ↔
      And (endpoint = renewalProofNext hk ring hn3 hndvd state selected)
        endpoint.IsTerminal := by
  classical
  unfold renewalSearchStep
  dsimp only
  split
  · rename_i hterminal
    constructor
    · intro heq
      cases heq
      exact ⟨rfl, hterminal⟩
    · rintro ⟨rfl, _⟩
      rfl
  · rename_i hactive
    constructor
    · intro heq
      cases heq
    · rintro ⟨rfl, hterminal⟩
      exact False.elim (hactive hterminal)

/-- A successful local edge retains the literal post-interaction endpoint. -/
theorem renewalSearchStep_success_physical {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state endpoint : RenewalProofState (r := r) hk ring) (selected : Fin n)
    (hactive : ¬ state.IsTerminal)
    (hsuccess : renewalSearchStep hk ring hn3 hndvd state selected =
      .success endpoint) :
    And endpoint.IsTerminal
      (And (endpoint.config = step hk ring state.config selected)
        (endpoint.tail =
          postStepBarrier hk ring state.config state.tail selected)) := by
  have hpayload := (renewalSearchStep_eq_success_iff hk ring hn3 hndvd state
    endpoint selected).1 hsuccess
  refine ⟨hpayload.2, ?_, ?_⟩
  · rw [hpayload.1]
    exact renewalProofNext_configuration hk ring hn3 hndvd state selected
      hactive
  · rw [hpayload.1]
    exact renewalProofNext_tail hk ring hn3 hndvd state selected hactive

private theorem successCount_le_pow {S : Type} {n : Nat}
    (stepFn : S -> Fin n -> StopNode S) (node : StopNode S) (T : Nat) :
    successCount stepFn node T <= n ^ T := by
  have hpartition := node_count_partition stepFn node T
  omega

/-- Pointwise finite-tree domination.  The generic counter may discard its
payload on the `4*n`-th target hit, but the physical search has already reached
an absorbing payload terminal on every such branch. -/
theorem targetCounter_success_le_renewalSearch_successMass
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (base : Nat)
    (st : ActiveHitState (RenewalProofState (r := r) hk ring) (4 * n))
    (hactive : ¬ st.payload.IsTerminal)
    (hclock : st.payload.hitClock = base + st.hits) : forall T,
    successCount
        (targetCounterStep (d := 4 * n) RenewalProofState.tail
          (renewalProofNext hk ring hn3 hndvd)) (.active st) T <=
      successMass (renewalSearchStep hk ring hn3 hndvd)
        (.active st.payload) T := by
  intro T
  induction T generalizing st base with
  | zero => exact Nat.le_refl _
  | succ T ih =>
      simp only [successCount, treeWeight, FiniteUniformStoppingTree.stepNode,
        successMass, PayloadFiniteStoppingTree.stepNode]
      apply ofFn_sum_le
      intro selected
      let next := renewalProofNext hk ring hn3 hndvd st.payload selected
      by_cases hterminal : next.IsTerminal
      · have hrhs : successMass (renewalSearchStep hk ring hn3 hndvd)
            (.success next) T = n ^ T :=
          successMass_success (renewalSearchStep hk ring hn3 hndvd) next T
        rw [show renewalSearchStep hk ring hn3 hndvd st.payload selected =
            .success next by
          classical
          simp [renewalSearchStep, next, hterminal]]
        rw [hrhs]
        exact successCount_le_pow
          (targetCounterStep (d := 4 * n) RenewalProofState.tail
            (renewalProofNext hk ring hn3 hndvd))
          (targetCounterStep (d := 4 * n) RenewalProofState.tail
            (renewalProofNext hk ring hn3 hndvd) st selected) T
      · have hstepClock := renewalProofNext_hitClock hk ring hn3 hndvd
          st.payload selected hactive hterminal
        by_cases htarget : selected = st.payload.tail
        · subst selected
          have hclockNext : next.hitClock = base + (st.hits + 1) := by
            rw [hstepClock, if_pos rfl, hclock]
            omega
          by_cases hdone : st.hits + 1 = 4 * n
          · have hbound := RenewalProofState.active_hitClock_lt_four_mul hn3
              next hterminal
            omega
          · let nextCounter :
                ActiveHitState (RenewalProofState (r := r) hk ring) (4 * n) := {
                payload := next
                hits := st.hits + 1
                hits_lt := by have := st.hits_lt; omega
              }
            have hrec := ih base nextCounter hterminal hclockNext
            have hcounterStep : targetCounterStep (d := 4 * n)
                RenewalProofState.tail (renewalProofNext hk ring hn3 hndvd)
                st st.payload.tail = .active nextCounter := by
              simp [targetCounterStep, hdone, nextCounter, next]
            have hsearchStep : renewalSearchStep hk ring hn3 hndvd st.payload
                st.payload.tail = .active next := by
              classical
              simp [renewalSearchStep, next, hterminal]
            rw [hcounterStep, hsearchStep]
            simpa only [successCount] using hrec
        · have hclockNext : next.hitClock = base + st.hits := by
            rw [hstepClock, if_neg htarget, Nat.add_zero, hclock]
          let nextCounter :
              ActiveHitState (RenewalProofState (r := r) hk ring) (4 * n) := {
              payload := next
              hits := st.hits
              hits_lt := st.hits_lt
            }
          have hrec := ih base nextCounter hterminal hclockNext
          have hcounterStep : targetCounterStep (d := 4 * n)
              RenewalProofState.tail (renewalProofNext hk ring hn3 hndvd)
              st selected = .active nextCounter := by
            simp [targetCounterStep, htarget, nextCounter, next]
          have hsearchStep : renewalSearchStep hk ring hn3 hndvd st.payload
              selected = .active next := by
            classical
            simp [renewalSearchStep, next, hterminal]
          rw [hcounterStep, hsearchStep]
          simpa only [successCount] using hrec

/-- Half of all depth-`8*n^2` scheduler words reach an actual payload-retaining
renewal terminal. -/
theorem initialRenewalSearch_success_half_by_eight_mul_sq
    {n k r : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) :
    n ^ (8 * n ^ 2) <= 2 *
      successMass (renewalSearchStep hk ring hn3 hndvd)
        (.active (initialRenewalProofState hk ring C tail hone hrank hr1))
        (8 * n ^ 2) := by
  let start := initialRenewalProofState hk ring C tail hone hrank hr1
  have hcounter := four_mul_success_half_by_eight_mul_sq
    (target := RenewalProofState.tail)
    (next := renewalProofNext hk ring hn3 hndvd) start (by omega)
  have hdom := targetCounter_success_le_renewalSearch_successMass hk ring hn3
    hndvd start.hitClock
    (initialState start (4 * n) (by omega)) (by
      change ¬ start.IsTerminal
      dsimp [start, initialRenewalProofState, RenewalProofState.IsTerminal]
      simp)
    (by simp [initialState]) (8 * n ^ 2)
  exact Nat.le_trans hcounter (Nat.mul_le_mul_left 2 hdom)

/-- Same-word universal contract at the sharp deterministic advance budget.
Because terminal states are absorbing, the returned endpoint is exactly the
first physical Good/RankDrop payload, not an unrelated trace or padded state. -/
def HasPathwiseBoundedRenewalSearch {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) : Prop :=
  let start := initialRenewalProofState hk ring C tail hone hrank hr1
  forall word : List (Fin n),
    n + n / 2 <= (renewalProofRun hk ring hn3 hndvd start word).advances ->
      let endpoint := renewalProofRun hk ring hn3 hndvd start word
      And endpoint.IsTerminal
        (Or (Nonempty (GoodFreshRenewal hk ring endpoint.config endpoint.tail))
          (PhiAt ring endpoint.tail endpoint.config < r))

theorem hasPathwiseBoundedRenewalSearch {n k r : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Fin n -> State k) (tail : Fin n)
    (hone : OneBarrierAt hk ring C tail) (hrank : PhiAt ring tail C = r)
    (hr1 : 1 < r) :
    HasPathwiseBoundedRenewalSearch hk ring hn3 hndvd C tail hone hrank hr1 := by
  let start := initialRenewalProofState hk ring C tail hone hrank hr1
  intro word hadvances
  let endpoint := renewalProofRun hk ring hn3 hndvd start word
  change n + n / 2 <= endpoint.advances at hadvances
  have hterminal : endpoint.IsTerminal := by
    by_cases hactive : ¬ endpoint.IsTerminal
    · have hlt := endpoint.active_advances_lt hn3 hactive
      omega
    · exact Classical.byContradiction (fun h => hactive h)
  exact ⟨hterminal, endpoint.terminal_payload hterminal⟩
/-- Pure advance arithmetic used after the first target crossing and the
at-most-half-ring repair segment. -/
theorem first_crossing_add_short_repair_le_two_n (n first repair : Nat)
    (hfirst : first <= n) (hrepair : repair <= n / 2) :
    first + repair <= 2 * n := by
  have hhalf : n / 2 <= n := Nat.div_le_self n 2
  omega

end RenewalSearch
end CenteredRenewal
end AAFJPK
