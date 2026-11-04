import Leader.AAFJ.Centered.RankMonotone
import Leader.Core.PlusTwoMinusOneFiniteTree

/-!
# Local proof state for the centered zero-leader trial

This module deliberately stops before the scheduler/probability layer.  It
packages the protocol-specific canonical-cut state needed by the centered
zero-leader stopped trial and proves the literal local branch equations.  In
particular, `P` gives `+2`, either phase of a nonterminal `Q` hit gives `-1`,
the exceptional `q = 1` hit clears every probe, and the top `P` hit reaches
tail-probe success.  A stopped proof-state wrapper packages those branches and
the strong irrelevant-edge frame as an actual
`PlusTwoMinusOneFiniteTree.Spec`.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace ZeroLeaderTrial

open BarrierAlgebra
open SingleBarrierSanitation

set_option autoImplicit false

/-- A zero-leader trial is expressed in canonical one-barrier cut coordinates.
The barrier is therefore the outgoing edge of `tailCoord ring`.  The two tail
marks are separated: a fresh tail bullet is needed for the eventual clean
conversion, while a tail probe is the success event and so is excluded while a
trial is active. -/
structure Active {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n → State k) : Prop where
  canonical : CanonicalOneBarrier hk ring X
  zeroLeaders : ∀ i : Fin n, (X i).leader = false
  tailBullet : (X (tailCoord ring)).bullet = false
  tailProbe : (X (tailCoord ring)).probe = false
  hasProbe : ∃ i : Fin n, (X i).probe = true

/-- `m` is a (not merely chosen) maximum probe coordinate in the current cut. -/
def MaxProbeAt {n k : Nat} (X : Fin n → State k) (m : Fin n) : Prop :=
  (X m).probe = true ∧
    ∀ i : Fin n, (X i).probe = true → i.val ≤ m.val

/-- An active trial together with its explicit maximum-probe witness.  Storing
the witness avoids an `argmax` construction in every local branch lemma. -/
structure Prepared {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n → State k) extends Active hk ring X where
  maxProbe : Fin n
  maxProbeAt : MaxProbeAt X maxProbe

/-- Physical information retained at the sole failed endpoint.  Although all
probes have been cleared, the canonical barrier and zero-leader lane survive,
and the new canonical tail is a phase-zero, bullet-free restart site. -/
structure RestartReady {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n → State k) : Prop where
  canonical : CanonicalOneBarrier hk ring X
  zeroLeaders : ∀ i : Fin n, (X i).leader = false
  tailBullet : (X (tailCoord ring)).bullet = false
  tailPhase : (X (tailCoord ring)).phase = false
  allProbesCleared : ∀ i : Fin n, (X i).probe = false

/-- The current barrier edge in canonical cut coordinates. -/
def barrierEdge {n : Nat} (ring : DirectedRing n) : Fin n := tailCoord ring

/-- The ordinary edge that advances the maximum probe. -/
def progressEdge {n : Nat} (m : Fin n) : Fin n := m

/-- The phase bit used in the doubled probe-front coordinate. -/
def trialPhase {n k : Nat} (ring : DirectedRing n) (X : Fin n → State k) : Nat :=
  phaseNat ((X (tailCoord ring)).phase)

/-- The terminal trial coordinate.  During an active trial it is positive;
after a successful `P` hit we extend it by the same formula with `m=tail`, and
after the sole failure branch we set it to zero externally. -/
def q {n k : Nat} (ring : DirectedRing n) (X : Fin n → State k)
    (m : Fin n) : Nat :=
  2 * (m.val + 1) - trialPhase ring X

/-- The physical centered step before rotating the cut. -/
def rawStep {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n → State k) (e : Fin n) : Fin n → State k :=
  (CenteredRenewal.protocol k hk).step ring X e

/-- The trial's successor is always viewed in the new canonical cut. -/
def trialStep {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n → State k) (e : Fin n) : Fin n → State k :=
  Rank.cutSuccessor hk ring X e

/-- A raw interaction frames every vertex other than its two endpoints.  The
geometric frame lemma for a whole trial is built by combining this literal
fact with the fact that neither endpoint can change the maximum probe except
on `P` or the tail phase except on `Q`. -/
theorem rawStep_frame {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n → State k) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    rawStep hk ring X e i = X i := by
  simp [rawStep, PopulationProtocol.step, hi, hj]

/-- Literal initiator projection of a raw centered step. -/
theorem rawStep_at_initiator {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n → State k) (e : Fin n) :
    rawStep hk ring X e e =
      (CenteredRenewal.transition hk (X e) (X (ring.rightNeighbor e))).1 := by
  simp [rawStep, PopulationProtocol.step, CenteredRenewal.protocol]

/-- Literal responder projection of a raw centered step on a nontrivial ring. -/
theorem rawStep_at_responder {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (X : Fin n → State k) (e : Fin n) :
    rawStep hk ring X e (ring.rightNeighbor e) =
      (CenteredRenewal.transition hk (X e) (X (ring.rightNeighbor e))).2 := by
  have hre : ring.rightNeighbor e ≠ e := rightNeighbor_ne_self ring hn2 e
  simp [rawStep, PopulationProtocol.step, CenteredRenewal.protocol, hre]

theorem maxProbeAt_probe {n k : Nat} {X : Fin n → State k} {m : Fin n}
    (h : MaxProbeAt X m) : (X m).probe = true := h.1

theorem maxProbeAt_le {n k : Nat} {X : Fin n → State k} {m i : Fin n}
    (h : MaxProbeAt X m) (hi : (X i).probe = true) : i.val ≤ m.val := h.2 i hi

theorem Prepared.maxProbe_ne_tail {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) : S.maxProbe ≠ tailCoord ring := by
  intro htail
  have hp := S.maxProbeAt.1
  rw [htail, S.tailProbe] at hp
  contradiction

theorem Prepared.maxProbe_le_n_sub_two {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) : S.maxProbe.val ≤ n - 2 := by
  have hlt := S.maxProbe.isLt
  have hne := S.maxProbe_ne_tail
  by_cases hle : S.maxProbe.val ≤ n - 2
  · exact hle
  exfalso
  have hge : n - 1 ≤ S.maxProbe.val := by omega
  have hval : S.maxProbe.val = n - 1 := by omega
  apply hne
  apply Fin.ext
  change S.maxProbe.val = n - 1
  exact hval

theorem Prepared.progress_ne_barrier {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) :
    progressEdge S.maxProbe ≠ barrierEdge ring :=
  S.maxProbe_ne_tail

theorem Prepared.barrier_isBarrier {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) :
    IsBarrier hk (X (barrierEdge ring))
      (X (ring.rightNeighbor (barrierEdge ring))) := by
  exact (S.canonical (barrierEdge ring)).2 rfl

theorem Prepared.progress_not_barrier {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) :
    ¬ IsBarrier hk (X (progressEdge S.maxProbe))
      (X (ring.rightNeighbor (progressEdge S.maxProbe))) := by
  intro hbar
  have hEq : progressEdge S.maxProbe = tailCoord ring :=
    (S.canonical (progressEdge S.maxProbe)).1 hbar
  exact S.progress_ne_barrier hEq

theorem Prepared.progress_responder_follower {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) :
    (X (ring.rightNeighbor (progressEdge S.maxProbe))).leader = false :=
  S.zeroLeaders _

theorem Prepared.barrier_head_follower {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) :
    (X (ring.rightNeighbor (barrierEdge ring))).leader = false :=
  S.zeroLeaders _

theorem q_of_phase_false {n k : Nat} (ring : DirectedRing n)
    (X : Fin n → State k) (m : Fin n)
    (hphase : (X (tailCoord ring)).phase = false) :
    q ring X m = 2 * (m.val + 1) := by
  simp [q, trialPhase, phaseNat, hphase]

theorem q_of_phase_true {n k : Nat} (ring : DirectedRing n)
    (X : Fin n → State k) (m : Fin n)
    (hphase : (X (tailCoord ring)).phase = true) :
    q ring X m = 2 * (m.val + 1) - 1 := by
  simp [q, trialPhase, phaseNat, hphase]

/-- Before absorption, the doubled front coordinate is positive. -/
theorem Prepared.q_pos {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n → State k} (S : Prepared hk ring X) :
    0 < q ring X S.maxProbe := by
  cases hphase : (X (tailCoord ring)).phase <;>
    simp [q, trialPhase, phaseNat, hphase] <;> omega

/-- The tail is probe-free during an active trial, hence its maximum probe is
strictly before the tail and the active coordinate is at most `2n - 2`.  The
two remaining values `2n-1, 2n` are respectively the phase-one success front
and its terminal extension, and are not represented by `Prepared`. -/
theorem Prepared.q_le_two_n_sub_two {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k} (S : Prepared hk ring X) :
    q ring X S.maxProbe ≤ 2 * n - 2 := by
  have hm : S.maxProbe.val ≤ n - 2 := Prepared.maxProbe_le_n_sub_two S
  have hn2 : 1 < n := by
    by_cases h : 1 < n
    · exact h
    exfalso
    have hn : n = 1 := by omega
    apply S.maxProbe_ne_tail
    apply Fin.ext
    change S.maxProbe.val = n - 1
    omega
  cases hphase : (X (tailCoord ring)).phase <;>
    simp [q, trialPhase, phaseNat, hphase] <;> omega

/-- The only active state at the lower endpoint is exactly the exceptional
phase-one, `M=0` case.  This is the centered branch whose barrier hit is the
unique failure branch `q = 1 → 0`. -/
theorem Prepared.q_eq_one_iff {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k} (S : Prepared hk ring X) :
    q ring X S.maxProbe = 1 ↔
      S.maxProbe.val = 0 ∧ (X (tailCoord ring)).phase = true := by
  cases hphase : (X (tailCoord ring)).phase
  · simp [q, trialPhase, phaseNat, hphase]
    omega
  · simp [q, trialPhase, phaseNat, hphase]
    omega

/-- Every nonbarrier interaction remains in the unrotated cut.  This makes
the `P` branch and all irrelevant interactions literal raw protocol steps. -/
theorem Prepared.trialStep_eq_raw_of_ne_barrier {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (e : Fin n) (he : e ≠ barrierEdge ring) :
    trialStep hk ring X e = rawStep hk ring X e := by
  have hnot : ¬ CenteredRenewal.AdvanceReady hk ring X e := by
    intro hready
    have hEq : e = tailCoord ring := (S.canonical e).1 hready.1
    exact he hEq
  unfold trialStep Rank.cutSuccessor
  dsimp
  change
    (if CenteredRenewal.AdvanceReady hk ring X e then
        rotateCut ring (fun j => ((CenteredRenewal.protocol k hk).step ring X e) j)
      else fun j => ((CenteredRenewal.protocol k hk).step ring X e) j) =
      fun j => ((CenteredRenewal.protocol k hk).step ring X e) j
  exact if_neg hnot

/-- On a phase-zero barrier hit the canonical cut does not rotate. -/
theorem trialStep_eq_raw_of_phase_zero {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (X : Fin n → State k)
    (_S : Active hk ring X)
    (hphase : (X (tailCoord ring)).phase = false) :
    trialStep hk ring X (barrierEdge ring) = rawStep hk ring X (barrierEdge ring) := by
  have hnot : ¬ CenteredRenewal.AdvanceReady hk ring X (barrierEdge ring) := by
    intro hready
    exact Bool.noConfusion (hready.2.symm.trans hphase)
  unfold trialStep Rank.cutSuccessor
  dsimp
  change
    (if CenteredRenewal.AdvanceReady hk ring X (barrierEdge ring) then
        rotateCut ring (fun j => ((CenteredRenewal.protocol k hk).step ring X
          (barrierEdge ring)) j)
      else fun j => ((CenteredRenewal.protocol k hk).step ring X
        (barrierEdge ring)) j) =
      fun j => ((CenteredRenewal.protocol k hk).step ring X
        (barrierEdge ring)) j
  exact if_neg hnot

/-- On a phase-one barrier hit the centered cut rotates unconditionally. -/
theorem trialStep_eq_rotate_raw_of_phase_one {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (X : Fin n → State k)
    (S : Active hk ring X)
    (hphase : (X (tailCoord ring)).phase = true) :
    trialStep hk ring X (barrierEdge ring) =
      rotateCut ring (rawStep hk ring X (barrierEdge ring)) := by
  have hready : CenteredRenewal.AdvanceReady hk ring X (barrierEdge ring) :=
    ⟨(S.canonical (barrierEdge ring)).2 rfl, hphase⟩
  unfold trialStep Rank.cutSuccessor
  dsimp
  change
    (if CenteredRenewal.AdvanceReady hk ring X (barrierEdge ring) then
        rotateCut ring (fun j => ((CenteredRenewal.protocol k hk).step ring X
          (barrierEdge ring)) j)
      else fun j => ((CenteredRenewal.protocol k hk).step ring X
        (barrierEdge ring)) j) =
      rotateCut ring (fun j => ((CenteredRenewal.protocol k hk).step ring X
        (barrierEdge ring)) j)
  exact if_pos hready

/-- Literal centered phase-zero normal form in an active zero-leader trial. -/
theorem Prepared.barrier_phase_zero_pair {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X)
    (hphase : (X (barrierEdge ring)).phase = false) :
    CenteredRenewal.transition hk (X (barrierEdge ring))
      (X (ring.rightNeighbor (barrierEdge ring))) =
      ({ X (barrierEdge ring) with phase := true },
       { X (ring.rightNeighbor (barrierEdge ring)) with probe := true }) := by
  rw [CenteredRenewal.transition_of_barrier hk _ _ S.barrier_isBarrier]
  rw [CenteredRenewal.barrierStep_phase_zero hk _ _ hphase]
  have htail : (X (barrierEdge ring)).probe = false := S.tailProbe
  simp [probeHitsBarrier, htail, S.barrier_head_follower]

/-- Literal centered phase-one normal form in an active zero-leader trial.
Unlike source Protocol 6, this branch has no head-probe hypothesis. -/
theorem Prepared.barrier_phase_one_pair {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X)
    (hphase : (X (barrierEdge ring)).phase = true) :
    CenteredRenewal.transition hk (X (barrierEdge ring))
      (X (ring.rightNeighbor (barrierEdge ring))) =
      (X (barrierEdge ring),
       { X (ring.rightNeighbor (barrierEdge ring)) with
         label := succLabel hk (X (barrierEdge ring)).label,
         phase := false, bullet := false, probe := false }) := by
  rw [CenteredRenewal.transition_of_barrier hk _ _ S.barrier_isBarrier]
  rw [CenteredRenewal.barrierStep_phase_one hk _ _ hphase]
  have htail : (X (barrierEdge ring)).probe = false := S.tailProbe
  simp [probeHitsBarrier, htail]

/-- Literal progress normal form when the responder of `P` carries a bullet.
The probe move survives because the AAFJ follower branch is sequential. -/
theorem Prepared.progress_pair_of_bullet {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X)
    (hbullet : (X (ring.rightNeighbor (progressEdge S.maxProbe))).bullet = true) :
    CenteredRenewal.transition hk (X (progressEdge S.maxProbe))
      (X (ring.rightNeighbor (progressEdge S.maxProbe))) =
      ({ X (progressEdge S.maxProbe) with bullet := true, probe := false },
       { X (ring.rightNeighbor (progressEdge S.maxProbe)) with
         bullet := false, probe := true }) := by
  rw [CenteredRenewal.transition_of_nonbarrier hk _ _ S.progress_not_barrier]
  exact nonBarrierStep_follower_bullet_probe _ _ S.progress_responder_follower
    hbullet S.maxProbeAt.1

/-- Literal progress normal form when the responder of `P` has no bullet. -/
theorem Prepared.progress_pair_of_no_bullet {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X)
    (hbullet : (X (ring.rightNeighbor (progressEdge S.maxProbe))).bullet = false) :
    CenteredRenewal.transition hk (X (progressEdge S.maxProbe))
      (X (ring.rightNeighbor (progressEdge S.maxProbe))) =
      ({ X (progressEdge S.maxProbe) with probe := false },
       { X (ring.rightNeighbor (progressEdge S.maxProbe)) with probe := true }) := by
  rw [CenteredRenewal.transition_of_nonbarrier hk _ _ S.progress_not_barrier]
  exact nonBarrierStep_follower_probe_only _ _ S.progress_responder_follower
    hbullet S.maxProbeAt.1

/-! ## The nonterminal progress branch -/

/-- A literal `P` hit moves the maximum probe to the responder, independently
of the responder's old bullet. -/
theorem Prepared.progress_raw_probe_fields {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n) :
    let D := rawStep hk ring X (progressEdge S.maxProbe)
    (D S.maxProbe).probe = false ∧
      (D (ring.rightNeighbor S.maxProbe)).probe = true := by
  simp only [progressEdge]
  by_cases hb : (X (ring.rightNeighbor S.maxProbe)).bullet = true
  · have hp := S.progress_pair_of_bullet hb
    simp only [progressEdge] at hp
    rw [rawStep_at_initiator hk ring X S.maxProbe,
      rawStep_at_responder hk ring hn2 X S.maxProbe, hp]
    simp
  · have hb0 : (X (ring.rightNeighbor S.maxProbe)).bullet = false := by
      cases h : (X (ring.rightNeighbor S.maxProbe)).bullet
      · rfl
      · exact False.elim (hb h)
    have hp := S.progress_pair_of_no_bullet hb0
    simp only [progressEdge] at hp
    rw [rawStep_at_initiator hk ring X S.maxProbe,
      rawStep_at_responder hk ring hn2 X S.maxProbe, hp]
    simp

/-- A `P` hit creates no leader in the active zero-leader lane. -/
theorem Prepared.progress_raw_zeroLeaders {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n) :
    ∀ i : Fin n,
      (rawStep hk ring X (progressEdge S.maxProbe) i).leader = false := by
  intro i
  by_cases hb : (X (ring.rightNeighbor S.maxProbe)).bullet = true
  · have hp := S.progress_pair_of_bullet hb
    simp only [progressEdge] at hp ⊢
    by_cases hie : i = S.maxProbe
    · subst i
      rw [rawStep_at_initiator hk ring X S.maxProbe, hp]
      simp [S.zeroLeaders]
    · by_cases hir : i = ring.rightNeighbor S.maxProbe
      · subst i
        rw [rawStep_at_responder hk ring hn2 X S.maxProbe, hp]
        simp [S.zeroLeaders]
      · rw [rawStep_frame hk ring X S.maxProbe i hie hir]
        exact S.zeroLeaders i
  · have hb0 : (X (ring.rightNeighbor S.maxProbe)).bullet = false := by
      cases h : (X (ring.rightNeighbor S.maxProbe)).bullet
      · rfl
      · exact False.elim (hb h)
    have hp := S.progress_pair_of_no_bullet hb0
    simp only [progressEdge] at hp ⊢
    by_cases hie : i = S.maxProbe
    · subst i
      rw [rawStep_at_initiator hk ring X S.maxProbe, hp]
      simp [S.zeroLeaders]
    · by_cases hir : i = ring.rightNeighbor S.maxProbe
      · subst i
        rw [rawStep_at_responder hk ring hn2 X S.maxProbe, hp]
        simp [S.zeroLeaders]
      · rw [rawStep_frame hk ring X S.maxProbe i hie hir]
        exact S.zeroLeaders i

/-- After a `P` hit, the responder is the new maximum probe. -/
theorem Prepared.progress_raw_maxProbeAt {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n) :
    MaxProbeAt (rawStep hk ring X (progressEdge S.maxProbe))
      (ring.rightNeighbor S.maxProbe) := by
  let D := rawStep hk ring X (progressEdge S.maxProbe)
  have hfields := S.progress_raw_probe_fields hn2
  refine ⟨hfields.2, ?_⟩
  intro i hi
  have hre : ring.rightNeighbor S.maxProbe ≠ S.maxProbe :=
    rightNeighbor_ne_self ring hn2 S.maxProbe
  by_cases him : i = S.maxProbe
  · subst i
    rw [hfields.1] at hi
    contradiction
  · by_cases hir : i = ring.rightNeighbor S.maxProbe
    · subst i
      exact Nat.le_refl _
    · have hold : (X i).probe = true := by
        have hframe := rawStep_frame hk ring X (progressEdge S.maxProbe) i
          (by simpa [progressEdge] using him)
          (by simpa [progressEdge] using hir)
        rw [hframe] at hi
        exact hi
      have hle := S.maxProbeAt.2 i hold
      have hval := rightNeighbor_val_of_ne_tail ring S.maxProbe
        S.maxProbe_ne_tail
      omega

/-! ## The strong irrelevant-edge frame -/

/-- On any ordinary edge, the follower normal form gives the exact two probe
projections needed by the maximum argument.  The responder may carry an old
bullet; source ordering still moves the initiator probe after the bullet. -/
theorem Prepared.nonbarrier_raw_probe_fields
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n) (e : Fin n)
    (he : e ≠ barrierEdge ring) :
    let D := rawStep hk ring X e
    (D e).probe = false ∧
      (D (ring.rightNeighbor e)).probe =
        ((X (ring.rightNeighbor e)).probe || (X e).probe) := by
  dsimp only
  have hnot : ¬ IsBarrier hk (X e) (X (ring.rightNeighbor e)) := by
    intro hbar
    have het : e = tailCoord ring := (S.canonical e).1 hbar
    exact he (by simpa [barrierEdge] using het)
  have hpair := CenteredRenewal.transition_of_nonbarrier hk
    (X e) (X (ring.rightNeighbor e)) hnot
  have hv : (X (ring.rightNeighbor e)).leader = false := S.zeroLeaders _
  rw [rawStep_at_initiator hk ring X e,
    rawStep_at_responder hk ring hn2 X e, hpair]
  cases hb : (X (ring.rightNeighbor e)).bullet <;>
    cases hp : (X e).probe <;>
    simp [nonBarrierStep, hv, hb, hp]

/-- An ordinary interaction in the zero-leader lane cannot create a leader. -/
theorem Prepared.nonbarrier_raw_zeroLeaders
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n) (e : Fin n)
    (he : e ≠ barrierEdge ring) :
    ∀ i : Fin n, (rawStep hk ring X e i).leader = false := by
  intro i
  have hnot : ¬ IsBarrier hk (X e) (X (ring.rightNeighbor e)) := by
    intro hbar
    have het : e = tailCoord ring := (S.canonical e).1 hbar
    exact he (by simpa [barrierEdge] using het)
  have hpair := CenteredRenewal.transition_of_nonbarrier hk
    (X e) (X (ring.rightNeighbor e)) hnot
  by_cases hie : i = e
  · subst i
    rw [rawStep_at_initiator hk ring X e, hpair]
    cases hb : (X (ring.rightNeighbor e)).bullet <;>
      cases hp : (X e).probe <;>
      simp [nonBarrierStep, S.zeroLeaders, hb, hp]
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      rw [rawStep_at_responder hk ring hn2 X e, hpair]
      cases hb : (X (ring.rightNeighbor e)).bullet <;>
        cases hp : (X e).probe <;>
        simp [nonBarrierStep, S.zeroLeaders, hb, hp]
    · rw [rawStep_frame hk ring X e i hie hir]
      exact S.zeroLeaders i

/-- If an ordinary edge is neither the maximum-probe edge nor the barrier
edge, the same maximum witness remains exact.  Lower probes and bullets may
move, so this is deliberately weaker than whole-configuration stuttering. -/
theorem Prepared.other_raw_maxProbeAt
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n) (e : Fin n)
    (heP : e ≠ progressEdge S.maxProbe)
    (heQ : e ≠ barrierEdge ring) :
    MaxProbeAt (rawStep hk ring X e) S.maxProbe := by
  have hn2 : 1 < n := by omega
  let r := ring.rightNeighbor e
  let D := rawStep hk ring X e
  have hfields := S.nonbarrier_raw_probe_fields hn2 e heQ
  have hmaxProbe : (D S.maxProbe).probe = true := by
    by_cases hmr : S.maxProbe = r
    · have hrProbe : (X (ring.rightNeighbor e)).probe = true := by
        rw [← show S.maxProbe = ring.rightNeighbor e by simpa [r] using hmr]
        exact S.maxProbeAt.1
      rw [hmr]
      change (rawStep hk ring X e (ring.rightNeighbor e)).probe = true
      rw [hfields.2, hrProbe]
      simp
    · have hme : S.maxProbe ≠ e := by
        intro h
        exact heP (by simpa [progressEdge] using h.symm)
      have hf := rawStep_frame hk ring X e S.maxProbe hme (by simpa [r] using hmr)
      change (rawStep hk ring X e S.maxProbe).probe = true
      rw [hf]
      exact S.maxProbeAt.1
  refine ⟨hmaxProbe, ?_⟩
  intro i hi
  by_cases hie : i = e
  · subst i
    change (D e).probe = true at hi
    rw [hfields.1] at hi
    contradiction
  · by_cases hir : i = r
    · subst i
      change (D (ring.rightNeighbor e)).probe = true at hi
      rw [hfields.2] at hi
      cases hr : (X (ring.rightNeighbor e)).probe
      · cases he : (X e).probe
        · simp [hr, he] at hi
        · have hle := S.maxProbeAt.2 e he
          have heTail : e ≠ tailCoord ring := by
            simpa [barrierEdge] using heQ
          have hval := rightNeighbor_val_of_ne_tail ring e heTail
          have hne : e.val ≠ S.maxProbe.val := by
            intro hv
            apply heP
            apply Fin.ext
            simpa [progressEdge] using hv
          omega
      · exact S.maxProbeAt.2 _ hr
    · have hf := rawStep_frame hk ring X e i hie (by simpa [r] using hir)
      change (rawStep hk ring X e i).probe = true at hi
      rw [hf] at hi
      exact S.maxProbeAt.2 i hi

/-- An irrelevant ordinary interaction leaves the complete current tail state
unchanged.  The only possible incoming tail edge has a probe-free initiator;
otherwise maximality would identify it with `P`. -/
theorem Prepared.other_raw_tail_frame
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n) (e : Fin n)
    (heP : e ≠ progressEdge S.maxProbe)
    (heQ : e ≠ barrierEdge ring) :
    rawStep hk ring X e (tailCoord ring) = X (tailCoord ring) := by
  have hn2 : 1 < n := by omega
  have hte : tailCoord ring ≠ e := by
    intro h
    exact heQ (by simpa [barrierEdge] using h.symm)
  by_cases htr : tailCoord ring = ring.rightNeighbor e
  · have heProbe : (X e).probe = false := by
      cases hp : (X e).probe
      · rfl
      · have hle := S.maxProbeAt.2 e hp
        have heTail : e ≠ tailCoord ring := by
          intro h
          exact hte h.symm
        have hrval := rightNeighbor_val_of_ne_tail ring e heTail
        have htailVal : (tailCoord ring).val = n - 1 := rfl
        have hmle := S.maxProbe_le_n_sub_two
        have hev : e.val = n - 2 := by
          have hv := congrArg Fin.val htr
          omega
        have hem : e = S.maxProbe := by
          apply Fin.ext
          omega
        exact False.elim (heP (by simpa [progressEdge] using hem))
    have hnot : ¬ IsBarrier hk (X e) (X (ring.rightNeighbor e)) := by
      intro hbar
      have het : e = tailCoord ring := (S.canonical e).1 hbar
      exact hte het.symm
    have hpair := CenteredRenewal.transition_of_nonbarrier hk
      (X e) (X (ring.rightNeighbor e)) hnot
    have hrBullet : (X (ring.rightNeighbor e)).bullet = false := by
      rw [← htr]
      exact S.tailBullet
    rw [htr, rawStep_at_responder hk ring hn2 X e, hpair]
    simp [nonBarrierStep, S.zeroLeaders, hrBullet, heProbe]
  · exact rawStep_frame hk ring X e (tailCoord ring) hte htr

/-- The full proof-facing frame for every scheduler edge other than `P` and
`Q`: it reconstructs the active trial with the same maximum witness and hence
the same physical selectors and doubled coordinate. -/
def Prepared.otherPrepared
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n) (e : Fin n)
    (heP : e ≠ progressEdge S.maxProbe)
    (heQ : e ≠ barrierEdge ring) :
    Prepared hk ring (trialStep hk ring X e) := by
  have hn2 : 1 < n := by omega
  have hstep := S.trialStep_eq_raw_of_ne_barrier e heQ
  rw [hstep]
  let D := rawStep hk ring X e
  have htail := S.other_raw_tail_frame hn3 e heP heQ
  have hlabels : labelsOf D = labelsOf X := by
    exact CenteredRenewal.labelsOf_step_eq_self_of_not_ready hk ring X e (by
      intro hready
      have het : e = tailCoord ring := (S.canonical e).1 hready.1
      exact heQ (by simpa [barrierEdge] using het))
  refine
    { canonical := ?_
      zeroLeaders := S.nonbarrier_raw_zeroLeaders hn2 e heQ
      tailBullet := by rw [htail]; exact S.tailBullet
      tailProbe := by rw [htail]; exact S.tailProbe
      hasProbe := ⟨S.maxProbe, (S.other_raw_maxProbeAt hn3 e heP heQ).1⟩
      maxProbe := S.maxProbe
      maxProbeAt := S.other_raw_maxProbeAt hn3 e heP heQ }
  intro i
  rw [← barrierAt_labelsOf_iff hk ring D i, hlabels,
    barrierAt_labelsOf_iff hk ring X i]
  exact S.canonical i

/-- Irrelevant edges preserve the proof coordinate exactly. -/
theorem Prepared.q_other
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n) (e : Fin n)
    (heP : e ≠ progressEdge S.maxProbe)
    (heQ : e ≠ barrierEdge ring) :
    q ring (trialStep hk ring X e) S.maxProbe = q ring X S.maxProbe := by
  have hstep := S.trialStep_eq_raw_of_ne_barrier e heQ
  rw [hstep]
  have htail := S.other_raw_tail_frame hn3 e heP heQ
  simp only [q, trialPhase]
  rw [htail]

/-- A nonterminal `P` hit (the new probe is not yet at the tail) reconstructs
the full prepared state in the same canonical cut. -/
def Prepared.progressPrepared {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hnonterminal : S.maxProbe.val ≤ n - 3) :
    Prepared hk ring
      (trialStep hk ring X (progressEdge S.maxProbe)) := by
  have hn2 : 1 < n := by omega
  have hstep : trialStep hk ring X (progressEdge S.maxProbe) =
      rawStep hk ring X (progressEdge S.maxProbe) :=
    S.trialStep_eq_raw_of_ne_barrier _ S.progress_ne_barrier
  rw [hstep]
  let D := rawStep hk ring X (progressEdge S.maxProbe)
  have hval := rightNeighbor_val_of_ne_tail ring S.maxProbe S.maxProbe_ne_tail
  have htailNeM : tailCoord ring ≠ S.maxProbe := Ne.symm S.maxProbe_ne_tail
  have htailNeR : tailCoord ring ≠ ring.rightNeighbor S.maxProbe := by
    intro h
    have hv := congrArg Fin.val h
    change n - 1 = (ring.rightNeighbor S.maxProbe).val at hv
    omega
  have htailFrame : D (tailCoord ring) = X (tailCoord ring) :=
    rawStep_frame hk ring X (progressEdge S.maxProbe) (tailCoord ring)
      htailNeM htailNeR
  have hlabels : labelsOf D = labelsOf X := by
    exact CenteredRenewal.labelsOf_step_eq_self_of_not_ready hk ring X
      (progressEdge S.maxProbe) (fun h ↦ S.progress_not_barrier h.1)
  refine
    { canonical := ?_
      zeroLeaders := S.progress_raw_zeroLeaders hn2
      tailBullet := by
        change (D (tailCoord ring)).bullet = false
        rw [htailFrame]
        exact S.tailBullet
      tailProbe := by
        change (D (tailCoord ring)).probe = false
        rw [htailFrame]
        exact S.tailProbe
      hasProbe := ⟨ring.rightNeighbor S.maxProbe,
        (S.progress_raw_probe_fields hn2).2⟩
      maxProbe := ring.rightNeighbor S.maxProbe
      maxProbeAt := S.progress_raw_maxProbeAt hn2 }
  intro i
  rw [← barrierAt_labelsOf_iff hk ring D i, hlabels,
    barrierAt_labelsOf_iff hk ring X i]
  exact S.canonical i

/-- The nonterminal progress edge gives the exact `+2` coordinate branch. -/
theorem Prepared.q_progress_add_two {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hnonterminal : S.maxProbe.val ≤ n - 3) :
    q ring (trialStep hk ring X (progressEdge S.maxProbe))
        (ring.rightNeighbor S.maxProbe) =
      q ring X S.maxProbe + 2 := by
  have hstep : trialStep hk ring X (progressEdge S.maxProbe) =
      rawStep hk ring X (progressEdge S.maxProbe) :=
    S.trialStep_eq_raw_of_ne_barrier _ S.progress_ne_barrier
  rw [hstep]
  have hval := rightNeighbor_val_of_ne_tail ring S.maxProbe S.maxProbe_ne_tail
  have htailNeM : tailCoord ring ≠ S.maxProbe := Ne.symm S.maxProbe_ne_tail
  have htailNeR : tailCoord ring ≠ ring.rightNeighbor S.maxProbe := by
    intro h
    have hv := congrArg Fin.val h
    change n - 1 = (ring.rightNeighbor S.maxProbe).val at hv
    omega
  have htail := rawStep_frame hk ring X (progressEdge S.maxProbe)
    (tailCoord ring) htailNeM htailNeR
  cases hphase : (X (tailCoord ring)).phase <;>
    simp [q, trialPhase, phaseNat, htail, hphase, hval] <;> omega

/-! ## The terminal progress branch -/

/-- At the top active maximum, the `P` responder is exactly the current tail. -/
theorem Prepared.progress_responder_eq_tail_of_maxProbe_top
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hmaxTop : S.maxProbe.val = n - 2) :
    ring.rightNeighbor S.maxProbe = tailCoord ring := by
  apply Fin.ext
  have hval := rightNeighbor_val_of_ne_tail ring S.maxProbe S.maxProbe_ne_tail
  change (ring.rightNeighbor S.maxProbe).val = n - 1
  omega

/-- A top `P` hit writes the maximal probe into the current tail.  The fresh
tail has no bullet, so the literal follower update changes only its probe. -/
theorem Prepared.progress_top_tail_state
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hmaxTop : S.maxProbe.val = n - 2) :
    trialStep hk ring X (progressEdge S.maxProbe) (tailCoord ring) =
      { X (tailCoord ring) with probe := true } := by
  have hn2 : 1 < n := by omega
  have htail := S.progress_responder_eq_tail_of_maxProbe_top hmaxTop
  have hbullet : (X (ring.rightNeighbor S.maxProbe)).bullet = false := by
    rw [htail]
    exact S.tailBullet
  have hpair := S.progress_pair_of_no_bullet hbullet
  simp only [progressEdge] at hpair ⊢
  rw [S.trialStep_eq_raw_of_ne_barrier S.maxProbe S.progress_ne_barrier,
    ← htail, rawStep_at_responder hk ring hn2 X S.maxProbe, hpair]

/-- Terminal `P` success: when `maxProbe = n-2`, the probe reaches the tail.
The extended terminal coordinate, evaluated at the tail witness, is still the
exact `+2` child required by the generic finite-tree arithmetic. -/
theorem Prepared.progress_top_terminal_success
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hmaxTop : S.maxProbe.val = n - 2) :
    let D := trialStep hk ring X (progressEdge S.maxProbe)
    (D (tailCoord ring)).probe = true ∧
      (D (tailCoord ring)).bullet = false ∧
      (D (tailCoord ring)).phase = (X (tailCoord ring)).phase ∧
      q ring D (tailCoord ring) = q ring X S.maxProbe + 2 := by
  dsimp only
  have htail := S.progress_top_tail_state hn3 hmaxTop
  refine ⟨by rw [htail], by rw [htail]; exact S.tailBullet,
    by rw [htail], ?_⟩
  have htailVal : (tailCoord ring).val = n - 1 := rfl
  cases hphase : (X (tailCoord ring)).phase <;>
    simp [q, trialPhase, phaseNat, htail, hphase] <;> omega

/-! ## The phase-zero barrier branch -/

theorem Prepared.barrier_phase_zero_raw_endpoints {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n)
    (hphase : (X (barrierEdge ring)).phase = false) :
    let D := rawStep hk ring X (barrierEdge ring)
    D (barrierEdge ring) = { X (barrierEdge ring) with phase := true } ∧
      D (ring.rightNeighbor (barrierEdge ring)) =
        { X (ring.rightNeighbor (barrierEdge ring)) with probe := true } := by
  have hp := S.barrier_phase_zero_pair hphase
  constructor
  · rw [rawStep_at_initiator hk ring X (barrierEdge ring), hp]
  · rw [rawStep_at_responder hk ring hn2 X (barrierEdge ring), hp]

theorem Prepared.barrier_phase_zero_raw_zeroLeaders {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n)
    (hphase : (X (barrierEdge ring)).phase = false) :
    ∀ i : Fin n,
      (rawStep hk ring X (barrierEdge ring) i).leader = false := by
  intro i
  have hend := S.barrier_phase_zero_raw_endpoints hn2 hphase
  by_cases hit : i = barrierEdge ring
  · subst i
    rw [hend.1]
    simp [S.zeroLeaders]
  · by_cases hih : i = ring.rightNeighbor (barrierEdge ring)
    · subst i
      rw [hend.2]
      simp [S.zeroLeaders]
    · rw [rawStep_frame hk ring X (barrierEdge ring) i hit hih]
      exact S.zeroLeaders i

/-- The phase-zero barrier hit adds only a coordinate-zero probe, so the same
maximum witness remains valid. -/
theorem Prepared.barrier_phase_zero_raw_maxProbeAt {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n)
    (hphase : (X (barrierEdge ring)).phase = false) :
    MaxProbeAt (rawStep hk ring X (barrierEdge ring)) S.maxProbe := by
  let D := rawStep hk ring X (barrierEdge ring)
  have hend := S.barrier_phase_zero_raw_endpoints hn2 hphase
  have hmt : S.maxProbe ≠ barrierEdge ring := S.progress_ne_barrier
  have hhead : ring.rightNeighbor (barrierEdge ring) =
      (⟨0, ring.hn⟩ : Fin n) := rightNeighbor_tailCoord ring
  have hmProbe : (D S.maxProbe).probe = true := by
    by_cases hmh : S.maxProbe = ring.rightNeighbor (barrierEdge ring)
    · rw [hmh]
      change (rawStep hk ring X (barrierEdge ring)
        (ring.rightNeighbor (barrierEdge ring))).probe = true
      rw [hend.2]
    · have hf := rawStep_frame hk ring X (barrierEdge ring) S.maxProbe
          hmt hmh
      change (rawStep hk ring X (barrierEdge ring) S.maxProbe).probe = true
      rw [hf]
      exact S.maxProbeAt.1
  refine ⟨hmProbe, ?_⟩
  intro i hi
  by_cases hit : i = barrierEdge ring
  · subst i
    have hfalse : (D (barrierEdge ring)).probe = false := by
      change (rawStep hk ring X (barrierEdge ring)
        (barrierEdge ring)).probe = false
      rw [hend.1]
      exact S.tailProbe
    rw [hfalse] at hi
    contradiction
  · by_cases hih : i = ring.rightNeighbor (barrierEdge ring)
    · subst i
      rw [hhead]
      simp
    · have hf := rawStep_frame hk ring X (barrierEdge ring) i hit hih
      rw [hf] at hi
      exact S.maxProbeAt.2 i hi

/-- A phase-zero barrier hit reconstructs `Prepared` with the same maximum
probe and changes only the phase contribution to `q`. -/
def Prepared.phaseZeroPrepared {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hphase : (X (barrierEdge ring)).phase = false) :
    Prepared hk ring (trialStep hk ring X (barrierEdge ring)) := by
  have hn2 : 1 < n := by omega
  have hstep := trialStep_eq_raw_of_phase_zero hk ring X S.toActive hphase
  rw [hstep]
  let D := rawStep hk ring X (barrierEdge ring)
  have hend := S.barrier_phase_zero_raw_endpoints hn2 hphase
  have hlabels : labelsOf D = labelsOf X := by
    exact CenteredRenewal.labelsOf_step_eq_self_of_not_ready hk ring X
      (barrierEdge ring) (by
        intro h
        exact Bool.noConfusion (h.2.symm.trans hphase))
  refine
    { canonical := ?_
      zeroLeaders := S.barrier_phase_zero_raw_zeroLeaders hn2 hphase
      tailBullet := by
        change (rawStep hk ring X (barrierEdge ring)
          (barrierEdge ring)).bullet = false
        rw [hend.1]
        exact S.tailBullet
      tailProbe := by
        change (rawStep hk ring X (barrierEdge ring)
          (barrierEdge ring)).probe = false
        rw [hend.1]
        exact S.tailProbe
      hasProbe := ⟨S.maxProbe,
        (S.barrier_phase_zero_raw_maxProbeAt hn2 hphase).1⟩
      maxProbe := S.maxProbe
      maxProbeAt := S.barrier_phase_zero_raw_maxProbeAt hn2 hphase }
  intro i
  rw [← barrierAt_labelsOf_iff hk ring D i, hlabels,
    barrierAt_labelsOf_iff hk ring X i]
  exact S.canonical i

/-- The phase-zero barrier edge gives the exact `-1` coordinate branch. -/
theorem Prepared.q_barrier_phase_zero_sub_one {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hphase : (X (barrierEdge ring)).phase = false) :
    q ring (trialStep hk ring X (barrierEdge ring)) S.maxProbe + 1 =
      q ring X S.maxProbe := by
  have hn2 : 1 < n := by omega
  have hstep := trialStep_eq_raw_of_phase_zero hk ring X S.toActive hphase
  rw [hstep]
  have hend := S.barrier_phase_zero_raw_endpoints hn2 hphase
  have hnewPhase :
      ((rawStep hk ring X (barrierEdge ring)) (tailCoord ring)).phase = true := by
    change ((rawStep hk ring X (barrierEdge ring)) (barrierEdge ring)).phase = true
    rw [hend.1]
  have holdPhase : (X (tailCoord ring)).phase = false := by
    simpa [barrierEdge] using hphase
  rw [q_of_phase_true ring _ S.maxProbe hnewPhase,
    q_of_phase_false ring X S.maxProbe holdPhase]
  omega

/-! ## The phase-one barrier branch -/

/-- A phase-one barrier hit leaves the old tail unchanged and sanitizes the
old head, which becomes the new tail after rotating the cut. -/
theorem Prepared.barrier_phase_one_raw_endpoints {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n)
    (hphase : (X (barrierEdge ring)).phase = true) :
    let D := rawStep hk ring X (barrierEdge ring)
    D (barrierEdge ring) = X (barrierEdge ring) ∧
      D (ring.rightNeighbor (barrierEdge ring)) =
        { X (ring.rightNeighbor (barrierEdge ring)) with
          label := succLabel hk (X (barrierEdge ring)).label,
          phase := false, bullet := false, probe := false } := by
  have hp := S.barrier_phase_one_pair hphase
  constructor
  · rw [rawStep_at_initiator hk ring X (barrierEdge ring), hp]
  · rw [rawStep_at_responder hk ring hn2 X (barrierEdge ring), hp]

/-- The ready phase-one raw step has the exact abstract label advance at the
old tail edge. -/
theorem Prepared.barrier_phase_one_raw_labels {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n)
    (hphase : (X (barrierEdge ring)).phase = true) :
    labelsOf (rawStep hk ring X (barrierEdge ring)) =
      advanceLabels hk ring (labelsOf X) (barrierEdge ring) := by
  exact CenteredRenewal.labelsOf_step_eq_advance_of_ready hk ring hn2 X
    (barrierEdge ring) ⟨S.barrier_isBarrier, hphase⟩

/-- A phase-one barrier hit creates no leader in the zero-leader lane. -/
theorem Prepared.barrier_phase_one_raw_zeroLeaders {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n)
    (hphase : (X (barrierEdge ring)).phase = true) :
    ∀ i : Fin n,
      (rawStep hk ring X (barrierEdge ring) i).leader = false := by
  intro i
  have hend := S.barrier_phase_one_raw_endpoints hn2 hphase
  by_cases hit : i = barrierEdge ring
  · subst i
    rw [hend.1]
    exact S.zeroLeaders _
  · by_cases hih : i = ring.rightNeighbor (barrierEdge ring)
    · subst i
      rw [hend.2]
      simp [S.zeroLeaders]
    · rw [rawStep_frame hk ring X (barrierEdge ring) i hit hih]
      exact S.zeroLeaders i

/-- The raw label write moves the unique barrier from the old tail to its
head.  This is proved from charged-barrier algebra alone and therefore does
not add a global nondivisibility premise to the local trial state. -/
theorem Prepared.barrier_phase_one_raw_oneBarrierAt_head
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n)
    (hphase : (X (barrierEdge ring)).phase = true) :
    OneBarrierAt hk ring (rawStep hk ring X (barrierEdge ring))
      (ring.rightNeighbor (barrierEdge ring)) := by
  letI : NeZero k := ⟨by omega⟩
  let t := barrierEdge ring
  let r := ring.rightNeighbor t
  let D := rawStep hk ring X t
  have hlabels : labelsOf D = advanceLabels hk ring (labelsOf X) t := by
    simpa [D, t] using S.barrier_phase_one_raw_labels hn2 hphase
  have hrt : r ≠ t := rightNeighbor_ne_self ring hn2 t
  have htbar : BarrierAt hk ring (labelsOf X) t := by
    apply (barrierAt_labelsOf_iff hk ring X t).2
    exact (S.canonical t).2 (by simp [t, barrierEdge])
  have hrnot : ¬ BarrierAt hk ring (labelsOf X) r := by
    intro hrbar
    have hrEq : r = tailCoord ring := by
      apply (S.canonical r).1
      exact (barrierAt_labelsOf_iff hk ring X r).1 hrbar
    exact hrt (by simpa [t, barrierEdge] using hrEq)
  have hrzero : defect hk ring (labelsOf X) r = zeroResidue hk :=
    Decidable.not_not.mp hrnot
  have hrbar : BarrierAt hk ring (labelsOf D) r := by
    unfold BarrierAt
    rw [hlabels]
    have hcharge := defect_advance_edgePlus hk ring hn2 (labelsOf X) t
    rw [hcharge, hrzero]
    unfold BarrierAt at htbar
    have hsum : defect hk ring (labelsOf X) t + zeroResidue hk =
        defect hk ring (labelsOf X) t := by
      apply Fin.ext
      change
        ((defect hk ring (labelsOf X) t).val + 0) % k =
          (defect hk ring (labelsOf X) t).val
      rw [Nat.add_zero, Nat.mod_eq_of_lt (defect hk ring (labelsOf X) t).isLt]
    rw [hsum]
    exact htbar
  intro j
  constructor
  · intro hj
    by_cases hjt : j = t
    · subst j
      have hjD : BarrierAt hk ring (labelsOf D) t := by
        simpa [D, t] using hj
      rw [hlabels] at hjD
      exact False.elim
        ((advance_repairs_edge hk ring hn2 (labelsOf X) t)
          hjD)
    · by_cases hjr : j = r
      · exact hjr
      · have hsame := defect_advance_other hk ring (labelsOf X) t j hjt hjr
        have hjold : BarrierAt hk ring (labelsOf X) j := by
          unfold BarrierAt at hj ⊢
          rw [hlabels, hsame] at hj
          exact hj
        have hjtail : j = tailCoord ring := by
          apply (S.canonical j).1
          exact (barrierAt_labelsOf_iff hk ring X j).1 hjold
        exact False.elim (hjt (by simpa [t, barrierEdge] using hjtail))
  · intro hjr
    subst j
    exact hrbar

/-- Rotating to the successor barrier restores the canonical one-barrier cut. -/
theorem Prepared.barrier_phase_one_canonical {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n)
    (hphase : (X (barrierEdge ring)).phase = true) :
    CanonicalOneBarrier hk ring
      (rotateCut ring (rawStep hk ring X (barrierEdge ring))) := by
  let D := rawStep hk ring X (barrierEdge ring)
  have hone : OneBarrierAt hk ring D
      (ring.rightNeighbor (barrierEdge ring)) := by
    simpa [D] using S.barrier_phase_one_raw_oneBarrierAt_head hn2 hphase
  have hcanon := canonicalOneBarrier_cutView hk ring D
    (ring.rightNeighbor (barrierEdge ring)) hone
  have hview :
      cutView ring (ring.rightNeighbor (barrierEdge ring)) D =
        rotateCut ring D := by
    simpa [barrierEdge] using
      (cutView_nextBarrier ring (tailCoord ring) D)
  rw [← hview]
  exact hcanon

/-- If the maximum probe is not the old head, the phase-one raw step clears
only the head probe and leaves that same maximum witness valid. -/
theorem Prepared.barrier_phase_one_raw_maxProbeAt {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n)
    (hphase : (X (barrierEdge ring)).phase = true)
    (hmaxPos : 0 < S.maxProbe.val) :
    MaxProbeAt (rawStep hk ring X (barrierEdge ring)) S.maxProbe := by
  let D := rawStep hk ring X (barrierEdge ring)
  have hend := S.barrier_phase_one_raw_endpoints hn2 hphase
  have hmt : S.maxProbe ≠ barrierEdge ring := S.maxProbe_ne_tail
  have hmh : S.maxProbe ≠ ring.rightNeighbor (barrierEdge ring) := by
    intro h
    have hv := congrArg Fin.val h
    simp [barrierEdge] at hv
    exact (by omega)
  have hmProbe : (D S.maxProbe).probe = true := by
    have hf := rawStep_frame hk ring X (barrierEdge ring) S.maxProbe hmt hmh
    change (rawStep hk ring X (barrierEdge ring) S.maxProbe).probe = true
    rw [hf]
    exact S.maxProbeAt.1
  refine ⟨hmProbe, ?_⟩
  intro i hi
  by_cases hit : i = barrierEdge ring
  · subst i
    have hfalse : (D (barrierEdge ring)).probe = false := by
      change (rawStep hk ring X (barrierEdge ring)
        (barrierEdge ring)).probe = false
      rw [hend.1]
      exact S.tailProbe
    rw [hfalse] at hi
    contradiction
  · by_cases hih : i = ring.rightNeighbor (barrierEdge ring)
    · subst i
      have hfalse : (D (ring.rightNeighbor (barrierEdge ring))).probe = false := by
        change (rawStep hk ring X (barrierEdge ring)
          (ring.rightNeighbor (barrierEdge ring))).probe = false
        rw [hend.2]
      rw [hfalse] at hi
      contradiction
    · have hf := rawStep_frame hk ring X (barrierEdge ring) i hit hih
      rw [hf] at hi
      exact S.maxProbeAt.2 i hi

/-- In the rotated successor cut, an old positive maximum coordinate becomes
its predecessor and remains the exact maximum probe. -/
theorem Prepared.barrier_phase_one_rotated_maxProbeAt
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n)
    (hphase : (X (barrierEdge ring)).phase = true)
    (hmaxPos : 0 < S.maxProbe.val) :
    MaxProbeAt
      (rotateCut ring (rawStep hk ring X (barrierEdge ring)))
      (ring.leftNeighbor S.maxProbe) := by
  let D := rawStep hk ring X (barrierEdge ring)
  have hraw := S.barrier_phase_one_raw_maxProbeAt hn2 hphase hmaxPos
  have hend := S.barrier_phase_one_raw_endpoints hn2 hphase
  refine ⟨?_, ?_⟩
  · change (D (ring.rightNeighbor (ring.leftNeighbor S.maxProbe))).probe = true
    rw [rightNeighbor_leftNeighbor_clean]
    exact hraw.1
  · intro i hi
    change (D (ring.rightNeighbor i)).probe = true at hi
    have hit : i ≠ tailCoord ring := by
      intro hit
      subst i
      have hfalse :
          (D (ring.rightNeighbor (barrierEdge ring))).probe = false := by
        change (rawStep hk ring X (barrierEdge ring)
          (ring.rightNeighbor (barrierEdge ring))).probe = false
        rw [hend.2]
      rw [show tailCoord ring = barrierEdge ring by rfl, hfalse] at hi
      contradiction
    have hle := hraw.2 (ring.rightNeighbor i) hi
    have hir := rightNeighbor_val_of_ne_tail ring i hit
    have hl := leftNeighbor_val_of_pos ring S.maxProbe hmaxPos
    omega

/-- A nonterminal phase-one barrier hit reconstructs the full active trial in
the rotated cut.  The explicit maximum witness shifts left by one coordinate. -/
def Prepared.phaseOnePrepared {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hphase : (X (barrierEdge ring)).phase = true)
    (hmaxPos : 0 < S.maxProbe.val) :
    Prepared hk ring (trialStep hk ring X (barrierEdge ring)) := by
  have hn2 : 1 < n := by omega
  have hstep := trialStep_eq_rotate_raw_of_phase_one hk ring X S.toActive hphase
  rw [hstep]
  let D := rawStep hk ring X (barrierEdge ring)
  have hend := S.barrier_phase_one_raw_endpoints hn2 hphase
  have hmax := S.barrier_phase_one_rotated_maxProbeAt hn2 hphase hmaxPos
  refine
    { canonical := S.barrier_phase_one_canonical hn2 hphase
      zeroLeaders := by
        intro i
        change (D (ring.rightNeighbor i)).leader = false
        exact S.barrier_phase_one_raw_zeroLeaders hn2 hphase _
      tailBullet := by
        change (D (ring.rightNeighbor (tailCoord ring))).bullet = false
        change (D (ring.rightNeighbor (barrierEdge ring))).bullet = false
        change (rawStep hk ring X (barrierEdge ring)
          (ring.rightNeighbor (barrierEdge ring))).bullet = false
        rw [hend.2]
      tailProbe := by
        change (D (ring.rightNeighbor (tailCoord ring))).probe = false
        change (D (ring.rightNeighbor (barrierEdge ring))).probe = false
        change (rawStep hk ring X (barrierEdge ring)
          (ring.rightNeighbor (barrierEdge ring))).probe = false
        rw [hend.2]
      hasProbe := ⟨ring.leftNeighbor S.maxProbe, hmax.1⟩
      maxProbe := ring.leftNeighbor S.maxProbe
      maxProbeAt := hmax }

/-- The nonterminal phase-one barrier edge gives the exact `-1` coordinate
branch: rotation lowers the maximum coordinate and resets the new tail phase. -/
theorem Prepared.q_barrier_phase_one_sub_one {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hphase : (X (barrierEdge ring)).phase = true)
    (hmaxPos : 0 < S.maxProbe.val) :
    q ring (trialStep hk ring X (barrierEdge ring))
        (ring.leftNeighbor S.maxProbe) + 1 =
      q ring X S.maxProbe := by
  have hn2 : 1 < n := by omega
  have hstep := trialStep_eq_rotate_raw_of_phase_one hk ring X S.toActive hphase
  rw [hstep]
  let D := rawStep hk ring X (barrierEdge ring)
  have hend := S.barrier_phase_one_raw_endpoints hn2 hphase
  have hnewPhase :
      ((rotateCut ring D) (tailCoord ring)).phase = false := by
    change (D (ring.rightNeighbor (tailCoord ring))).phase = false
    change (D (ring.rightNeighbor (barrierEdge ring))).phase = false
    change (rawStep hk ring X (barrierEdge ring)
      (ring.rightNeighbor (barrierEdge ring))).phase = false
    rw [hend.2]
  have holdPhase : (X (tailCoord ring)).phase = true := by
    simpa [barrierEdge] using hphase
  have hl := leftNeighbor_val_of_pos ring S.maxProbe hmaxPos
  rw [q_of_phase_false ring _ (ring.leftNeighbor S.maxProbe) hnewPhase,
    q_of_phase_true ring X S.maxProbe holdPhase]
  omega

/-- In phase one, being nonterminal (`q > 1`) is exactly having a positive
maximum-probe coordinate. -/
theorem Prepared.q_gt_one_iff_maxProbe_pos_of_phase_one
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X)
    (hphase : (X (barrierEdge ring)).phase = true) :
    1 < q ring X S.maxProbe ↔ 0 < S.maxProbe.val := by
  have htailPhase : (X (tailCoord ring)).phase = true := by
    simpa [barrierEdge] using hphase
  rw [q_of_phase_true ring X S.maxProbe htailPhase]
  omega

/-- Consumer-facing form of the nonterminal phase-one branch, stated with the
stopped trial's coordinate guard rather than the equivalent maximum bound. -/
def Prepared.phaseOnePrepared_of_q_gt_one
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hphase : (X (barrierEdge ring)).phase = true)
    (hq : 1 < q ring X S.maxProbe) :
    Prepared hk ring (trialStep hk ring X (barrierEdge ring)) :=
  S.phaseOnePrepared hn3 hphase
    ((S.q_gt_one_iff_maxProbe_pos_of_phase_one hphase).1 hq)

/-- Consumer-facing exact drift equation for the `q > 1` phase-one branch. -/
theorem Prepared.q_barrier_phase_one_sub_one_of_q_gt_one
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hphase : (X (barrierEdge ring)).phase = true)
    (hq : 1 < q ring X S.maxProbe) :
    q ring (trialStep hk ring X (barrierEdge ring))
        (ring.leftNeighbor S.maxProbe) + 1 =
      q ring X S.maxProbe :=
  S.q_barrier_phase_one_sub_one hn3 hphase
    ((S.q_gt_one_iff_maxProbe_pos_of_phase_one hphase).1 hq)

/-- At the exceptional phase-one state with maximum probe coordinate zero,
the raw barrier hit clears every probe. -/
theorem Prepared.barrier_phase_one_zero_raw_allProbesCleared
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn2 : 1 < n)
    (hphase : (X (barrierEdge ring)).phase = true)
    (hmaxZero : S.maxProbe.val = 0) :
    ∀ i : Fin n,
      (rawStep hk ring X (barrierEdge ring) i).probe = false := by
  intro i
  have hend := S.barrier_phase_one_raw_endpoints hn2 hphase
  by_cases hit : i = barrierEdge ring
  · subst i
    rw [hend.1]
    exact S.tailProbe
  · by_cases hih : i = ring.rightNeighbor (barrierEdge ring)
    · subst i
      rw [hend.2]
    · have hf := rawStep_frame hk ring X (barrierEdge ring) i hit hih
      rw [hf]
      cases hp : (X i).probe
      · rfl
      · have hle := S.maxProbeAt.2 i hp
        have hiz : i.val = 0 := by omega
        have hihead : i = ring.rightNeighbor (barrierEdge ring) := by
          apply Fin.ext
          simpa [barrierEdge] using hiz
        exact False.elim (hih hihead)

/-- The exceptional `q = 1` phase-one hit is the literal failure branch:
after the mandatory cut rotation, every probe is gone. -/
theorem Prepared.barrier_phase_one_zero_terminal_failure
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hphase : (X (barrierEdge ring)).phase = true)
    (hmaxZero : S.maxProbe.val = 0) :
    q ring X S.maxProbe = 1 ∧
      (∀ i : Fin n,
        (trialStep hk ring X (barrierEdge ring) i).probe = false) ∧
      CanonicalOneBarrier hk ring
        (trialStep hk ring X (barrierEdge ring)) ∧
      (∀ i : Fin n,
        (trialStep hk ring X (barrierEdge ring) i).leader = false) := by
  have hn2 : 1 < n := by omega
  have hstep := trialStep_eq_rotate_raw_of_phase_one hk ring X S.toActive hphase
  refine ⟨(S.q_eq_one_iff).2 ⟨hmaxZero, by simpa [barrierEdge] using hphase⟩,
    ?_, ?_, ?_⟩
  · intro i
    rw [hstep]
    change (rawStep hk ring X (barrierEdge ring)
      (ring.rightNeighbor i)).probe = false
    exact S.barrier_phase_one_zero_raw_allProbesCleared hn2 hphase hmaxZero _
  · rw [hstep]
    exact S.barrier_phase_one_canonical hn2 hphase
  · intro i
    rw [hstep]
    change (rawStep hk ring X (barrierEdge ring)
      (ring.rightNeighbor i)).leader = false
    exact S.barrier_phase_one_raw_zeroLeaders hn2 hphase _

/-- The literal failure branch retains exactly the physical data needed for a
fresh phase-zero barrier hit. -/
theorem Prepared.barrier_phase_one_zero_restartReady
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hphase : (X (barrierEdge ring)).phase = true)
    (hmaxZero : S.maxProbe.val = 0) :
    RestartReady hk ring
      (trialStep hk ring X (barrierEdge ring)) := by
  have hn2 : 1 < n := by omega
  have hterminal :=
    S.barrier_phase_one_zero_terminal_failure hn3 hphase hmaxZero
  have hstep := trialStep_eq_rotate_raw_of_phase_one hk ring X S.toActive hphase
  have hend := S.barrier_phase_one_raw_endpoints hn2 hphase
  refine
    { canonical := hterminal.2.2.1
      zeroLeaders := hterminal.2.2.2
      tailBullet := ?_
      tailPhase := ?_
      allProbesCleared := hterminal.2.1 }
  · rw [hstep]
    change (rawStep hk ring X (barrierEdge ring)
      (ring.rightNeighbor (tailCoord ring))).bullet = false
    simpa [barrierEdge] using congrArg State.bullet hend.2
  · rw [hstep]
    change (rawStep hk ring X (barrierEdge ring)
      (ring.rightNeighbor (tailCoord ring))).phase = false
    simpa [barrierEdge] using congrArg State.phase hend.2

/-- A restart-ready endpoint does not rotate its cut on the phase-zero
barrier hit. -/
theorem RestartReady.trialStep_eq_raw
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (F : RestartReady hk ring X) :
    trialStep hk ring X (barrierEdge ring) =
      rawStep hk ring X (barrierEdge ring) := by
  have hnot : ¬ CenteredRenewal.AdvanceReady hk ring X (barrierEdge ring) := by
    intro hready
    exact Bool.noConfusion (hready.2.symm.trans F.tailPhase)
  unfold trialStep Rank.cutSuccessor
  dsimp
  exact if_neg hnot

/-- Exact local pair created by the one-edge restart hit. -/
theorem RestartReady.barrier_phase_zero_raw_endpoints
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (F : RestartReady hk ring X) (hn2 : 1 < n) :
    let D := rawStep hk ring X (barrierEdge ring)
    D (barrierEdge ring) = { X (barrierEdge ring) with phase := true } ∧
      D (ring.rightNeighbor (barrierEdge ring)) =
        { X (ring.rightNeighbor (barrierEdge ring)) with probe := true } := by
  have hbar : IsBarrier hk (X (barrierEdge ring))
      (X (ring.rightNeighbor (barrierEdge ring))) :=
    (F.canonical (barrierEdge ring)).2 rfl
  have hpair :
      CenteredRenewal.transition hk (X (barrierEdge ring))
        (X (ring.rightNeighbor (barrierEdge ring))) =
        ({ X (barrierEdge ring) with phase := true },
          { X (ring.rightNeighbor (barrierEdge ring)) with probe := true }) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    have hphase : (X (barrierEdge ring)).phase = false := by
      simpa [barrierEdge] using F.tailPhase
    rw [CenteredRenewal.barrierStep_phase_zero hk _ _ hphase]
    simp [probeHitsBarrier, F.allProbesCleared, F.zeroLeaders]
  constructor
  · rw [rawStep_at_initiator hk ring X (barrierEdge ring), hpair]
  · rw [rawStep_at_responder hk ring hn2 X (barrierEdge ring), hpair]

/-- The one physical barrier edge after failure creates a fresh prepared trial.
The new maximum is the canonical head, i.e. coordinate zero. -/
def RestartReady.restartPrepared
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (F : RestartReady hk ring X) (hn3 : 3 ≤ n) :
    Prepared hk ring (trialStep hk ring X (barrierEdge ring)) := by
  have hn2 : 1 < n := by omega
  rw [F.trialStep_eq_raw]
  let D := rawStep hk ring X (barrierEdge ring)
  let z := ring.rightNeighbor (barrierEdge ring)
  have hend := F.barrier_phase_zero_raw_endpoints hn2
  have hlabels : labelsOf D = labelsOf X := by
    exact CenteredRenewal.labelsOf_step_eq_self_of_not_ready hk ring X
      (barrierEdge ring) (by
        intro h
        exact Bool.noConfusion (h.2.symm.trans F.tailPhase))
  have hzero : ∀ i : Fin n, (D i).leader = false := by
    intro i
    by_cases hit : i = barrierEdge ring
    · subst i
      change (rawStep hk ring X (barrierEdge ring)
        (barrierEdge ring)).leader = false
      rw [hend.1]
      simp [F.zeroLeaders]
    · by_cases hih : i = z
      · subst i
        change (rawStep hk ring X (barrierEdge ring)
          (ring.rightNeighbor (barrierEdge ring))).leader = false
        rw [hend.2]
        simp [F.zeroLeaders]
      · change (rawStep hk ring X (barrierEdge ring) i).leader = false
        rw [rawStep_frame hk ring X (barrierEdge ring) i hit hih]
        exact F.zeroLeaders i
  have hmax : MaxProbeAt D z := by
    refine ⟨by simpa [z] using congrArg State.probe hend.2, ?_⟩
    intro i hi
    by_cases hiz : i = z
    · subst i
      exact Nat.le_refl _
    · by_cases hit : i = barrierEdge ring
      · subst i
        have hfalse : (D (barrierEdge ring)).probe = false := by
          simpa [D, F.allProbesCleared] using congrArg State.probe hend.1
        rw [hfalse] at hi
        contradiction
      · have hframe := rawStep_frame hk ring X (barrierEdge ring) i hit hiz
        exfalso
        change (rawStep hk ring X (barrierEdge ring) i).probe = true at hi
        rw [hframe, F.allProbesCleared i] at hi
        contradiction
  refine
    { canonical := ?_
      zeroLeaders := hzero
      tailBullet := ?_
      tailProbe := ?_
      hasProbe := ⟨z, hmax.1⟩
      maxProbe := z
      maxProbeAt := hmax }
  · intro i
    rw [← barrierAt_labelsOf_iff hk ring D i, hlabels,
      barrierAt_labelsOf_iff hk ring X i]
    exact F.canonical i
  · change (D (tailCoord ring)).bullet = false
    simpa [D, barrierEdge, F.tailBullet] using congrArg State.bullet hend.1
  · change (D (tailCoord ring)).probe = false
    simpa [D, barrierEdge, F.allProbesCleared] using congrArg State.probe hend.1

/-- The restart hit creates exactly one probe, at the canonical head. -/
theorem RestartReady.restart_probe_iff_eq_head
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (F : RestartReady hk ring X) (hn2 : 1 < n) (i : Fin n) :
    (trialStep hk ring X (barrierEdge ring) i).probe = true ↔
      i = ring.rightNeighbor (barrierEdge ring) := by
  rw [F.trialStep_eq_raw]
  have hend := F.barrier_phase_zero_raw_endpoints hn2
  constructor
  · intro hi
    by_cases hit : i = barrierEdge ring
    · subst i
      have hfalse := congrArg State.probe hend.1
      simp [F.allProbesCleared] at hfalse
      rw [hfalse] at hi
      contradiction
    · by_cases hih : i = ring.rightNeighbor (barrierEdge ring)
      · exact hih
      · rw [rawStep_frame hk ring X (barrierEdge ring) i hit hih,
          F.allProbesCleared i] at hi
        contradiction
  · intro hi
    subst i
    simpa using congrArg State.probe hend.2

/-- The fresh trial produced by the restart edge starts at coordinate one. -/
theorem RestartReady.q_restartPrepared
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (F : RestartReady hk ring X) (hn3 : 3 ≤ n) :
    let S := F.restartPrepared hn3
    q ring (trialStep hk ring X (barrierEdge ring)) S.maxProbe = 1 := by
  dsimp only
  have hn2 : 1 < n := by omega
  let S := F.restartPrepared hn3
  have hend := F.barrier_phase_zero_raw_endpoints hn2
  have hstep := F.trialStep_eq_raw
  have hphase :
      (trialStep hk ring X (barrierEdge ring) (tailCoord ring)).phase = true := by
    rw [hstep]
    simpa [barrierEdge] using congrArg State.phase hend.1
  have hz : S.maxProbe.val = 0 := by
    have hm : S.maxProbe = ring.rightNeighbor (barrierEdge ring) :=
      (F.restart_probe_iff_eq_head hn2 S.maxProbe).1 S.maxProbeAt.1
    rw [hm]
    simp [barrierEdge]
  rw [q_of_phase_true ring _ S.maxProbe hphase]
  omega

/-- Away from the barrier, a restart-waiting configuration does not rotate its
canonical cut. -/
theorem RestartReady.trialStep_eq_raw_of_ne_barrier
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (F : RestartReady hk ring X) (e : Fin n)
    (he : e ≠ barrierEdge ring) :
    trialStep hk ring X e = rawStep hk ring X e := by
  have hnot : ¬ CenteredRenewal.AdvanceReady hk ring X e := by
    intro hready
    have het : e = tailCoord ring := (F.canonical e).1 hready.1
    exact he (by simpa [barrierEdge] using het)
  unfold trialStep Rank.cutSuccessor
  dsimp
  exact if_neg hnot

/-- Every nonbarrier scheduler edge preserves the physical restart domain.
Thus waiting for the unique barrier edge does not assume scheduler stuttering. -/
theorem RestartReady.otherRestartReady
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (F : RestartReady hk ring X) (hn3 : 3 ≤ n) (e : Fin n)
    (he : e ≠ barrierEdge ring) :
    RestartReady hk ring (trialStep hk ring X e) := by
  have hn2 : 1 < n := by omega
  rw [F.trialStep_eq_raw_of_ne_barrier e he]
  let D := rawStep hk ring X e
  have hnot : ¬ IsBarrier hk (X e) (X (ring.rightNeighbor e)) := by
    intro hbar
    have het : e = tailCoord ring := (F.canonical e).1 hbar
    exact he (by simpa [barrierEdge] using het)
  have hpair := CenteredRenewal.transition_of_nonbarrier hk
    (X e) (X (ring.rightNeighbor e)) hnot
  have hlabels : labelsOf D = labelsOf X := by
    exact CenteredRenewal.labelsOf_step_eq_self_of_not_ready hk ring X e (by
      intro hready
      have het : e = tailCoord ring := (F.canonical e).1 hready.1
      exact he (by simpa [barrierEdge] using het))
  have hzero : ∀ i : Fin n, (D i).leader = false := by
    intro i
    by_cases hie : i = e
    · subst i
      change (rawStep hk ring X e e).leader = false
      rw [rawStep_at_initiator hk ring X e, hpair]
      cases hb : (X (ring.rightNeighbor e)).bullet <;>
        simp [nonBarrierStep, F.zeroLeaders, F.allProbesCleared, hb]
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        change (rawStep hk ring X e (ring.rightNeighbor e)).leader = false
        rw [rawStep_at_responder hk ring hn2 X e, hpair]
        cases hb : (X (ring.rightNeighbor e)).bullet <;>
          simp [nonBarrierStep, F.zeroLeaders, F.allProbesCleared, hb]
      · change (rawStep hk ring X e i).leader = false
        rw [rawStep_frame hk ring X e i hie hir]
        exact F.zeroLeaders i
  have hprobes : ∀ i : Fin n, (D i).probe = false := by
    intro i
    by_cases hie : i = e
    · subst i
      change (rawStep hk ring X e e).probe = false
      rw [rawStep_at_initiator hk ring X e, hpair]
      cases hb : (X (ring.rightNeighbor e)).bullet <;>
        simp [nonBarrierStep, F.zeroLeaders, F.allProbesCleared, hb]
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        change (rawStep hk ring X e (ring.rightNeighbor e)).probe = false
        rw [rawStep_at_responder hk ring hn2 X e, hpair]
        cases hb : (X (ring.rightNeighbor e)).bullet <;>
          simp [nonBarrierStep, F.zeroLeaders, F.allProbesCleared, hb]
      · change (rawStep hk ring X e i).probe = false
        rw [rawStep_frame hk ring X e i hie hir]
        exact F.allProbesCleared i
  have htail : D (tailCoord ring) = X (tailCoord ring) := by
    have hte : tailCoord ring ≠ e := by
      intro h
      exact he (by simpa [barrierEdge] using h.symm)
    by_cases htr : tailCoord ring = ring.rightNeighbor e
    · rw [htr]
      change rawStep hk ring X e (ring.rightNeighbor e) =
        X (ring.rightNeighbor e)
      rw [rawStep_at_responder hk ring hn2 X e, hpair]
      have hb : (X (ring.rightNeighbor e)).bullet = false := by
        rw [← htr]
        exact F.tailBullet
      simp [nonBarrierStep, F.zeroLeaders, F.allProbesCleared, hb]
    · change rawStep hk ring X e (tailCoord ring) = X (tailCoord ring)
      exact rawStep_frame hk ring X e (tailCoord ring) hte htr
  refine
    { canonical := ?_
      zeroLeaders := hzero
      tailBullet := by
        simpa [D, F.tailBullet] using congrArg State.bullet htail
      tailPhase := by
        simpa [D, F.tailPhase] using congrArg State.phase htail
      allProbesCleared := hprobes }
  intro i
  rw [← barrierAt_labelsOf_iff hk ring D i, hlabels,
    barrierAt_labelsOf_iff hk ring X i]
  exact F.canonical i

/-- Repack the progress successor with a definitionally visible maximum field.
The older branch constructor rewrites a dependent configuration index and thus
leaves a harmless cast around projections; the finite-tree adapter benefits
from exposing this field literally. -/
def Prepared.progressProofPrepared
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (h : S.maxProbe.val ≤ n - 3) :
    Prepared hk ring (trialStep hk ring X (progressEdge S.maxProbe)) :=
  { toActive := (S.progressPrepared hn3 h).toActive
    maxProbe := ring.rightNeighbor S.maxProbe
    maxProbeAt := by
      have hn2 : 1 < n := by omega
      rw [S.trialStep_eq_raw_of_ne_barrier _ S.progress_ne_barrier]
      exact S.progress_raw_maxProbeAt hn2 }

/-- Repack an irrelevant successor with the unchanged maximum field exposed
definitionally for the generic frame law. -/
def Prepared.otherProofPrepared
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n) (e : Fin n)
    (heP : e ≠ progressEdge S.maxProbe)
    (heQ : e ≠ barrierEdge ring) :
    Prepared hk ring (trialStep hk ring X e) :=
  { toActive := (S.otherPrepared hn3 e heP heQ).toActive
    maxProbe := S.maxProbe
    maxProbeAt := by
      rw [S.trialStep_eq_raw_of_ne_barrier e heQ]
      exact S.other_raw_maxProbeAt hn3 e heP heQ }

/-- Repack the phase-zero successor with its unchanged maximum exposed. -/
def Prepared.phaseZeroProofPrepared
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hphase : (X (barrierEdge ring)).phase = false) :
    Prepared hk ring (trialStep hk ring X (barrierEdge ring)) :=
  { toActive := (S.phaseZeroPrepared hn3 hphase).toActive
    maxProbe := S.maxProbe
    maxProbeAt := by
      have hn2 : 1 < n := by omega
      rw [trialStep_eq_raw_of_phase_zero hk ring X S.toActive hphase]
      exact S.barrier_phase_zero_raw_maxProbeAt hn2 hphase }

/-- Repack the phase-one successor with its shifted maximum exposed. -/
def Prepared.phaseOneProofPrepared
    {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {X : Fin n → State k}
    (S : Prepared hk ring X) (hn3 : 3 ≤ n)
    (hphase : (X (barrierEdge ring)).phase = true)
    (hmaxPos : 0 < S.maxProbe.val) :
    Prepared hk ring (trialStep hk ring X (barrierEdge ring)) :=
  { toActive := (S.phaseOnePrepared hn3 hphase hmaxPos).toActive
    maxProbe := ring.leftNeighbor S.maxProbe
    maxProbeAt := by
      have hn2 : 1 < n := by omega
      rw [trialStep_eq_rotate_raw_of_phase_one hk ring X S.toActive hphase]
      exact S.barrier_phase_one_rotated_maxProbeAt hn2 hphase hmaxPos }

/-! ## Proof-state packaging for the finite action tree -/

/-- A stopped trial node.  Active nodes retain the full `Prepared` witness.
Success nodes retain the concrete tail-probe configuration and the extended
upper coordinate produced by the terminal `P` step; failure nodes retain the
probe-free configuration together with its one-edge restart witness and have
coordinate zero. -/
inductive ProofState {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) where
  | active (X : Fin n → State k) (prepared : Prepared hk ring X)
  | success (X : Fin n → State k)
      (tailProbe : (X (tailCoord ring)).probe = true)
      (coord : Nat) (coord_le : coord ≤ 2 * n)
  | failure (X : Fin n → State k) (restartReady : RestartReady hk ring X)

/-- Only `active` proof nodes are expanded by the stopped action tree. -/
def ProofState.isActive {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} :
    ProofState hk ring → Bool
  | .active _ _ => true
  | .success _ _ _ _ => false
  | .failure _ _ => false

/-- Active nodes use the doubled probe-front coordinate, successful endpoints
use their terminal upper coordinate, and failed endpoints use zero. -/
def ProofState.coord {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} :
    ProofState hk ring → Nat
  | .active X S => q ring X S.maxProbe
  | .success _ _ c _ => c
  | .failure _ _ => 0

/-- The predictable `+2` edge selected from the current proof state. -/
def ProofState.upEdge {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} :
    ProofState hk ring → Fin n
  | .active _ S => progressEdge S.maxProbe
  | .success _ _ _ _ => ⟨0, ring.hn⟩
  | .failure _ _ => ⟨0, ring.hn⟩

/-- The predictable `-1` barrier edge selected from the current proof state. -/
def ProofState.downEdge {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} :
    ProofState hk ring → Fin n
  | .active _ _ => barrierEdge ring
  | .success _ _ _ _ => ⟨0, ring.hn⟩
  | .failure _ _ => ⟨0, ring.hn⟩

/-- Total scheduler step on proof states.  Terminal nodes are absorbing.  An
active node is classified by the selected physical edge and then by the exact
top/phase/zero subcase proved above. -/
def ProofState.next {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 ≤ n) : ProofState hk ring → Fin n → ProofState hk ring
  | .success X hp c hc, _ => .success X hp c hc
  | .failure X hp, _ => .failure X hp
  | .active X S, e =>
      if hP : e = progressEdge S.maxProbe then
        if htop : S.maxProbe.val = n - 2 then
          let D := trialStep hk ring X (progressEdge S.maxProbe)
          let hsuccess := S.progress_top_terminal_success hn3 htop
          .success D hsuccess.1 (q ring X S.maxProbe + 2) (by
            have hq := S.q_le_two_n_sub_two
            omega)
        else
          .active (trialStep hk ring X (progressEdge S.maxProbe))
            (S.progressProofPrepared hn3 (by
              have hle := S.maxProbe_le_n_sub_two
              omega))
      else if hQ : e = barrierEdge ring then
        match hphase : (X (barrierEdge ring)).phase with
        | false =>
            .active (trialStep hk ring X (barrierEdge ring))
              (S.phaseZeroProofPrepared hn3 hphase)
        | true =>
            if hzero : S.maxProbe.val = 0 then
              let D := trialStep hk ring X (barrierEdge ring)
              .failure D
                (S.barrier_phase_one_zero_restartReady hn3 hphase hzero)
            else
              .active (trialStep hk ring X (barrierEdge ring))
                (S.phaseOneProofPrepared hn3 hphase (by omega))
      else
        .active (trialStep hk ring X e) (S.otherProofPrepared hn3 e hP hQ)

/-- The stopped proof transition realizes the generic predictable
plus-two/minus-one finite-tree interface with global coordinate cap `2*n`. -/
def finiteTreeSpec {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) :
    PlusTwoMinusOneFiniteTree.Spec (ProofState hk ring) n (2 * n) := by
  refine
    { active := ProofState.isActive
      next := ProofState.next hn3
      coord := ProofState.coord
      upEdge := ProofState.upEdge
      downEdge := ProofState.downEdge
      edge_count := by omega
      coord_le := ?_
      active_pos := ?_
      active_up_le := ?_
      edges_ne := ?_
      up_coord := ?_
      down_coord := ?_
      frame_coord := ?_ }
  · intro s
    cases s with
    | active X S =>
        exact Nat.le_trans S.q_le_two_n_sub_two (by omega)
    | success X hp c hc => exact hc
    | failure X hp => simp [ProofState.coord]
  · intro s hs
    cases s with
    | active X S => exact S.q_pos
    | success X hp c hc => simp [ProofState.isActive] at hs
    | failure X hp => simp [ProofState.isActive] at hs
  · intro s hs
    cases s with
    | active X S =>
        change q ring X S.maxProbe + 2 ≤ 2 * n
        have hq := S.q_le_two_n_sub_two
        omega
    | success X hp c hc => simp [ProofState.isActive] at hs
    | failure X hp => simp [ProofState.isActive] at hs
  · intro s hs
    cases s with
    | active X S => exact S.progress_ne_barrier
    | success X hp c hc => simp [ProofState.isActive] at hs
    | failure X hp => simp [ProofState.isActive] at hs
  · intro s hs
    cases s with
    | success X hp c hc => simp [ProofState.isActive] at hs
    | failure X hp => simp [ProofState.isActive] at hs
    | active X S =>
        simp only [ProofState.upEdge, ProofState.next, dite_true]
        by_cases htop : S.maxProbe.val = n - 2
        · simp [htop, ProofState.coord]
        · have hnonterminal : S.maxProbe.val ≤ n - 3 := by
            have hle := S.maxProbe_le_n_sub_two
            omega
          simp only [htop, dite_false, ProofState.coord]
          change q ring (trialStep hk ring X (progressEdge S.maxProbe))
              (ring.rightNeighbor S.maxProbe) = q ring X S.maxProbe + 2
          exact S.q_progress_add_two hn3 hnonterminal
  · intro s hs
    cases s with
    | success X hp c hc => simp [ProofState.isActive] at hs
    | failure X hp => simp [ProofState.isActive] at hs
    | active X S =>
        simp only [ProofState.downEdge, ProofState.next]
        rw [dif_neg (Ne.symm S.progress_ne_barrier)]
        rw [dif_pos True.intro]
        split
        · rename_i hphase
          simp only [ProofState.coord]
          change q ring (trialStep hk ring X (barrierEdge ring)) S.maxProbe + 1 =
            q ring X S.maxProbe
          exact S.q_barrier_phase_zero_sub_one hn3 hphase
        · rename_i hphase
          by_cases hzero : S.maxProbe.val = 0
          · have hfailure :=
              S.barrier_phase_one_zero_terminal_failure hn3 hphase hzero
            simp [hzero, ProofState.coord, hfailure.1]
          · have hpos : 0 < S.maxProbe.val := by omega
            simp only [hzero, dite_false, ProofState.coord]
            change q ring (trialStep hk ring X (barrierEdge ring))
                (ring.leftNeighbor S.maxProbe) + 1 = q ring X S.maxProbe
            exact S.q_barrier_phase_one_sub_one hn3 hphase hpos
  · intro s hs e heP heQ
    cases s with
    | success X hp c hc => simp [ProofState.isActive] at hs
    | failure X hp => simp [ProofState.isActive] at hs
    | active X S =>
        simp only [ProofState.upEdge, ProofState.downEdge] at heP heQ
        simp only [ProofState.next, heP, heQ, dite_false, ProofState.coord]
        change q ring (trialStep hk ring X e) S.maxProbe = q ring X S.maxProbe
        exact S.q_other hn3 e heP heQ

end ZeroLeaderTrial
end CenteredRenewal
end AAFJPK
