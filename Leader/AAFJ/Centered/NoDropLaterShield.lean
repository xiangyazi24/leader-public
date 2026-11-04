import Leader.AAFJ.Centered.RankMonotone

/-!
# The later-shield seam for the centered one-barrier rank race

This file isolates the history-sensitive invariant needed by the `Phi > 1`
rank block.  A bare later leader is not stable on a `Phi` plateau: it may
already carry a bullet, die, and trade one leader for the dangerous-probe bit.
The race therefore remembers a bullet-free rightmost later leader together
with a bullet-free follower suffix.

The first consumer proved below is deliberately local.  Deleting a target
leader while a strictly later leader survives cannot create a new dangerous
probe, and hence strictly lowers `Phi` above the floor at one.  This is the
semantic bridge required at the final tracked-bullet hit.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace NoDropLaterShield

open BarrierAlgebra
open SingleBarrierSanitation

set_option autoImplicit false

/-- Strict order in the cut whose unique barrier tail is `b`. -/
def StrictlyLaterAt {n : Nat} (ring : DirectedRing n)
    (b x y : Fin n) : Prop :=
  (cutCoord ring b x).val < (cutCoord ring b y).val

/-- A leader strictly later than the tracked target in the current cut. -/
def LaterLeaderAt {n k : Nat} (ring : DirectedRing n)
    (C : Fin n -> State k) (b target : Fin n) : Prop :=
  exists witness : Fin n,
    StrictlyLaterAt ring b target witness /\
      (C witness).leader = true

/-- Every site strictly after `witness` is a bullet-free follower. -/
def CleanAfter {n k : Nat} (ring : DirectedRing n)
    (C : Fin n -> State k) (b witness : Fin n) : Prop :=
  forall x : Fin n, StrictlyLaterAt ring b witness x ->
    (C x).leader = false /\ (C x).bullet = false

/-- Race-specific strengthening of `LaterLeaderAt`.

The witness is a bullet-free rightmost leader above the target.  Unlike the
bare existential later-leader predicate, this structure prevents an
unrelated incoming bullet from deleting the witness on a plateau step. -/
def FreshRightmostAbove {n k : Nat} (ring : DirectedRing n)
    (C : Fin n -> State k) (b target : Fin n) : Prop :=
  exists witness : Fin n,
    StrictlyLaterAt ring b target witness /\
      (C witness).leader = true /\
      (C witness).bullet = false /\
      CleanAfter ring C b witness

theorem FreshRightmostAbove.laterLeader {n k : Nat}
    {ring : DirectedRing n} {C : Fin n -> State k} {b target : Fin n}
    (h : FreshRightmostAbove ring C b target) :
    LaterLeaderAt ring C b target := by
  obtain ⟨witness, hlater, hleader, _⟩ := h
  exact ⟨witness, hlater, hleader⟩

/-- The physical barrier tail is the last coordinate of its own cut. -/
@[simp] theorem cutCoord_self {n : Nat} (ring : DirectedRing n)
    (b : Fin n) : cutCoord ring b b = tailCoord ring := by
  apply cutPos_injective ring b
  rw [cutPos_cutCoord, cutPos_tailCoord]

/-- Every other vertex is strictly before the current barrier tail. -/
theorem strictlyLater_tail_of_ne {n : Nat} (ring : DirectedRing n)
    (x b : Fin n) (hxb : x ≠ b) : StrictlyLaterAt ring b x b := by
  unfold StrictlyLaterAt
  rw [cutCoord_self]
  change (cutCoord ring b x).val < n - 1
  have hxlt := (cutCoord ring b x).isLt
  have hxne : (cutCoord ring b x).val ≠ n - 1 := by
    intro hval
    apply hxb
    have hcoord : cutCoord ring b x = tailCoord ring := by
      apply Fin.ext
      exact hval
    calc
      x = cutPos ring b (cutCoord ring b x) :=
        (cutPos_cutCoord ring b x).symm
      _ = cutPos ring b (tailCoord ring) := congrArg (cutPos ring b) hcoord
      _ = b := cutPos_tailCoord ring b
  omega

/-- A fresh rightmost witness makes the current tail bullet-free. -/
theorem FreshRightmostAbove.tail_bullet_false {n k : Nat}
    {ring : DirectedRing n} {C : Fin n -> State k} {b target : Fin n}
    (h : FreshRightmostAbove ring C b target) :
    (C b).bullet = false := by
  obtain ⟨witness, _htarget, _hleader, hbullet, hclean⟩ := h
  by_cases hwb : witness = b
  · simpa [hwb] using hbullet
  · exact (hclean b (strictlyLater_tail_of_ne ring witness b hwb)).2

/-- Abstract exact deletion of one leader.  All probe bits and every other
leader bit are retained; these are precisely the fields relevant to `Phi`. -/
structure DeletesOnlyLeaderAt {n k : Nat} (target : Fin n)
    (before after : Fin n -> State k) : Prop where
  before_leader : (before target).leader = true
  after_leader : (after target).leader = false
  other_leaders : forall i : Fin n, i ≠ target ->
    (after i).leader = (before i).leader
  probes : forall i : Fin n, (after i).probe = (before i).probe

/-- Deleting a leader with a surviving strictly later leader cannot turn a
previously safe cut into a dangerous one.  Any probe which used the deleted
target as a shield is also strictly before the later witness. -/
theorem not_dangerous_after_delete_of_later {n k : Nat}
    (before after : Fin n -> State k) (target : Fin n)
    (hdelete : DeletesOnlyLeaderAt target before after)
    (hlater : exists witness : Fin n,
      target.val < witness.val /\ (after witness).leader = true)
    (hsafe : ¬ Dangerous before) :
    ¬ Dangerous after := by
  rw [not_dangerous_iff] at hsafe |- 
  intro p hp
  have hpBefore : (before p).probe = true := by
    rw [← hdelete.probes p]
    exact hp
  obtain ⟨oldWitness, hpold, holdLeader⟩ := hsafe p hpBefore
  by_cases hot : oldWitness = target
  · subst oldWitness
    obtain ⟨laterWitness, htl, hlLeader⟩ := hlater
    exact ⟨laterWitness, Nat.lt_trans hpold htl, hlLeader⟩
  · exact ⟨oldWitness, hpold, by
      rw [hdelete.other_leaders oldWitness hot]
      exact holdLeader⟩

/-- Removing exactly one leader strictly lowers `Phi` above its floor whenever
dangerousness cannot be created from a previously safe state. -/
theorem phi_lt_of_single_delete {n k : Nat}
    (before after : Fin n -> State k)
    (hdrop : leaderCount after + 1 = leaderCount before)
    (hpositive : 1 < Phi before)
    (hsafe : ¬ Dangerous before -> ¬ Dangerous after) :
    Phi after < Phi before := by
  by_cases hbefore : Dangerous before
  · have hafter := dangerBit_le_one after
    simp [Phi, dangerBit, hbefore] at hafter |- 
    omega
  · have hafter : ¬ Dangerous after := hsafe hbefore
    simp [Phi, dangerBit, hbefore, hafter] at hpositive |- 
    omega

/-- The local rank seam: an exact target deletion with a surviving later
leader is a strict rank decrease whenever the old rank exceeds one. -/
theorem phi_lt_after_delete_with_later {n k : Nat}
    (before after : Fin n -> State k) (target : Fin n)
    (hdelete : DeletesOnlyLeaderAt target before after)
    (hlater : exists witness : Fin n,
      target.val < witness.val /\ (after witness).leader = true)
    (hpositive : 1 < Phi before) :
    Phi after < Phi before := by
  have hdrop : leaderCount after + 1 = leaderCount before := by
    unfold leaderCount
    exact bitCount_single_drop
      (fun i => (before i).leader) (fun i => (after i).leader) target
      hdelete.before_leader hdelete.after_leader hdelete.other_leaders
  apply phi_lt_of_single_delete before after hdrop hpositive
  intro hsafe
  exact not_dangerous_after_delete_of_later before after target hdelete
    hlater hsafe

/-! ## Literal centered target hit -/

/-- A nonbarrier bullet hit on a responder leader deletes exactly that
leader, also for the centered protocol (whose only modification is in the
barrier branch). -/
theorem centered_nonbarrier_leader_hit_deletes_only {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (e : Fin n)
    (hbarrier : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hleader : (C (ring.rightNeighbor e)).leader = true)
    (hbullet : (C (ring.rightNeighbor e)).bullet = true) :
    DeletesOnlyLeaderAt (ring.rightNeighbor e) C
      ((CenteredRenewal.protocol k hk).step ring C e) := by
  let target := ring.rightNeighbor e
  have hre : target ≠ e := rightNeighbor_ne_self ring hn2 e
  have hpair : CenteredRenewal.transition hk (C e) (C target) =
      (C e, { C target with leader := false }) := by
    rw [CenteredRenewal.transition_of_nonbarrier hk _ _ hbarrier]
    exact nonBarrierStep_leader_hit (C e) (C target) hleader hbullet
  refine {
    before_leader := hleader
    after_leader := ?_
    other_leaders := ?_
    probes := ?_
  }
  · simp [PopulationProtocol.step, CenteredRenewal.protocol, target, hpair,
      hre]
  · intro i hit
    by_cases hie : i = e
    · subst i
      simp [PopulationProtocol.step, CenteredRenewal.protocol, target, hpair,
        hre]
    · simp [PopulationProtocol.step, CenteredRenewal.protocol, target, hpair,
        hie, hit]
  · intro i
    by_cases hie : i = e
    · subst i
      simp [PopulationProtocol.step, CenteredRenewal.protocol, target, hpair,
        hre]
    · by_cases hit : i = target
      · subst i
        simp [PopulationProtocol.step, CenteredRenewal.protocol, target, hpair,
          hre]
      · simp [PopulationProtocol.step, CenteredRenewal.protocol, target, hpair,
          hie, hit]

/-- A protected target hit in canonical cut coordinates is a strict `Phi`
drop.  This is the exact consumer of `NoDropLaterShield` in the bullet race. -/
theorem centered_target_hit_phi_lt {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (e : Fin n)
    (hbarrier : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hleader : (C (ring.rightNeighbor e)).leader = true)
    (hbullet : (C (ring.rightNeighbor e)).bullet = true)
    (hlater : exists witness : Fin n,
      (ring.rightNeighbor e).val < witness.val /\
        (C witness).leader = true)
    (hpositive : 1 < Phi C) :
    Phi ((CenteredRenewal.protocol k hk).step ring C e) < Phi C := by
  let D := (CenteredRenewal.protocol k hk).step ring C e
  have hdelete := centered_nonbarrier_leader_hit_deletes_only hk ring hn2 C e
    hbarrier hleader hbullet
  have hlaterD : exists witness : Fin n,
      (ring.rightNeighbor e).val < witness.val /\
        (D witness).leader = true := by
    obtain ⟨witness, horder, hwitness⟩ := hlater
    refine ⟨witness, horder, ?_⟩
    rw [hdelete.other_leaders witness]
    · exact hwitness
    · intro h
      subst witness
      omega
  exact phi_lt_after_delete_with_later C D (ring.rightNeighbor e) hdelete
    hlaterD hpositive

/-! ## Canonical fresh-rightmost invariant -/

/-- Cut-coordinate form of the clean suffix. -/
def CanonicalCleanAfter {n k : Nat} (C : Fin n -> State k)
    (witness : Fin n) : Prop :=
  forall x : Fin n, witness.val < x.val ->
    (C x).leader = false /\ (C x).bullet = false

/-- Cut-coordinate form used for the literal branch induction. -/
def CanonicalFreshRightmostAbove {n k : Nat} (C : Fin n -> State k)
    (target : Fin n) : Prop :=
  exists witness : Fin n,
    target.val < witness.val /\
      (C witness).leader = true /\
      (C witness).bullet = false /\
      CanonicalCleanAfter C witness

/-- The canonical fresh-rightmost invariant also certifies that the current
tail cannot already carry a bullet. -/
theorem CanonicalFreshRightmostAbove.tail_bullet_false {n k : Nat}
    {ring : DirectedRing n} {C : Fin n -> State k} {target : Fin n}
    (h : CanonicalFreshRightmostAbove C target) :
    (C (tailCoord ring)).bullet = false := by
  obtain ⟨witness, _htarget, _hleader, hbullet, hclean⟩ := h
  by_cases hwt : witness = tailCoord ring
  · simpa [hwt] using hbullet
  · apply (hclean (tailCoord ring) ?_).2
    change witness.val < n - 1
    have hwlt := witness.isLt
    have hwne : witness.val ≠ n - 1 := by
      intro hval
      apply hwt
      apply Fin.ext
      exact hval
    omega

/-- An ordinary centered step preserves the fresh rightmost suffix.  This is
the branch where the moving cut does not rotate. -/
theorem canonicalFreshRightmostAbove_nonbarrier_step {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n -> State k) (target e : Fin n)
    (he : e ≠ tailCoord ring)
    (hbarrier : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hfresh : CanonicalFreshRightmostAbove C target) :
    CanonicalFreshRightmostAbove
      ((CenteredRenewal.protocol k hk).step ring C e) target := by
  obtain ⟨witness, htarget, hleader, hbullet, hclean⟩ := hfresh
  let responder := ring.rightNeighbor e
  have hrespVal : responder.val = e.val + 1 := by
    exact rightNeighbor_val_of_ne_tail ring e he
  have hpair : CenteredRenewal.transition hk (C e) (C responder) =
      nonBarrierStep (C e) (C responder) := by
    exact CenteredRenewal.transition_of_nonbarrier hk _ _ hbarrier
  refine ⟨witness, htarget, ?_, ?_, ?_⟩
  · by_cases hwInit : witness = e
    · subst witness
      have hrespLater : e.val < responder.val := by omega
      have hrespClean := hclean responder hrespLater
      cases hprobe : (C e).probe <;>
        simpa [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
          responder, nonBarrierStep, hrespClean.1, hrespClean.2, hprobe]
          using hleader
    · by_cases hwResp : witness = responder
      · subst witness
        simp [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
          responder, hwInit, hleader, hbullet, nonBarrierStep]
      · simpa [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
          responder, hwInit, hwResp, Ne.symm hwResp] using hleader
  · by_cases hwInit : witness = e
    · subst witness
      have hrespLater : e.val < responder.val := by omega
      have hrespClean := hclean responder hrespLater
      cases hprobe : (C e).probe <;>
        simp [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
          responder, nonBarrierStep, hrespClean.1, hrespClean.2, hbullet,
          hprobe]
    · by_cases hwResp : witness = responder
      · subst witness
        simp [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
          responder, hwInit, hleader, hbullet, nonBarrierStep]
      · simpa [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
          responder, hwInit, hwResp, Ne.symm hwResp] using hbullet
  · intro x hwx
    have hxClean := hclean x hwx
    by_cases hxInit : x = e
    · subst x
      have hrespLater : e.val < responder.val := by omega
      have hrespClean := hclean responder (Nat.lt_trans hwx hrespLater)
      cases hprobe : (C e).probe <;>
        simp [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
          responder, nonBarrierStep, hrespClean.1, hrespClean.2,
          hxClean.1, hxClean.2, hprobe]
    · by_cases hxResp : x = responder
      · subst x
        cases hprobe : (C e).probe <;>
          simp [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
            responder, hxInit, nonBarrierStep, hxClean.1, hxClean.2,
            hprobe]
      · simpa [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
          responder, hxInit, hxResp] using hxClean

/-- A phase-zero hit on the canonical barrier preserves the fresh suffix.  If
the old tail carries a probe, `probeHitsBarrier` itself supplies a new maximal
bullet-free witness. -/
theorem canonicalFreshRightmostAbove_barrier_phase_zero_step {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (target : Fin n)
    (hbarrier : IsBarrier hk (C (tailCoord ring))
      (C (ring.rightNeighbor (tailCoord ring))))
    (hphase : (C (tailCoord ring)).phase = false)
    (hfresh : CanonicalFreshRightmostAbove C target) :
    CanonicalFreshRightmostAbove
      ((CenteredRenewal.protocol k hk).step ring C (tailCoord ring)) target := by
  let tail := tailCoord ring
  let head := ring.rightNeighbor tail
  let D := (CenteredRenewal.protocol k hk).step ring C tail
  change CanonicalFreshRightmostAbove D target
  have hne : head ≠ tail := rightNeighbor_ne_self ring hn2 tail
  have hbarrierLocal : IsBarrier hk (C tail) (C head) := by
    simpa [tail, head] using hbarrier
  have hphaseLocal : (C tail).phase = false := by
    simpa [tail] using hphase
  cases hprobe : (C tail).probe with
  | true =>
      have htailBullet : (C tail).bullet = false := by
        simpa [tail] using hfresh.tail_bullet_false (ring := ring)
      obtain ⟨witness, htarget, _hleader, _hbullet, _hclean⟩ := hfresh
      have htargetTail : target.val < tail.val := by
        have hwlt := witness.isLt
        change target.val < n - 1
        change target.val < witness.val at htarget
        omega
      refine ⟨tail, htargetTail, ?_, ?_, ?_⟩
      · simp [D, PopulationProtocol.step, CenteredRenewal.protocol,
          CenteredRenewal.transition, CenteredRenewal.barrierStep,
          hbarrierLocal, hphaseLocal, head, hne, probeHitsBarrier, hprobe]
      · simpa [D, PopulationProtocol.step, CenteredRenewal.protocol,
          CenteredRenewal.transition, CenteredRenewal.barrierStep,
          hbarrierLocal, hphaseLocal, head, hne, probeHitsBarrier, hprobe]
          using htailBullet
      · intro x hx
        change n - 1 < x.val at hx
        have hxlt := x.isLt
        omega
  | false =>
      obtain ⟨witness, htarget, hleader, hbullet, hclean⟩ := hfresh
      have hleaders : forall i : Fin n, (D i).leader = (C i).leader := by
        intro i
        by_cases hit : i = tail
        · subst i
          simp [D, PopulationProtocol.step, CenteredRenewal.protocol,
            CenteredRenewal.transition, CenteredRenewal.barrierStep,
            hbarrierLocal, hphaseLocal, head, hne, probeHitsBarrier, hprobe]
        · by_cases hih : i = head
          · subst i
            cases hheadLeader : (C head).leader <;>
              simp [D, PopulationProtocol.step, CenteredRenewal.protocol,
                CenteredRenewal.transition, CenteredRenewal.barrierStep,
                hbarrierLocal, hphaseLocal, head, hne, hheadLeader]
          · have hih' : i ≠ ring.rightNeighbor tail := by
              simpa [head] using hih
            simp [D, PopulationProtocol.step, CenteredRenewal.protocol,
              hit, hih']
      have hbullets : forall i : Fin n, (D i).bullet = (C i).bullet := by
        intro i
        by_cases hit : i = tail
        · subst i
          simp [D, PopulationProtocol.step, CenteredRenewal.protocol,
            CenteredRenewal.transition, CenteredRenewal.barrierStep,
            hbarrierLocal, hphaseLocal, head, hne, probeHitsBarrier, hprobe]
        · by_cases hih : i = head
          · subst i
            cases hheadLeader : (C head).leader <;>
              simp [D, PopulationProtocol.step, CenteredRenewal.protocol,
                CenteredRenewal.transition, CenteredRenewal.barrierStep,
                hbarrierLocal, hphaseLocal, head, hne, hheadLeader]
          · have hih' : i ≠ ring.rightNeighbor tail := by
              simpa [head] using hih
            simp [D, PopulationProtocol.step, CenteredRenewal.protocol,
              hit, hih']
      refine ⟨witness, htarget, ?_, ?_, ?_⟩
      · rw [hleaders witness]
        exact hleader
      · rw [hbullets witness]
        exact hbullet
      · intro x hx
        have hxClean := hclean x hx
        rw [hleaders x, hbullets x]
        exact hxClean

/-- Exact pointwise normal form of a phase-one hit on the canonical barrier.
Keeping this normal form separate prevents the moving-cut proof below from
depending on simplifier choices inside `PopulationProtocol.step`. -/
theorem centered_barrier_phase_one_step_eq {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k)
    (hbarrier : IsBarrier hk (C (tailCoord ring))
      (C (ring.rightNeighbor (tailCoord ring))))
    (hphase : (C (tailCoord ring)).phase = true) :
    (CenteredRenewal.protocol k hk).step ring C (tailCoord ring) =
      fun i =>
        if i = tailCoord ring then
          probeHitsBarrier (C (tailCoord ring))
        else if i = ring.rightNeighbor (tailCoord ring) then
          { C (ring.rightNeighbor (tailCoord ring)) with
            label := succLabel hk (C (tailCoord ring)).label
            phase := false
            bullet := false
            probe := false }
        else C i := by
  have hne : ring.rightNeighbor (tailCoord ring) ≠ tailCoord ring :=
    rightNeighbor_ne_self ring hn2 (tailCoord ring)
  have hpair : CenteredRenewal.transition hk
      (C (tailCoord ring)) (C (ring.rightNeighbor (tailCoord ring))) =
      (probeHitsBarrier (C (tailCoord ring)),
        { C (ring.rightNeighbor (tailCoord ring)) with
          label := succLabel hk (C (tailCoord ring)).label
          phase := false
          bullet := false
          probe := false }) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _]
    · exact CenteredRenewal.barrierStep_phase_one hk _ _ (by
        exact hphase)
    · exact hbarrier
  funext i
  simp only [PopulationProtocol.step, CenteredRenewal.protocol]
  rw [hpair]

/-- A phase-one barrier hit rotates the cut and preserves the fresh-rightmost
invariant until the barrier catches the target.  The proof explicitly handles
the two possible replacement witnesses: a sanitized leader at the new tail,
or a probe-created leader at the old tail. -/
theorem canonicalFreshRightmostAbove_barrier_phase_one_step {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (target : Fin n)
    (hbarrier : IsBarrier hk (C (tailCoord ring))
      (C (ring.rightNeighbor (tailCoord ring))))
    (hphase : (C (tailCoord ring)).phase = true)
    (hfresh : CanonicalFreshRightmostAbove C target)
    (hactive : ring.leftNeighbor target ≠ tailCoord ring) :
    CanonicalFreshRightmostAbove
      (rotateCut ring
        ((CenteredRenewal.protocol k hk).step ring C (tailCoord ring)))
      (ring.leftNeighbor target) := by
  let tail := tailCoord ring
  let head := ring.rightNeighbor tail
  let oldTailNew := ring.leftNeighbor tail
  let D := (CenteredRenewal.protocol k hk).step ring C tail
  let Y := rotateCut ring D
  change CanonicalFreshRightmostAbove Y (ring.leftNeighbor target)
  have hne : head ≠ tail := rightNeighbor_ne_self ring hn2 tail
  have hDFormula : D = fun i =>
      if i = tail then
        probeHitsBarrier (C tail)
      else if i = head then
        { C head with
          label := succLabel hk (C tail).label
          phase := false
          bullet := false
          probe := false }
      else C i := by
    simpa [D, tail, head] using
      centered_barrier_phase_one_step_eq hk ring hn2 C hbarrier hphase
  have hDtail : D tail = probeHitsBarrier (C tail) := by
    rw [hDFormula]
    simp
    rfl
  have hDhead : D head =
      { C head with
        label := succLabel hk (C tail).label
        phase := false
        bullet := false
        probe := false } := by
    rw [hDFormula]
    simp [hne]
    rfl
  have hDother (x : Fin n) (hxt : x ≠ tail) (hxh : x ≠ head) :
      D x = C x := by
    rw [hDFormula]
    simp [hxt, hxh]
    rfl
  have hYshift (x : Fin n) : Y (ring.leftNeighbor x) = D x := by
    simp [Y, rotateCut, rightNeighbor_leftNeighbor_clean]
    rfl
  have hYtail : Y tail = D head := by
    simp [Y, rotateCut, head]
    rfl
  have htargetPos : 0 < target.val := by
    by_cases hzero : target.val = 0
    · exfalso
      apply hactive
      apply Fin.ext
      simp [DirectedRing.leftNeighbor, hzero, tailCoord]
    · omega
  have htailBullet : (C tail).bullet = false := by
    simpa [tail] using
      (CanonicalFreshRightmostAbove.tail_bullet_false (ring := ring) hfresh)
  obtain ⟨witness, htargetWitness, hleader, hbullet, hclean⟩ := hfresh
  have hwitnessPos : 0 < witness.val := by omega
  have htargetLeft := leftNeighbor_val_of_pos ring target htargetPos
  have hwitnessLeft := leftNeighbor_val_of_pos ring witness hwitnessPos
  have htargetTail : target.val < tail.val := by
    have hwlt := witness.isLt
    change target.val < n - 1
    omega
  cases hheadLeader : (C head).leader with
  | true =>
      refine ⟨tail, ?_, ?_, ?_, ?_⟩
      · change (ring.leftNeighbor target).val < n - 1
        rw [htargetLeft]
        omega
      · rw [hYtail, hDhead]
        simpa using hheadLeader
      · rw [hYtail, hDhead]
      · intro x hx
        change n - 1 < x.val at hx
        have hxlt := x.isLt
        omega
  | false =>
      cases htailProbe : (C tail).probe with
      | true =>
          have htailPos : 0 < tail.val := by
            change 0 < n - 1
            omega
          have holdTailVal := leftNeighbor_val_of_pos ring tail htailPos
          refine ⟨oldTailNew, ?_, ?_, ?_, ?_⟩
          · change (ring.leftNeighbor target).val <
                (ring.leftNeighbor tail).val
            rw [htargetLeft, holdTailVal]
            change target.val - 1 < (n - 1) - 1
            omega
          · rw [show oldTailNew = ring.leftNeighbor tail by rfl,
              hYshift, hDtail]
            simp [probeHitsBarrier, htailProbe]
          · rw [show oldTailNew = ring.leftNeighbor tail by rfl,
              hYshift, hDtail]
            simpa [probeHitsBarrier, htailProbe] using htailBullet
          · intro x hx
            have hxlt := x.isLt
            have hOldTailVal : oldTailNew.val = n - 2 := by
              change (ring.leftNeighbor tail).val = n - 2
              rw [holdTailVal]
              change (n - 1) - 1 = n - 2
              omega
            have hxtail : x = tail := by
              apply Fin.ext
              change x.val = n - 1
              omega
            subst x
            rw [hYtail, hDhead]
            exact ⟨by simpa using hheadLeader, rfl⟩
      | false =>
          have hrawLeaders : forall x : Fin n, x ≠ head ->
              (D x).leader = (C x).leader := by
            intro x hxhead
            by_cases hxtail : x = tail
            · subst x
              rw [hDtail]
              simp [probeHitsBarrier, htailProbe]
            · rw [hDother x hxtail hxhead]
          have hrawBullets : forall x : Fin n, x ≠ head ->
              (D x).bullet = (C x).bullet := by
            intro x hxhead
            by_cases hxtail : x = tail
            · subst x
              rw [hDtail]
              simp [probeHitsBarrier, htailProbe]
            · rw [hDother x hxtail hxhead]
          have hwitnessNeHead : witness ≠ head := by
            intro h
            subst witness
            have hheadVal : head.val = 0 := by
              simp [head, tail, rightNeighbor_tailCoord]
            omega
          refine ⟨ring.leftNeighbor witness, ?_, ?_, ?_, ?_⟩
          · rw [htargetLeft, hwitnessLeft]
            omega
          · rw [hYshift, hrawLeaders witness hwitnessNeHead]
            exact hleader
          · rw [hYshift, hrawBullets witness hwitnessNeHead]
            exact hbullet
          · intro y hwy
            by_cases hytail : y = tail
            · subst y
              rw [hYtail, hDhead]
              exact ⟨by simpa using hheadLeader, rfl⟩
            · let oldY := ring.rightNeighbor y
              have hyVal : oldY.val = y.val + 1 := by
                exact rightNeighbor_val_of_ne_tail ring y hytail
              have hOldLater : witness.val < oldY.val := by
                rw [hwitnessLeft] at hwy
                omega
              have hOldClean := hclean oldY hOldLater
              have hOldNeHead : oldY ≠ head := by
                intro h
                have hval := congrArg Fin.val h
                have hheadVal : head.val = 0 := by
                  simp [head, tail, rightNeighbor_tailCoord]
                omega
              change (D (ring.rightNeighbor y)).leader = false /\
                (D (ring.rightNeighbor y)).bullet = false
              change (D oldY).leader = false /\ (D oldY).bullet = false
              rw [hrawLeaders oldY hOldNeHead,
                hrawBullets oldY hOldNeHead]
              exact hOldClean

/-! ## One-step moving-cut interface -/

/-- The physical target's coordinate in the successor cut.  It shifts left
exactly on a genuine centered barrier advance. -/
def nextTarget {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n -> State k) (e target : Fin n) : Fin n :=
  if CenteredRenewal.AdvanceReady hk ring C e then
    ring.leftNeighbor target
  else target

/-- Unified one-step preservation surface.  The only side condition excludes
the terminal step which crosses the tracked physical target; that step is
reported separately by the run-level consumer. -/
theorem canonicalFreshRightmostAbove_cutSuccessor_step {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (target e : Fin n)
    (hbar : CanonicalOneBarrier hk ring C)
    (hfresh : CanonicalFreshRightmostAbove C target)
    (hbefore : CenteredRenewal.AdvanceReady hk ring C e ->
      ring.leftNeighbor target ≠ tailCoord ring) :
    CanonicalFreshRightmostAbove
      (Rank.cutSuccessor hk ring C e)
      (nextTarget hk ring C e target) := by
  by_cases hready : CenteredRenewal.AdvanceReady hk ring C e
  · have he : e = tailCoord ring := (hbar e).1 hready.1
    subst e
    have hactive := hbefore hready
    simpa [Rank.cutSuccessor, nextTarget, hready] using
      canonicalFreshRightmostAbove_barrier_phase_one_step
        hk ring hn2 C target hready.1 hready.2 hfresh hactive
  · by_cases he : e = tailCoord ring
    · subst e
      have hbarrier : IsBarrier hk (C (tailCoord ring))
          (C (ring.rightNeighbor (tailCoord ring))) :=
        (hbar (tailCoord ring)).2 rfl
      have hphase : (C (tailCoord ring)).phase = false := by
        cases hp : (C (tailCoord ring)).phase
        · rfl
        · exact False.elim (hready ⟨hbarrier, hp⟩)
      simpa [Rank.cutSuccessor, nextTarget, hready] using
        canonicalFreshRightmostAbove_barrier_phase_zero_step
          hk ring hn2 C target hbarrier hphase hfresh
    · have hnonbarrier :
          ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro hb
        exact he ((hbar e).1 hb)
      simpa [Rank.cutSuccessor, nextTarget, hready] using
        canonicalFreshRightmostAbove_nonbarrier_step
          hk ring C target e he hnonbarrier hfresh

/-- The centered successor cut again has its unique barrier at the canonical
wrap edge.  This is the frame field used by trace induction. -/
theorem canonicalOneBarrier_cutSuccessor {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (e : Fin n) (hndvd : ¬ k ∣ n)
    (hbar : CanonicalOneBarrier hk ring C) :
    CanonicalOneBarrier hk ring (Rank.cutSuccessor hk ring C e) := by
  let D : Fin n -> State k := fun j =>
    ((CenteredRenewal.protocol k hk).step ring C e) j
  have honeC : OneBarrierAt hk ring C (tailCoord ring) :=
    canonicalOneBarrier_oneBarrierAt_tail hk ring C hbar
  have honeD := Sanitation.oneBarrierAt_step hk ring hn2 C
    (tailCoord ring) e hndvd honeC
  by_cases hready : CenteredRenewal.AdvanceReady hk ring C e
  · have honeReady : OneBarrierAt hk ring D
        (ring.rightNeighbor (tailCoord ring)) := by
      simpa [D, hready] using honeD
    have hcanon := canonicalOneBarrier_cutView hk ring D
      (ring.rightNeighbor (tailCoord ring)) honeReady
    have hview : cutView ring (ring.rightNeighbor (tailCoord ring)) D =
        rotateCut ring D := by
      rw [cutView_nextBarrier, cutView_tailCoord_identity]
    unfold Rank.cutSuccessor
    simp only [hready, if_true]
    rw [← hview]
    exact hcanon
  · have honeFixed : OneBarrierAt hk ring D (tailCoord ring) := by
      simpa [D, hready] using honeD
    have hcanon := canonicalOneBarrier_cutView hk ring D
      (tailCoord ring) honeFixed
    unfold Rank.cutSuccessor
    simp only [hready, if_false]
    simpa using hcanon

/-- On an ordinary edge, losing a leader at `target` can only be the literal
responder-leader/bullet hit branch. -/
theorem centered_nonbarrier_target_death {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (target e : Fin n)
    (hnonbarrier : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (htarget : (C target).leader = true)
    (hdead : (((CenteredRenewal.protocol k hk).step ring C e) target).leader =
      false) :
    target = ring.rightNeighbor e ∧ (C target).bullet = true := by
  let responder := ring.rightNeighbor e
  have hre : responder ≠ e := rightNeighbor_ne_self ring hn2 e
  have hpair : CenteredRenewal.transition hk (C e) (C responder) =
      nonBarrierStep (C e) (C responder) :=
    CenteredRenewal.transition_of_nonbarrier hk _ _ hnonbarrier
  have hstep : (CenteredRenewal.protocol k hk).step ring C e = fun i =>
      if i = e then (nonBarrierStep (C e) (C responder)).1
      else if i = responder then (nonBarrierStep (C e) (C responder)).2
      else C i := by
    funext i
    simp only [PopulationProtocol.step, CenteredRenewal.protocol]
    rw [hpair]
  rw [hstep] at hdead
  by_cases hte : target = e
  · subst target
    simp only [if_pos] at hdead
    have hinit : (nonBarrierStep (C e) (C responder)).1.leader =
        (C e).leader := by
      cases hp : (C e).probe <;>
        cases hl : (C responder).leader <;>
        cases hb : (C responder).bullet <;>
        simp [nonBarrierStep, hp, hl, hb]
    rw [hinit, htarget] at hdead
    contradiction
  · by_cases htr : target = responder
    · subst target
      simp only [hte, if_false, if_pos] at hdead
      cases hb : (C responder).bullet
      · simp [nonBarrierStep, htarget, hb] at hdead
      · exact ⟨rfl, rfl⟩
    · simp [hte, htr, htarget] at hdead

/-- A centered barrier interaction never deletes an existing leader. -/
theorem centered_barrier_step_preserves_leader {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (target e : Fin n)
    (hbarrier : IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (htarget : (C target).leader = true) :
    (((CenteredRenewal.protocol k hk).step ring C e) target).leader = true := by
  let responder := ring.rightNeighbor e
  have hre : responder ≠ e := rightNeighbor_ne_self ring hn2 e
  have hpair : CenteredRenewal.transition hk (C e) (C responder) =
      CenteredRenewal.barrierStep hk (C e) (C responder) :=
    CenteredRenewal.transition_of_barrier hk _ _ hbarrier
  have hresp :
      (CenteredRenewal.barrierStep hk (C e) (C responder)).2.leader =
        (C responder).leader := by
    cases hp : (C e).phase <;>
      cases hq : (C e).probe <;>
      cases hl : (C responder).leader <;>
      simp [CenteredRenewal.barrierStep, probeHitsBarrier, hp, hq, hl]
  by_cases hte : target = e
  · subst target
    have hinit :
        (CenteredRenewal.barrierStep hk (C e) (C responder)).1.leader =
          true := by
      cases hp : (C e).phase <;>
        cases hq : (C e).probe <;>
        simp [CenteredRenewal.barrierStep, probeHitsBarrier, hp, hq,
          htarget]
    simpa [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
      responder, hre] using hinit
  · by_cases htr : target = responder
    · subst target
      simpa [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
        responder, hre, hte] using (hresp.trans htarget)
    · simpa [PopulationProtocol.step, CenteredRenewal.protocol, hte,
        show target ≠ ring.rightNeighbor e by simpa [responder] using htr]
        using htarget

/-- Before the crossing terminal, a live protected target cannot disappear on
a `Phi` plateau. -/
theorem canonical_target_survives_plateau_step {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n -> State k) (target e : Fin n)
    (hbar : CanonicalOneBarrier hk ring C)
    (hfresh : CanonicalFreshRightmostAbove C target)
    (htarget : (C target).leader = true)
    (hpositive : 1 < Phi C)
    (hplateau : Phi (Rank.cutSuccessor hk ring C e) = Phi C) :
    ((Rank.cutSuccessor hk ring C e)
      (nextTarget hk ring C e target)).leader = true := by
  have hn2 : 1 < n := by omega
  by_cases hready : CenteredRenewal.AdvanceReady hk ring C e
  · have hpersist := centered_barrier_step_preserves_leader hk ring hn2
      C target e hready.1 htarget
    have hcut : Rank.cutSuccessor hk ring C e =
        rotateCut ring ((CenteredRenewal.protocol k hk).step ring C e) := by
      simp [Rank.cutSuccessor, hready]
    have hnext : nextTarget hk ring C e target =
        ring.leftNeighbor target := by simp [nextTarget, hready]
    rw [hcut, hnext]
    simpa [rotateCut, rightNeighbor_leftNeighbor_clean] using hpersist
  · by_cases he : e = tailCoord ring
    · have hbarrier : IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
        (hbar e).2 he
      have hpersist := centered_barrier_step_preserves_leader hk ring hn2
        C target e hbarrier htarget
      have hcut : Rank.cutSuccessor hk ring C e =
          (CenteredRenewal.protocol k hk).step ring C e := by
        simp [Rank.cutSuccessor, hready]
        funext j
        rfl
      have hnext : nextTarget hk ring C e target = target := by
        simp [nextTarget, hready]
      rw [hcut, hnext]
      exact hpersist
    · have hnonbarrier :
          ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
        intro hb
        exact he ((hbar e).1 hb)
      have hcut : Rank.cutSuccessor hk ring C e =
          (CenteredRenewal.protocol k hk).step ring C e := by
        simp [Rank.cutSuccessor, hready]
        funext j
        rfl
      have hnext : nextTarget hk ring C e target = target := by
        simp [nextTarget, hready]
      cases hval : (((CenteredRenewal.protocol k hk).step ring C e)
        target).leader
      · obtain ⟨htargetResp, hbullet⟩ :=
          centered_nonbarrier_target_death hk ring hn2 C target e
            hnonbarrier htarget hval
        obtain ⟨witness, hlater, hwleader, _⟩ := hfresh
        have hstrict := centered_target_hit_phi_lt hk ring hn2 C e
          hnonbarrier (by simpa [← htargetResp] using htarget)
          (by simpa [← htargetResp] using hbullet)
          ⟨witness, by simpa [← htargetResp] using hlater, hwleader⟩
          hpositive
        rw [hcut] at hplateau
        omega
      · rw [hcut, hnext]
        exact hval

/-! ## Good-renewal and run-level interfaces -/

/-- Minimal adapter expected from renewal search.  When the fresh endpoint is
the canonical tail, choosing it as witness makes the clean suffix vacuous;
the predecessor becomes the tracked target. -/
theorem goodFreshRenewal_to_CanonicalFreshRightmostAbove {n k : Nat}
    (ring : DirectedRing n) (C : Fin n -> State k) (predecessor : Fin n)
    (hne : predecessor ≠ tailCoord ring)
    (htailLeader : (C (tailCoord ring)).leader = true)
    (htailBullet : (C (tailCoord ring)).bullet = false) :
    CanonicalFreshRightmostAbove C predecessor := by
  refine ⟨tailCoord ring, ?_, htailLeader, htailBullet, ?_⟩
  · change predecessor.val < n - 1
    have hlt := predecessor.isLt
    have hval : predecessor.val ≠ n - 1 := by
      intro hv
      apply hne
      apply Fin.ext
      exact hv
    omega
  · intro x hx
    change n - 1 < x.val at hx
    have hlt := x.isLt
    omega

/-- The exact terminal omitted from active shield induction. -/
def BarrierCrossedTarget {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k)
    (e target : Fin n) : Prop :=
  CenteredRenewal.AdvanceReady hk ring C e ∧
    ring.leftNeighbor target = tailCoord ring

/-- Every literal step either crosses the tracked target or preserves the
fresh-rightmost shield in the successor cut. -/
theorem canonicalFreshRightmostAbove_step_or_crossed {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (target e : Fin n)
    (hbar : CanonicalOneBarrier hk ring C)
    (hfresh : CanonicalFreshRightmostAbove C target) :
    BarrierCrossedTarget hk ring C e target ∨
      CanonicalFreshRightmostAbove
        (Rank.cutSuccessor hk ring C e)
        (nextTarget hk ring C e target) := by
  by_cases hcross : BarrierCrossedTarget hk ring C e target
  · exact Or.inl hcross
  · right
    apply canonicalFreshRightmostAbove_cutSuccessor_step hk ring hn2 C
      target e hbar hfresh
    intro hready heq
    exact hcross ⟨hready, heq⟩

/-- Proof-side state of an active (not-yet-crossed) target race.  No protocol
field is added: `target` and the shield are ghost data only. -/
structure ActiveRaceState {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) where
  config : Fin n -> State k
  target : Fin n
  barrier : CanonicalOneBarrier hk ring config
  fresh : CanonicalFreshRightmostAbove config target
  targetLeader : (config target).leader = true
  rankPositive : 1 < Phi config

/-- One plateau step before the crossing terminal, packaged so arbitrary
interleavings can be folded without re-proving frame closure. -/
def ActiveRaceState.next {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : ActiveRaceState hk ring) (e : Fin n)
    (hplateau : Phi (Rank.cutSuccessor hk ring s.config e) = Phi s.config)
    (hnotcross : ¬ BarrierCrossedTarget hk ring s.config e s.target) :
    ActiveRaceState hk ring where
  config := Rank.cutSuccessor hk ring s.config e
  target := nextTarget hk ring s.config e s.target
  barrier := canonicalOneBarrier_cutSuccessor hk ring (by omega) s.config e
    hndvd s.barrier
  fresh := canonicalFreshRightmostAbove_cutSuccessor_step hk ring (by omega)
    s.config s.target e s.barrier s.fresh (by
      intro hready heq
      exact hnotcross ⟨hready, heq⟩)
  targetLeader := canonical_target_survives_plateau_step hk ring hn3
    s.config s.target e s.barrier s.fresh s.targetLeader s.rankPositive
    hplateau
  rankPositive := by rw [hplateau]; exact s.rankPositive

/-- Reflexive-transitive active race traces.  A constructor is unavailable on
the target-crossing step, so the false unbounded shield theorem cannot be
stated through this interface. -/
inductive ActiveRaceReach {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (start : ActiveRaceState hk ring) : ActiveRaceState hk ring -> Prop
  | refl : ActiveRaceReach hk ring hn3 hndvd start start
  | step {current : ActiveRaceState hk ring}
      (reach : ActiveRaceReach hk ring hn3 hndvd start current)
      (e : Fin n)
      (plateau : Phi (Rank.cutSuccessor hk ring current.config e) =
        Phi current.config)
      (notCrossed : ¬ BarrierCrossedTarget hk ring current.config e
        current.target) :
      ActiveRaceReach hk ring hn3 hndvd start
        (current.next hn3 hndvd e plateau notCrossed)

/-- Run-level target survival, now valid because crossing is an explicit
terminal rather than an unbounded continuation. -/
theorem ActiveRaceReach.target_survives {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {hn3 : 3 ≤ n} {hndvd : ¬ k ∣ n}
    {start current : ActiveRaceState hk ring}
    (_reach : ActiveRaceReach hk ring hn3 hndvd start current) :
    (current.config current.target).leader = true :=
  current.targetLeader

/-- The shield itself is retained at every active trace endpoint. -/
theorem ActiveRaceReach.freshRightmost {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {hn3 : 3 ≤ n} {hndvd : ¬ k ∣ n}
    {start current : ActiveRaceState hk ring}
    (_reach : ActiveRaceReach hk ring hn3 hndvd start current) :
    CanonicalFreshRightmostAbove current.config current.target :=
  current.fresh

/-- The final tracked progress edge consumes the active shield directly: a
bullet-bearing target responder is a strict rank drop. -/
theorem ActiveRaceState.target_hit_phi_lt {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n)
    (s : ActiveRaceState hk ring) (e : Fin n)
    (hresponder : ring.rightNeighbor e = s.target)
    (hnonbarrier : ¬ IsBarrier hk (s.config e)
      (s.config (ring.rightNeighbor e)))
    (hbullet : (s.config s.target).bullet = true) :
    Phi (Rank.cutSuccessor hk ring s.config e) < Phi s.config := by
  have hn2 : 1 < n := by omega
  obtain ⟨witness, hlater, hwleader, _⟩ := s.fresh
  have hstrict := centered_target_hit_phi_lt hk ring hn2 s.config e
    hnonbarrier (by simpa [hresponder] using s.targetLeader)
    (by simpa [hresponder] using hbullet)
    ⟨witness, by simpa [hresponder] using hlater, hwleader⟩
    s.rankPositive
  have hnotready : ¬ CenteredRenewal.AdvanceReady hk ring s.config e := by
    intro hready
    exact hnonbarrier hready.1
  unfold Rank.cutSuccessor
  simp only [hnotready, if_false]
  exact hstrict

end NoDropLaterShield
end CenteredRenewal
end AAFJPK
