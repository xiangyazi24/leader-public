import Leader.AAFJ.Centered.RankBlockTrial
import Leader.AAFJ.Centered.PlateauCases
import Leader.Core.PredictableCounterRaceFiniteTree

/-!
# Physical tracked-bullet race for the centered `Phi > 1` block

This module starts from the payload-retaining firing endpoint.  Coordinates
are canonical cut coordinates: after every genuine barrier advance, ghost
coordinates are transported one step left by `rotateCut`; the underlying
physical target and bullet holder do not change merely because the cut moved.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace RankBlockRace

open BarrierAlgebra
open SingleBarrierSanitation
open OneBarrierCleanup
open RenewalSearch
open NoDropLaterShield
open RankBlockTrial
open FiniteUniformStoppingTree
open PayloadFiniteStoppingTree

set_option autoImplicit false

/-! ## Active physical race invariant -/

/-- Literal race state.  `target` and `holder` are coordinates in the current
cut.  A genuine barrier advance applies `leftNeighbor` to both, preserving
their physical identities under `rotateCut`.

`firstHits` counts tracked-bullet moves/hits, while `secondHits` counts raw
barrier selections.  The two clock equations prevent the barrier from
crossing the target before the second counter reaches `gap`. -/
structure BulletRaceState {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (r : Nat) : Type where
  race : NoDropLaterShield.ActiveRaceState hk ring
  holder : Fin n
  holderBullet : (race.config holder).bullet = true
  gap : Nat
  gap_pos : 0 < gap
  gap_le_half : gap ≤ n / 2
  firstHits : Nat
  secondHits : Nat
  advances : Nat
  first_lt : firstHits < gap
  second_lt : secondHits < gap
  target_progress : race.target.val + advances + gap = n - 1
  holder_progress : race.target.val + (gap - 1) =
    holder.val + firstHits
  second_clock : secondHits = 2 * advances +
    CenteredRenewal.phaseNat (race.config (tailCoord ring)).phase
  corridor : forall i : Fin n, race.target.val < i.val ->
    i.val ≤ holder.val -> (race.config i).leader = false
  rank_eq : Phi race.config = r

def BulletRaceState.firstEdge {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (s : BulletRaceState hk ring r) : Fin n :=
  ring.leftNeighbor s.holder

def BulletRaceState.secondEdge {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (_s : BulletRaceState hk ring r) : Fin n :=
  tailCoord ring

theorem fireEdge_val {n : Nat} (ring : DirectedRing n) (hn3 : 3 ≤ n) :
    (fireEdge ring).val = n - 2 := by
  have htail : (tailCoord ring).val = n - 1 := rfl
  have hpos : 0 < (tailCoord ring).val := by rw [htail]; omega
  change (ring.leftNeighbor (tailCoord ring)).val = n - 2
  rw [leftNeighbor_val_of_pos ring (tailCoord ring) hpos, htail]
  omega

/-- The exact post-fire payload starts the physical race with both counters
and the barrier-advance count at zero. -/
def FiredRaceState.toBulletRaceState {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n)
    {X : Fin n -> State k} (F : FiredRaceState hk ring X)
    (hrank : Phi X = r) : BulletRaceState hk ring r := by
  rcases F with
    ⟨S, rfl, hholder, _htailLeader, _htailBullet, _htailProbe,
      htailPhase, G⟩
  refine {
    race := S
    holder := fireEdge ring
    holderBullet := hholder
    gap := G.gap
    gap_pos := G.gap_pos
    gap_le_half := G.gap_le_half
    firstHits := 0
    secondHits := 0
    advances := 0
    first_lt := G.gap_pos
    second_lt := G.gap_pos
    target_progress := G.target_gap
    holder_progress := ?_
    second_clock := ?_
    corridor := ?_
    rank_eq := hrank }
  · have hfire := fireEdge_val ring hn3
    have hgap := G.target_gap
    have hgapOne : 1 ≤ G.gap := G.gap_pos
    have hsub : S.target.val + (G.gap - 1) =
        (S.target.val + G.gap) - 1 := by omega
    change S.target.val + (G.gap - 1) = (fireEdge ring).val + 0
    rw [hsub, hgap, hfire]
    omega
  · simp [htailPhase, CenteredRenewal.phaseNat]
  · intro i hlater hbefore
    apply G.followers i hlater
    have hfire := fireEdge_val ring hn3
    change i.val < n - 1
    omega

theorem BulletRaceState.two_gap_le {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (s : BulletRaceState hk ring r) :
    2 * s.gap ≤ n := by
  have h := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).1 s.gap_le_half
  simpa [Nat.mul_comm] using h

/-- A live second counter leaves the transported physical target strictly
inside the cut, so the next advance has not crossed it. -/
theorem BulletRaceState.target_pos {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n)
    (s : BulletRaceState hk ring r) : 0 < s.race.target.val := by
  have h2gap := s.two_gap_le
  have hgapPos := s.gap_pos
  have hsecondLt := s.second_lt
  have hclock := s.second_clock
  have hprogress := s.target_progress
  have hphase : CenteredRenewal.phaseNat
      (s.race.config (tailCoord ring)).phase ≤ 1 := by
    cases h : (s.race.config (tailCoord ring)).phase <;>
      simp [CenteredRenewal.phaseNat, h]
  omega

theorem BulletRaceState.target_le_holder {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (s : BulletRaceState hk ring r) :
    s.race.target.val ≤ s.holder.val := by
  have hgapPos := s.gap_pos
  have hfirstLt := s.first_lt
  have hholder := s.holder_progress
  omega

theorem BulletRaceState.holder_lt_tail {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (s : BulletRaceState hk ring r) :
    s.holder.val < (tailCoord ring).val := by
  have htarget := s.target_progress
  have hholder := s.holder_progress
  have hgapPos := s.gap_pos
  change s.holder.val < n - 1
  omega

theorem BulletRaceState.firstEdge_ne_secondEdge {n k r : Nat}
    {hk : 0 < k} {ring : DirectedRing n} (hn3 : 3 ≤ n)
    (s : BulletRaceState hk ring r) :
    s.firstEdge ≠ s.secondEdge := by
  have hholderPos : 0 < s.holder.val :=
    Nat.lt_of_lt_of_le (s.target_pos hn3) s.target_le_holder
  have hleft := leftNeighbor_val_of_pos ring s.holder hholderPos
  intro h
  have hv := congrArg Fin.val h
  change (ring.leftNeighbor s.holder).val = n - 1 at hv
  rw [hleft] at hv
  have hholderLt := s.holder_lt_tail
  change s.holder.val < n - 1 at hholderLt
  omega

theorem BulletRaceState.first_done_holder_eq_target {n k r : Nat}
    {hk : 0 < k} {ring : DirectedRing n}
    (s : BulletRaceState hk ring r)
    (hdone : s.firstHits + 1 = s.gap) :
    s.holder = s.race.target := by
  apply Fin.ext
  have hholder := s.holder_progress
  have hgapPos := s.gap_pos
  omega

/-! ## Literal ordinary-edge bullet transport -/

/-- A bullet-bearing follower responder moves the bullet onto the initiator,
independently of the initiator probe. -/
theorem step_moves_follower_bullet {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (e : Fin n)
    (hnonbarrier : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hfollower : (C (ring.rightNeighbor e)).leader = false)
    (hbullet : (C (ring.rightNeighbor e)).bullet = true) :
    (((CenteredRenewal.protocol k hk).step ring C e) e).bullet = true := by
  have htrans : CenteredRenewal.transition hk (C e)
      (C (ring.rightNeighbor e)) =
      nonBarrierStep (C e) (C (ring.rightNeighbor e)) :=
    CenteredRenewal.transition_of_nonbarrier hk _ _ hnonbarrier
  have hre := rightNeighbor_ne_self ring hn2 e
  cases hprobe : (C e).probe <;>
    simp [PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      nonBarrierStep, hfollower, hbullet, hprobe, hre]

/-- On an ordinary interaction other than the unique incoming edge of a
holder, an existing holder bullet survives. -/
theorem step_preserves_holder_bullet_of_not_incoming {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n -> State k) (holder e : Fin n)
    (hnonbarrier : ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)))
    (hbullet : (C holder).bullet = true)
    (hnotIncoming : e ≠ ring.leftNeighbor holder) :
    (((CenteredRenewal.protocol k hk).step ring C e) holder).bullet = true := by
  have hre := rightNeighbor_ne_self ring hn2 e
  have hnotResponder : holder ≠ ring.rightNeighbor e := by
    intro h
    apply hnotIncoming
    calc
      e = ring.leftNeighbor (ring.rightNeighbor e) :=
        (leftNeighbor_rightNeighbor_clean ring e).symm
      _ = ring.leftNeighbor holder := congrArg ring.leftNeighbor h.symm
  by_cases hinit : holder = e
  · subst holder
    have htrans : CenteredRenewal.transition hk (C e)
        (C (ring.rightNeighbor e)) =
        nonBarrierStep (C e) (C (ring.rightNeighbor e)) :=
      CenteredRenewal.transition_of_nonbarrier hk _ _ hnonbarrier
    cases hleader : (C (ring.rightNeighbor e)).leader <;>
      cases hrespBullet : (C (ring.rightNeighbor e)).bullet <;>
      cases hprobe : (C e).probe <;>
      simp [PopulationProtocol.step, CenteredRenewal.protocol, htrans,
        nonBarrierStep, hleader, hrespBullet, hprobe, hbullet, hre]
  · simp [PopulationProtocol.step, CenteredRenewal.protocol,
      hinit, hnotResponder, hbullet]

/-! ## Progress-edge semantics -/

/-- The threshold progress selection is the literal bullet hit on the
protected predecessor, hence strictly lowers `Phi`. -/
theorem BulletRaceState.first_done_phi_lt {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n)
    (s : BulletRaceState hk ring r)
    (hdone : s.firstHits + 1 = s.gap) :
    Phi (Rank.cutSuccessor hk ring s.race.config s.firstEdge) <
      Phi s.race.config := by
  have hholder := s.first_done_holder_eq_target hdone
  have hresponder : ring.rightNeighbor s.firstEdge = s.race.target := by
    simp [BulletRaceState.firstEdge, hholder,
      rightNeighbor_leftNeighbor_clean]
  have hne := s.firstEdge_ne_secondEdge hn3
  have hnonbarrier : ¬ IsBarrier hk
      (s.race.config s.firstEdge)
      (s.race.config (ring.rightNeighbor s.firstEdge)) := by
    intro hb
    exact hne ((s.race.barrier s.firstEdge).1 hb)
  apply s.race.target_hit_phi_lt hn3 s.firstEdge hresponder hnonbarrier
  simpa [hholder] using s.holderBullet

/-- Every packaged protocol step literally frames sites outside its two local
endpoints. -/
theorem protocol_step_frame {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n -> State k)
    (e i : Fin n) (hinit : i ≠ e)
    (hresp : i ≠ ring.rightNeighbor e) :
    (CenteredRenewal.protocol k hk).step ring C e i = C i := by
  simp [PopulationProtocol.step, CenteredRenewal.protocol, hinit, hresp]

/-- A nonterminal progress selection moves the tracked bullet one canonical
coordinate left and increments only the first counter. -/
noncomputable def BulletRaceState.afterFirst {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : BulletRaceState hk ring r)
    (hlive : s.firstHits + 1 < s.gap)
    (hplateau : Phi (Rank.cutSuccessor hk ring s.race.config s.firstEdge) =
      Phi s.race.config) : BulletRaceState hk ring r := by
  let e := s.firstEdge
  let D := Rank.cutSuccessor hk ring s.race.config e
  have hne : e ≠ tailCoord ring := s.firstEdge_ne_secondEdge hn3
  have hnonbarrier : ¬ IsBarrier hk (s.race.config e)
      (s.race.config (ring.rightNeighbor e)) := by
    intro hb
    exact hne ((s.race.barrier e).1 hb)
  have hnotready : ¬ CenteredRenewal.AdvanceReady hk ring
      s.race.config e := by
    intro hready
    exact hnonbarrier hready.1
  have hcut : D =
      (CenteredRenewal.protocol k hk).step ring s.race.config e := by
    dsimp only [D]
    unfold Rank.cutSuccessor
    simp only [hnotready, if_false]
    funext i
    rfl
  have hnotcross : ¬ BarrierCrossedTarget hk ring
      s.race.config e s.race.target := by
    intro hcross
    exact hnotready hcross.1
  let N := s.race.next hn3 hndvd e hplateau hnotcross
  have hNtarget : N.target = s.race.target := by
    simp [N, NoDropLaterShield.ActiveRaceState.next, nextTarget, hnotready]
  have htargetHolder : s.race.target.val < s.holder.val := by
    have hholder := s.holder_progress
    omega
  have hholderPos : 0 < s.holder.val :=
    Nat.lt_trans (s.target_pos hn3) htargetHolder
  have hleft := leftNeighbor_val_of_pos ring s.holder hholderPos
  have hresponder : ring.rightNeighbor e = s.holder := by
    simp [e, BulletRaceState.firstEdge, rightNeighbor_leftNeighbor_clean]
  have hholderFollower : (s.race.config s.holder).leader = false :=
    s.corridor s.holder htargetHolder (Nat.le_refl _)
  have hmove :
      (((CenteredRenewal.protocol k hk).step ring s.race.config e) e).bullet =
        true := by
    apply step_moves_follower_bullet hk ring (by omega)
      s.race.config e hnonbarrier
    · simpa [hresponder] using hholderFollower
    · simpa [hresponder] using s.holderBullet
  have hphase : (D (tailCoord ring)).phase =
      (s.race.config (tailCoord ring)).phase := by
    rw [hcut]
    exact step_phases_eq_of_nonbarrier hk ring s.race.config e
      hnonbarrier (tailCoord ring)
  refine {
    race := N
    holder := e
    holderBullet := ?_
    gap := s.gap
    gap_pos := s.gap_pos
    gap_le_half := s.gap_le_half
    firstHits := s.firstHits + 1
    secondHits := s.secondHits
    advances := s.advances
    first_lt := hlive
    second_lt := s.second_lt
    target_progress := ?_
    holder_progress := ?_
    second_clock := ?_
    corridor := ?_
    rank_eq := ?_ }
  · change (D e).bullet = true
    rw [hcut]
    exact hmove
  · change N.target.val + s.advances + s.gap = n - 1
    rw [hNtarget]
    exact s.target_progress
  · change N.target.val + (s.gap - 1) = e.val + (s.firstHits + 1)
    rw [hNtarget]
    change s.race.target.val + (s.gap - 1) =
      (ring.leftNeighbor s.holder).val + (s.firstHits + 1)
    have hholder := s.holder_progress
    have hleftAdd : (ring.leftNeighbor s.holder).val + 1 =
        s.holder.val := by omega
    omega
  · change s.secondHits = 2 * s.advances +
      CenteredRenewal.phaseNat (D (tailCoord ring)).phase
    rw [hphase]
    exact s.second_clock
  · intro i hlater hbefore
    change (D i).leader = false
    cases hi : (D i).leader with
    | false => rfl
    | true =>
        have hiRaw :
            (((CenteredRenewal.protocol k hk).step ring s.race.config e)
              i).leader = true := by
          rw [← hcut]
          exact hi
        have hiOld := step_no_leader_birth_of_nonbarrier hk ring (by omega)
          s.race.config e hnonbarrier i hiRaw
        have hupper : i.val ≤ s.holder.val := by
          change i.val ≤ (ring.leftNeighbor s.holder).val at hbefore
          rw [hleft] at hbefore
          omega
        have hfalse := s.corridor i (by simpa [hNtarget] using hlater) hupper
        rw [hfalse] at hiOld
        contradiction
  · change Phi D = r
    rw [hplateau, s.rank_eq]

/-! ## Barrier-clock semantics -/

/-- A nonterminal phase-zero barrier selection arms the same tail and
increments only the second counter. -/
noncomputable def BulletRaceState.afterSecondPhaseZero
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : BulletRaceState hk ring r)
    (hphase : (s.race.config (tailCoord ring)).phase = false)
    (hlive : s.secondHits + 1 < s.gap)
    (hplateau : Phi (Rank.cutSuccessor hk ring s.race.config
      (tailCoord ring)) = Phi s.race.config) :
    BulletRaceState hk ring r := by
  let e := tailCoord ring
  let D := Rank.cutSuccessor hk ring s.race.config e
  have hbarrier : IsBarrier hk (s.race.config e)
      (s.race.config (ring.rightNeighbor e)) :=
    (s.race.barrier e).2 rfl
  have hnotready : ¬ CenteredRenewal.AdvanceReady hk ring
      s.race.config e := by
    intro hready
    have hp : (s.race.config (tailCoord ring)).phase = true := by
      simpa [e] using hready.2
    rw [hphase] at hp
    contradiction
  have hcut : D =
      (CenteredRenewal.protocol k hk).step ring s.race.config e := by
    dsimp only [D]
    unfold Rank.cutSuccessor
    simp only [hnotready, if_false]
    funext i
    rfl
  have hnotcross : ¬ BarrierCrossedTarget hk ring
      s.race.config e s.race.target := by
    intro hcross
    exact hnotready hcross.1
  let N := s.race.next hn3 hndvd e hplateau hnotcross
  have hNtarget : N.target = s.race.target := by
    simp [N, NoDropLaterShield.ActiveRaceState.next, nextTarget, hnotready]
  have hholderPos : 0 < s.holder.val :=
    Nat.lt_of_lt_of_le (s.target_pos hn3) s.target_le_holder
  have hholderNeTail : s.holder ≠ e := by
    intro h
    have hv := congrArg Fin.val h
    have hlt := s.holder_lt_tail
    change s.holder.val < n - 1 at hlt
    change s.holder.val = n - 1 at hv
    omega
  have hholderNeHead : s.holder ≠ ring.rightNeighbor e := by
    intro h
    have hv := congrArg Fin.val h
    have hhead : (ring.rightNeighbor (tailCoord ring)).val = 0 := by
      simp
    change s.holder.val = (ring.rightNeighbor (tailCoord ring)).val at hv
    rw [hhead] at hv
    omega
  have hholderFrame :
      (((CenteredRenewal.protocol k hk).step ring s.race.config e)
        s.holder) = s.race.config s.holder :=
    protocol_step_frame hk ring s.race.config e s.holder
      hholderNeTail hholderNeHead
  have hnewPhase : (D (tailCoord ring)).phase = true := by
    rw [hcut]
    simpa [e, OneBarrierCleanup.step] using
      barrier_phase_zero_arms_tail hk ring (by omega)
      s.race.config (tailCoord ring) hbarrier hphase
  refine {
    race := N
    holder := s.holder
    holderBullet := ?_
    gap := s.gap
    gap_pos := s.gap_pos
    gap_le_half := s.gap_le_half
    firstHits := s.firstHits
    secondHits := s.secondHits + 1
    advances := s.advances
    first_lt := s.first_lt
    second_lt := hlive
    target_progress := ?_
    holder_progress := ?_
    second_clock := ?_
    corridor := ?_
    rank_eq := ?_ }
  · change (D s.holder).bullet = true
    rw [hcut, hholderFrame]
    exact s.holderBullet
  · change N.target.val + s.advances + s.gap = n - 1
    rw [hNtarget]
    exact s.target_progress
  · change N.target.val + (s.gap - 1) =
      s.holder.val + s.firstHits
    rw [hNtarget]
    exact s.holder_progress
  · change s.secondHits + 1 = 2 * s.advances +
      CenteredRenewal.phaseNat (D (tailCoord ring)).phase
    rw [hnewPhase]
    simp only [CenteredRenewal.phaseNat]
    have hclock := s.second_clock
    rw [hphase] at hclock
    simp only [CenteredRenewal.phaseNat, Nat.add_zero] at hclock
    omega
  · intro i hlater hbefore
    change (D i).leader = false
    have hiPos : 0 < i.val := by
      have htPos := s.target_pos hn3
      rw [hNtarget] at hlater
      omega
    have hiNeTail : i ≠ e := by
      intro h
      have hv := congrArg Fin.val h
      have hholderLt := s.holder_lt_tail
      change s.holder.val < n - 1 at hholderLt
      change i.val = n - 1 at hv
      omega
    have hiNeHead : i ≠ ring.rightNeighbor e := by
      intro h
      have hv := congrArg Fin.val h
      have hhead : (ring.rightNeighbor (tailCoord ring)).val = 0 := by simp
      change i.val = (ring.rightNeighbor (tailCoord ring)).val at hv
      rw [hhead] at hv
      omega
    rw [hcut, protocol_step_frame hk ring s.race.config e i
      hiNeTail hiNeHead]
    exact s.corridor i (by simpa [hNtarget] using hlater) hbefore
  · change Phi D = r
    rw [hplateau, s.rank_eq]

/-- A nonterminal phase-one barrier selection advances the physical cut.
Both ghost coordinates shift left, while their physical identities and the
tracked bullet are preserved. -/
noncomputable def BulletRaceState.afterSecondPhaseOne
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : BulletRaceState hk ring r)
    (hphase : (s.race.config (tailCoord ring)).phase = true)
    (hlive : s.secondHits + 1 < s.gap)
    (hplateau : Phi (Rank.cutSuccessor hk ring s.race.config
      (tailCoord ring)) = Phi s.race.config) :
    BulletRaceState hk ring r := by
  let e := tailCoord ring
  let raw := (CenteredRenewal.protocol k hk).step ring s.race.config e
  let D := Rank.cutSuccessor hk ring s.race.config e
  have hbarrier : IsBarrier hk (s.race.config e)
      (s.race.config (ring.rightNeighbor e)) :=
    (s.race.barrier e).2 rfl
  have hready : CenteredRenewal.AdvanceReady hk ring s.race.config e :=
    ⟨hbarrier, by simpa [e] using hphase⟩
  have hcut : D = rotateCut ring raw := by
    simp [D, Rank.cutSuccessor, hready, raw]
  have htargetPos := s.target_pos hn3
  have htargetLeft := leftNeighbor_val_of_pos ring s.race.target htargetPos
  have hnotcross : ¬ BarrierCrossedTarget hk ring
      s.race.config e s.race.target := by
    intro hcross
    have hv := congrArg Fin.val hcross.2
    change (ring.leftNeighbor s.race.target).val = n - 1 at hv
    rw [htargetLeft] at hv
    have htlt := s.race.target.isLt
    omega
  let N := s.race.next hn3 hndvd e hplateau hnotcross
  have hNtarget : N.target = ring.leftNeighbor s.race.target := by
    simp [N, NoDropLaterShield.ActiveRaceState.next, nextTarget, hready]
  have hholderPos : 0 < s.holder.val :=
    Nat.lt_of_lt_of_le htargetPos s.target_le_holder
  have hholderLeft := leftNeighbor_val_of_pos ring s.holder hholderPos
  have hholderNeTail : s.holder ≠ e := by
    intro h
    have hv := congrArg Fin.val h
    have hlt := s.holder_lt_tail
    change s.holder.val < n - 1 at hlt
    change s.holder.val = n - 1 at hv
    omega
  have hholderNeHead : s.holder ≠ ring.rightNeighbor e := by
    intro h
    have hv := congrArg Fin.val h
    have hhead : (ring.rightNeighbor (tailCoord ring)).val = 0 := by simp
    change s.holder.val = (ring.rightNeighbor (tailCoord ring)).val at hv
    rw [hhead] at hv
    omega
  have hholderFrame : raw s.holder = s.race.config s.holder := by
    exact protocol_step_frame hk ring s.race.config e s.holder
      hholderNeTail hholderNeHead
  have hone : OneBarrierAt hk ring s.race.config (tailCoord ring) :=
    canonicalOneBarrier_oneBarrierAt_tail hk ring s.race.config
      s.race.barrier
  have hsanitized := advance_sanitizes_new_tail hk ring (by omega)
    s.race.config (tailCoord ring) hone hphase
  have hnewPhase : (D (tailCoord ring)).phase = false := by
    rw [hcut]
    change (raw (ring.rightNeighbor (tailCoord ring))).phase = false
    simpa [raw, OneBarrierCleanup.step] using hsanitized.1
  refine {
    race := N
    holder := ring.leftNeighbor s.holder
    holderBullet := ?_
    gap := s.gap
    gap_pos := s.gap_pos
    gap_le_half := s.gap_le_half
    firstHits := s.firstHits
    secondHits := s.secondHits + 1
    advances := s.advances + 1
    first_lt := s.first_lt
    second_lt := hlive
    target_progress := ?_
    holder_progress := ?_
    second_clock := ?_
    corridor := ?_
    rank_eq := ?_ }
  · change (D (ring.leftNeighbor s.holder)).bullet = true
    rw [hcut]
    change (raw (ring.rightNeighbor (ring.leftNeighbor s.holder))).bullet =
      true
    rw [rightNeighbor_leftNeighbor_clean, hholderFrame]
    exact s.holderBullet
  · change N.target.val + (s.advances + 1) + s.gap = n - 1
    rw [hNtarget, htargetLeft]
    have hprogress := s.target_progress
    omega
  · change N.target.val + (s.gap - 1) =
      (ring.leftNeighbor s.holder).val + s.firstHits
    rw [hNtarget, htargetLeft, hholderLeft]
    have hprogress := s.holder_progress
    omega
  · change s.secondHits + 1 = 2 * (s.advances + 1) +
      CenteredRenewal.phaseNat (D (tailCoord ring)).phase
    rw [hnewPhase]
    simp only [CenteredRenewal.phaseNat, Nat.add_zero]
    have hclock := s.second_clock
    rw [hphase] at hclock
    simp only [CenteredRenewal.phaseNat] at hclock
    omega
  · intro i hlater hbefore
    change (D i).leader = false
    have hnewHolderLt : (ring.leftNeighbor s.holder).val <
        (tailCoord ring).val := by
      rw [hholderLeft]
      have hlt := s.holder_lt_tail
      omega
    have hiNeTail : i ≠ tailCoord ring := by
      intro h
      have hv := congrArg Fin.val h
      omega
    have hrightVal := rightNeighbor_val_of_ne_tail ring i hiNeTail
    let oldI := ring.rightNeighbor i
    have holdLower : s.race.target.val < oldI.val := by
      rw [hNtarget] at hlater
      change (ring.leftNeighbor s.race.target).val < i.val at hlater
      change (ring.rightNeighbor i).val = i.val + 1 at hrightVal
      rw [htargetLeft] at hlater
      change s.race.target.val < (ring.rightNeighbor i).val
      omega
    have holdUpper : oldI.val ≤ s.holder.val := by
      change i.val ≤ (ring.leftNeighbor s.holder).val at hbefore
      change (ring.rightNeighbor i).val = i.val + 1 at hrightVal
      rw [hholderLeft] at hbefore
      change (ring.rightNeighbor i).val ≤ s.holder.val
      omega
    have holdNeTail : oldI ≠ e := by
      intro h
      have hv := congrArg Fin.val h
      have hlt := s.holder_lt_tail
      change s.holder.val < n - 1 at hlt
      change oldI.val = n - 1 at hv
      omega
    have holdNeHead : oldI ≠ ring.rightNeighbor e := by
      intro h
      have hv := congrArg Fin.val h
      have hhead : (ring.rightNeighbor (tailCoord ring)).val = 0 := by simp
      change oldI.val = (ring.rightNeighbor (tailCoord ring)).val at hv
      rw [hhead] at hv
      have htpos := s.target_pos hn3
      omega
    rw [hcut]
    change (raw oldI).leader = false
    have hframe : raw oldI = s.race.config oldI := by
      simpa [raw] using protocol_step_frame hk ring s.race.config e oldI
        holdNeTail holdNeHead
    rw [hframe]
    exact s.corridor oldI holdLower holdUpper
  · change Phi D = r
    rw [hplateau, s.rank_eq]

/-- Unified nonterminal barrier-counter update. -/
noncomputable def BulletRaceState.afterSecond
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : BulletRaceState hk ring r)
    (hlive : s.secondHits + 1 < s.gap)
    (hplateau : Phi (Rank.cutSuccessor hk ring s.race.config
      s.secondEdge) = Phi s.race.config) :
    BulletRaceState hk ring r := by
  if hphase : (s.race.config (tailCoord ring)).phase = false then
    exact s.afterSecondPhaseZero hn3 hndvd hphase hlive (by
      simpa [BulletRaceState.secondEdge] using hplateau)
  else
    have htrue : (s.race.config (tailCoord ring)).phase = true := by
      cases h : (s.race.config (tailCoord ring)).phase <;> simp_all
    exact s.afterSecondPhaseOne hn3 hndvd htrue hlive (by
      simpa [BulletRaceState.secondEdge] using hplateau)

@[simp] theorem BulletRaceState.afterSecond_race_config
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : BulletRaceState hk ring r)
    (hlive : s.secondHits + 1 < s.gap)
    (hplateau : Phi (Rank.cutSuccessor hk ring s.race.config
      s.secondEdge) = Phi s.race.config) :
    (s.afterSecond hn3 hndvd hlive hplateau).race.config =
      Rank.cutSuccessor hk ring s.race.config s.secondEdge := by
  unfold BulletRaceState.afterSecond
  split
  · simp [BulletRaceState.afterSecondPhaseZero,
      NoDropLaterShield.ActiveRaceState.next,
      BulletRaceState.secondEdge]
  · simp [BulletRaceState.afterSecondPhaseOne,
      NoDropLaterShield.ActiveRaceState.next,
      BulletRaceState.secondEdge]

/-- Every edge outside the two adaptive race targets executes literally and,
on a rank plateau, preserves the entire race invariant. -/
noncomputable def BulletRaceState.afterOther
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : BulletRaceState hk ring r) (e : Fin n)
    (hfirst : e ≠ s.firstEdge) (hsecond : e ≠ s.secondEdge)
    (hplateau : Phi (Rank.cutSuccessor hk ring s.race.config e) =
      Phi s.race.config) : BulletRaceState hk ring r := by
  let D := Rank.cutSuccessor hk ring s.race.config e
  have hnonbarrier : ¬ IsBarrier hk (s.race.config e)
      (s.race.config (ring.rightNeighbor e)) := by
    intro hb
    have heq : e = tailCoord ring := (s.race.barrier e).1 hb
    exact hsecond (by simpa [BulletRaceState.secondEdge] using heq)
  have hnotready : ¬ CenteredRenewal.AdvanceReady hk ring
      s.race.config e := by
    intro hready
    exact hnonbarrier hready.1
  have hcut : D =
      (CenteredRenewal.protocol k hk).step ring s.race.config e := by
    dsimp only [D]
    unfold Rank.cutSuccessor
    simp only [hnotready, if_false]
    funext i
    rfl
  have hnotcross : ¬ BarrierCrossedTarget hk ring
      s.race.config e s.race.target := by
    intro hcross
    exact hnotready hcross.1
  let N := s.race.next hn3 hndvd e hplateau hnotcross
  have hNtarget : N.target = s.race.target := by
    simp [N, NoDropLaterShield.ActiveRaceState.next, nextTarget, hnotready]
  have hbullet : (D s.holder).bullet = true := by
    rw [hcut]
    apply step_preserves_holder_bullet_of_not_incoming hk ring (by omega)
      s.race.config s.holder e hnonbarrier s.holderBullet
    simpa [BulletRaceState.firstEdge] using hfirst
  have hphase : (D (tailCoord ring)).phase =
      (s.race.config (tailCoord ring)).phase := by
    rw [hcut]
    exact step_phases_eq_of_nonbarrier hk ring s.race.config e
      hnonbarrier (tailCoord ring)
  refine {
    race := N
    holder := s.holder
    holderBullet := hbullet
    gap := s.gap
    gap_pos := s.gap_pos
    gap_le_half := s.gap_le_half
    firstHits := s.firstHits
    secondHits := s.secondHits
    advances := s.advances
    first_lt := s.first_lt
    second_lt := s.second_lt
    target_progress := ?_
    holder_progress := ?_
    second_clock := ?_
    corridor := ?_
    rank_eq := ?_ }
  · change N.target.val + s.advances + s.gap = n - 1
    rw [hNtarget]
    exact s.target_progress
  · change N.target.val + (s.gap - 1) =
      s.holder.val + s.firstHits
    rw [hNtarget]
    exact s.holder_progress
  · change s.secondHits = 2 * s.advances +
      CenteredRenewal.phaseNat (D (tailCoord ring)).phase
    rw [hphase]
    exact s.second_clock
  · intro i hlater hbefore
    change (D i).leader = false
    cases hi : (D i).leader with
    | false => rfl
    | true =>
        have hiRaw :
            (((CenteredRenewal.protocol k hk).step ring s.race.config e)
              i).leader = true := by
          rw [← hcut]
          exact hi
        have hiOld := step_no_leader_birth_of_nonbarrier hk ring (by omega)
          s.race.config e hnonbarrier i hiRaw
        have hfalse := s.corridor i (by simpa [hNtarget] using hlater)
          hbefore
        rw [hfalse] at hiOld
        contradiction
  · change Phi D = r
    rw [hplateau, s.rank_eq]

/-! ## Total endpoint-carrying physical race -/

/-- Total proof state.  Both terminal constructors retain the actual
normalized post-step configuration selected by `next`. -/
inductive RaceProofState {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (r : Nat) : Type where
  | active (state : BulletRaceState hk ring r)
  | success (config : Fin n -> State k) (rank_lt : Phi config < r)
  | failure (config : Fin n -> State k)

def RaceProofState.configuration {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : RaceProofState hk ring r -> Fin n -> State k
  | .active s => s.race.config
  | .success X _ => X
  | .failure X => X

def RaceProofState.isActive {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : RaceProofState hk ring r -> Bool
  | .active _ => true
  | _ => false

def RaceProofState.isSuccess {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : RaceProofState hk ring r -> Bool
  | .success _ _ => true
  | _ => false

def RaceProofState.isFailure {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : RaceProofState hk ring r -> Bool
  | .failure _ => true
  | _ => false

/-- Execute the literal normalized step first.  A strict rank drop has
priority over both counter thresholds; the second threshold is otherwise a
conservative failure carrying that same post-step configuration. -/
noncomputable def RaceProofState.next {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n) :
    RaceProofState hk ring r -> Fin n -> RaceProofState hk ring r
  | z@(.success _ _), _ => z
  | z@(.failure _), _ => z
  | .active s, e => by
      let D := Rank.cutSuccessor hk ring s.race.config e
      if hdrop : Phi D < r then
        exact .success D hdrop
      else
        have hle := Rank.canonical_phi_step_le hk ring hn3 s.race.config
          s.race.barrier e
        have hDrank : Phi D = r := Nat.le_antisymm
          (by simpa [D, s.rank_eq] using hle) (Nat.le_of_not_gt hdrop)
        have hplateau : Phi D = Phi s.race.config := by
          rw [hDrank, s.rank_eq]
        if hfirst : e = s.firstEdge then
          if hdone : s.firstHits + 1 = s.gap then
            have hstrict := s.first_done_phi_lt hn3 hdone
            have hstrictR : Phi D < r := by
              simpa [D, hfirst, s.rank_eq] using hstrict
            exact False.elim (hdrop hstrictR)
          else
            have hlive : s.firstHits + 1 < s.gap := by
              have := s.first_lt
              omega
            exact .active (s.afterFirst hn3 hndvd hlive (by
              simpa [D, hfirst] using hplateau))
        else if hsecond : e = s.secondEdge then
          if hdone : s.secondHits + 1 = s.gap then
            exact .failure D
          else
            have hlive : s.secondHits + 1 < s.gap := by
              have := s.second_lt
              omega
            exact .active (s.afterSecond hn3 hndvd hlive (by
              simpa [D, hsecond] using hplateau))
        else
          exact .active (s.afterOther hn3 hndvd e hfirst hsecond hplateau)

/-- Every active machine edge retains the exact normalized physical
successor, including both success and conservative-failure terminals. -/
theorem RaceProofState.configuration_next {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (z : RaceProofState hk ring r) (e : Fin n)
    (hactive : z.isActive = true) :
    (z.next hn3 hndvd e).configuration =
      Rank.cutSuccessor hk ring z.configuration e := by
  cases z with
  | success X h => simp [RaceProofState.isActive] at hactive
  | failure X => simp [RaceProofState.isActive] at hactive
  | active s =>
      simp only [RaceProofState.next]
      split
      · rfl
      · split
        · split
          · contradiction
          · simp_all [RaceProofState.configuration,
              BulletRaceState.afterFirst,
              NoDropLaterShield.ActiveRaceState.next]
        · split
          · split
            · rfl
            · cases hp : (s.race.config (tailCoord ring)).phase <;>
                simp_all [RaceProofState.configuration,
                  BulletRaceState.afterSecond,
                  BulletRaceState.afterSecondPhaseZero,
                  BulletRaceState.afterSecondPhaseOne,
                  BulletRaceState.secondEdge,
                  NoDropLaterShield.ActiveRaceState.next]
          · rfl

def RaceProofState.payloadNode {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : RaceProofState hk ring r ->
      PayloadFiniteStoppingTree.PayloadNode
        (RaceProofState hk ring r) (RaceProofState hk ring r)
        (RaceProofState hk ring r)
  | z@(.active _) => .active z
  | z@(.success _ _) => .success z
  | z@(.failure _) => .failure z

noncomputable def RaceProofState.payloadStep {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (z : RaceProofState hk ring r) (e : Fin n) :
    PayloadFiniteStoppingTree.PayloadNode
      (RaceProofState hk ring r) (RaceProofState hk ring r)
      (RaceProofState hk ring r) :=
  (z.next hn3 hndvd e).payloadNode

/-! ## Exact abstract-race numerator -/

private theorem nodup_ofFn_of_injective {n : Nat} {A : Type}
    (f : Fin n -> A) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem nodup_ofFn_fin (n : Nat) :
    (List.ofFn (fun i : Fin n => i)).Nodup :=
  nodup_ofFn_of_injective (fun i : Fin n => i) (fun _ _ h => h)

/-- Public copy of the exact counter-race recurrence.  The generic library
keeps this equality private because its public consumers only need the
symmetric quarter bound; the physical refinement below needs the recurrence
itself. -/
theorem counterRace_successCount_eq_successNumerator
    {S : Type} {n d : Nat} (first second : S -> Fin n)
    (next : S -> Fin n -> S)
    (hdistinct : forall s, first s ≠ second s) :
    forall (st : PredictableCounterRaceFiniteTree.ActiveRaceState S d) T,
      successCount
          (PredictableCounterRaceFiniteTree.counterRaceStep first second next)
          (.active st) T =
        PredictableCounterRaceFiniteTree.successNumerator n d
          st.firstHits st.secondHits T := by
  intro st T
  induction T generalizing st with
  | zero => rfl
  | succ T ih =>
      simp only [successCount] at ih
      simp only [successCount, treeWeight]
      have hsum := sum_two_exceptions
        (List.ofFn (fun i : Fin n => i))
        (first st.payload) (second st.payload)
        (fun e => treeWeight
          (PredictableCounterRaceFiniteTree.counterRaceStep
            first second next)
          successWeight
          (FiniteUniformStoppingTree.stepNode
            (PredictableCounterRaceFiniteTree.counterRaceStep
              first second next) (.active st) e) T)
        (PredictableCounterRaceFiniteTree.successNumerator n d
          st.firstHits st.secondHits T)
        (nodup_ofFn_fin n)
        (by rw [List.mem_ofFn]; exact ⟨first st.payload, rfl⟩)
        (by rw [List.mem_ofFn]; exact ⟨second st.payload, rfl⟩)
        (hdistinct st.payload) (by
          intro e _ hef hes
          simp only [FiniteUniformStoppingTree.stepNode]
          rw [show
            PredictableCounterRaceFiniteTree.counterRaceStep
                first second next st e =
              .active
                { payload := next st.payload e
                  firstHits := st.firstHits
                  secondHits := st.secondHits
                  first_lt := st.first_lt
                  second_lt := st.second_lt } by
            simp [PredictableCounterRaceFiniteTree.counterRaceStep,
              hef, hes]]
          exact ih _)
      have hsum' :
          (List.ofFn (fun e => treeWeight
            (PredictableCounterRaceFiniteTree.counterRaceStep
              first second next) successWeight
            (FiniteUniformStoppingTree.stepNode
              (PredictableCounterRaceFiniteTree.counterRaceStep
                first second next) (.active st) e) T)).sum =
          treeWeight
              (PredictableCounterRaceFiniteTree.counterRaceStep
                first second next) successWeight
              (FiniteUniformStoppingTree.stepNode
                (PredictableCounterRaceFiniteTree.counterRaceStep
                  first second next) (.active st) (first st.payload)) T +
            treeWeight
              (PredictableCounterRaceFiniteTree.counterRaceStep
                first second next) successWeight
              (FiniteUniformStoppingTree.stepNode
                (PredictableCounterRaceFiniteTree.counterRaceStep
                  first second next) (.active st) (second st.payload)) T +
            (n - 2) *
              PredictableCounterRaceFiniteTree.successNumerator n d
                st.firstHits st.secondHits T := by
        simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn]
          using hsum
      rw [hsum']
      simp only [PredictableCounterRaceFiniteTree.successNumerator]
      by_cases hp : st.firstHits + 1 = d <;>
        by_cases hq : st.secondHits + 1 = d <;>
        simp [FiniteUniformStoppingTree.stepNode,
          PredictableCounterRaceFiniteTree.counterRaceStep, hp, hq,
          (hdistinct st.payload).symm, treeWeight_success,
          treeWeight_failure, successWeight, ih]

/-- No success recurrence can count more than all scheduler words. -/
theorem successNumerator_le_pow (n d p q T : Nat)
    (hn2 : 2 <= n) :
    PredictableCounterRaceFiniteTree.successNumerator n d p q T <= n ^ T := by
  induction T generalizing p q with
  | zero => simp [PredictableCounterRaceFiniteTree.successNumerator]
  | succ T ih =>
      simp only [PredictableCounterRaceFiniteTree.successNumerator]
      have hpp := ih (p + 1) q
      have hpq := ih p (q + 1)
      have hp0 := ih p q
      let a := if p + 1 = d then n ^ T else
        PredictableCounterRaceFiniteTree.successNumerator n d (p + 1) q T
      let b := if q + 1 = d then 0 else
        PredictableCounterRaceFiniteTree.successNumerator n d p (q + 1) T
      have ha : a <= n ^ T := by
        dsimp [a]
        split <;> simp_all
      have hb : b <= n ^ T := by
        dsimp [b]
        split <;> simp_all
      have hc : (n - 2) *
          PredictableCounterRaceFiniteTree.successNumerator n d p q T <=
          (n - 2) * n ^ T := Nat.mul_le_mul_left _ hp0
      change a + b + (n - 2) *
          PredictableCounterRaceFiniteTree.successNumerator n d p q T <=
        n ^ (T + 1)
      calc
        a + b + (n - 2) *
            PredictableCounterRaceFiniteTree.successNumerator n d p q T <=
            n ^ T + n ^ T + (n - 2) * n ^ T :=
          Nat.add_le_add (Nat.add_le_add ha hb) hc
        _ = n * n ^ T := by
          rw [show n ^ T + n ^ T = 2 * n ^ T by omega,
            <- Nat.add_mul, Nat.add_sub_of_le hn2]
        _ = n ^ (T + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- Numeric quarter bound for the payload-free recurrence, exposed for the
physical simulation below. -/
theorem initial_successNumerator_quarter (n d : Nat) (hn2 : 2 <= n)
    (hd : 0 < d) (hdn : 2 * d <= n) :
    n ^ (4 * n ^ 2) <= 4 *
      PredictableCounterRaceFiniteTree.successNumerator n d 0 0
        (4 * n ^ 2) := by
  let first : Unit -> Fin n := fun _ => ⟨0, by omega⟩
  let second : Unit -> Fin n := fun _ => ⟨1, by omega⟩
  let next : Unit -> Fin n -> Unit := fun _ _ => ()
  have hdistinct : forall u, first u ≠ second u := by
    intro u h
    have hv := congrArg Fin.val h
    simp [first, second] at hv
  have h :=
    PredictableCounterRaceFiniteTree.initial_success_quarter_by_four_mul_sq
      first second next hdistinct () hd hdn
  rw [counterRace_successCount_eq_successNumerator
    first second next hdistinct] at h
  simpa [PredictableCounterRaceFiniteTree.initialState] using h

/-! ## Abstract race dominated by the literal physical race -/

private theorem firstContribution_le_physicalChild
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (s : BulletRaceState hk ring r) (T : Nat)
    (ih : forall s' : BulletRaceState hk ring r,
      PredictableCounterRaceFiniteTree.successNumerator n s'.gap
          s'.firstHits s'.secondHits T <=
        successMass (RaceProofState.payloadStep hn3 hndvd)
          (.active (.active s')) T) :
    (if s.firstHits + 1 = s.gap then n ^ T else
      PredictableCounterRaceFiniteTree.successNumerator n s.gap
        (s.firstHits + 1) s.secondHits T) <=
      successMass (RaceProofState.payloadStep hn3 hndvd)
        (RaceProofState.payloadStep hn3 hndvd (.active s) s.firstEdge) T := by
  let D := Rank.cutSuccessor hk ring s.race.config s.firstEdge
  by_cases hdone : s.firstHits + 1 = s.gap
  · have hstrict := s.first_done_phi_lt hn3 hdone
    have hdrop : Phi D < r := by
      simpa [D, s.rank_eq] using hstrict
    simp [RaceProofState.payloadStep, RaceProofState.payloadNode,
      RaceProofState.next, D, hdrop, hdone]
  · have hlive : s.firstHits + 1 < s.gap := by
      have := s.first_lt
      omega
    by_cases hdrop : Phi D < r
    · have hbound := successNumerator_le_pow n s.gap
        (s.firstHits + 1) s.secondHits T (by omega)
      simpa [RaceProofState.payloadStep, RaceProofState.payloadNode,
        RaceProofState.next, D, hdrop, hdone] using hbound
    · have hle := Rank.canonical_phi_step_le hk ring hn3 s.race.config
        s.race.barrier s.firstEdge
      have hDrank : Phi D = r := Nat.le_antisymm
        (by simpa [D, s.rank_eq] using hle) (Nat.le_of_not_gt hdrop)
      have hplateau : Phi D = Phi s.race.config := by
        rw [hDrank, s.rank_eq]
      let s' := s.afterFirst hn3 hndvd hlive hplateau
      have hrec := ih s'
      simpa [s', RaceProofState.payloadStep, RaceProofState.payloadNode,
        RaceProofState.next, D, hdrop, hdone,
        BulletRaceState.afterFirst] using hrec

private theorem secondContribution_le_physicalChild
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (s : BulletRaceState hk ring r) (T : Nat)
    (ih : forall s' : BulletRaceState hk ring r,
      PredictableCounterRaceFiniteTree.successNumerator n s'.gap
          s'.firstHits s'.secondHits T <=
        successMass (RaceProofState.payloadStep hn3 hndvd)
          (.active (.active s')) T) :
    (if s.secondHits + 1 = s.gap then 0 else
      PredictableCounterRaceFiniteTree.successNumerator n s.gap
        s.firstHits (s.secondHits + 1) T) <=
      successMass (RaceProofState.payloadStep hn3 hndvd)
        (RaceProofState.payloadStep hn3 hndvd (.active s) s.secondEdge) T := by
  let D := Rank.cutSuccessor hk ring s.race.config s.secondEdge
  by_cases hdone : s.secondHits + 1 = s.gap
  · simp [hdone]
  · have hlive : s.secondHits + 1 < s.gap := by
      have := s.second_lt
      omega
    by_cases hdrop : Phi D < r
    · have hbound := successNumerator_le_pow n s.gap s.firstHits
        (s.secondHits + 1) T (by omega)
      simpa [RaceProofState.payloadStep, RaceProofState.payloadNode,
        RaceProofState.next, D, hdrop, hdone,
        s.firstEdge_ne_secondEdge hn3] using hbound
    · have hle := Rank.canonical_phi_step_le hk ring hn3 s.race.config
        s.race.barrier s.secondEdge
      have hDrank : Phi D = r := Nat.le_antisymm
        (by simpa [D, s.rank_eq] using hle) (Nat.le_of_not_gt hdrop)
      have hplateau : Phi D = Phi s.race.config := by
        rw [hDrank, s.rank_eq]
      let s' := s.afterSecond hn3 hndvd hlive hplateau
      have hrec := ih s'
      by_cases hphase :
          (s.race.config (tailCoord ring)).phase = false
      · simpa [s', RaceProofState.payloadStep, RaceProofState.payloadNode,
          RaceProofState.next, D, hdrop, hdone,
          s.firstEdge_ne_secondEdge hn3,
          (s.firstEdge_ne_secondEdge hn3).symm,
          BulletRaceState.afterSecond, hphase,
          BulletRaceState.afterSecondPhaseZero] using hrec
      · simpa [s', RaceProofState.payloadStep, RaceProofState.payloadNode,
          RaceProofState.next, D, hdrop, hdone,
          s.firstEdge_ne_secondEdge hn3,
          (s.firstEdge_ne_secondEdge hn3).symm,
          BulletRaceState.afterSecond, hphase,
          BulletRaceState.afterSecondPhaseOne] using hrec

private theorem otherContribution_le_physicalChild
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (s : BulletRaceState hk ring r) (T : Nat)
    (ih : forall s' : BulletRaceState hk ring r,
      PredictableCounterRaceFiniteTree.successNumerator n s'.gap
          s'.firstHits s'.secondHits T <=
        successMass (RaceProofState.payloadStep hn3 hndvd)
          (.active (.active s')) T)
    (e : Fin n) (hfirst : e ≠ s.firstEdge)
    (hsecond : e ≠ s.secondEdge) :
    PredictableCounterRaceFiniteTree.successNumerator n s.gap
        s.firstHits s.secondHits T <=
      successMass (RaceProofState.payloadStep hn3 hndvd)
        (RaceProofState.payloadStep hn3 hndvd (.active s) e) T := by
  let D := Rank.cutSuccessor hk ring s.race.config e
  by_cases hdrop : Phi D < r
  · have hbound := successNumerator_le_pow n s.gap s.firstHits
      s.secondHits T (by omega)
    simpa [RaceProofState.payloadStep, RaceProofState.payloadNode,
      RaceProofState.next, D, hdrop, hfirst, hsecond] using hbound
  · have hle := Rank.canonical_phi_step_le hk ring hn3 s.race.config
      s.race.barrier e
    have hDrank : Phi D = r := Nat.le_antisymm
      (by simpa [D, s.rank_eq] using hle) (Nat.le_of_not_gt hdrop)
    have hplateau : Phi D = Phi s.race.config := by
      rw [hDrank, s.rank_eq]
    let s' := s.afterOther hn3 hndvd e hfirst hsecond hplateau
    have hrec := ih s'
    simpa [s', RaceProofState.payloadStep, RaceProofState.payloadNode,
      RaceProofState.next, D, hdrop, hfirst, hsecond,
      BulletRaceState.afterOther] using hrec

/-- Every abstract first-counter success word is realized by a literal
physical word ending at an exact post-step configuration of smaller rank. -/
theorem successNumerator_le_physicalSuccessMass
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    forall (s : BulletRaceState hk ring r) T,
      PredictableCounterRaceFiniteTree.successNumerator n s.gap
          s.firstHits s.secondHits T <=
        successMass (RaceProofState.payloadStep hn3 hndvd)
          (.active (.active s)) T := by
  intro s T
  induction T generalizing s with
  | zero =>
      simp [PredictableCounterRaceFiniteTree.successNumerator,
        successMass]
  | succ T ih =>
      let A := if s.firstHits + 1 = s.gap then n ^ T else
        PredictableCounterRaceFiniteTree.successNumerator n s.gap
          (s.firstHits + 1) s.secondHits T
      let B := if s.secondHits + 1 = s.gap then 0 else
        PredictableCounterRaceFiniteTree.successNumerator n s.gap
          s.firstHits (s.secondHits + 1) T
      let C := PredictableCounterRaceFiniteTree.successNumerator n s.gap
        s.firstHits s.secondHits T
      let lower : Fin n -> Nat := fun e =>
        if e = s.firstEdge then A else
        if e = s.secondEdge then B else C
      have hab := s.firstEdge_ne_secondEdge hn3
      have hsumLower : (List.ofFn lower).sum =
          A + B + (n - 2) * C := by
        have hsum := sum_two_exceptions
          (List.ofFn (fun i : Fin n => i)) s.firstEdge s.secondEdge
          lower C (nodup_ofFn_fin n)
          (by rw [List.mem_ofFn]; exact ⟨s.firstEdge, rfl⟩)
          (by rw [List.mem_ofFn]; exact ⟨s.secondEdge, rfl⟩)
          hab (by
            intro e _ hfirst hsecond
            simp [lower, hfirst, hsecond])
        simpa [lower, hab, hab.symm, List.map_ofFn,
          Function.comp_def] using hsum
      have hpoint : forall e : Fin n,
          lower e <=
            successMass (RaceProofState.payloadStep hn3 hndvd)
              (RaceProofState.payloadStep hn3 hndvd (.active s) e) T := by
        intro e
        by_cases hfirst : e = s.firstEdge
        · subst e
          simpa [lower, A] using
            firstContribution_le_physicalChild hn3 hndvd s T ih
        · by_cases hsecond : e = s.secondEdge
          · subst e
            simpa [lower, B, hfirst, hab.symm] using
              secondContribution_le_physicalChild hn3 hndvd s T ih
          · simpa [lower, C, hfirst, hsecond] using
              otherContribution_le_physicalChild hn3 hndvd s T ih e
                hfirst hsecond
      have hsumLe := ofFn_sum_le lower
        (fun e => successMass (RaceProofState.payloadStep hn3 hndvd)
          (RaceProofState.payloadStep hn3 hndvd (.active s) e) T) hpoint
      simp only [PredictableCounterRaceFiniteTree.successNumerator]
      change A + B + (n - 2) * C <=
        (List.ofFn (fun e : Fin n =>
          successMass (RaceProofState.payloadStep hn3 hndvd)
            (RaceProofState.payloadStep hn3 hndvd (.active s) e) T)).sum
      rw [<- hsumLower]
      exact hsumLe

/-- The literal bullet/barrier race succeeds on at least one quarter of all
raw scheduler words at horizon `4*n^2`, when started with equal zero
counters.  Every successful leaf retains its exact smaller-rank endpoint. -/
theorem physicalRace_success_quarter_by_four_mul_sq
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (s : BulletRaceState hk ring r)
    (hfirst : s.firstHits = 0) (hsecond : s.secondHits = 0) :
    n ^ (4 * n ^ 2) <= 4 *
      successMass (RaceProofState.payloadStep hn3 hndvd)
        (.active (.active s)) (4 * n ^ 2) := by
  have habstract := initial_successNumerator_quarter n s.gap
    (by omega) s.gap_pos s.two_gap_le
  have hphysical := successNumerator_le_physicalSuccessMass
    hn3 hndvd s (4 * n ^ 2)
  rw [hfirst, hsecond] at hphysical
  exact Nat.le_trans habstract (Nat.mul_le_mul_left 4 hphysical)

/-- The exact post-fire payload initializes the quarter-success physical
race without any carried probabilistic assumption. -/
theorem firedRace_success_quarter_by_four_mul_sq
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (F : FiredRaceState hk ring X)
    (hrank : Phi X = r) :
    n ^ (4 * n ^ 2) <= 4 *
      successMass (RaceProofState.payloadStep hn3 hndvd)
        (.active (.active
          (RankBlockRace.FiredRaceState.toBulletRaceState hn3 F hrank)))
        (4 * n ^ 2) := by
  apply physicalRace_success_quarter_by_four_mul_sq hn3 hndvd
  · rcases F with ⟨S, rfl, hholder, htailLeader, htailBullet,
      htailProbe, htailPhase, G⟩
    rfl
  · rcases F with ⟨S, rfl, hholder, htailLeader, htailBullet,
      htailProbe, htailPhase, G⟩
    rfl

end RankBlockRace
end CenteredRenewal
end AAFJPK
