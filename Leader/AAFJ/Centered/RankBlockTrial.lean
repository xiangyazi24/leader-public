import Leader.AAFJ.Centered.RenewalSearch
import Leader.AAFJ.Centered.NoDropLaterShield
import Leader.Core.PredictableTwoTargetFiniteTree
import Leader.Core.PayloadFiniteStoppingTree

/-!
# Physical trial interface for the centered `Phi > 1` rank block

This module connects the physical good-renewal endpoint to the canonical
moving-cut shield.  It also records the exact fire-before-arm state needed by
the finite scheduler tree.  Scheduler counting is added only after each
physical terminal has been discharged; no probabilistic independence premise
is used.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace RankBlockTrial

open BarrierAlgebra
open SingleBarrierSanitation
open OneBarrierCleanup
open RenewalSearch
open NoDropLaterShield

set_option autoImplicit false

/-- Re-cut a physical good renewal at its current barrier.  Its physical
predecessor becomes the canonical tracked target, while the fresh tail is the
rightmost shield witness. -/
def GoodFreshRenewal.toActiveRaceState {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n -> State k} {tail : Fin n}
    (G : GoodFreshRenewal hk ring C tail)
    (hrank : 1 < Phi (cutView ring tail C)) :
    NoDropLaterShield.ActiveRaceState hk ring where
  config := cutView ring tail C
  target := cutCoord ring tail G.predecessor
  barrier := canonicalOneBarrier_cutView hk ring C tail G.barrier
  fresh := by
    apply goodFreshRenewal_to_CanonicalFreshRightmostAbove
    · intro heq
      apply G.predecessor_ne
      calc
        G.predecessor = cutPos ring tail
            (cutCoord ring tail G.predecessor) :=
          (cutPos_cutCoord ring tail G.predecessor).symm
        _ = cutPos ring tail (tailCoord ring) := by rw [heq]
        _ = tail := cutPos_tailCoord ring tail
    · simpa [cutView] using G.tailLeader
    · simpa [cutView] using G.tailFresh.1
  targetLeader := by
    simpa [cutView] using G.predecessorLeader
  rankPositive := hrank

/-- The adapter retains the exact physical predecessor identity. -/
@[simp] theorem GoodFreshRenewal.toActiveRaceState_target {n k : Nat}
    {hk : 0 < k} {ring : DirectedRing n}
    {C : Fin n -> State k} {tail : Fin n}
    (G : GoodFreshRenewal hk ring C tail)
    (hrank : 1 < Phi (cutView ring tail C)) :
    (GoodFreshRenewal.toActiveRaceState G hrank).target =
      cutCoord ring tail G.predecessor := rfl

/-- The physical incoming edge of the fresh tail in canonical coordinates. -/
def fireEdge {n : Nat} (ring : DirectedRing n) : Fin n :=
  ring.leftNeighbor (tailCoord ring)

@[simp] theorem rightNeighbor_fireEdge {n : Nat} (ring : DirectedRing n) :
    ring.rightNeighbor (fireEdge ring) = tailCoord ring := by
  exact rightNeighbor_leftNeighbor_clean ring (tailCoord ring)

/-- For `n >= 3`, the incoming ordinary fire edge and the outgoing barrier
edge are distinct. -/
theorem fireEdge_ne_barrierEdge {n : Nat} (ring : DirectedRing n)
    (hn3 : 3 ≤ n) : fireEdge ring ≠ tailCoord ring := by
  intro h
  have hv := congrArg Fin.val h
  have htailVal : (tailCoord ring).val = n - 1 := rfl
  have htailPos : 0 < (tailCoord ring).val := by
    rw [htailVal]
    omega
  have hleft := leftNeighbor_val_of_pos ring (tailCoord ring) htailPos
  change (ring.leftNeighbor (tailCoord ring)).val = n - 1 at hv
  rw [hleft] at hv
  rw [htailVal] at hv
  change (n - 1) - 1 = n - 1 at hv
  omega

/-- The incoming fire edge is ordinary in every canonical one-barrier state. -/
theorem fireEdge_nonbarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (X : Fin n -> State k) (hbar : CanonicalOneBarrier hk ring X) :
    ¬ IsBarrier hk (X (fireEdge ring))
      (X (ring.rightNeighbor (fireEdge ring))) := by
  intro hb
  exact fireEdge_ne_barrierEdge ring hn3 ((hbar (fireEdge ring)).1 hb)

/-- Literal firing at a fresh canonical tail.  The incoming initiator receives
the tracked bullet, its probe is cleared, and the tail is unchanged. -/
theorem fireEdge_exact {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (X : Fin n -> State k) (hbar : CanonicalOneBarrier hk ring X)
    (htailLeader : (X (tailCoord ring)).leader = true)
    (htailBullet : (X (tailCoord ring)).bullet = false) :
    let D := (CenteredRenewal.protocol k hk).step ring X (fireEdge ring)
    (D (fireEdge ring)).bullet = true ∧
      (D (fireEdge ring)).probe = false ∧
      D (tailCoord ring) = X (tailCoord ring) := by
  have hn2 : 1 < n := by omega
  have hordinary := fireEdge_nonbarrier hk ring hn3 X hbar
  have hre : tailCoord ring ≠ fireEdge ring := by
    exact Ne.symm (fireEdge_ne_barrierEdge ring hn3)
  have htrans : CenteredRenewal.transition hk (X (fireEdge ring))
      (X (ring.rightNeighbor (fireEdge ring))) =
      ({ X (fireEdge ring) with bullet := true, probe := false },
        X (ring.rightNeighbor (fireEdge ring))) := by
    rw [CenteredRenewal.transition_of_nonbarrier hk _ _ hordinary]
    apply nonBarrierStep_leader_fires
    · simpa using htailLeader
    · simpa using htailBullet
  rw [rightNeighbor_fireEdge] at htrans
  simp [PopulationProtocol.step, CenteredRenewal.protocol, htrans,
    rightNeighbor_fireEdge, hre]

/-! ## Static short corridor retained until firing -/

private theorem cwDist_add_reverse_of_ne_fire {n : Nat}
    (ring : DirectedRing n) (i j : Fin n) (hne : i ≠ j) :
    cwDist ring i j + cwDist ring j i = n := by
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  unfold cwDist
  by_cases hij : i.val < j.val
  · have hfirst : (j.val + n - i.val) % n = j.val - i.val := by
      have heq : j.val + n - i.val = n + (j.val - i.val) := by omega
      have hdiff : j.val - i.val < n := by
        have := j.isLt
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
        have := i.isLt
        omega
      rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add]
      simpa [Nat.mod_mod] using Nat.mod_eq_of_lt hdiff
    rw [hfirst, hsecond]
    omega

/-- Coordinate/distance identity for a non-tail point in a canonical cut. -/
theorem cutCoord_val_add_cwDist_to_barrier {n : Nat}
    (ring : DirectedRing n) (barrier i : Fin n) (hne : i ≠ barrier) :
    (cutCoord ring barrier i).val + cwDist ring i barrier = n - 1 := by
  let c := cutCoord ring barrier i
  have hcne : c ≠ tailCoord ring := by
    intro h
    apply hne
    calc
      i = cutPos ring barrier c := (cutPos_cutCoord ring barrier i).symm
      _ = cutPos ring barrier (tailCoord ring) := by rw [h]
      _ = barrier := cutPos_tailCoord ring barrier
  have hcval : c.val ≠ n - 1 := by
    intro hval
    apply hcne
    exact Fin.ext hval
  have hclt : c.val + 1 < n := by
    have := c.isLt
    omega
  have hwalk : cwPos ring barrier (c.val + 1) = i := by
    rw [← cwPos_rightNeighbor ring barrier c.val]
    exact cutPos_cutCoord ring barrier i
  have hforward : c.val + 1 = cwDist ring barrier i :=
    cwPos_bounded_unique ring barrier i (c.val + 1) hclt hwalk
  have hsum := cwDist_add_reverse_of_ne_fire ring i barrier hne
  change c.val + cwDist ring i barrier = n - 1
  omega

/-- A short leader-free corridor from the tracked predecessor to the fresh
tail.  `gap` counts progress-edge selections through the final predecessor
hit, hence `target.val + gap = n-1`. -/
structure ShortGapCorridor {n k : Nat} (ring : DirectedRing n)
    (X : Fin n -> State k) (target : Fin n) : Type where
  gap : Nat
  gap_pos : 0 < gap
  gap_le_half : gap ≤ n / 2
  target_gap : target.val + gap = n - 1
  followers : forall i : Fin n, target.val < i.val ->
    i.val < (tailCoord ring).val -> (X i).leader = false

/-- Ordinary centered interactions create no leaders, so a fixed-coordinate
corridor survives every fire-stage waiting step. -/
def ShortGapCorridor.afterNonbarrier {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    {X : Fin n -> State k} {target e : Fin n}
    (G : ShortGapCorridor ring X target)
    (hbar : ¬ IsBarrier hk (X e) (X (ring.rightNeighbor e))) :
    ShortGapCorridor ring
      ((CenteredRenewal.protocol k hk).step ring X e) target where
  gap := G.gap
  gap_pos := G.gap_pos
  gap_le_half := G.gap_le_half
  target_gap := G.target_gap
  followers := by
    intro i hlater hbefore
    cases hi : (((CenteredRenewal.protocol k hk).step ring X e) i).leader with
    | false => rfl
    | true =>
        have hold := step_no_leader_birth_of_nonbarrier hk ring hn2 X e
          hbar i hi
        have hfalse := G.followers i hlater hbefore
        rw [hfalse] at hold
        contradiction

/-- Nearest-predecessor minimality supplies the static canonical corridor. -/
def GoodFreshRenewal.toShortGapCorridor {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n -> State k} {tail : Fin n}
    (G : GoodFreshRenewal hk ring C tail) :
    ShortGapCorridor ring (cutView ring tail C)
      (cutCoord ring tail G.predecessor) where
  gap := cwDist ring G.predecessor tail
  gap_pos := G.gap_pos
  gap_le_half := G.gap_le_half
  target_gap := cutCoord_val_add_cwDist_to_barrier ring tail
    G.predecessor G.predecessor_ne
  followers := by
    intro i hlater hbefore
    cases hi : ((cutView ring tail C) i).leader with
    | false => rfl
    | true =>
        let other := cutPos ring tail i
        have hotherNe : other ≠ tail := by
          intro h
          have hc := congrArg (cutCoord ring tail) h
          simp [other] at hc
          have := congrArg Fin.val hc
          omega
        have hotherLeader : (C other).leader = true := by
          simpa [other, cutView] using hi
        have hnearest := G.nearest other hotherNe hotherLeader
        have hpredGap := cutCoord_val_add_cwDist_to_barrier ring tail
          G.predecessor G.predecessor_ne
        have hotherGap := cutCoord_val_add_cwDist_to_barrier ring tail
          other hotherNe
        have hotherCoord : cutCoord ring tail other = i := by
          simp [other]
        rw [hotherCoord] at hotherGap
        omega

/-- Exact state consumed by the fire-before-arm two-target tree. -/
structure FireReady {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (X : Fin n -> State k) : Type where
  race : NoDropLaterShield.ActiveRaceState hk ring
  config_eq : race.config = X
  tailLeader : (X (tailCoord ring)).leader = true
  tailBullet : (X (tailCoord ring)).bullet = false
  tailProbe : (X (tailCoord ring)).probe = false
  tailPhase : (X (tailCoord ring)).phase = false
  corridor : ShortGapCorridor ring X race.target

/-- Every physical good renewal is fire-ready; the sanitized phase field is
part of the renewal certificate rather than an external assumption. -/
def GoodFreshRenewal.toFireReady {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Fin n -> State k} {tail : Fin n}
    (G : GoodFreshRenewal hk ring C tail)
    (hrank : 1 < Phi (cutView ring tail C)) :
    FireReady hk ring (cutView ring tail C) where
  race := GoodFreshRenewal.toActiveRaceState G hrank
  config_eq := rfl
  tailLeader := by simpa [cutView] using G.tailLeader
  tailBullet := by simpa [cutView] using G.tailFresh.1
  tailProbe := by simpa [cutView] using G.tailFresh.2
  tailPhase := by simpa [cutView] using G.tailPhase
  corridor := toShortGapCorridor G

/-- Post-fire physical/canonical payload.  The tail is still the same fresh
leader, while the incoming initiator now holds the tracked bullet. -/
structure FiredRaceState {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (X : Fin n -> State k) : Type where
  race : NoDropLaterShield.ActiveRaceState hk ring
  config_eq : race.config = X
  holderBullet : (X (fireEdge ring)).bullet = true
  tailLeader : (X (tailCoord ring)).leader = true
  tailBullet : (X (tailCoord ring)).bullet = false
  tailProbe : (X (tailCoord ring)).probe = false
  tailPhase : (X (tailCoord ring)).phase = false
  corridor : ShortGapCorridor ring X race.target

/-- Selecting the incoming edge at a fire-ready renewal either already lowers
`Phi` (by clearing an exposed probe) or starts the active tracked-bullet race
at the literal protocol successor. -/
theorem FireReady.fire_or_rankDrop {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (F : FireReady hk ring X) :
    let D := Rank.cutSuccessor hk ring X (fireEdge ring)
    Phi D < Phi X ∨ Nonempty (FiredRaceState hk ring D) := by
  rcases F with
    ⟨S, rfl, htailLeader, htailBullet, htailProbe, htailPhase, hcorridor⟩
  let e := fireEdge ring
  let D := Rank.cutSuccessor hk ring S.config e
  have hordinary := fireEdge_nonbarrier hk ring hn3 S.config S.barrier
  have hnotready : ¬ CenteredRenewal.AdvanceReady hk ring S.config e := by
    intro hready
    exact hordinary hready.1
  have hcut : D =
      (CenteredRenewal.protocol k hk).step ring S.config e := by
    dsimp only [D]
    unfold Rank.cutSuccessor
    simp only [hnotready, if_false]
    funext i
    rfl
  have hlocal := fireEdge_exact hk ring hn3 S.config S.barrier
    htailLeader htailBullet
  have hmono := Rank.canonical_phi_step_le hk ring hn3 S.config S.barrier e
  rcases Nat.lt_or_eq_of_le hmono with hdrop | hplateau
  · exact Or.inl hdrop
  · right
    have hnotcross : ¬ BarrierCrossedTarget hk ring S.config e S.target := by
      intro hcross
      exact hnotready hcross.1
    let N := S.next hn3 hndvd e hplateau hnotcross
    have hNtarget : N.target = S.target := by
      simp [N, NoDropLaterShield.ActiveRaceState.next, nextTarget, hnotready]
    have hcorrD : ShortGapCorridor ring D S.target := by
      rw [hcut]
      exact hcorridor.afterNonbarrier hk ring (by omega) hordinary
    refine ⟨{
      race := N
      config_eq := rfl
      holderBullet := ?_
      tailLeader := ?_
      tailBullet := ?_
      tailProbe := ?_
      tailPhase := ?_
      corridor := ?_
    }⟩
    · change (D (fireEdge ring)).bullet = true
      rw [hcut]
      exact hlocal.1
    · change (D (tailCoord ring)).leader = true
      rw [hcut, hlocal.2.2]
      exact htailLeader
    · change (D (tailCoord ring)).bullet = false
      rw [hcut, hlocal.2.2]
      exact htailBullet
    · change (D (tailCoord ring)).probe = false
      rw [hcut, hlocal.2.2]
      exact htailProbe
    · change (D (tailCoord ring)).phase = false
      rw [hcut, hlocal.2.2]
      exact htailPhase
    · simpa [hNtarget] using hcorrD

/-- An edge other than the incoming fire edge and the outgoing barrier edge
does not touch the canonical tail.  This is a literal frame fact for the
packaged centered protocol, independent of any rank hypothesis. -/
theorem irrelevant_tail_frame {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (X : Fin n -> State k) (e : Fin n)
    (hfire : e ≠ fireEdge ring) (hbarrier : e ≠ tailCoord ring) :
    (CenteredRenewal.protocol k hk).step ring X e (tailCoord ring) =
      X (tailCoord ring) := by
  have hresponder : tailCoord ring ≠ ring.rightNeighbor e := by
    intro h
    apply hfire
    calc
      e = ring.leftNeighbor (ring.rightNeighbor e) :=
        (leftNeighbor_rightNeighbor_clean ring e).symm
      _ = ring.leftNeighbor (tailCoord ring) := congrArg _ h.symm
      _ = fireEdge ring := rfl
  simp [PopulationProtocol.step, CenteredRenewal.protocol,
    Ne.symm hbarrier, hresponder]

/-- Every non-fire, non-barrier interaction from a fire-ready renewal either
already lowers `Phi`, or preserves the complete fire-ready payload at the
literal cut successor.  This is the closure consumed by the adaptive
two-target stopping tree. -/
theorem FireReady.irrelevant_or_rankDrop {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    {X : Fin n -> State k} (F : FireReady hk ring X) (e : Fin n)
    (hfire : e ≠ fireEdge ring) (hbarrier : e ≠ tailCoord ring) :
    let D := Rank.cutSuccessor hk ring X e
    Phi D < Phi X ∨ Nonempty (FireReady hk ring D) := by
  rcases F with
    ⟨S, rfl, htailLeader, htailBullet, htailProbe, htailPhase, hcorridor⟩
  let D := Rank.cutSuccessor hk ring S.config e
  have hordinary : ¬ IsBarrier hk (S.config e)
      (S.config (ring.rightNeighbor e)) := by
    intro hb
    exact hbarrier ((S.barrier e).1 hb)
  have hnotready : ¬ CenteredRenewal.AdvanceReady hk ring S.config e := by
    intro hready
    exact hordinary hready.1
  have hcut : D =
      (CenteredRenewal.protocol k hk).step ring S.config e := by
    dsimp only [D]
    unfold Rank.cutSuccessor
    simp only [hnotready, if_false]
    funext i
    rfl
  have htailFrame : D (tailCoord ring) = S.config (tailCoord ring) := by
    rw [hcut]
    exact irrelevant_tail_frame hk ring S.config e hfire hbarrier
  have hmono := Rank.canonical_phi_step_le hk ring hn3 S.config S.barrier e
  rcases Nat.lt_or_eq_of_le hmono with hdrop | hplateau
  · exact Or.inl hdrop
  · right
    have hnotcross : ¬ BarrierCrossedTarget hk ring S.config e S.target := by
      intro hcross
      exact hnotready hcross.1
    let N := S.next hn3 hndvd e hplateau hnotcross
    have hNtarget : N.target = S.target := by
      simp [N, NoDropLaterShield.ActiveRaceState.next, nextTarget, hnotready]
    have hcorrD : ShortGapCorridor ring D S.target := by
      rw [hcut]
      exact hcorridor.afterNonbarrier hk ring (by omega) hordinary
    refine ⟨{
      race := N
      config_eq := rfl
      tailLeader := ?_
      tailBullet := ?_
      tailProbe := ?_
      tailPhase := ?_
      corridor := ?_
    }⟩
    · change (D (tailCoord ring)).leader = true
      rw [htailFrame]
      exact htailLeader
    · change (D (tailCoord ring)).bullet = false
      rw [htailFrame]
      exact htailBullet
    · change (D (tailCoord ring)).probe = false
      rw [htailFrame]
      exact htailProbe
    · change (D (tailCoord ring)).phase = false
      rw [htailFrame]
      exact htailPhase
    · simpa [hNtarget] using hcorrD

/-! ## Payload-preserving fire-before-arm stage -/

/-- Physical proof state for the first probabilistic stage at one fixed rank
`r`.  Favorable terminals retain either the strict-drop configuration or the
literal post-fire race payload; the barrier-first terminal retains its literal
configuration as well. -/
inductive FireProofState {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (r : Nat) where
  | active (X : Fin n -> State k) (ready : FireReady hk ring X)
      (rank_eq : Phi X = r)
  | fired (X : Fin n -> State k) (race : FiredRaceState hk ring X)
      (rank_eq : Phi X = r)
  | dropped (X : Fin n -> State k) (rank_lt : Phi X < r)
  | missed (X : Fin n -> State k)

def FireProofState.configuration {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : FireProofState hk ring r -> Fin n -> State k
  | .active X _ _ => X
  | .fired X _ _ => X
  | .dropped X _ => X
  | .missed X => X

def FireProofState.isActive {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : FireProofState hk ring r -> Bool
  | .active _ _ _ => true
  | _ => false

def FireProofState.isFavorable {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : FireProofState hk ring r -> Bool
  | .fired _ _ _ => true
  | .dropped _ _ => true
  | _ => false

def FireProofState.isMissed {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} : FireProofState hk ring r -> Bool
  | .missed _ => true
  | _ => false

/-- Total literal scheduler transition for the fire stage.  Terminal proof
states are absorbing.  At an active state the protocol is executed first;
only then is the successor classified as rank drop, fired race, missed arm,
or another fire-ready state. -/
noncomputable def FireProofState.next {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n) :
    FireProofState hk ring r -> Fin n -> FireProofState hk ring r
  | s@(.fired _ _ _), _ => s
  | s@(.dropped _ _), _ => s
  | s@(.missed _), _ => s
  | .active X F hrank, e =>
      let D := Rank.cutSuccessor hk ring X e
      have hbarX : CanonicalOneBarrier hk ring X := by
        simpa [F.config_eq] using F.race.barrier
      if hdrop : Phi D < r then
        .dropped D hdrop
      else if hfire : e = fireEdge ring then
        let result := F.fire_or_rankDrop hn3 hndvd
        have hnotLocal : ¬ Phi D < Phi X := by simpa [hrank] using hdrop
        have result' : Phi D < Phi X ∨
            Nonempty (FiredRaceState hk ring D) := by
          simpa [D, hfire] using result
        have hfired : Nonempty (FiredRaceState hk ring D) :=
          result'.resolve_left hnotLocal
        have hle := Rank.canonical_phi_step_le hk ring hn3 X hbarX e
        have heq : Phi D = r := Nat.le_antisymm
          (by simpa [D, hrank] using hle) (Nat.le_of_not_gt hdrop)
        .fired D (Classical.choice hfired) heq
      else if hbarrier : e = tailCoord ring then
        .missed D
      else
        let result := F.irrelevant_or_rankDrop hn3 hndvd e hfire hbarrier
        have hnotLocal : ¬ Phi D < Phi X := by simpa [hrank] using hdrop
        have hready : Nonempty (FireReady hk ring D) :=
          result.resolve_left hnotLocal
        have hle := Rank.canonical_phi_step_le hk ring hn3 X hbarX e
        have heq : Phi D = r := Nat.le_antisymm
          (by simpa [D, hrank] using hle) (Nat.le_of_not_gt hdrop)
        .active D (Classical.choice hready) heq

/-- The proof-state transition carries the literal protocol successor at
every active node.  The apparent cut rotation cannot occur in this stage:
the fresh tail has phase zero, and every non-tail edge is ordinary. -/
theorem FireProofState.configuration_next {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : FireProofState hk ring r) (e : Fin n)
    (hactive : s.isActive = true) :
    (s.next hn3 hndvd e).configuration =
      (CenteredRenewal.protocol k hk).step ring s.configuration e := by
  cases s with
  | fired X F hr => simp [FireProofState.isActive] at hactive
  | dropped X h => simp [FireProofState.isActive] at hactive
  | missed X => simp [FireProofState.isActive] at hactive
  | active X F hr =>
      have hbarX : CanonicalOneBarrier hk ring X := by
        simpa [F.config_eq] using F.race.barrier
      have hnotready : ¬ CenteredRenewal.AdvanceReady hk ring X e := by
        intro hready
        have he : e = tailCoord ring := (hbarX e).1 hready.1
        subst e
        have hphase := hready.2
        rw [F.tailPhase] at hphase
        contradiction
      have hcut : Rank.cutSuccessor hk ring X e =
          (CenteredRenewal.protocol k hk).step ring X e := by
        unfold Rank.cutSuccessor
        simp only [hnotready, if_false]
        funext i
        rfl
      simp only [FireProofState.next]
      split
      · simp only [FireProofState.configuration]
        exact hcut
      · split
        · simp only [FireProofState.configuration]
          exact hcut
        · split
          · simp only [FireProofState.configuration]
            exact hcut
          · simp only [FireProofState.configuration]
            exact hcut

/-- Convert the payload-preserving physical state into the absorbing
success/failure API used by the finite scheduler tree. -/
def FireProofState.stopNode {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} :
    FireProofState hk ring r ->
      FiniteUniformStoppingTree.StopNode (FireProofState hk ring r)
  | s@(.active _ _ _) => .active s
  | .fired _ _ _ => .success
  | .dropped _ _ => .success
  | .missed _ => .failure

noncomputable def FireProofState.stoppedStep {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : FireProofState hk ring r) (e : Fin n) :
    FiniteUniformStoppingTree.StopNode (FireProofState hk ring r) :=
  (s.next hn3 hndvd e).stopNode

@[simp] theorem FireProofState.stopNode_eq_success_iff {n k r : Nat}
    {hk : 0 < k} {ring : DirectedRing n} (s : FireProofState hk ring r) :
    s.stopNode = .success ↔ s.isFavorable = true := by
  cases s <;> simp [FireProofState.stopNode, FireProofState.isFavorable]

@[simp] theorem FireProofState.stopNode_eq_failure_iff {n k r : Nat}
    {hk : 0 < k} {ring : DirectedRing n} (s : FireProofState hk ring r) :
    s.stopNode = .failure ↔ s.isMissed = true := by
  cases s <;> simp [FireProofState.stopNode, FireProofState.isMissed]

/-- The physical fire target always becomes a favorable terminal: either the
same interaction strictly drops rank, or it returns the concrete fired race. -/
theorem FireProofState.stoppedStep_fire {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (X : Fin n -> State k) (F : FireReady hk ring X)
    (hrank : Phi X = r) :
    FireProofState.stoppedStep hn3 hndvd (.active X F hrank)
      (fireEdge ring) = .success := by
  simp only [FireProofState.stoppedStep, FireProofState.next]
  split
  · rfl
  · split
    · rfl
    · contradiction

/-- The barrier target is terminal on its first selection.  If that phase-zero
interaction unexpectedly already lowers rank it is favorable; otherwise it
is the barrier-first loss. -/
theorem FireProofState.stoppedStep_barrier_terminal {n k r : Nat}
    {hk : 0 < k} {ring : DirectedRing n} (hn3 : 3 ≤ n)
    (hndvd : ¬ k ∣ n) (X : Fin n -> State k)
    (F : FireReady hk ring X) (hrank : Phi X = r) :
    FireProofState.stoppedStep hn3 hndvd (.active X F hrank)
        (tailCoord ring) = .success ∨
      FireProofState.stoppedStep hn3 hndvd (.active X F hrank)
        (tailCoord ring) = .failure := by
  simp only [FireProofState.stoppedStep, FireProofState.next]
  split
  · exact Or.inl rfl
  · split
    · rename_i hfire
      exact False.elim (fireEdge_ne_barrierEdge ring hn3 hfire.symm)
    · split
      · exact Or.inr rfl
      · contradiction

/-- Every irrelevant physical edge either produces an extra favorable rank
drop or remains an active fire-ready payload.  It can never enter the missed
terminal. -/
theorem FireProofState.stoppedStep_other {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (X : Fin n -> State k) (F : FireReady hk ring X)
    (hrank : Phi X = r) (e : Fin n)
    (hfire : e ≠ fireEdge ring) (hbarrier : e ≠ tailCoord ring) :
    FireProofState.stoppedStep hn3 hndvd (.active X F hrank) e = .success ∨
      ∃ X' F' hrank',
        FireProofState.stoppedStep hn3 hndvd (.active X F hrank) e =
          .active (.active X' F' hrank') := by
  let D := Rank.cutSuccessor hk ring X e
  by_cases hdrop : Phi D < r
  · left
    simp [FireProofState.stoppedStep, FireProofState.next, D, hdrop]
    rfl
  · have hbarX : CanonicalOneBarrier hk ring X := by
      simpa [F.config_eq] using F.race.barrier
    have hle := Rank.canonical_phi_step_le hk ring hn3 X hbarX e
    have heq : Phi D = r := Nat.le_antisymm
      (by simpa [D, hrank] using hle) (Nat.le_of_not_gt hdrop)
    right
    simp [FireProofState.stoppedStep, FireProofState.next, D, hdrop,
      hfire, hbarrier]
    refine ⟨_, _, ?_, rfl⟩
    exact heq

/-! ## Exact finite-tree quarter bound with terminal payload -/

open FiniteUniformStoppingTree
open PayloadFiniteStoppingTree

/-- Payload-retaining version of the stopped firing transition. -/
noncomputable def FireProofState.payloadStep {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : FireProofState hk ring r) (e : Fin n) :
    PayloadNode (FireProofState hk ring r) (FireProofState hk ring r)
      (FireProofState hk ring r) :=
  match s.next hn3 hndvd e with
  | a@(.active _ _ _) => .active a
  | f@(.fired _ _ _) => .success f
  | d@(.dropped _ _) => .success d
  | m@(.missed _) => .failure m

@[simp] theorem FireProofState.erase_payloadStep {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : FireProofState hk ring r) (e : Fin n) :
    (s.payloadStep hn3 hndvd e).erase = s.stoppedStep hn3 hndvd e := by
  unfold FireProofState.payloadStep FireProofState.stoppedStep
  cases h : s.next hn3 hndvd e <;> rfl

@[simp] theorem FireProofState.eraseStep_payloadStep {n k r : Nat}
    {hk : 0 < k} {ring : DirectedRing n} (hn3 : 3 ≤ n)
    (hndvd : ¬ k ∣ n) :
    (PayloadFiniteStoppingTree.eraseStep
        (FireProofState.payloadStep (hk := hk) (ring := ring)
          (r := r) hn3 hndvd) :
      FireProofState hk ring r -> Fin n ->
        StopNode (FireProofState hk ring r)) =
      (FireProofState.stoppedStep (hk := hk) (ring := ring)
        (r := r) hn3 hndvd :
      FireProofState hk ring r -> Fin n ->
        StopNode (FireProofState hk ring r)) := by
  funext s e
  exact FireProofState.erase_payloadStep hn3 hndvd s e

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

/-- Constant active potential used for the fire-before-arm waiting time. -/
def firePotential {S : Type} (n : Nat) : StopNode S -> Nat
  | .active _ => n
  | .success => 0
  | .failure => 0

theorem FireProofState.stoppedStep_fire_all_terminal {n k r : Nat}
    {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : FireProofState hk ring r) :
    s.stoppedStep hn3 hndvd (fireEdge ring) = .success ∨
      s.stoppedStep hn3 hndvd (fireEdge ring) = .failure := by
  cases s with
  | active X F hr => exact Or.inl (stoppedStep_fire hn3 hndvd X F hr)
  | fired X F hr => exact Or.inl rfl
  | dropped X h => exact Or.inl rfl
  | missed X => exact Or.inr rfl

theorem FireProofState.stoppedStep_barrier_all_terminal
    {n k r : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : FireProofState hk ring r) :
    s.stoppedStep hn3 hndvd (tailCoord ring) = .success ∨
      s.stoppedStep hn3 hndvd (tailCoord ring) = .failure := by
  cases s with
  | active X F hr => exact stoppedStep_barrier_terminal hn3 hndvd X F hr
  | fired X F hr => exact Or.inl rfl
  | dropped X h => exact Or.inl rfl
  | missed X => exact Or.inr rfl

/-- The two distinguished physical children have zero residual potential;
every other child has residual at most `n`. -/
theorem firePotential_child_sum_le {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : FireProofState hk ring r) :
    (List.ofFn (fun e : Fin n =>
      firePotential n (s.stoppedStep hn3 hndvd e))).sum ≤
        (n - 2) * n := by
  let a := fireEdge ring
  let b := tailCoord ring
  let upper : Fin n -> Nat := fun e =>
    if e = a then 0 else if e = b then 0 else n
  have hab : a ≠ b := fireEdge_ne_barrierEdge ring hn3
  have hpoint : forall e : Fin n,
      firePotential n (s.stoppedStep hn3 hndvd e) ≤ upper e := by
    intro e
    by_cases hea : e = a
    · subst e
      rcases FireProofState.stoppedStep_fire_all_terminal
        hn3 hndvd s with h | h <;> rw [h] <;>
        simp [firePotential, upper, a]
    · by_cases heb : e = b
      · subst e
        rcases FireProofState.stoppedStep_barrier_all_terminal
          hn3 hndvd s with h | h <;> rw [h] <;>
          simp [firePotential, upper, hea, b]
      · cases hstep : s.stoppedStep hn3 hndvd e <;>
          simp [firePotential, upper, hea, heb]
  have hsumLe := ofFn_sum_le
    (fun e : Fin n => firePotential n (s.stoppedStep hn3 hndvd e))
    upper hpoint
  have hsumUpper : (List.ofFn upper).sum = (n - 2) * n := by
    have hsum := sum_two_exceptions
      (List.ofFn (fun i : Fin n => i)) a b upper n
      (nodup_ofFn_fin n)
      (by rw [List.mem_ofFn]; exact ⟨a, rfl⟩)
      (by rw [List.mem_ofFn]; exact ⟨b, rfl⟩) hab (by
        intro e _ hea heb
        simp [upper, hea, heb])
    simpa [upper, hab, List.map_ofFn, Function.comp_def] using hsum
  rwa [hsumUpper] at hsumLe

/-- Scale-two Bellman certificate for the payload-preserving physical firing
stage.  Extra rank-drop children only reduce the residual potential. -/
theorem fire_natBellmanSuperSolution {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n) :
    NatBellmanSuperSolution
      (FireProofState.stoppedStep (r := r) hn3 hndvd) 2
      (firePotential (S := FireProofState hk ring r) n) := by
  refine ⟨rfl, rfl, ?_⟩
  intro s
  have hsum := firePotential_child_sum_le hn3 hndvd s
  change 2 * n +
      (List.ofFn (fun e : Fin n =>
        firePotential n (s.stoppedStep hn3 hndvd e))).sum ≤ n * n
  calc
    2 * n +
        (List.ofFn (fun e : Fin n =>
          firePotential n (s.stoppedStep hn3 hndvd e))).sum ≤
        2 * n + (n - 2) * n := Nat.add_le_add_left hsum _
    _ = (2 + (n - 2)) * n := (Nat.add_mul 2 (n - 2) n).symm
    _ = n * n := by rw [Nat.add_sub_of_le (by omega : 2 ≤ n)]

theorem fire_two_mul_truncatedCost_le {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : FireProofState hk ring r) (T : Nat) :
    2 * truncatedActiveCostNumerator
        (FireProofState.stoppedStep (r := r) hn3 hndvd) (.active s) T ≤
      n ^ T * n := by
  simpa [firePotential] using
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (FireProofState.stoppedStep (r := r) hn3 hndvd) 2
      (firePotential (S := FireProofState hk ring r) n)
      (fire_natBellmanSuperSolution hn3 hndvd) (.active s) T

/-- At horizon `2*n`, at most one quarter of the firing tree is unresolved. -/
theorem fire_four_mul_activeCount_le {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (s : FireProofState hk ring r) :
    4 * activeCount (FireProofState.stoppedStep (r := r) hn3 hndvd)
        (.active s) (2 * n) ≤ n ^ (2 * n) := by
  let step : FireProofState hk ring r -> Fin n ->
      StopNode (FireProofState hk ring r) :=
    FireProofState.stoppedStep hn3 hndvd
  have hcost := fire_two_mul_truncatedCost_le hn3 hndvd s (2 * n)
  have hlive :=
    PredictableTwoTargetFiniteTree.horizon_mul_activeCount_le_truncatedActiveCost
    step (.active s) (2 * n)
  have hscaled := Nat.mul_le_mul_left 2 hlive
  have hcancel : n * (4 * activeCount step (.active s) (2 * n)) ≤
      n * n ^ (2 * n) := by
    calc
      n * (4 * activeCount step (.active s) (2 * n)) =
          2 * ((2 * n) * activeCount step (.active s) (2 * n)) := by
            rw [show 4 = 2 * 2 by decide]
            ac_rfl
      _ ≤ 2 * truncatedActiveCostNumerator step (.active s) (2 * n) :=
        hscaled
      _ ≤ n ^ (2 * n) * n := hcost
      _ = n * n ^ (2 * n) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hcancel (by omega)

/-- Extra early rank drops can only favor the first-hit side: from every
fire-ready active payload, failed mass is bounded by successful mass at every
horizon. -/
theorem fire_failureCount_le_successCount {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n) :
    forall (X : Fin n -> State k) (F : FireReady hk ring X)
      (hrank : Phi X = r) T,
      failureCount (FireProofState.stoppedStep (r := r) hn3 hndvd)
          (.active (.active X F hrank)) T ≤
        successCount (FireProofState.stoppedStep (r := r) hn3 hndvd)
          (.active (.active X F hrank)) T := by
  intro X F hrank T
  induction T generalizing X with
  | zero => exact Nat.le_refl _
  | succ T ih =>
      let s : FireProofState hk ring r := .active X F hrank
      let step : FireProofState hk ring r -> Fin n ->
          StopNode (FireProofState hk ring r) :=
        FireProofState.stoppedStep hn3 hndvd
      let fail : Fin n -> Nat := fun e =>
        treeWeight step failureWeight (step s e) T
      let succ : Fin n -> Nat := fun e =>
        treeWeight step successWeight (step s e) T
      let a := fireEdge ring
      let b := tailCoord ring
      let swapped : Fin n -> Nat := fun e =>
        if e = a then succ b else if e = b then succ a else succ e
      have hab : a ≠ b := fireEdge_ne_barrierEdge ring hn3
      have hswap : (List.ofFn swapped).sum = (List.ofFn succ).sum := by
        apply PredictableTwoTargetFiniteTree.ofFn_sum_eq_of_swap_two
          a b swapped succ hab
        · simp [swapped, hab]
        · simp [swapped, hab.symm]
        · intro e hea heb
          simp [swapped, hea, heb]
      have hpoint : forall e : Fin n, fail e ≤ swapped e := by
        intro e
        by_cases hea : e = a
        · subst e
          have hfire := FireProofState.stoppedStep_fire
            hn3 hndvd X F hrank
          simp only [swapped, if_pos rfl]
          change treeWeight step failureWeight (step s a) T ≤
            treeWeight step successWeight (step s b) T
          dsimp [step, s, a, b]
          rw [hfire, treeWeight_success]
          simp [failureWeight]
        · by_cases heb : e = b
          · subst e
            have hfire : step s a = .success := by
              exact FireProofState.stoppedStep_fire hn3 hndvd X F hrank
            dsimp [step, s, a] at hfire
            rcases FireProofState.stoppedStep_barrier_all_terminal
              hn3 hndvd s with hbar | hbar
            · simp only [swapped, if_neg hab.symm, if_pos rfl]
              change treeWeight step failureWeight (step s b) T ≤
                treeWeight step successWeight (step s a) T
              dsimp [step, s, a, b]
              rw [hbar, hfire, treeWeight_success, treeWeight_success]
              simp [failureWeight, successWeight]
            · simp only [swapped, if_neg hab.symm, if_pos rfl]
              change treeWeight step failureWeight (step s b) T ≤
                treeWeight step successWeight (step s a) T
              dsimp [step, s, a, b]
              rw [hbar, hfire, treeWeight_failure, treeWeight_success]
              simp [failureWeight, successWeight]
          · rcases FireProofState.stoppedStep_other hn3 hndvd X F hrank e
              hea heb with hsuccess | ⟨X', F', hrank', hactive⟩
            · simp only [swapped, if_neg hea, if_neg heb]
              change treeWeight step failureWeight (step s e) T ≤
                treeWeight step successWeight (step s e) T
              dsimp [step, s]
              rw [hsuccess, treeWeight_success, treeWeight_success]
              simp [failureWeight, successWeight]
            · simp only [swapped, if_neg hea, if_neg heb]
              change treeWeight step failureWeight (step s e) T ≤
                treeWeight step successWeight (step s e) T
              dsimp [step, s]
              rw [hactive]
              simpa [failureCount, successCount] using ih X' F' hrank'
      have hsum := ofFn_sum_le fail swapped hpoint
      change (List.ofFn fail).sum ≤ (List.ofFn succ).sum
      calc
        (List.ofFn fail).sum ≤ (List.ofFn swapped).sum := hsum
        _ = (List.ofFn succ).sum := hswap

/-- Payload-retaining `1/4` firing theorem at the actual first terminal. -/
theorem freshFire_success_quarter_by_two_mul {n k r : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (X : Fin n -> State k) (F : FireReady hk ring X)
    (hrank : Phi X = r) :
    n ^ (2 * n) ≤ 4 *
      PayloadFiniteStoppingTree.successMass
        (FireProofState.payloadStep (r := r) hn3 hndvd)
        (.active (.active X F hrank)) (2 * n) := by
  let s : FireProofState hk ring r := .active X F hrank
  let stopped : FireProofState hk ring r -> Fin n ->
      StopNode (FireProofState hk ring r) :=
    FireProofState.stoppedStep hn3 hndvd
  have hactive := fire_four_mul_activeCount_le hn3 hndvd s
  have hfail := fire_failureCount_le_successCount hn3 hndvd X F hrank (2 * n)
  have hpartition := node_count_partition stopped (.active s) (2 * n)
  have hquarter : n ^ (2 * n) ≤
      4 * successCount stopped (.active s) (2 * n) := by
    dsimp [stopped, s] at hactive hfail hpartition ⊢
    omega
  rw [PayloadFiniteStoppingTree.successMass_eq_successCount]
  rw [FireProofState.eraseStep_payloadStep (hk := hk) (ring := ring)]
  exact hquarter

end RankBlockTrial
end CenteredRenewal
end AAFJPK
