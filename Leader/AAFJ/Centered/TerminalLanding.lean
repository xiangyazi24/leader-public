import Leader.AAFJ.Centered.ZeroLeaderTrial
import Leader.Core.FiniteUniformStoppingTree
import Leader.AAFJ.Centered.NoDropLaterShield
import Leader.AAFJ.Centered.OneBarrierCleanup

/-!
# Literal terminal landing for centered AAFJ

The stopped zero-leader renewal process reaches a concrete configuration with
a probe on the canonical barrier tail.  This module retains that configuration
and proves that one further interaction of the barrier edge reaches the exact
`CanonicalClean` predicate, in both phase branches of the centered protocol.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace TerminalLanding

open BarrierAlgebra
open SingleBarrierSanitation
open OneBarrierCleanup
open ZeroLeaderTrial

set_option autoImplicit false

/-- The concrete endpoint retained after the local zero-leader trial succeeds. -/
structure TailProbeReady {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n -> State k) : Prop where
  canonical : CanonicalOneBarrier hk ring X
  zeroLeaders : forall i : Fin n, (X i).leader = false
  tailBullet : (X (tailCoord ring)).bullet = false
  tailProbe : (X (tailCoord ring)).probe = true

/-- A top progress hit retains all the data needed by the final barrier hit. -/
theorem Prepared.progress_top_tailProbeReady
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (S : Prepared hk ring X)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (htop : S.maxProbe.val = n - 2) :
    TailProbeReady hk ring
      (trialStep hk ring X (progressEdge S.maxProbe)) := by
  let D := trialStep hk ring X (progressEdge S.maxProbe)
  have hn2 : 1 < n := by omega
  have hraw : D = rawStep hk ring X (progressEdge S.maxProbe) :=
    S.trialStep_eq_raw_of_ne_barrier _ S.progress_ne_barrier
  have hterminal := S.progress_top_terminal_success hn3 htop
  refine
    { canonical := NoDropLaterShield.canonicalOneBarrier_cutSuccessor
        hk ring hn2 X (progressEdge S.maxProbe) hndvd S.canonical
      zeroLeaders := ?_
      tailBullet := hterminal.2.1
      tailProbe := hterminal.1 }
  intro i
  change (D i).leader = false
  rw [hraw]
  exact S.progress_raw_zeroLeaders hn2 i

private theorem tail_ne_head {n : Nat} (ring : DirectedRing n)
    (hn2 : 1 < n) :
    tailCoord ring ≠ ring.rightNeighbor (tailCoord ring) := by
  exact Ne.symm (rightNeighbor_ne_self ring hn2 (tailCoord ring))

/-- Literal pair written by the final barrier hit. -/
theorem TailProbeReady.barrier_raw_endpoints
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (S : TailProbeReady hk ring X)
    (hn2 : 1 < n) :
    let D := rawStep hk ring X (barrierEdge ring)
    (D (tailCoord ring)).leader = true ∧
      (D (tailCoord ring)).bullet = false ∧
      (D (tailCoord ring)).probe = false ∧
      (forall i : Fin n, i ≠ tailCoord ring -> (D i).leader = false) := by
  let t := tailCoord ring
  let h := ring.rightNeighbor t
  have hbar : IsBarrier hk (X t) (X h) := (S.canonical t).2 rfl
  have hre : h ≠ t := rightNeighbor_ne_self ring hn2 t
  have htProbe : (X t).probe = true := by simpa [t] using S.tailProbe
  have htBullet : (X t).bullet = false := by simpa [t] using S.tailBullet
  have hconverted : probeHitsBarrier (X t) =
      { X t with leader := true, probe := false } :=
    probeHitsBarrier_of_probe _ htProbe
  have hconvertedLeader : (probeHitsBarrier (X t)).leader = true := by
    rw [hconverted]
  have hconvertedBullet : (probeHitsBarrier (X t)).bullet = false := by
    rw [hconverted]
    exact htBullet
  have hconvertedProbe : (probeHitsBarrier (X t)).probe = false := by
    rw [hconverted]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (rawStep hk ring X t t).leader = true
    rw [rawStep_at_initiator]
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    cases hphase : (X t).phase <;>
      simpa [CenteredRenewal.barrierStep, hphase] using hconvertedLeader
  · change (rawStep hk ring X t t).bullet = false
    rw [rawStep_at_initiator]
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    cases hphase : (X t).phase <;>
      simpa [CenteredRenewal.barrierStep, hphase] using hconvertedBullet
  · change (rawStep hk ring X t t).probe = false
    rw [rawStep_at_initiator]
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    cases hphase : (X t).phase <;>
      simpa [CenteredRenewal.barrierStep, hphase] using hconvertedProbe
  · intro i hit
    by_cases hih : i = h
    · subst i
      change (rawStep hk ring X t h).leader = false
      rw [rawStep_at_responder hk ring hn2]
      rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
      cases hphase : (X t).phase <;>
        simp [CenteredRenewal.barrierStep, hphase, hconverted,
          S.zeroLeaders]
    · change (rawStep hk ring X t i).leader = false
      rw [rawStep_frame hk ring X t i hit hih]
      exact S.zeroLeaders i

/-- If the final tail is unarmed, its hit creates the unique leader at the
same canonical tail and every remaining mark is automatically earlier. -/
theorem TailProbeReady.phaseZero_barrier_clean
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (S : TailProbeReady hk ring X)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (hphase : (X (tailCoord ring)).phase = false) :
    CanonicalClean hk ring
      (Rank.cutSuccessor hk ring X (barrierEdge ring)) (tailCoord ring) := by
  have hn2 : 1 < n := by omega
  let D := rawStep hk ring X (barrierEdge ring)
  have hnotReady : ¬ AdvanceReady hk ring X (barrierEdge ring) := by
    intro h
    exact Bool.noConfusion (h.2.symm.trans hphase)
  have hcut : Rank.cutSuccessor hk ring X (barrierEdge ring) = D := by
    unfold Rank.cutSuccessor
    simp only [hnotReady, if_false]
    rfl
  have hend := S.barrier_raw_endpoints hn2
  rw [hcut]
  refine ⟨?_, hend.1, ?_, ?_⟩
  · simpa [hcut] using
      NoDropLaterShield.canonicalOneBarrier_cutSuccessor
        hk ring hn2 X (barrierEdge ring) hndvd S.canonical
  · intro i hi
    by_cases hit : i = tailCoord ring
    · exact hit
    · rw [hend.2.2.2 i hit] at hi
      contradiction
  · intro i hmarked
    by_cases hit : i = tailCoord ring
    · subst i
      rcases hmarked with hb | hp
      · rw [hend.2.1] at hb
        contradiction
      · rw [hend.2.2.1] at hp
        contradiction
    · change i.val < n - 1
      have hi := i.isLt
      have hine : i.val ≠ n - 1 := by
        intro hv
        apply hit
        apply Fin.ext
        exact hv
      omega

/-- If the final tail is armed, the same hit advances the barrier.  The old
tail leader becomes coordinate `n-2`; the old head becomes the new sanitized
tail, so every remaining mark is strictly before that leader. -/
theorem TailProbeReady.phaseOne_barrier_clean
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (S : TailProbeReady hk ring X)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (hphase : (X (tailCoord ring)).phase = true) :
    CanonicalClean hk ring
      (Rank.cutSuccessor hk ring X (barrierEdge ring))
      (ring.leftNeighbor (tailCoord ring)) := by
  have hn2 : 1 < n := by omega
  let t := tailCoord ring
  let e := ring.leftNeighbor t
  let R := rawStep hk ring X (barrierEdge ring)
  let D := Rank.cutSuccessor hk ring X (barrierEdge ring)
  have hbar : IsBarrier hk (X (barrierEdge ring))
      (X (ring.rightNeighbor (barrierEdge ring))) :=
    (S.canonical (barrierEdge ring)).2 rfl
  have hbPhase : (X (barrierEdge ring)).phase = true := by
    simpa [barrierEdge] using hphase
  have hready : AdvanceReady hk ring X (barrierEdge ring) :=
    ⟨hbar, hbPhase⟩
  have hcut : D = rotateCut ring R := by
    simp [D, R, Rank.cutSuccessor, rawStep, hready]
  have hend := S.barrier_raw_endpoints hn2
  have heRight : ring.rightNeighbor e = t := by
    exact rightNeighbor_leftNeighbor_clean ring t
  have heVal : e.val = n - 2 := by
    have htailVal : t.val = n - 1 := rfl
    have hpos : 0 < t.val := by omega
    have hleft := leftNeighbor_val_of_pos ring t hpos
    change e.val = t.val - 1 at hleft
    omega
  have hnewTail :
      (R (ring.rightNeighbor (tailCoord ring))).bullet = false ∧
        (R (ring.rightNeighbor (tailCoord ring))).probe = false := by
    have hresp := rawStep_at_responder hk ring hn2 X (barrierEdge ring)
    have htransition := CenteredRenewal.transition_of_barrier hk _ _ hbar
    constructor
    · change (rawStep hk ring X (barrierEdge ring)
          (ring.rightNeighbor (barrierEdge ring))).bullet = false
      rw [hresp, htransition]
      simp [CenteredRenewal.barrierStep, hbPhase]
    · change (rawStep hk ring X (barrierEdge ring)
          (ring.rightNeighbor (barrierEdge ring))).probe = false
      rw [hresp, htransition]
      simp [CenteredRenewal.barrierStep, hbPhase]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact NoDropLaterShield.canonicalOneBarrier_cutSuccessor
      hk ring hn2 X (barrierEdge ring) hndvd S.canonical
  · change (D e).leader = true
    rw [hcut]
    change (R (ring.rightNeighbor e)).leader = true
    rw [heRight]
    exact hend.1
  · intro i hi
    change (D i).leader = true at hi
    rw [hcut] at hi
    change (R (ring.rightNeighbor i)).leader = true at hi
    have hold : ring.rightNeighbor i = t := by
      by_cases hEq : ring.rightNeighbor i = t
      · exact hEq
      · rw [hend.2.2.2 _ hEq] at hi
        contradiction
    exact rightNeighbor_injective ring (hold.trans heRight.symm)
  · intro i hmarked
    change Marked (D i) at hmarked
    by_cases hie : i = e
    · subst i
      exfalso
      rw [hcut] at hmarked
      change Marked (R (ring.rightNeighbor e)) at hmarked
      rw [heRight] at hmarked
      rcases hmarked with hb | hp
      · rw [hend.2.1] at hb
        contradiction
      · rw [hend.2.2.1] at hp
        contradiction
    · by_cases hit : i = tailCoord ring
      · subst i
        exfalso
        rw [hcut] at hmarked
        change Marked
          (R (ring.rightNeighbor (tailCoord ring))) at hmarked
        rcases hmarked with hb | hp
        · have hfalse :
              (R (ring.rightNeighbor (tailCoord ring))).bullet = false :=
              hnewTail.1
          rw [hfalse] at hb
          contradiction
        · have hfalse :
              (R (ring.rightNeighbor (tailCoord ring))).probe = false :=
              hnewTail.2
          rw [hfalse] at hp
          contradiction
      · change i.val < e.val
        rw [heVal]
        have hiLt := i.isLt
        have hiNeTop : i.val ≠ n - 1 := by
          intro hv
          apply hit
          apply Fin.ext
          exact hv
        have hiNePred : i.val ≠ n - 2 := by
          intro hv
          apply hie
          apply Fin.ext
          simpa [heVal] using hv
        omega

/-- One literal barrier interaction from a retained renewal success always
lands in `CanonicalClean`; the witness depends only on the current phase. -/
theorem TailProbeReady.barrier_reaches_canonicalClean
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {X : Fin n -> State k} (S : TailProbeReady hk ring X)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    exists ell : Fin n,
      CanonicalClean hk ring
        (Rank.cutSuccessor hk ring X (barrierEdge ring)) ell := by
  cases hphase : (X (tailCoord ring)).phase
  · exact ⟨tailCoord ring, S.phaseZero_barrier_clean hn3 hndvd hphase⟩
  · exact ⟨ring.leftNeighbor (tailCoord ring),
      S.phaseOne_barrier_clean hn3 hndvd hphase⟩

end TerminalLanding
end CenteredRenewal
end AAFJPK
