import Leader.AAFJ.Protocol
import Leader.AAFJ.NonbarrierWord
import Leader.AAFJ.OneBarrier.Sanitation
import Leader.AAFJ.OneBarrier.Sweep
import Leader.AAFJ.OneBarrier.PushLeaders




set_option autoImplicit false




namespace AAFJPK.OriginalOneBarrierSweptFresh




open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord




/-- The original fresh tail leader B and every site strictly after it in the
current barrier cut form a mark-free swept suffix. -/
def SweptFresh {n k : Nat} (ring : DirectedRing n)
    (B b : Fin n) (C : Fin n → State k) : Prop :=
  let j := cutCoord ring b B
  (C B).leader = true ∧
    (C B).bullet = false ∧
    (C B).probe = false ∧
    ∀ q : Fin n, j.val < q.val →
      let x := cutPos ring b q
      (C x).leader = false ∧
        (C x).bullet = false ∧
        (C x).probe = false




/-- Canonical-cut version used internally by the one-step proof. -/
private def SweptFreshCut {n k : Nat} (X : Fin n → State k)
    (t : Fin n) : Prop :=
  (X t).leader = true ∧
    (X t).bullet = false ∧
    (X t).probe = false ∧
    ∀ q : Fin n, t.val < q.val →
      (X q).leader = false ∧
        (X q).bullet = false ∧
        (X q).probe = false




private theorem sweptFresh_iff_cut {n k : Nat}
    (ring : DirectedRing n) (B b : Fin n) (C : Fin n → State k) :
    SweptFresh ring B b C ↔
      SweptFreshCut (cutView ring b C) (cutCoord ring b B) := by
  constructor
  · intro h
    dsimp [SweptFresh] at h
    dsimp [SweptFreshCut]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [cutView] using h.1
    · simpa [cutView] using h.2.1
    · simpa [cutView] using h.2.2.1
    · intro q hq
      have hx := h.2.2.2 q hq
      simpa [cutView] using hx
  · intro h
    dsimp [SweptFreshCut] at h
    dsimp [SweptFresh]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [cutView] using h.1
    · simpa [cutView] using h.2.1
    · simpa [cutView] using h.2.2.1
    · intro q hq
      have hx := h.2.2.2 q hq
      simpa [cutView] using hx




private theorem step_other_state {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (e i : Fin n) (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    ((protocol k hk).step ring C e) i = C i := by
  simp [PopulationProtocol.step, protocol, hie, hir]




private theorem canonical_nonbarrier_of_ne_tail {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n → State k) (hbar : CanonicalOneBarrier hk ring X)
    (e : Fin n) (he : e ≠ tailCoord ring) :
    ¬ IsBarrier hk (X e) (X (ring.rightNeighbor e)) := by
  intro hb
  exact he ((hbar e).1 hb)




private theorem transition_barrier_left_fields_of_probe_false {k : Nat}
    (hk : 0 < k) (u v : State k)
    (hbar : IsBarrier hk u v) (hprobe : u.probe = false) :
    (transition hk u v).1.leader = u.leader ∧
      (transition hk u v).1.bullet = u.bullet ∧
      (transition hk u v).1.probe = false := by
  rw [transition_of_barrier hk u v hbar]
  cases hphase : u.phase <;>
    cases hvprobe : v.probe <;>
      cases hvleader : v.leader <;>
        simp [barrierStep, probeHitsBarrier, hprobe, hphase,
          hvprobe, hvleader]




private theorem transition_barrier_right_eq_of_phase_zero_leader {k : Nat}
    (hk : 0 < k) (u v : State k)
    (hbar : IsBarrier hk u v)
    (hphase : u.phase = false) (hleader : v.leader = true) :
    (transition hk u v).2 = v := by
  rw [transition_of_barrier hk u v hbar]
  rw [barrierStep_phase_zero hk u v hphase]
  simp [hleader]




private theorem transition_barrier_right_clean_of_ready_follower {k : Nat}
    (hk : 0 < k) (u v : State k)
    (hbar : IsBarrier hk u v)
    (hphase : u.phase = true) (hprobe : v.probe = false)
    (hleader : v.leader = false) :
    (transition hk u v).2.leader = false ∧
      (transition hk u v).2.bullet = false ∧
      (transition hk u v).2.probe = false := by
  rw [transition_of_barrier hk u v hbar]
  rw [barrierStep_phase_one_probe_free hk u v hphase hprobe]
  simp [hleader, hprobe]




private theorem transition_nonbarrier_eq_of_right_clean_left_probe_false
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hbar : ¬ IsBarrier hk u v)
    (hleader : v.leader = false) (hbullet : v.bullet = false)
    (hprobe : u.probe = false) :
    transition hk u v = (u, v) := by
  rw [transition_of_nonbarrier hk u v hbar]
  exact nonBarrierStep_follower_quiet u v hleader hbullet hprobe




private theorem transition_nonbarrier_right_eq_of_fresh_leader {k : Nat}
    (hk : 0 < k) (u v : State k)
    (hbar : ¬ IsBarrier hk u v)
    (hleader : v.leader = true) (hbullet : v.bullet = false) :
    (transition hk u v).2 = v := by
  rw [transition_of_nonbarrier hk u v hbar]
  rw [nonBarrierStep_leader_fires u v hleader hbullet]




/-- A non-advancing literal interaction preserves the fixed canonical swept
suffix. -/
private theorem sweptFreshCut_step_not_ready {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (X : Fin n → State k) (t e : Fin n)
    (hbar : CanonicalOneBarrier hk ring X)
    (hfresh : SweptFreshCut X t)
    (hnot : ¬ AdvanceReady hk ring X e) :
    SweptFreshCut ((protocol k hk).step ring X e) t := by
  have hn2 : 1 < n := by omega
  have hzeroVal : (⟨0, ring.hn⟩ : Fin n).val = 0 := rfl
  have htailVal : (tailCoord ring).val = n - 1 := rfl
  have hzeroTail : (⟨0, ring.hn⟩ : Fin n) ≠ tailCoord ring := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = n - 1 at hv
    omega
  dsimp [SweptFreshCut] at hfresh
  rcases hfresh with ⟨htLeader, htBullet, htProbe, hsuffix⟩
  let D := (protocol k hk).step ring X e




  have htOut :
      (D t).leader = true ∧
        (D t).bullet = false ∧
        (D t).probe = false := by
    by_cases het : e = t
    · subst e
      by_cases htTail : t = tailCoord ring
      · subst t
        have hbarTail : IsBarrier hk (X (tailCoord ring))
            (X (ring.rightNeighbor (tailCoord ring))) :=
          (hbar (tailCoord ring)).2 rfl
        have hlocal :=
          transition_barrier_left_fields_of_probe_false hk
            (X (tailCoord ring))
            (X (ring.rightNeighbor (tailCoord ring)))
            hbarTail htProbe
        refine ⟨?_, ?_, ?_⟩
        · calc
            (D (tailCoord ring)).leader =
                (X (tailCoord ring)).leader := by
              simpa [D, PopulationProtocol.step, protocol] using hlocal.1
            _ = true := htLeader
        · calc
            (D (tailCoord ring)).bullet =
                (X (tailCoord ring)).bullet := by
              simpa [D, PopulationProtocol.step, protocol] using hlocal.2.1
            _ = false := htBullet
        · simpa [D, PopulationProtocol.step, protocol] using hlocal.2.2
      · have hnon :=
          canonical_nonbarrier_of_ne_tail hk ring X hbar t htTail
        have hrespVal :=
          rightNeighbor_val_of_ne_tail ring t htTail
        have hrespLater :
            t.val < (ring.rightNeighbor t).val := by
          rw [hrespVal]
          omega
        have hrespClean := hsuffix (ring.rightNeighbor t) hrespLater
        have hpair :=
          transition_nonbarrier_eq_of_right_clean_left_probe_false hk
            (X t) (X (ring.rightNeighbor t)) hnon
            hrespClean.1 hrespClean.2.1 htProbe
        have hleft := congrArg Prod.fst hpair
        have hDt : D t = X t := by
          simpa [D, PopulationProtocol.step, protocol] using hleft
        rw [hDt]
        exact ⟨htLeader, htBullet, htProbe⟩
    · by_cases hresp : ring.rightNeighbor e = t
      · by_cases heTail : e = tailCoord ring
        · subst e
          have hbarTail : IsBarrier hk (X (tailCoord ring))
              (X (ring.rightNeighbor (tailCoord ring))) :=
            (hbar (tailCoord ring)).2 rfl
          have hrespProbe :
              (X (ring.rightNeighbor (tailCoord ring))).probe = false := by
            rw [hresp]
            exact htProbe
          cases hphase : (X (tailCoord ring)).phase with
          | false =>
              have hrespLeader :
                  (X (ring.rightNeighbor (tailCoord ring))).leader = true := by
                rw [hresp]
                exact htLeader
              have hlocal :=
                transition_barrier_right_eq_of_phase_zero_leader hk
                  (X (tailCoord ring))
                  (X (ring.rightNeighbor (tailCoord ring)))
                  hbarTail hphase hrespLeader
              have hre :=
                rightNeighbor_ne_self ring hn2 (tailCoord ring)
              have hDright :
                  D (ring.rightNeighbor (tailCoord ring)) =
                    X (ring.rightNeighbor (tailCoord ring)) := by
                simpa [D, PopulationProtocol.step, protocol, hre,
                  hzeroTail] using hlocal
              have hDt : D t = X t := by
                simpa [hresp] using hDright
              rw [hDt]
              exact ⟨htLeader, htBullet, htProbe⟩
          | true =>
              exact False.elim
                (hnot ⟨hbarTail, hphase, hrespProbe⟩)
        · have hnon :=
            canonical_nonbarrier_of_ne_tail hk ring X hbar e heTail
          have hrespLeader :
              (X (ring.rightNeighbor e)).leader = true := by
            rw [hresp]
            exact htLeader
          have hrespBullet :
              (X (ring.rightNeighbor e)).bullet = false := by
            rw [hresp]
            exact htBullet
          have hlocal :=
            transition_nonbarrier_right_eq_of_fresh_leader hk
              (X e) (X (ring.rightNeighbor e)) hnon
              hrespLeader hrespBullet
          have hre := rightNeighbor_ne_self ring hn2 e
          have hDright :
              D (ring.rightNeighbor e) = X (ring.rightNeighbor e) := by
            simpa [D, PopulationProtocol.step, protocol, hre] using hlocal
          have hDt : D t = X t := by
            simpa [hresp] using hDright
          rw [hDt]
          exact ⟨htLeader, htBullet, htProbe⟩
      · have hsame :=
          step_other_state hk ring X e t (Ne.symm het) (Ne.symm hresp)
        have hDt : D t = X t := by
          simpa [D] using hsame
        rw [hDt]
        exact ⟨htLeader, htBullet, htProbe⟩




  have hsuffixOut :
      ∀ q : Fin n, t.val < q.val →
        (D q).leader = false ∧
          (D q).bullet = false ∧
          (D q).probe = false := by
    intro q hq
    have hqClean := hsuffix q hq
    by_cases heq : e = q
    · subst e
      by_cases hqTail : q = tailCoord ring
      · subst q
        have hbarTail : IsBarrier hk (X (tailCoord ring))
            (X (ring.rightNeighbor (tailCoord ring))) :=
          (hbar (tailCoord ring)).2 rfl
        have hlocal :=
          transition_barrier_left_fields_of_probe_false hk
            (X (tailCoord ring))
            (X (ring.rightNeighbor (tailCoord ring)))
            hbarTail hqClean.2.2
        refine ⟨?_, ?_, ?_⟩
        · calc
            (D (tailCoord ring)).leader =
                (X (tailCoord ring)).leader := by
              simpa [D, PopulationProtocol.step, protocol] using hlocal.1
            _ = false := hqClean.1
        · calc
            (D (tailCoord ring)).bullet =
                (X (tailCoord ring)).bullet := by
              simpa [D, PopulationProtocol.step, protocol] using hlocal.2.1
            _ = false := hqClean.2.1
        · simpa [D, PopulationProtocol.step, protocol] using hlocal.2.2
      · have hnon :=
          canonical_nonbarrier_of_ne_tail hk ring X hbar q hqTail
        have hrespVal :=
          rightNeighbor_val_of_ne_tail ring q hqTail
        have hrespLater :
            t.val < (ring.rightNeighbor q).val := by
          rw [hrespVal]
          omega
        have hrespClean := hsuffix (ring.rightNeighbor q) hrespLater
        have hpair :=
          transition_nonbarrier_eq_of_right_clean_left_probe_false hk
            (X q) (X (ring.rightNeighbor q)) hnon
            hrespClean.1 hrespClean.2.1 hqClean.2.2
        have hleft := congrArg Prod.fst hpair
        have hDq : D q = X q := by
          simpa [D, PopulationProtocol.step, protocol] using hleft
        rw [hDq]
        exact hqClean
    · by_cases hresp : ring.rightNeighbor e = q
      · by_cases heTail : e = tailCoord ring
        · subst e
          have hv := congrArg Fin.val hresp
          rw [rightNeighbor_tailCoord ring] at hv
          omega
        · have hnon :=
            canonical_nonbarrier_of_ne_tail hk ring X hbar e heTail
          have hrespVal :=
            rightNeighbor_val_of_ne_tail ring e heTail
          rw [hresp] at hrespVal
          have heProbe : (X e).probe = false := by
            by_cases het : e = t
            · subst e
              exact htProbe
            · have hneVal : e.val ≠ t.val := by
                intro hv
                apply het
                apply Fin.ext
                exact hv
              have hlt : t.val < e.val := by
                omega
              exact (hsuffix e hlt).2.2
          have hrespClean := hqClean
          rw [← hresp] at hrespClean
          have hpair :=
            transition_nonbarrier_eq_of_right_clean_left_probe_false hk
              (X e) (X (ring.rightNeighbor e)) hnon
              hrespClean.1 hrespClean.2.1 heProbe
          have hright := congrArg Prod.snd hpair
          have hre := rightNeighbor_ne_self ring hn2 e
          have hDq : D q = X q := by
            rw [← hresp]
            simpa [D, PopulationProtocol.step, protocol, hre] using hright
          rw [hDq]
          exact hqClean
      · have hsame :=
          step_other_state hk ring X e q (Ne.symm heq) (Ne.symm hresp)
        have hDq : D q = X q := by
          simpa [D] using hsame
        rw [hDq]
        exact hqClean




  change SweptFreshCut D t
  unfold SweptFreshCut
  exact ⟨htOut.1, htOut.2.1, htOut.2.2, hsuffixOut⟩




/-- On a genuine canonical barrier advance whose old head is a follower, the
cut shifts left and the swept suffix is extended by the sanitized new tail. -/
private theorem sweptFreshCut_step_ready_tail {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (X : Fin n → State k) (t : Fin n)
    (hbar : CanonicalOneBarrier hk ring X)
    (hfresh : SweptFreshCut X t)
    (hready : AdvanceReady hk ring X (tailCoord ring))
    (hheadFollower :
      (X (⟨0, ring.hn⟩ : Fin n)).leader = false) :
    SweptFreshCut
      (rotateCut ring
        ((protocol k hk).step ring X (tailCoord ring)))
      (ring.leftNeighbor t) := by
  have hn2 : 1 < n := by omega
  have hzeroVal : (⟨0, ring.hn⟩ : Fin n).val = 0 := rfl
  have htailVal : (tailCoord ring).val = n - 1 := rfl
  have hzeroTail : (⟨0, ring.hn⟩ : Fin n) ≠ tailCoord ring := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = n - 1 at hv
    omega
  dsimp [SweptFreshCut] at hfresh
  rcases hfresh with ⟨htLeader, htBullet, htProbe, hsuffix⟩
  let D := (protocol k hk).step ring X (tailCoord ring)
  let Y := rotateCut ring D




  have htPos : 0 < t.val := by
    by_cases hzero : t.val = 0
    · have ht0 : t = (⟨0, ring.hn⟩ : Fin n) := by
        apply Fin.ext
        exact hzero
      subst t
      rw [hheadFollower] at htLeader
      contradiction
    · omega




  have htD :
      (D t).leader = true ∧
        (D t).bullet = false ∧
        (D t).probe = false := by
    by_cases htTail : t = tailCoord ring
    · subst t
      have hlocal :=
        transition_barrier_left_fields_of_probe_false hk
          (X (tailCoord ring))
          (X (ring.rightNeighbor (tailCoord ring)))
          hready.1 htProbe
      refine ⟨?_, ?_, ?_⟩
      · calc
          (D (tailCoord ring)).leader =
              (X (tailCoord ring)).leader := by
            simpa [D, PopulationProtocol.step, protocol] using hlocal.1
          _ = true := htLeader
      · calc
          (D (tailCoord ring)).bullet =
              (X (tailCoord ring)).bullet := by
            simpa [D, PopulationProtocol.step, protocol] using hlocal.2.1
          _ = false := htBullet
      · simpa [D, PopulationProtocol.step, protocol] using hlocal.2.2
    · have htHead :
          t ≠ ring.rightNeighbor (tailCoord ring) := by
        intro h
        have hv := congrArg Fin.val h
        rw [rightNeighbor_tailCoord ring] at hv
        omega
      have hsame :=
        step_other_state hk ring X (tailCoord ring) t htTail htHead
      have hDt : D t = X t := by
        simpa [D] using hsame
      rw [hDt]
      exact ⟨htLeader, htBullet, htProbe⟩




  have htY :
      (Y (ring.leftNeighbor t)).leader = true ∧
        (Y (ring.leftNeighbor t)).bullet = false ∧
        (Y (ring.leftNeighbor t)).probe = false := by
    simpa [Y, rotateCut, rightNeighbor_leftNeighbor_clean] using htD




  have hsuffixY :
      ∀ q : Fin n, (ring.leftNeighbor t).val < q.val →
        (Y q).leader = false ∧
          (Y q).bullet = false ∧
          (Y q).probe = false := by
    intro q hq
    by_cases hqTail : q = tailCoord ring
    · subst q
      have hheadFollowerRaw :
          (X (ring.rightNeighbor (tailCoord ring))).leader = false := by
        simpa [rightNeighbor_tailCoord] using hheadFollower
      have hlocal :=
        transition_barrier_right_clean_of_ready_follower hk
          (X (tailCoord ring))
          (X (ring.rightNeighbor (tailCoord ring)))
          hready.1 hready.2.1 hready.2.2 hheadFollowerRaw
      have hre :=
        rightNeighbor_ne_self ring hn2 (tailCoord ring)
      have hDhead :
          (D (ring.rightNeighbor (tailCoord ring))).leader = false ∧
            (D (ring.rightNeighbor (tailCoord ring))).bullet = false ∧
            (D (ring.rightNeighbor (tailCoord ring))).probe = false := by
        refine ⟨?_, ?_, ?_⟩
        · simpa [D, PopulationProtocol.step, protocol, hre,
            hzeroTail] using hlocal.1
        · simpa [D, PopulationProtocol.step, protocol, hre,
            hzeroTail] using hlocal.2.1
        · simpa [D, PopulationProtocol.step, protocol, hre,
            hzeroTail] using hlocal.2.2
      simpa [Y, rotateCut] using hDhead
    · have htLeft :=
        leftNeighbor_val_of_pos ring t htPos
      have hqSucc :=
        rightNeighbor_val_of_ne_tail ring q hqTail
      have hOldLater :
          t.val < (ring.rightNeighbor q).val := by
        rw [htLeft] at hq
        rw [hqSucc]
        omega
      have hOldClean :=
        hsuffix (ring.rightNeighbor q) hOldLater
      have hDClean :
          (D (ring.rightNeighbor q)).leader = false ∧
            (D (ring.rightNeighbor q)).bullet = false ∧
            (D (ring.rightNeighbor q)).probe = false := by
        by_cases hrTail :
            ring.rightNeighbor q = tailCoord ring
        · have hOldTail := hOldClean
          rw [hrTail] at hOldTail
          have hlocal :=
            transition_barrier_left_fields_of_probe_false hk
              (X (tailCoord ring))
              (X (ring.rightNeighbor (tailCoord ring)))
              hready.1 hOldTail.2.2
          have hDtail :
              (D (tailCoord ring)).leader = false ∧
                (D (tailCoord ring)).bullet = false ∧
                (D (tailCoord ring)).probe = false := by
            refine ⟨?_, ?_, ?_⟩
            · calc
                (D (tailCoord ring)).leader =
                    (X (tailCoord ring)).leader := by
                  simpa [D, PopulationProtocol.step, protocol] using hlocal.1
                _ = false := hOldTail.1
            · calc
                (D (tailCoord ring)).bullet =
                    (X (tailCoord ring)).bullet := by
                  simpa [D, PopulationProtocol.step, protocol] using hlocal.2.1
                _ = false := hOldTail.2.1
            · simpa [D, PopulationProtocol.step, protocol] using hlocal.2.2
          rw [hrTail]
          exact hDtail
        · have hrHead :
              ring.rightNeighbor q ≠
                ring.rightNeighbor (tailCoord ring) := by
            intro h
            apply hqTail
            exact rightNeighbor_injective ring h
          have hsame :=
            step_other_state hk ring X (tailCoord ring)
              (ring.rightNeighbor q) hrTail hrHead
          have hDsame :
              D (ring.rightNeighbor q) =
                X (ring.rightNeighbor q) := by
            simpa [D] using hsame
          rw [hDsame]
          exact hOldClean
      simpa [Y, rotateCut] using hDClean




  change SweptFreshCut Y (ring.leftNeighbor t)
  unfold SweptFreshCut
  exact ⟨htY.1, htY.2.1, htY.2.2, hsuffixY⟩




/-- Unified canonical one-step preservation.  The sole excluded step is a
genuine barrier advance whose pre-step head is a leader. -/
private theorem sweptFreshCut_step {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (X : Fin n → State k) (t e : Fin n)
    (hbar : CanonicalOneBarrier hk ring X)
    (hfresh : SweptFreshCut X t)
    (hnoCross :
      ¬ (AdvanceReady hk ring X e ∧
        (X (⟨0, ring.hn⟩ : Fin n)).leader = true)) :
    SweptFreshCut
      (cutSuccessor hk ring X e)
      (if AdvanceReady hk ring X e then ring.leftNeighbor t else t) := by
  by_cases hready : AdvanceReady hk ring X e
  · have he : e = tailCoord ring := (hbar e).1 hready.1
    subst e
    have hheadFollower :
        (X (⟨0, ring.hn⟩ : Fin n)).leader = false := by
      cases hh : (X (⟨0, ring.hn⟩ : Fin n)).leader with
      | false => rfl
      | true => exact False.elim (hnoCross ⟨hready, hh⟩)
    simpa [cutSuccessor, hready] using
      sweptFreshCut_step_ready_tail hk ring hn3 X t hbar hfresh
        hready hheadFollower
  · simpa [cutSuccessor, hready] using
      sweptFreshCut_step_not_ready hk ring hn3 X t e hbar hfresh hready




/-- One literal original-Protocol-6 interaction preserves the swept-fresh
suffix unless that interaction is exactly a genuine barrier advance across a
leader at the pre-step head.




The exclusion is an explicit decidable proposition on C, b, and e.  Barrier
uniqueness in the successor is supplied by
SingleBarrierSanitation.oneBarrierAt_step. -/
theorem sweptFresh_step {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (B b e : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hfresh : SweptFresh ring B b C)
    (hnoCross :
      ¬ (e = b ∧
        AdvanceReady hk ring C e ∧
        (C (ring.rightNeighbor b)).leader = true)) :
    ∃ b' : Fin n,
      b' =
          (if AdvanceReady hk ring C e then
            ring.rightNeighbor b
          else b) ∧
      OneBarrierAt hk ring (rawRun hk ring C [e]) b' ∧
      SweptFresh ring B b' (rawRun hk ring C [e]) := by
  have hn2 : 1 < n := by omega
  let D := rawRun hk ring C [e]
  let X := cutView ring b C
  let t := cutCoord ring b B
  let i := cutCoord ring b e




  have hbarX : CanonicalOneBarrier hk ring X := by
    simpa [X] using canonicalOneBarrier_cutView hk ring C b hB
  have hfreshX : SweptFreshCut X t := by
    simpa [X, t] using
      (sweptFresh_iff_cut ring B b C).1 hfresh
  have hreadyIff :
      AdvanceReady hk ring X i ↔
        AdvanceReady hk ring C e := by
    simpa [X, i] using
      (advanceReady_cutView_iff hk ring C b (cutCoord ring b e))
  have hnoCrossX :
      ¬ (AdvanceReady hk ring X i ∧
        (X (⟨0, ring.hn⟩ : Fin n)).leader = true) := by
    intro hx
    have hreadyPhysical : AdvanceReady hk ring C e :=
      hreadyIff.1 hx.1
    have heB : e = b := by
      apply (hB e).1
      exact (barrierAt_labelsOf_iff hk ring C e).2 hreadyPhysical.1
    apply hnoCross
    refine ⟨heB, hreadyPhysical, ?_⟩
    simpa [X, cutView] using hx.2




  have hpost :=
    sweptFreshCut_step hk ring hn3 X t i hbarX hfreshX hnoCrossX
  have hview0 :
      cutView ring b D =
        (protocol k hk).step ring X i := by
    simpa [D, X, i, rawRun] using
      (cutView_step_at_cutPos hk ring b C (cutCoord ring b e))
  have hstepBarrier :=
    oneBarrierAt_step hk ring hn2 C b e hnd hB




  by_cases hready : AdvanceReady hk ring C e
  · have hreadyX : AdvanceReady hk ring X i :=
      hreadyIff.2 hready
    have hB' :
        OneBarrierAt hk ring D (ring.rightNeighbor b) := by
      simpa [D, rawRun, hready] using hstepBarrier
    have hcut :
        SweptFreshCut
          (cutView ring (ring.rightNeighbor b) D)
          (cutCoord ring (ring.rightNeighbor b) B) := by
      rw [cutView_nextBarrier ring b D]
      rw [cutCoord_nextBarrier ring b B]
      rw [hview0]
      simpa [cutSuccessor, hreadyX, t] using hpost
    have hSF' :
        SweptFresh ring B (ring.rightNeighbor b) D :=
      (sweptFresh_iff_cut ring B (ring.rightNeighbor b) D).2 hcut
    refine ⟨ring.rightNeighbor b, ?_, ?_, ?_⟩
    · simp [hready]
    · simpa [D] using hB'
    · simpa [D] using hSF'
  · have hnotReadyX : ¬ AdvanceReady hk ring X i := by
      intro hx
      exact hready (hreadyIff.1 hx)
    have hB' : OneBarrierAt hk ring D b := by
      simpa [D, rawRun, hready] using hstepBarrier
    have hcut :
        SweptFreshCut (cutView ring b D) (cutCoord ring b B) := by
      rw [hview0]
      simpa [cutSuccessor, hnotReadyX, t] using hpost
    have hSF' : SweptFresh ring B b D :=
      (sweptFresh_iff_cut ring B b D).2 hcut
    refine ⟨b, ?_, ?_, ?_⟩
    · simp [hready]
    · simpa [D] using hB'
    · simpa [D] using hSF'




/-- In particular, the tracked cut-last leader cannot die in such a step and
its bullet field stays false.  The stronger no-leader-after-B conclusion is
the suffix clause of the SweptFresh witness returned by sweptFresh_step. -/
theorem cutLast_leader_survives {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (B b e : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hfresh : SweptFresh ring B b C)
    (hnoCross :
      ¬ (e = b ∧
        AdvanceReady hk ring C e ∧
        (C (ring.rightNeighbor b)).leader = true)) :
    (rawRun hk ring C [e] B).leader = true ∧
      (rawRun hk ring C [e] B).bullet = false := by
  obtain ⟨b', _hb', _hbarrier, hSF⟩ :=
    sweptFresh_step hk ring hn3 hnd C B b e hB hfresh hnoCross
  dsimp [SweptFresh] at hSF
  exact ⟨hSF.1, hSF.2.1⟩




end AAFJPK.OriginalOneBarrierSweptFresh




#print axioms AAFJPK.OriginalOneBarrierSweptFresh.sweptFresh_step
#print axioms AAFJPK.OriginalOneBarrierSweptFresh.cutLast_leader_survives
