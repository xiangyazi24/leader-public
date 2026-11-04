import Leader.Wu.Elimination.SinkTwoGapRankBoundaryDischarged
import Leader.Wu.Elimination.SinkTwoGapStageCells

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDSinkGapDoneInvariant
open LDTwoGapFrame LDSinkTwoGapNoResetKernel LDSinkTwoGapEntrance
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapEpochSuccessor LDSinkTwoGapRestartClosure

namespace LDSinkTwoGapRaceEntranceLocalService

variable {n psi : Nat}

/-!
Physical producers for a revised entrance service.  The old parked phase
cannot carry the cost of a new shot.  This file derives the actual new-shot
entry from a clean attack gap and an outgoing shooter FIRE, and simplifies
the recovery-clean target to the shared signal bit under the proved gap
invariant.  No entrance-time or Bellman estimate is assumed here.
-/

/-- Signal/bullet order makes recovery cleanliness equivalent to its
shooter's signal bit: a nonzero bullet anywhere in the positive sector
would force that terminal signal to zero. -/
theorem cleanReady_iff_shooter_signal (hpsi : psi > 0) (G : GapFrame n)
    (C : Fin n → AgentState psi) (hi : GapInvariant hpsi G C) :
    CleanReady G C ↔ (C (G.pos G.d)).signal_B = (1 : Fin 2) := by
  constructor
  · exact fun h => h.1
  · intro hs
    refine ⟨hs, ?_⟩
    intro k hk hkd
    by_cases hb : (C (G.pos k)).bullet = (0 : Fin 3)
    · exact hb
    · have hz := hi.2.2.2 k G.d hk hkd hb hkd (Nat.le_refl _)
      rw [hs] at hz
      exact (by decide : (1 : Fin 2) ≠ 0) hz |>.elim

/-- On the physical gap domain the race entrance is a two-cell predicate.
No phase bit or interior signal pattern is needed. -/
theorem raceReady_iff_two_cells (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) :
    RaceReady F b.conf ↔
      (b.conf (F.attack.pos 1)).bullet = (2 : Fin 3) ∧
      (b.conf (F.attack.pos 0)).signal_B = (1 : Fin 2) := by
  unfold RaceReady
  rw [cleanReady_iff_shooter_signal hpsi F.recovery b.conf hg.recovery,
    F.shared]

/-- A parked live shot that has not reached the entrance necessarily faces
a zero shared signal.  In particular the next victim interaction cannot
re-shield by FIRE in this case. -/
theorem parked_not_ready_shared_signal_zero (hpsi : psi > 0)
    (F : TwoGapFrame n) (b : AState n psi) (hg : GapPair hpsi F b)
    (hb : (b.conf (F.attack.pos 1)).bullet = (2 : Fin 3))
    (hn : ¬ RaceReady F b.conf) :
    (b.conf (F.attack.pos 0)).signal_B = (0 : Fin 2) := by
  have hn1 : (b.conf (F.attack.pos 0)).signal_B ≠ (1 : Fin 2) := by
    intro hs
    exact hn ((raceReady_iff_two_cells hpsi F b hg).mpr ⟨hb, hs⟩)
  apply Fin.ext
  have hbnd := (b.conf (F.attack.pos 0)).signal_B.isLt
  have hv : (b.conf (F.attack.pos 0)).signal_B.val ≠ 1 := by
    intro he
    exact hn1 (Fin.ext he)
  omega

/-- Initiator FIRE leaves the entire shooter in its fresh live-shot state.
Its new shield prevents the subsequent MOVE from deleting it, regardless
of the outside responder's fields. -/
theorem kernelC_outgoing_fire_left (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = true) (hs : l.signal_B = (1 : Fin 2)) :
    (sinkKernelC hpsi l r).1 =
      { l with bullet := 2, shield := true, signal_B := 0 } := by
  simp [sinkKernelC, eliminateLeadersNoCollisionFire, hl, hs,
    absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]

/-- An outgoing FIRE preserves every leader bit of the whole ring.  Only
the initiator could lose leadership in K2, and its just-created shield
prevents that loss. -/
theorem outgoing_fire_leaders (hpsi : psi > 0) (G : GapFrame n)
    (C : Fin n → AgentState psi) (e : Fin n)
    (hl : (C e).leader = true) (hs : (C e).signal_B = (1 : Fin 2)) :
    ∀ v : Fin n, (sinkStepC hpsi G C e v).leader = (C v).leader := by
  intro v
  by_cases hv : v = e
  · subst v
    have hrow := congrArg AgentState.leader
      (kernelC_outgoing_fire_left hpsi (C e) (C (G.ring.rightNeighbor e)) hl hs)
    simpa [sinkStepC, updatePair] using hrow
  · by_cases hr : v = G.ring.rightNeighbor e
    · subst v
      simpa [sinkStepC, updatePair, hv] using
        kernelC_right_leader_eq hpsi (C e) (C (G.ring.rightNeighbor e))
    · rw [sinkStepC_other hpsi G C e v hv hr]

private theorem gapPair_not_success (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) : ¬ NoResetSuccess F b.conf := by
  intro hd
  rcases hd with (hl | hr) | (hl | hr)
  · have h := hg.attack.1.1
    rw [h] at hl
    cases hl
  · have h := hg.attack.1.2
    rw [h] at hr
    cases hr
  · have h := hg.recovery.1.1
    rw [h] at hl
    cases hl
  · have h := hg.recovery.1.2
    rw [h] at hr
    cases hr

/-- The outgoing shooter edge creates the unique fresh attack live bullet.
Every earlier positive attack cell is framed by the outgoing edge. -/
theorem clean_outgoing_uniqueLiveShot (hpsi : psi > 0)
    (F : TwoGapFrame n) (b : AState n psi) (hg : GapPair hpsi F b)
    (hc : CleanReady F.attack b.conf) :
    UniqueLiveShot F
      (attemptStepConf hpsi F b (F.attack.pos F.attack.d)) := by
  rw [attemptStepConf_eq_sinkStepC]
  have ha := F.attack.hd
  have hr := F.recovery.hd
  have hn := F.length_lt
  have hdn : F.attack.d + 1 < n := by omega
  have hframe : ∀ u : Nat, 1 ≤ u → u < F.attack.d →
      sinkStepC hpsi F.attack b.conf (F.attack.pos F.attack.d) (F.attack.pos u) =
        b.conf (F.attack.pos u) := by
    intro u hu hud
    apply sinkStepC_other
    · intro he
      have heq := pos_injective_below_n F.attack u F.attack.d (by omega)
        F.attack.hdn he
      omega
    · rw [gap_rightNeighbor_pos]
      intro he
      have heq := pos_injective_below_n F.attack u (F.attack.d + 1)
        (by omega) hdn he
      omega
  have hshot :
      (sinkStepC hpsi F.attack b.conf (F.attack.pos F.attack.d)
        (F.attack.pos F.attack.d)).bullet = (2 : Fin 3) := by
    have hrow := congrArg AgentState.bullet (kernelC_outgoing_fire_left hpsi
      (b.conf (F.attack.pos F.attack.d))
      (b.conf (F.attack.ring.rightNeighbor (F.attack.pos F.attack.d)))
      hg.attack.1.2 hc.1)
    simpa [sinkStepC, updatePair] using hrow
  refine ⟨F.attack.d, by omega, Nat.le_refl _, hshot, ?_⟩
  intro u hu hud hb
  by_cases he : u = F.attack.d
  · exact he
  · have hul : u < F.attack.d := by omega
    rw [hframe u (by omega) hul] at hb
    exact (hb (hc.2 u (by omega) hud)).elim

/-- A real outgoing FIRE from a clean gap produces the old fresh-shot
`AttemptEntrance`, including its non-done and phase/position conditions.
Only the proof-only phase is reinitialized; the raw configuration is the
actual one-edge successor and is not reset. -/
theorem clean_outgoing_attemptEntrance (hpsi : psi > 0)
    (F : TwoGapFrame n) (b : AState n psi) (hg : GapPair hpsi F b)
    (hc : CleanReady F.attack b.conf) :
    AttemptEntrance hpsi F
      ⟨attemptStepConf hpsi F b (F.attack.pos F.attack.d), .transit⟩ := by
  let e := F.attack.pos F.attack.d
  let C := attemptStepConf hpsi F b e
  have hlead : ∀ v : Fin n, (C v).leader = (b.conf v).leader := by
    exact outgoing_fire_leaders hpsi F.attack b.conf e hg.attack.1.2 hc.1
  have hns : ¬ NoResetSuccess F C := by
    intro hd
    apply gapPair_not_success hpsi F b hg
    simpa only [NoResetSuccess, EndpointDeleted, hlead] using hd
  have hstep : physicalBlockStep hpsi F b e = .active (postState hpsi F b e) := by
    classical
    rw [physicalBlockStep_normal_form, if_neg hns]
  have hgpost := gapPair_physical_step hpsi F
    (CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2 hpsi F)
    b e (postState hpsi F b e) hg hstep
  have hshot : UniqueLiveShot F C := clean_outgoing_uniqueLiveShot hpsi F b hg hc
  have hbullet : (C (F.attack.pos F.attack.d)).bullet = (2 : Fin 3) := by
    have hrow := congrArg AgentState.bullet (kernelC_outgoing_fire_left hpsi
      (b.conf e) (b.conf (F.attack.ring.rightNeighbor e)) hg.attack.1.2 hc.1)
    simpa [C, e, attemptStepConf_eq_sinkStepC, sinkStepC, updatePair] using hrow
  have hnotOne : (C (F.attack.pos 1)).bullet ≠ (2 : Fin 3) := by
    intro h1
    rcases hshot with ⟨t, ht, htd, hb, hu⟩
    have he1 := hu 1 (by decide) (by have h := F.attack.hd; omega)
      (by rw [h1]; decide)
    have hed := hu F.attack.d (by have h := F.attack.hd; omega)
      (Nat.le_refl _) (by rw [hbullet]; decide)
    have hd := F.attack.hd
    omega
  have hnotDone : ¬ GapDoneC F.attack C := by
    intro hd
    rcases hd with hclean | hdel
    · have hz := hclean.2 F.attack.d (by have h := F.attack.hd; omega)
        (Nat.le_refl _)
      rw [hbullet] at hz
      exact (by decide : (2 : Fin 3) ≠ 0) hz
    · exact hns (.inl hdel)
  refine ⟨⟨hgpost.recovery, hgpost.attack, hshot, ?_, hnotDone⟩, rfl, hbullet⟩
  constructor
  · intro h
    cases h
  · intro h
    exact (hnotOne h).elim

end LDSinkTwoGapRaceEntranceLocalService

#print axioms LDSinkTwoGapRaceEntranceLocalService.raceReady_iff_two_cells
#print axioms LDSinkTwoGapRaceEntranceLocalService.kernelC_outgoing_fire_left
#print axioms LDSinkTwoGapRaceEntranceLocalService.clean_outgoing_uniqueLiveShot
#print axioms LDSinkTwoGapRaceEntranceLocalService.clean_outgoing_attemptEntrance
