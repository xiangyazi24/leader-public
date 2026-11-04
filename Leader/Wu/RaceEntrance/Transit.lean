import Leader.Wu.RaceEntrance.LocalService

set_option autoImplicit false

open PPLLRepair LDSinkGapCleanup LDSinkProtectedAbsorption LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptResidual LDSinkTwoGapAttemptCells
open LDSinkTwoGapReachInvariant

namespace LDSinkTwoGapRaceEntranceTransit

variable {n psi : Nat}

/-!
The position of a fresh in-transit attack shot has an exact scheduler-only
update.  Its predecessor edge moves it one cell left; every other raw edge
keeps the same position.  In particular, changing the recovery-side fields
does not change this update while the fresh-shot invariant is available.
This row statement is not a probabilistic independence assumption.
-/

def nextShotPosition (F : TwoGapFrame n) (t : Nat) (e : Fin n) : Nat :=
  if e = F.attack.pos (t - 1) then t - 1 else t

private theorem predecessor_of_head (G : GapFrame n) (e : Fin n)
    (t : Nat) (ht : 1 ≤ t) (he : G.ring.rightNeighbor e = G.pos t) :
    e = G.pos (t - 1) := by
  have hh : G.ring.rightNeighbor e = G.ring.rightNeighbor (G.pos (t - 1)) := by
    simpa only [gap_rightNeighbor_pos, Nat.sub_add_cancel ht] using he
  have hv := congrArg Fin.val hh
  change (e.val + 1) % n = ((G.pos (t - 1)).val + 1) % n at hv
  have heB := e.isLt
  have hfB := (G.pos (t - 1)).isLt
  apply Fin.ext
  by_cases ha : e.val + 1 < n <;>
    by_cases hb : (G.pos (t - 1)).val + 1 < n
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
    omega
  · have hn : (G.pos (t - 1)).val + 1 = n := by omega
    rw [hn, Nat.mod_self, Nat.mod_eq_of_lt ha] at hv
    omega
  · have hn : e.val + 1 = n := by omega
    rw [hn, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
    omega
  · omega

/-- The actual shot position is determined by the scheduled edge, even
when another tagged endpoint is deleted during that same interaction. -/
theorem transit_position_row (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (t : Nat) (ht : 1 < t) (htd : t ≤ F.attack.d)
    (hb : (x.val.conf (F.attack.pos t)).bullet = (2 : Fin 3)) (e : Fin n) :
    (attemptStepConf hpsi F x.val e (F.attack.pos (nextShotPosition F t e))).bullet =
      (2 : Fin 3) := by
  by_cases he : e = F.attack.pos (t - 1)
  · rw [nextShotPosition, if_pos he, he, attemptStepConf_eq_sinkStepC,
      sinkStepC, updatePair_initiator, gap_rightNeighbor_pos,
      Nat.sub_add_cancel (by omega : 1 ≤ t)]
    apply (pair_transfer_live hpsi
      (x.val.conf (F.attack.pos (t - 1))) (x.val.conf (F.attack.pos t))
      (x.property.attack.2.1 (t - 1) (by omega) (by omega))
      (attack_cell_quiet hpsi F x t (by omega) htd) hb ?_).1
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using
      x.property.attack.2.2.1 (t - 1) (by omega)
  · rw [nextShotPosition, if_neg he, attemptStepConf_eq_sinkStepC]
    by_cases htouched : e = F.attack.pos t
    · subst e
      rw [sinkStepC, updatePair_initiator]
      by_cases hlast : t = F.attack.d
      · subst t
        exact pair_leader_left_live hpsi _ _ x.property.attack.1.2
          (attack_shooter_signal_zero hpsi F x) hb
      · have hlt : t < F.attack.d := by omega
        rw [gap_rightNeighbor_pos]
        have hz : (x.val.conf (F.attack.pos (t + 1))).bullet = (0 : Fin 3) := by
          by_cases hz : (x.val.conf (F.attack.pos (t + 1))).bullet = (0 : Fin 3)
          · exact hz
          · have heq := old_bullet_unique hpsi F x t (t + 1)
              (by omega) htd (by omega) (by omega) (by rw [hb]; decide) hz
            omega
        exact pair_left_live_empty_right hpsi _ _
          (attack_cell_quiet hpsi F x t (by omega) htd)
          (attack_cell_quiet hpsi F x (t + 1) (by omega) (by omega)) hb hz
    · rw [sinkStepC_other hpsi F.attack x.val.conf e (F.attack.pos t)
        (fun h => htouched h.symm) ?_]
      · exact hb
      · intro hh
        exact he (predecessor_of_head F.attack e t (by omega) hh.symm)

/-- The exact updated position also identifies every nonzero post-shot
cell; no extra bullet may be inserted behind this projection. -/
theorem transit_unique_row (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (t : Nat) (ht : 1 < t) (htd : t ≤ F.attack.d)
    (hb : (x.val.conf (F.attack.pos t)).bullet = (2 : Fin 3)) (e : Fin n) :
    let u := nextShotPosition F t e
    0 < u ∧ u ≤ F.attack.d ∧
    (attemptStepConf hpsi F x.val e (F.attack.pos u)).bullet = (2 : Fin 3) ∧
    ∀ v : Nat, 0 < v → v ≤ F.attack.d →
      (attemptStepConf hpsi F x.val e (F.attack.pos v)).bullet ≠ (0 : Fin 3) → v = u := by
  have hu : 0 < nextShotPosition F t e ∧ nextShotPosition F t e ≤ F.attack.d := by
    unfold nextShotPosition
    split <;> omega
  have hlive := transit_position_row hpsi F x t ht htd hb e
  refine ⟨hu.1, hu.2, hlive, ?_⟩
  intro v hv hvd hbv
  exact post_bullet_unique hpsi F x e v (nextShotPosition F t e)
    hv hvd hu.1 hu.2 hbv (by rw [hlive]; decide)

/-- Every recovery-sector edge, including both edges that can FIRE the
shared leader, is outside the unique current shot-moving port. -/
theorem recovery_edges_hold_position (F : TwoGapFrame n) (t : Nat)
    (ht : 1 < t) (htd : t ≤ F.attack.d) (k : Nat) (hk : k ≤ F.recovery.d) :
    nextShotPosition F t (F.recovery.pos k) = t := by
  unfold nextShotPosition
  rw [if_neg (F.recovery_ne_attack_positive k (t - 1) hk (by omega) (by omega))]

end LDSinkTwoGapRaceEntranceTransit

#print axioms LDSinkTwoGapRaceEntranceTransit.transit_position_row
#print axioms LDSinkTwoGapRaceEntranceTransit.transit_unique_row
#print axioms LDSinkTwoGapRaceEntranceTransit.recovery_edges_hold_position
