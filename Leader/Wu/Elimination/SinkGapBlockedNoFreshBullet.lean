/-
Surviving public capstones:
* gapWC_eq_gapRank_of_not_doneC
* gapWC_le_gapRank
* gapWC_pos_of_not_doneC
* blocked_step_tail_bullets_zero

Removed with their dependents for the zero-error final cut:
* the entire topIdx helper section and its blocked-rank addendum;
* blocked_nonvictim_gapWC_le / protected_gapRank_le_R7 and their R7 helpers;
* the nonblocked/off-guard chain;
* the bullet/signal-top reconstruction chain;
* the strict-decrease helpers and exists_gapWC_step_lt'.
-/

import Leader.Wu.Elimination.SinkGapRearmCounterexample

open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
  LDSinkGapDoneInvariant LDSinkGapBlockedPreStep LDSinkGapServiceRank
  LDSinkGapRearmCounterexample PPLLRepair LDTwoGapFrame
open Classical

namespace LDSinkGapServiceRankPhysical

set_option autoImplicit false
variable {n ψ : Nat}

/-! ## Ring geometry and two-cell projections used by O1 -/

private theorem head_ne (F : GapFrame n) (e : Fin n) :
    F.ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  have he := e.isLt
  have hd := F.hd
  have hdn := F.hdn
  by_cases ha : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    omega
  · have hh : e.val + 1 = n := by omega
    rw [hh, Nat.mod_self] at hv
    omega

private theorem edge_of_head (F : GapFrame n) (e : Fin n)
    (k : Nat) (hk : 1 ≤ k)
    (he : F.ring.rightNeighbor e = F.pos k) :
    e = F.pos (k - 1) := by
  have h : F.ring.rightNeighbor e =
      F.ring.rightNeighbor (F.pos (k - 1)) := by
    simpa only [gap_rightNeighbor_pos, Nat.sub_add_cancel hk] using he
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (e.val + 1) % n =
    ((F.pos (k - 1)).val + 1) % n at hv
  have heB := e.isLt
  have hfB := (F.pos (k - 1)).isLt
  by_cases ha : e.val + 1 < n <;>
    by_cases hb : (F.pos (k - 1)).val + 1 < n
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
    omega
  · have hh : (F.pos (k - 1)).val + 1 = n := by omega
    rw [hh, Nat.mod_self, Nat.mod_eq_of_lt ha] at hv
    omega
  · have hh : e.val + 1 = n := by omega
    rw [hh, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
    omega
  · omega

private theorem sinkStepC_at_left (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ F C e e =
      (sinkKernelC hψ (C e) (C (F.ring.rightNeighbor e))).1 := by
  simp [sinkStepC, updatePair]

private theorem sinkStepC_at_right (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ F C e (F.ring.rightNeighbor e) =
      (sinkKernelC hψ (C e) (C (F.ring.rightNeighbor e))).2 := by
  simp [sinkStepC, updatePair, head_ne F e]

macro "c3c_concrete" : tactic => `(tactic|
  (simp_all [sinkKernelC, absorbProtectedMove,
    eliminateLeadersNoCollisionFire,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionMove,
    eliminateLeadersNoCollisionSignalLeaderSink,
    dummyBulletSink, nextLabel] <;>
   repeat (first | assumption | rfl | contradiction | omega |
     (apply Fin.ext; omega) | (split <;> simp_all))))

/-! ## Stable rank facts -/

theorem gapWC_eq_gapRank_of_not_doneC
    (F : GapFrame n) (C : Fin n → AgentState ψ)
    (hn : ¬ GapDoneC F C) :
    gapWC F C = gapRank F C := by
  unfold gapWC gapRank
  rw [if_neg hn]

theorem gapWC_le_gapRank
    (F : GapFrame n) (C : Fin n → AgentState ψ) :
    gapWC F C ≤ gapRank F C := by
  unfold gapWC gapRank
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

theorem gapWC_pos_of_not_doneC
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ)
    (hi : GapInvariant hψ F C)
    (hn : ¬ GapDoneC F C) :
    0 < gapWC F C := by
  by_cases hb : GapBlocked F C
  · have hlt := gapWC_blocked_victim_lt hψ F C hb hi
    omega
  · have hOld : ¬ GapDone F C := by
      intro h
      apply hn
      exact GapDoneC_of_GapDone_not_blocked F C h hb
    rcases gapW_drop hψ F C hi hOld with ⟨e, hdrop⟩
    have hpre := gapW_eq_gapWC_of_not_blocked F C hb
    rw [hpre] at hdrop
    omega

/-! ## O1: a blocked K2 step cannot create a service bullet above position 1 -/

private theorem gapBlocked_signal_tail
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ)
    (hb : GapBlocked F C) (hi : GapInvariant hψ F C) :
    ∀ j, 1 ≤ j → j ≤ F.d →
      (C (F.pos j)).signal_B = (0 : Fin 2) := by
  intro j hj hjd
  have hbnz : (C (F.pos 1)).bullet ≠ (0 : Fin 3) := by
    rw [hb.1]
    decide
  exact hi.2.2.2 1 j (by omega) (by
    have hd := F.hd
    omega) hbnz hj hjd

private theorem kernelC_no_fresh
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false)
    (hf : r.leader = true → r.signal_B = (0 : Fin 2))
    (hb : l.bullet = (0 : Fin 3))
    (hc : r.bullet = (0 : Fin 3)) :
    (sinkKernelC hψ l r).1.bullet = (0 : Fin 3) := by
  c3c_concrete

private theorem kernelC_right_clear
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false) :
    (sinkKernelC hψ l r).2.bullet = (0 : Fin 3) := by
  have bc : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
  have sc : ∀ s : Fin 2, s = 0 ∨ s = 1 := by decide
  rcases bc r.bullet with hb | hb | hb <;>
    rcases sc r.signal_B with hs | hs <;>
    cases hr : r.leader <;> cases hh : l.shield <;> c3c_concrete

/-- Right-endpoint safety: even an arbitrary outside responder cannot inject its
bullet into a zero-bullet shooter. The only left-copy MOVE branch requires the
initiator to be a follower. -/
private theorem kernelC_leader_zero_no_ingress
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true)
    (hs : l.signal_B = (0 : Fin 2))
    (hb : l.bullet = (0 : Fin 3)) :
    (sinkKernelC hψ l r).1.bullet = (0 : Fin 3) := by
  have bc : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
  have sc : ∀ s : Fin 2, s = 0 ∨ s = 1 := by decide
  rcases bc r.bullet with hrb | hrb | hrb <;>
    rcases sc r.signal_B with hrs | hrs <;>
    cases hr : r.leader <;> cases hh : l.shield <;> c3c_concrete

/-- O1 in its cell-level form. It covers interior gap edges, the shooter
outgoing edge, the incoming edge at the victim, and fully exterior edges. -/
theorem blocked_step_tail_bullets_zero
    (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hi : GapInvariant hψ F C)
    (hb : GapBlocked F C) :
    ∀ j, 2 ≤ j → j ≤ F.d →
      (sinkStepC hψ F C e (F.pos j)).bullet = (0 : Fin 3) := by
  intro j hj hjd
  have hsig := gapBlocked_signal_tail hψ F C hb hi
  by_cases hleft : F.pos j = e
  · have he : e = F.pos j := hleft.symm
    subst e
    rw [sinkStepC_at_left]
    by_cases hjdEq : j = F.d
    · have hl : (C (F.pos j)).leader = true := by
        simpa [hjdEq] using hi.1.2
      have hs : (C (F.pos j)).signal_B = (0 : Fin 2) :=
        hsig j (by omega) hjd
      have hb0 : (C (F.pos j)).bullet = (0 : Fin 3) :=
        hb.2.1 j hj hjd
      exact kernelC_leader_zero_no_ingress hψ
        (C (F.pos j)) (C (F.ring.rightNeighbor (F.pos j))) hl hs hb0
    · have hjlt : j < F.d := by omega
      have hl : (C (F.pos j)).leader = false :=
        hi.2.1 j (by omega) hjlt
      have hb0 : (C (F.pos j)).bullet = (0 : Fin 3) :=
        hb.2.1 j hj hjd
      have hrn : F.ring.rightNeighbor (F.pos j) = F.pos (j + 1) := by
        rw [gap_rightNeighbor_pos]
      have hbr : (C (F.ring.rightNeighbor (F.pos j))).bullet =
          (0 : Fin 3) := by
        rw [hrn]
        exact hb.2.1 (j + 1) (by omega) (by omega)
      have hrf : (C (F.ring.rightNeighbor (F.pos j))).leader = true →
          (C (F.ring.rightNeighbor (F.pos j))).signal_B = (0 : Fin 2) := by
        intro _
        rw [hrn]
        exact hsig (j + 1) (by omega) (by omega)
      exact kernelC_no_fresh hψ
        (C (F.pos j)) (C (F.ring.rightNeighbor (F.pos j)))
        hl hrf hb0 hbr
  · by_cases hright : F.pos j = F.ring.rightNeighbor e
    · have heprev := edge_of_head F e j (by omega) hright.symm
      have hl : (C e).leader = false := by
        rw [heprev]
        exact hi.2.1 (j - 1) (by omega) (by omega)
      rw [hright, sinkStepC_at_right]
      exact kernelC_right_clear hψ (C e) (C (F.ring.rightNeighbor e)) hl
    · rw [sinkStepC_other hψ F C e (F.pos j) hleft hright]
      exact hb.2.1 j hj hjd

end LDSinkGapServiceRankPhysical
