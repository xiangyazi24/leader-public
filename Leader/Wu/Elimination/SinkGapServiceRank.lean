import Leader.Wu.Elimination.SinkGapStageFrames
import Leader.Wu.Elimination.TwoGapFrame

open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
  LDSinkGapDoneInvariant LDSinkGapBlockedPreStep PPLLRepair LDTwoGapFrame
open Classical

namespace LDSinkGapServiceRank

set_option autoImplicit false

variable {n ψ : Nat}

/-- K2 service rank.  Unlike the R7 rank, a blocked state is not terminal. -/
noncomputable def gapWC (F : GapFrame n) (C : Fin n → AgentState ψ) : Nat := by
  classical
  exact
    if GapDoneC F C then 0
    else if bulletTop F C = 0 then F.d - signalTop F C
    else F.d + bulletTop F C

private theorem topIdx_eq_zero_of_false (P : Nat → Bool) :
    ∀ m : Nat,
      (∀ k, 1 ≤ k → k ≤ m → P k = false) →
      topIdx P m = 0 := by
  intro m
  induction m with
  | zero =>
      intro _
      rfl
  | succ m ih =>
      intro h
      unfold topIdx
      have hlast : P (m + 1) = false :=
        h (m + 1) (by omega) (Nat.le_refl _)
      rw [hlast]
      apply ih
      intro k hk hkm
      exact h k hk (Nat.le_trans hkm (Nat.le_succ m))

private theorem bulletTop_eq_zero_of_all
    (F : GapFrame n) (C : Fin n → AgentState ψ)
    (hz : ∀ k, 1 ≤ k → k ≤ F.d →
      (C (F.pos k)).bullet = (0 : Fin 3)) :
    bulletTop F C = 0 := by
  unfold bulletTop
  apply topIdx_eq_zero_of_false
  intro k hk hkd
  have h := hz k hk hkd
  rw [h]
  decide

private theorem one_le_bulletTop_of_live_one
    (F : GapFrame n) (C : Fin n → AgentState ψ)
    (h1d : 1 ≤ F.d)
    (hb : (C (F.pos 1)).bullet = (2 : Fin 3)) :
    1 ≤ bulletTop F C := by
  rcases Nat.eq_zero_or_pos (bulletTop F C) with h0 | hpos
  · have hlt : bulletTop F C < 1 := by omega
    have hf := topIdx_above
      (fun k => decide (0 < (C (F.pos k)).bullet.val)) hlt h1d
    have ht : decide (0 < (C (F.pos 1)).bullet.val) = true := by
      rw [hb]
      decide
    rw [ht] at hf
    cases hf
  · exact hpos

private theorem one_le_signalTop_of_signal_one
    (F : GapFrame n) (C : Fin n → AgentState ψ)
    (h1d : 1 ≤ F.d)
    (hs : (C (F.pos 1)).signal_B = (1 : Fin 2)) :
    1 ≤ signalTop F C := by
  rcases Nat.eq_zero_or_pos (signalTop F C) with h0 | hpos
  · have hlt : signalTop F C < 1 := by omega
    have hf := topIdx_above
      (fun k => decide ((C (F.pos k)).signal_B.val = 1)) hlt h1d
    have ht : decide ((C (F.pos 1)).signal_B.val = 1) = true := by
      rw [hs]
      decide
    rw [ht] at hf
    cases hf
  · exact hpos

private theorem pos_ne_of_le_d (F : GapFrame n) (i j : Nat)
    (hi : i ≤ F.d) (hj : j ≤ F.d) (hij : i ≠ j) :
    F.pos i ≠ F.pos j := by
  intro h
  exact hij (pos_injective_below_n F i j
    (Nat.lt_of_le_of_lt hi F.hdn)
    (Nat.lt_of_le_of_lt hj F.hdn) h)

/-- Away from the old blocked stopping set, R7's `gapW` is exactly K2's
`gapWC`. -/
theorem gapW_eq_gapWC_of_not_blocked
    (F : GapFrame n) (C : Fin n → AgentState ψ)
    (hb : ¬ GapBlocked F C) :
    gapW F C = gapWC F C := by
  classical
  unfold gapW gapWC
  by_cases hdc : GapDoneC F C
  · have hd : GapDone F C := by
      rcases hdc with hc | he
      · exact Or.inl hc
      · exact Or.inr (Or.inl he)
    rw [if_pos hd, if_pos hdc]
  · have hd : ¬ GapDone F C := by
      intro h
      apply hdc
      exact GapDoneC_of_GapDone_not_blocked F C h hb
    rw [if_neg hd, if_neg hdc]
    unfold gapRank
    rfl

/-- R1: K2's rank is bounded by `2 d`.  The proof only needs the range
bounds on `bulletTop` and `signalTop`. -/
theorem gapWC_le_two_d (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (_hi : GapInvariant hψ F C) :
    gapWC F C ≤ 2 * F.d := by
  unfold gapWC
  split
  · exact Nat.zero_le _
  · split
    · have hs := signalTop_le F C
      omega
    · have hb := bulletTop_le F C
      omega

/-- The blocked K2 victim edge is a strict service step: its incoming live
bullet is absorbed, every higher bullet is already zero, and SIGNAL puts `1`
at `pos 1`.  Hence the post-rank is at most `d-1`, while the pre-rank is at
least `d+1`. -/
theorem gapWC_blocked_victim_lt (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ)
    (hb : GapBlocked F C) (hi : GapInvariant hψ F C) :
    gapWC F (sinkStepC hψ F C (F.pos 0)) < gapWC F C := by
  classical
  have hd := F.hd
  have h1d : 1 ≤ F.d := by omega
  have hpreTop := one_le_bulletTop_of_live_one F C h1d hb.1
  have hpreNZ : bulletTop F C ≠ 0 := by omega
  have hnot := gapBlocked_not_doneC hψ F C hb hi
  have hstep := blocked_pre_steps_protected_or_fire hψ F C hb hi
  have hzero : ∀ k, 1 ≤ k → k ≤ F.d →
      (sinkStepC hψ F C (F.pos 0) (F.pos k)).bullet = (0 : Fin 3) := by
    intro k hk hkd
    by_cases hk1 : k = 1
    · subst k
      exact hstep.2.2.1
    · have hk2 : 2 ≤ k := by omega
      have hne0 : F.pos k ≠ F.pos 0 :=
        pos_ne_of_le_d F k 0 hkd (by omega) (by omega)
      have hne1 : F.pos k ≠ F.ring.rightNeighbor (F.pos 0) := by
        rw [gap_rightNeighbor_pos F 0]
        exact pos_ne_of_le_d F k 1 hkd (by omega) (by omega)
      rw [sinkStepC_other hψ F C (F.pos 0) (F.pos k) hne0 hne1]
      exact hb.2.1 k hk2 hkd
  have hpostTop :
      bulletTop F (sinkStepC hψ F C (F.pos 0)) = 0 :=
    bulletTop_eq_zero_of_all F (sinkStepC hψ F C (F.pos 0)) hzero
  have hpostSignal :
      1 ≤ signalTop F (sinkStepC hψ F C (F.pos 0)) :=
    one_le_signalTop_of_signal_one F
      (sinkStepC hψ F C (F.pos 0)) h1d hstep.2.2.2
  unfold gapWC
  rw [if_neg hnot, if_neg hpreNZ]
  by_cases hdone : GapDoneC F (sinkStepC hψ F C (F.pos 0))
  · rw [if_pos hdone]
    omega
  · rw [if_neg hdone, if_pos hpostTop]
    omega

/-- The one residual interface left by the current C2b public surface.

The name `hR7land` is retained deliberately: its main missing case is the old
R7 step from a nonblocked state whose successor first satisfies `GapBlocked`.
C2b also does not expose a rank-frame theorem for a blocked non-victim edge,
or a rank projection for a nonblocked protected edge, so those two projection
cases are carried in the same explicit seam instead of being hidden as axioms.

The second conjunct is only consumed for the edge supplied by R7's
`gapW_drop`. -/
def CRankResidual (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) : Prop :=
  ∀ e,
    ((GapBlocked F C ∧ e ≠ F.pos 0 ∧
        GapInvariant hψ F (sinkStepC hψ F C e)) ∨
      (¬ GapBlocked F C ∧
        (ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e)) ∨
          GapBlocked F (sinkStep hψ F C e)))) →
    gapWC F (sinkStepC hψ F C e) ≤ gapWC F C ∧
      (¬ GapBlocked F C →
        gapW F (sinkStep hψ F C e) + 1 ≤ gapW F C →
        gapWC F (sinkStepC hψ F C e) < gapWC F C)

/-- R2, modulo exactly the explicit `hR7land` residual above.  Off the C guard
and away from a newly blocked R7 successor this is a direct transport of
`gapW_step_le`; the blocked victim edge is discharged by the theorem above. -/
theorem gapWC_step_le (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hi : GapInvariant hψ F C) (hn : ¬ GapDoneC F C)
    (hR7land : CRankResidual hψ F C) :
    gapWC F (sinkStepC hψ F C e) ≤ gapWC F C := by
  classical
  by_cases hb : GapBlocked F C
  · by_cases he : e = F.pos 0
    · subst e
      exact Nat.le_of_lt (gapWC_blocked_victim_lt hψ F C hb hi)
    · rcases blocked_pre_other_edges_frame hψ F C e hb hi he with
        hdone | hi'
      · have hz : gapWC F (sinkStepC hψ F C e) = 0 := by
          unfold gapWC
          rw [if_pos hdone]
        rw [hz]
        exact Nat.zero_le _
      · exact (hR7land e (Or.inl ⟨hb, he, hi'⟩)).1
  · have hOld : ¬ GapDone F C := by
      intro h
      apply hn
      exact GapDoneC_of_GapDone_not_blocked F C h hb
    by_cases hg :
        ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e))
    · exact (hR7land e (Or.inr ⟨hb, Or.inl hg⟩)).1
    · have heq := sinkStepC_eq_of_not_guard hψ F C e hg
      by_cases hp : GapBlocked F (sinkStep hψ F C e)
      · exact (hR7land e (Or.inr ⟨hb, Or.inr hp⟩)).1
      · have hw := gapW_step_le hψ F C hi hOld e
        have hpre := gapW_eq_gapWC_of_not_blocked F C hb
        have hpost := gapW_eq_gapWC_of_not_blocked F
          (sinkStep hψ F C e) hp
        rw [hpre, hpost] at hw
        rw [heq]
        exact hw

/-- R3, with the same residual seam.  A blocked state uses the concrete victim
edge.  A nonblocked state reuses R7's strict-drop edge, transporting it through
`gapW = gapWC` unless that edge is one of the explicitly isolated residual
cases. -/
theorem exists_gapWC_step_lt (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ)
    (hi : GapInvariant hψ F C) (hn : ¬ GapDoneC F C)
    (hR7land : CRankResidual hψ F C) :
    ∃ e : Fin n, gapWC F (sinkStepC hψ F C e) < gapWC F C := by
  classical
  by_cases hb : GapBlocked F C
  · exact ⟨F.pos 0, gapWC_blocked_victim_lt hψ F C hb hi⟩
  · have hOld : ¬ GapDone F C := by
      intro h
      apply hn
      exact GapDoneC_of_GapDone_not_blocked F C h hb
    rcases gapW_drop hψ F C hi hOld with ⟨e, hdrop⟩
    refine ⟨e, ?_⟩
    by_cases hg :
        ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e))
    · exact (hR7land e (Or.inr ⟨hb, Or.inl hg⟩)).2 hb hdrop
    · have heq := sinkStepC_eq_of_not_guard hψ F C e hg
      by_cases hp : GapBlocked F (sinkStep hψ F C e)
      · exact (hR7land e (Or.inr ⟨hb, Or.inr hp⟩)).2 hb hdrop
      · have hpre := gapW_eq_gapWC_of_not_blocked F C hb
        have hpost := gapW_eq_gapWC_of_not_blocked F
          (sinkStep hψ F C e) hp
        rw [hpre, hpost] at hdrop
        rw [heq]
        omega

end LDSinkGapServiceRank

#print axioms LDSinkGapServiceRank.gapWC_le_two_d
#print axioms LDSinkGapServiceRank.gapW_eq_gapWC_of_not_blocked
#print axioms LDSinkGapServiceRank.gapWC_blocked_victim_lt
#print axioms LDSinkGapServiceRank.gapWC_step_le
#print axioms LDSinkGapServiceRank.exists_gapWC_step_lt
