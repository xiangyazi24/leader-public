import Leader.Wu.Elimination.SinkGapBlockedNoFreshBullet
import Leader.Wu.Elimination.SinkGapRankBellman

open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
  LDSinkGapDoneInvariant LDSinkGapBlockedPreStep LDSinkGapServiceRank
  LDSinkGapServiceRankPhysical LDSinkGapRankBellman
  FiniteUniformStoppingTree PPLLRepair LDTwoGapFrame
open Classical

namespace LDSinkGapCleanupBound

set_option autoImplicit false

variable {n ψ : Nat}

/-!
# C5: the K2 one-gap cleanup bound, with the `CRankResidual` seam removed

C3 proved rank monotonicity and the strict drop for the K2 kernel only modulo
`CRankResidual` (`hR7land`), and C3b refuted the transfer that residual was
supposed to package.  This file discharges both rank facts directly, and then
re-derives C4's four quantitative capstones without any residual hypothesis.

The two seam-free rank theorems are `gapWC_step_le'` and
`exists_gapWC_step_lt'`.  Neither goes through R7's `gapW`, whose stopping set
contains `GapBlocked` and is therefore discontinuous for K2.  They compare the
*physical* rank `gapRank` instead, using `gapWC_le_gapRank` in one direction
and `gapWC_eq_gapRank_of_not_doneC` in the other.
-/

/-! ## Rank arithmetic helpers -/

private theorem gapRank_le_of_bulletTop_le (F : GapFrame n)
    (D : Fin n → AgentState ψ) (t : Nat) (h : bulletTop F D ≤ t) :
    gapRank F D ≤ F.d + t := by
  unfold gapRank
  split
  · have := signalTop_le F D
    omega
  · omega

private theorem gapRank_congr_of_frame (F : GapFrame n)
    (C D : Fin n → AgentState ψ)
    (h : ∀ k, 1 ≤ k → k ≤ F.d → D (F.pos k) = C (F.pos k)) :
    gapRank F D = gapRank F C := by
  have hb : bulletTop F D = bulletTop F C := by
    unfold bulletTop
    apply topIdx_congr
    intro k hk hkd
    rw [h k hk hkd]
  have hs : signalTop F D = signalTop F C := by
    unfold signalTop
    apply topIdx_congr
    intro k hk hkd
    rw [h k hk hkd]
  unfold gapRank
  rw [hb, hs]

private theorem stepC_left (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ F C e e =
      (sinkKernelC hψ (C e) (C (F.ring.rightNeighbor e))).1 := by
  simp only [sinkStepC, updatePair_initiator]

/-! ## Two guard-failure criteria

Both are consequences of `ProtectedGuard` being evaluated after FIRE together
with FIRE's inertness on a follower. -/

/-- If the responder of `e` is a gap cell without a live bullet, the K2 guard
cannot hold at `e`. -/
private theorem not_guard_of_responder_bullet_ne
    (hψ : ψ > 0) (F : GapFrame n) (C : Fin n → AgentState ψ) (e : Fin n)
    (k : Nat) (he : F.ring.rightNeighbor e = F.pos k)
    (hbne : (C (F.pos k)).bullet ≠ (2 : Fin 3)) :
    ¬ ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e)) := by
  intro hg
  have hr : (C (F.ring.rightNeighbor e)).leader = false :=
    (protectedGuard_input_leaders hψ _ _ hg).2
  have hfr := fire_right_eq hψ (C e) (C (F.ring.rightNeighbor e)) (Or.inl hr)
  have hbb : (C (F.ring.rightNeighbor e)).bullet = (2 : Fin 3) :=
    (congrArg (fun s : AgentState ψ => s.bullet) hfr).symm.trans hg.2.2.2
  rw [he] at hbb
  exact hbne hbb

/-- A follower initiator can never satisfy the K2 guard. -/
private theorem not_guard_of_initiator_follower
    (hψ : ψ > 0) (F : GapFrame n) (C : Fin n → AgentState ψ) (e : Fin n)
    (hl : (C e).leader = false) :
    ¬ ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e)) := by
  intro hg
  have h := (protectedGuard_input_leaders hψ _ _ hg).1
  rw [hl] at h
  exact Bool.noConfusion h

/-! ## O2: a protected step away from the victim edge frames the gap sector -/

private theorem protected_nonvictim_frame (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hi : GapInvariant hψ F C) (hdone : ¬ GapDone F C)
    (hg : ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e)))
    (hne : e ≠ F.pos 0) :
    ∀ k, 1 ≤ k → k ≤ F.d → sinkStepC hψ F C e (F.pos k) = C (F.pos k) := by
  intro k hk hkd
  by_cases hR : F.pos k = F.ring.rightNeighbor e
  · exact absurd
      (protected_edge_is_victim_edge hψ F C e k hi hg hk hkd hR.symm) hne
  · by_cases hL : F.pos k = e
    · have hkeq : k = F.d := by
        rcases Nat.lt_or_ge k F.d with hlt | hge
        · exfalso
          have hfollow : (C e).leader = false := by
            rw [← hL]
            exact hi.2.1 k hk hlt
          exact not_guard_of_initiator_follower hψ F C e hfollow hg
        · have := hkd
          omega
      have hsig : (C e).signal_B = ⟨0, by omega⟩ := by
        rw [← hL, hkeq]
        exact signal_shooter_zero hψ F C hi hdone
      have hfl := fire_left_eq hψ (C e)
        (C (F.ring.rightNeighbor e)) (Or.inr hsig)
      rw [hL, stepC_left]
      exact (sinkKernelC_protected_initiator hψ _ _ hg).trans hfl
    · exact sinkStepC_other hψ F C e (F.pos k) hL hR

/-! ## The victim edge under the guard, on a non-blocked state -/

/-- If the K2 guard holds at the victim edge of a **non-blocked** invariant
gap, then the sector still carries a bullet strictly above position one.
The gap invariant is not needed: the guard alone pins the responder down. -/
private theorem victim_guard_bulletTop_ge_two (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ)
    (hg : ProtectedGuard hψ (C (F.pos 0))
      (C (F.ring.rightNeighbor (F.pos 0))))
    (hnb : ¬ GapBlocked F C) :
    2 ≤ bulletTop F C := by
  have hd := F.hd
  have hrn : F.ring.rightNeighbor (F.pos 0) = F.pos 1 := by
    rw [gap_rightNeighbor_pos]
  have hr : (C (F.ring.rightNeighbor (F.pos 0))).leader = false :=
    (protectedGuard_input_leaders hψ _ _ hg).2
  have hfr := fire_right_eq hψ (C (F.pos 0))
    (C (F.ring.rightNeighbor (F.pos 0))) (Or.inl hr)
  have hbb : (C (F.ring.rightNeighbor (F.pos 0))).bullet = (2 : Fin 3) :=
    (congrArg (fun s : AgentState ψ => s.bullet) hfr).symm.trans hg.2.2.2
  rw [hrn] at hbb
  have hb2 : (C (F.pos 1)).bullet = ⟨2, by omega⟩ := hbb
  have hprot : (C (F.pos 0)).shield = true ∨
      (C (F.pos 0)).signal_B = ⟨1, by omega⟩ := by
    rcases fin2_cases (C (F.pos 0)).signal_B with hs | hs
    · have hfl := fire_left_eq hψ (C (F.pos 0))
        (C (F.ring.rightNeighbor (F.pos 0))) (Or.inr hs)
      exact Or.inl
        ((congrArg (fun s : AgentState ψ => s.shield) hfl).symm.trans hg.2.1)
    · exact Or.inr hs
  rcases Nat.lt_or_ge (bulletTop F C) 2 with hlt | hge
  · exact absurd
      ⟨hb2, fun k hk hkd => bulletTop_zero_at F C (by omega) hkd, hprot⟩ hnb
  · exact hge

/-! ## R1': the seam-free K2 rank nonincrease -/

/-- Every raw K2 edge is rank nonincreasing on an active gap.  No residual. -/
theorem gapWC_step_le' (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hi : GapInvariant hψ F C)
    (hn : ¬ GapDoneC F C) (e : Fin n) :
    gapWC F (sinkStepC hψ F C e) ≤ gapWC F C := by
  classical
  have hd := F.hd
  have hpre : gapWC F C = gapRank F C := gapWC_eq_gapRank_of_not_doneC F C hn
  by_cases hb : GapBlocked F C
  · by_cases he : e = F.pos 0
    · rw [he]
      exact Nat.le_of_lt (gapWC_blocked_victim_lt hψ F C hb hi)
    · -- Blocked non-victim edge: O1 caps the successor's bullet front at one.
      have hge1 : 1 ≤ bulletTop F C := by
        apply bulletTop_ge_of F C (by omega)
        rw [hb.1]
        exact fin3_two_ne_zero
      have hle1 : bulletTop F C ≤ 1 := by
        unfold bulletTop
        apply topIdx_le_of
        intro k hk hkd
        simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]
        rw [hb.2.1 k (by omega) hkd]
      have hrankC : gapRank F C = F.d + 1 := by
        unfold gapRank
        rw [if_neg (by omega)]
        omega
      have htail := blocked_step_tail_bullets_zero hψ F C e hi hb
      have hbt : bulletTop F (sinkStepC hψ F C e) ≤ 1 := by
        unfold bulletTop
        apply topIdx_le_of
        intro k hk hkd
        simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]
        have hz : (sinkStepC hψ F C e (F.pos k)).bullet = ⟨0, by omega⟩ :=
          htail k (by omega) hkd
        rw [hz]
      have hstep := gapRank_le_of_bulletTop_le F (sinkStepC hψ F C e) 1 hbt
      have hpost := gapWC_le_gapRank F (sinkStepC hψ F C e)
      omega
  · have hOld : ¬ GapDone F C := fun h =>
      hn (GapDoneC_of_GapDone_not_blocked F C h hb)
    by_cases hg : ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e))
    · by_cases he : e = F.pos 0
      · -- The one non-framing protected edge: absorption at position one only.
        subst he
        have h2 := victim_guard_bulletTop_ge_two hψ F C hg hb
        have hrankC : gapRank F C = F.d + bulletTop F C := by
          unfold gapRank
          rw [if_neg (by omega)]
        have hkey : ∀ k, bulletTop F C < k → k ≤ F.d →
            (sinkStepC hψ F C (F.pos 0) (F.pos k)).bullet = ⟨0, by omega⟩ := by
          intro k hk hkd
          have hdn := F.hdn
          have hk3 : 3 ≤ k := by omega
          have hkn : k < n := by omega
          have hnpos : (0 : Nat) < n := by omega
          have h1n : (1 : Nat) < n := by omega
          have hne0 : F.pos k ≠ F.pos 0 := F.pos_ne hkn hnpos (by omega)
          have hrn : F.ring.rightNeighbor (F.pos 0) = F.pos 1 := by
            rw [gap_rightNeighbor_pos]
          have hne1 : F.pos k ≠ F.ring.rightNeighbor (F.pos 0) := by
            rw [hrn]
            exact F.pos_ne hkn h1n (by omega)
          rw [sinkStepC_other hψ F C (F.pos 0) (F.pos k) hne0 hne1]
          exact bulletTop_zero_at F C hk hkd
        have hbt : bulletTop F (sinkStepC hψ F C (F.pos 0)) ≤
            bulletTop F C := by
          unfold bulletTop
          apply topIdx_le_of
          intro k hk hkd
          simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]
          rw [hkey k hk hkd]
        have hstep := gapRank_le_of_bulletTop_le F
          (sinkStepC hψ F C (F.pos 0)) (bulletTop F C) hbt
        have hpost := gapWC_le_gapRank F (sinkStepC hψ F C (F.pos 0))
        omega
      · have hfr := protected_nonvictim_frame hψ F C e hi hOld hg he
        have hcongr := gapRank_congr_of_frame F C (sinkStepC hψ F C e) hfr
        have hpost := gapWC_le_gapRank F (sinkStepC hψ F C e)
        omega
    · rw [sinkStepC_eq_of_not_guard hψ F C e hg]
      have hle := gapRank_step_le hψ F C hi hOld e
      have hpost := gapWC_le_gapRank F (sinkStep hψ F C e)
      omega

/-! ## R2': the seam-free strict drop

The drop edge is produced explicitly, exactly as in R7's `gapW_drop`, but the
conclusion is about the *physical* rank `gapRank` (plus the K2 stopping set),
never about `gapW`.  This is what avoids C3b's refuted transfer: R7's rank is
killed to zero on `GapBlocked`, which K2 does not treat as terminal. -/

private theorem exists_strict_R7_edge (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hi : GapInvariant hψ F C)
    (hn : ¬ GapDoneC F C) (hnb : ¬ GapBlocked F C) :
    ∃ e : Fin n, ¬ ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e)) ∧
      (GapDoneC F (sinkStep hψ F C e) ∨
        gapRank F (sinkStep hψ F C e) < gapRank F C) := by
  classical
  have hdone : ¬ GapDone F C := fun h =>
    hn (GapDoneC_of_GapDone_not_blocked F C h hnb)
  have hdpos : 2 ≤ F.d := F.hd
  have hdn : F.d < n := F.hdn
  rcases Nat.eq_zero_or_pos (bulletTop F C) with hb0 | hbpos
  · -- Bullet-free sector: the absence signal advances one cell.
    have hbz : ∀ i, 1 ≤ i → i ≤ F.d →
        (C (F.pos i)).bullet = ⟨0, by omega⟩ := fun i hi1 hid =>
      bulletTop_zero_at F C (by omega) hid
    have hsltd : signalTop F C < F.d := by
      rcases Nat.lt_or_ge (signalTop F C) F.d with h | h
      · exact h
      · exfalso
        have heq : signalTop F C = F.d := Nat.le_antisymm (signalTop_le F C) h
        have hpos : 0 < signalTop F C := by omega
        have h1 := signalTop_one_at F C hpos
        rw [heq] at h1
        exact hdone (Or.inl ⟨h1, hbz⟩)
    refine ⟨F.pos (signalTop F C), ?_, Or.inr ?_⟩
    · refine not_guard_of_responder_bullet_ne hψ F C _ (signalTop F C + 1)
        (gap_rightNeighbor_pos F (signalTop F C)) ?_
      rw [hbz (signalTop F C + 1) (by omega) (by omega)]
      exact fin3_zero_ne_two
    · have hresp : sinkStep hψ F C (F.pos (signalTop F C))
          (F.pos (signalTop F C + 1)) =
          (sinkKernel hψ (C (F.pos (signalTop F C)))
            (C (F.pos (signalTop F C + 1)))).2 :=
        sinkStep_pos_responder hψ F C (signalTop F C) (by omega)
      have hsig1 : (sinkStep hψ F C (F.pos (signalTop F C))
          (F.pos (signalTop F C + 1))).signal_B = ⟨1, by omega⟩ := by
        rw [hresp]
        rcases Nat.eq_zero_or_pos (signalTop F C) with h0 | hpos
        · have habs : (sinkKernel hψ (C (F.pos (signalTop F C)))
              (C (F.pos (signalTop F C + 1)))).2.signal_B =
              ⟨1, by omega⟩ := by
            rw [h0]
            exact (sinkKernel_victim_absorb hψ (C (F.pos 0)) (C (F.pos 1))
              hi.1.1 (hi.2.1 1 (by omega) (by omega))
              (by rw [hbz 1 (by omega) (by omega)];
                  exact fin3_zero_ne_two)).2.1
          exact habs
        · have hidle := sinkKernel_idle hψ (C (F.pos (signalTop F C)))
            (C (F.pos (signalTop F C + 1))) (hi.2.1 _ hpos hsltd)
            (interior_no_right_fire hψ F C hi hdone (signalTop F C + 1)
              (by omega) (by omega))
            (hbz (signalTop F C + 1) (by omega) (by omega))
            (hi.2.2.1 _ hsltd)
          exact hidle.2.2.1 (signalTop_one_at F C hpos)
      have hbstep :
          bulletTop F (sinkStep hψ F C (F.pos (signalTop F C))) = 0 := by
        have := bulletTop_step_le hψ F C hi hdone (F.pos (signalTop F C))
        omega
      have hsstep : signalTop F C + 1 ≤
          signalTop F (sinkStep hψ F C (F.pos (signalTop F C))) :=
        signalTop_ge_of F _ (by omega) hsig1
      have hrank : gapRank F (sinkStep hψ F C (F.pos (signalTop F C))) ≤
          F.d - signalTop F C - 1 := by
        unfold gapRank
        rw [if_pos hbstep]
        omega
      have hrankC : gapRank F C = F.d - signalTop F C := by
        unfold gapRank
        rw [if_pos hb0]
      omega
  · rcases Nat.lt_or_ge (bulletTop F C) 2 with h1 | h2
    · -- One bullet, already adjacent to the victim.
      have ht1 : bulletTop F C = 1 := by omega
      have hb1 : (C (F.pos 1)).bullet ≠ ⟨0, by omega⟩ := by
        have h := bulletTop_ne_zero F C hbpos
        rwa [ht1] at h
      have hrest : ∀ k, 2 ≤ k → k ≤ F.d →
          (C (F.pos k)).bullet = ⟨0, by omega⟩ := fun k hk2 hkd =>
        bulletTop_zero_at F C (by omega) hkd
      have hrankC : gapRank F C = F.d + 1 := by
        unfold gapRank
        rw [if_neg (by omega), ht1]
      have hfollow1 : (C (F.pos 1)).leader = false :=
        hi.2.1 1 (by omega) (by omega)
      have hrn : F.ring.rightNeighbor (F.pos 0) = F.pos 1 := by
        rw [gap_rightNeighbor_pos]
      rcases fin3_cases (C (F.pos 1)).bullet with h | h | h
      · exact absurd h hb1
      · -- A dummy at the victim is absorbed and the signal is seeded.
        refine ⟨F.pos 0, ?_, Or.inr ?_⟩
        · refine not_guard_of_responder_bullet_ne hψ F C _ 1 hrn ?_
          rw [h]
          exact fin3_one_ne_two
        · have hab := sinkKernel_victim_absorb hψ (C (F.pos 0)) (C (F.pos 1))
            hi.1.1 hfollow1 (by rw [h]; exact fin3_one_ne_two)
          have hresp : sinkStep hψ F C (F.pos 0) (F.pos 1) =
              (sinkKernel hψ (C (F.pos 0)) (C (F.pos 1))).2 :=
            sinkStep_pos_responder hψ F C 0 (by omega)
          have hbstep : bulletTop F (sinkStep hψ F C (F.pos 0)) = 0 := by
            apply bulletTop_eq_zero_of
            intro i hi1 hid
            by_cases hii : i = 1
            · rw [hii, hresp]
              exact hab.1
            · rw [sinkStep_pos_eq hψ F C 0 i (by omega) hi1 hid
                (by omega) (by omega)]
              exact hrest i (by omega) hid
          have hsig : (sinkStep hψ F C (F.pos 0) (F.pos 1)).signal_B =
              ⟨1, by omega⟩ := by
            rw [hresp]
            exact hab.2.1
          have hsstep : 1 ≤ signalTop F (sinkStep hψ F C (F.pos 0)) :=
            signalTop_ge_of F _ (by omega) hsig
          have hrank : gapRank F (sinkStep hψ F C (F.pos 0)) ≤ F.d - 1 := by
            unfold gapRank
            rw [if_pos hbstep]
            omega
          omega
      · -- A live bullet at an unprotected victim deletes it.
        have hprot : ¬ ((C (F.pos 0)).shield = true ∨
            (C (F.pos 0)).signal_B = ⟨1, by omega⟩) := fun hp =>
          hnb ⟨h, hrest, hp⟩
        have hsh : (C (F.pos 0)).shield = false := by
          cases hshv : (C (F.pos 0)).shield
          · rfl
          · exact absurd (Or.inl hshv) hprot
        have hsg : (C (F.pos 0)).signal_B = ⟨0, by omega⟩ := by
          rcases fin2_cases (C (F.pos 0)).signal_B with hx | hx
          · exact hx
          · exact absurd (Or.inr hx) hprot
        refine ⟨F.pos 0, ?_, Or.inl ?_⟩
        · intro hgg
          have hfl := fire_left_eq hψ (C (F.pos 0))
            (C (F.ring.rightNeighbor (F.pos 0))) (Or.inr hsg)
          have hshtrue : (C (F.pos 0)).shield = true :=
            (congrArg (fun s : AgentState ψ => s.shield) hfl).symm.trans
              hgg.2.1
          rw [hsh] at hshtrue
          exact Bool.noConfusion hshtrue
        · have hkill := sinkKernel_kill hψ (C (F.pos 0)) (C (F.pos 1))
            hi.1.1 hsh hsg hfollow1 h
          have hinit : sinkStep hψ F C (F.pos 0) (F.pos 0) =
              (sinkKernel hψ (C (F.pos 0)) (C (F.pos 1))).1 :=
            sinkStep_pos_initiator hψ F C 0
          have hstep0 : (sinkStep hψ F C (F.pos 0) (F.pos 0)).leader =
              false := by
            rw [hinit]
            exact hkill
          exact Or.inr (Or.inl hstep0)
    · -- The front bullet is still in the interior: it moves one cell down.
      obtain ⟨m, hm⟩ : ∃ m, bulletTop F C = m + 1 :=
        ⟨bulletTop F C - 1, by omega⟩
      have hm1 : 1 ≤ m := by omega
      have hmd : m + 1 ≤ F.d := by
        have := bulletTop_le F C
        omega
      have hbne : (C (F.pos (m + 1))).bullet ≠ ⟨0, by omega⟩ := by
        have h := bulletTop_ne_zero F C hbpos
        rwa [hm] at h
      have hbval : 0 < (C (F.pos (m + 1))).bullet.val := by
        rcases Nat.eq_zero_or_pos (C (F.pos (m + 1))).bullet.val with hz | hp
        · exact absurd (Fin.ext hz) hbne
        · exact hp
      have hfollowm : (C (F.pos m)).leader = false :=
        hi.2.1 m hm1 (by omega)
      have hmove := sinkKernel_move_down hψ (C (F.pos m)) (C (F.pos (m + 1)))
        hfollowm
        (interior_no_right_fire hψ F C hi hdone (m + 1) (by omega) hmd)
        hbval (hi.2.2.1 m (by omega))
      refine ⟨F.pos m, not_guard_of_initiator_follower hψ F C
        (F.pos m) hfollowm, Or.inr ?_⟩
      have hinit : sinkStep hψ F C (F.pos m) (F.pos m) =
          (sinkKernel hψ (C (F.pos m)) (C (F.pos (m + 1)))).1 :=
        sinkStep_pos_initiator hψ F C m
      have hresp : sinkStep hψ F C (F.pos m) (F.pos (m + 1)) =
          (sinkKernel hψ (C (F.pos m)) (C (F.pos (m + 1)))).2 :=
        sinkStep_pos_responder hψ F C m (by omega)
      have hstepm : (sinkStep hψ F C (F.pos m) (F.pos m)).bullet =
          (C (F.pos (m + 1))).bullet := by
        rw [hinit]
        exact hmove.1
      have hge : m ≤ bulletTop F (sinkStep hψ F C (F.pos m)) := by
        apply bulletTop_ge_of F _ (by omega)
        rw [hstepm]
        exact hbne
      have hle : bulletTop F (sinkStep hψ F C (F.pos m)) ≤ m := by
        apply topIdx_le_of
        intro i hi' hid
        simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]
        have hzero : (sinkStep hψ F C (F.pos m) (F.pos i)).bullet =
            ⟨0, by omega⟩ := by
          by_cases hi1 : i = m + 1
          · rw [hi1, hresp]
            exact hmove.2.2.1
          · rw [sinkStep_pos_eq hψ F C m i (by omega) (by omega) hid
              (by omega) hi1]
            exact bulletTop_zero_at F C (by omega) hid
        rw [hzero]
      have hrankC : gapRank F C = F.d + (m + 1) := by
        unfold gapRank
        rw [if_neg (by omega), hm]
      have hrankstep : gapRank F (sinkStep hψ F C (F.pos m)) = F.d + m := by
        unfold gapRank
        rw [if_neg (by omega)]
        omega
      omega

/-- R2': some raw K2 edge strictly lowers the K2 service rank on every active
gap.  No residual hypothesis. -/
theorem exists_gapWC_step_lt' (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hi : GapInvariant hψ F C)
    (hn : ¬ GapDoneC F C) :
    ∃ e : Fin n, gapWC F (sinkStepC hψ F C e) < gapWC F C := by
  classical
  by_cases hb : GapBlocked F C
  · exact ⟨F.pos 0, gapWC_blocked_victim_lt hψ F C hb hi⟩
  · obtain ⟨e, hg, hcase⟩ := exists_strict_R7_edge hψ F C hi hn hb
    refine ⟨e, ?_⟩
    rw [sinkStepC_eq_of_not_guard hψ F C e hg]
    have hpos := gapWC_pos_of_not_doneC hψ F C hi hn
    have hpre := gapWC_eq_gapRank_of_not_doneC F C hn
    rcases hcase with hd | hlt
    · rw [gapWC_doneC F _ hd]
      omega
    · have hle := gapWC_le_gapRank F (sinkStep hψ F C e)
      omega

/-! ## C5: C4's four quantitative capstones, with `hR7land` removed

Same statements as `LDSinkGapRankBellman`, same proof structure, but the uniform
residual hypothesis is gone: the two rank inputs are now `gapWC_step_le'` and
`exists_gapWC_step_lt'`.  The stopped-process objects (`ActiveC`,
`LDSinkGapRankBellman.stepC`, `potentialC`) are reused verbatim from C4, since
their definitions never mentioned the residual. -/

private theorem rankCertificate' (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hi : GapInvariant hψ F C) :
    n * gapWC F C ≤ n * (2 * F.d) ∧
    (∀ D : Fin n → AgentState ψ, GapDoneC F D → n * gapWC F D = 0) ∧
    ∀ D : Fin n → AgentState ψ, GapInvariant hψ F D → ¬ GapDoneC F D →
      n + (List.ofFn (fun e : Fin n =>
        n * gapWC F (sinkStepC hψ F D e))).sum ≤
          n * (n * gapWC F D) := by
  exact rank_to_bellman
    (sinkStepC hψ F) (GapInvariant hψ F) (GapDoneC F)
    (gapWC F) (2 * F.d)
    (gapWC_le_two_d hψ F)
    (gapWC_doneC F)
    (fun D e hD hnD => gapWC_step_le' hψ F D hD hnD e)
    (by
      intro D hD hnD
      obtain ⟨e, he⟩ := exists_gapWC_step_lt' hψ F D hD hnD
      exact ⟨e, by omega⟩)
    C hi

/-- B1': `V D = n * gapWC F D` is an unconditional division-free `2nd`
certificate for the K2 kernel on one interleader gap. -/
theorem sinkC_gap_cleanup_2nd' (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hi : GapInvariant hψ F C) :
    ∃ V : (Fin n → AgentState ψ) → Nat,
      V C ≤ 2 * n * F.d ∧
      (∀ D, GapDoneC F D → V D = 0) ∧
      ∀ D, GapInvariant hψ F D → ¬ GapDoneC F D →
        n + (List.ofFn (fun e : Fin n =>
          V (sinkStepC hψ F D e))).sum ≤ n * V D := by
  obtain ⟨hle, hzero, hbell⟩ := rankCertificate' hψ F C hi
  refine ⟨(fun D => n * gapWC F D), ?_, hzero, hbell⟩
  calc
    n * gapWC F C ≤ n * (2 * F.d) := hle
    _ = 2 * n * F.d := by ac_rfl

/-- A rank budget pays for a finite successful K2 scheduler word. -/
theorem gapC_reaches_done' (hψ : ψ > 0) (F : GapFrame n) :
    ∀ (m : Nat) (C : Fin n → AgentState ψ),
      GapInvariant hψ F C → gapWC F C ≤ m →
      ∃ w : List (Fin n),
        w.length ≤ m ∧ GapDoneC F (gapRunC hψ F C w) := by
  intro m
  induction m with
  | zero =>
      intro C hi hm
      by_cases hd : GapDoneC F C
      · exact ⟨[], Nat.le_refl 0, hd⟩
      · exfalso
        obtain ⟨e, he⟩ := exists_gapWC_step_lt' hψ F C hi hd
        omega
  | succ m ih =>
      intro C hi hm
      by_cases hd : GapDoneC F C
      · exact ⟨[], Nat.zero_le _, hd⟩
      · obtain ⟨e, he⟩ := exists_gapWC_step_lt' hψ F C hi hd
        rcases sinkStepC_invariant_or_done' hψ F C e hi hd with
          hdone | hi'
        · refine ⟨[e], ?_, hdone⟩
          change 1 ≤ m + 1
          omega
        · have hnext : gapWC F (sinkStepC hψ F C e) ≤ m := by omega
          obtain ⟨w, hw, hdone⟩ := ih (sinkStepC hψ F C e) hi' hnext
          refine ⟨e :: w, ?_, ?_⟩
          · simpa only [List.length_cons] using Nat.succ_le_succ hw
          · simpa only [gapRunC_cons] using hdone

/-- B2': an unconditional successful scheduler word of length at most `2 d`. -/
theorem gapC_cleanup_within_two_d' (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (hi : GapInvariant hψ F C) :
    ∃ w : List (Fin n), w.length ≤ 2 * F.d ∧
      GapDoneC F (gapRunC hψ F C w) :=
  gapC_reaches_done' hψ F (2 * F.d) C hi (gapWC_le_two_d hψ F C hi)

/-- B3': the stopped K2 process pays one unit per active raw interaction. -/
theorem stepC_natBellmanSuperSolution' (hψ : ψ > 0) (F : GapFrame n) :
    NatBellmanSuperSolution (LDSinkGapRankBellman.stepC hψ F) 1
      (potentialC hψ F) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x
  have hsum := FiniteUniformStoppingTree.ofFn_sum_eq
    (fun e : Fin n => potentialC hψ F (LDSinkGapRankBellman.stepC hψ F x e))
    (fun e : Fin n => n * gapWC F (sinkStepC hψ F x.1 e))
    (fun e => potentialC_step_eq hψ F x e)
  change 1 * n + (List.ofFn (fun e : Fin n =>
    potentialC hψ F (LDSinkGapRankBellman.stepC hψ F x e))).sum ≤
      n * (n * gapWC F x.1)
  rw [Nat.one_mul, hsum]
  exact (rankCertificate' hψ F x.1 x.2.1).2.2 x.1 x.2.1 x.2.2

/-- B4': the unconditional finite-horizon truncated-cost bound. -/
theorem sinkC_gap_cleanup_truncated' (hψ : ψ > 0) (F : GapFrame n)
    (x : StopNode (ActiveC hψ F)) (T : Nat) :
    truncatedActiveCostNumerator (LDSinkGapRankBellman.stepC hψ F) x T ≤
      n ^ T * (n * 2 * F.d) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (LDSinkGapRankBellman.stepC hψ F) 1 (potentialC hψ F)
    (stepC_natBellmanSuperSolution' hψ F) x T
  have hcost :
      truncatedActiveCostNumerator (LDSinkGapRankBellman.stepC hψ F) x T ≤
        n ^ T * potentialC hψ F x := by
    simpa only [Nat.one_mul] using h
  exact Nat.le_trans hcost
    (Nat.mul_le_mul_left (n ^ T) (potentialC_le hψ F x))

end LDSinkGapCleanupBound

#print axioms LDSinkGapCleanupBound.gapWC_step_le'
#print axioms LDSinkGapCleanupBound.exists_gapWC_step_lt'
#print axioms LDSinkGapCleanupBound.sinkC_gap_cleanup_2nd'
#print axioms LDSinkGapCleanupBound.gapC_reaches_done'
#print axioms LDSinkGapCleanupBound.gapC_cleanup_within_two_d'
#print axioms LDSinkGapCleanupBound.stepC_natBellmanSuperSolution'
#print axioms LDSinkGapCleanupBound.sinkC_gap_cleanup_truncated'
