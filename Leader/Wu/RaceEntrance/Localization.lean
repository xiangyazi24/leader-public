import Leader.Wu.RaceEntrance.Transit
import Leader.Wu.RaceEntrance.StageComposition

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair LDTwoGapFrame LDSinkGapCleanup
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptResidual LDSinkTwoGapAttemptCells
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant LDSinkTwoGapRaceEntranceTransit

namespace LDSinkTwoGapRaceEntranceLocalization

variable {n psi : Nat}

/-! Transport a certified unique live shot only as far as a fixed positive
interior position.  Every edge is the original K2 edge, and the terminal
payload retains the actual post-state and the unique shot at that position. -/

structure LocalState (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) where
  raw : AActive hpsi F
  position : Nat
  lower : L < position
  upper : position ≤ F.attack.d
  live : (raw.val.conf (F.attack.pos position)).bullet = (2 : Fin 3)

private theorem local_not_absorbed (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) (hL : 2 ≤ L)
    (z : LocalState hpsi F L) (e : Fin n) :
    ¬ NoResetAbsorbedAt F z.raw.val e (attemptStepConf hpsi F z.raw.val e) := by
  intro ha
  have hb := z.raw.property.tag.parked_iff.mp ha.1
  have hp := old_bullet_unique hpsi F z.raw 1 z.position
    (by decide) (by have h := F.attack.hd; omega)
    (by have h := z.lower; omega) z.upper (by rw [hb]; decide) (by rw [z.live]; decide)
  have hlo := z.lower
  omega

theorem local_post_invariant (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) (hL : 2 ≤ L)
    (z : LocalState hpsi F L) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val e)) :
    AInvariant hpsi F (postState hpsi F z.raw.val e) := by
  have ha := local_not_absorbed hpsi F L hL z e
  apply (attemptLaws_K2 hpsi F).continuation z.raw e _
  simp only [attemptStepRaw, if_neg hn, if_neg ha]
  rfl

private theorem local_position_bounds (F : TwoGapFrame n) (L t : Nat) (ht : L < t) (e : Fin n) :
    L ≤ nextShotPosition F t e ∧ nextShotPosition F t e ≤ t := by
  unfold nextShotPosition
  split <;> omega

noncomputable def localNext (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) (hL : 2 ≤ L)
    (z : LocalState hpsi F L) (e : Fin n)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val e))
    (hu : nextShotPosition F z.position e ≠ L) : LocalState hpsi F L := by
  have hp := local_position_bounds F L z.position z.lower e
  have hl := transit_position_row hpsi F z.raw z.position (by have h := z.lower; omega)
    z.upper z.live e
  exact ⟨⟨postState hpsi F z.raw.val e, local_post_invariant hpsi F L hL z e hn⟩,
    nextShotPosition F z.position e, by omega, Nat.le_trans hp.2 z.upper, hl⟩

noncomputable def localStep (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) (hL : 2 ≤ L)
    (z : LocalState hpsi F L) (e : Fin n) : StopNode (LocalState hpsi F L) := by
  classical
  exact if h : NoResetSuccess F (attemptStepConf hpsi F z.raw.val e) then .success
    else if hu : nextShotPosition F z.position e = L then .success
    else .active (localNext hpsi F L hL z e h hu)

theorem local_active_data (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) (hL : 2 ≤ L)
    (z y : LocalState hpsi F L) (e : Fin n) (he : localStep hpsi F L hL z e = .active y) :
    y.raw.val = postState hpsi F z.raw.val e ∧ ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val e) := by
  classical
  unfold localStep at he
  split at he
  · cases he
  · rename_i hn
    split at he
    · cases he
    · exact ⟨congrArg (fun z => z.raw.val) (StopNode.active.inj he).symm, hn⟩

theorem local_success_payload (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) (hL : 2 ≤ L)
    (z : LocalState hpsi F L) (e : Fin n) (he : localStep hpsi F L hL z e = .success) :
    NoResetSuccess F (attemptStepConf hpsi F z.raw.val e) ∨
      (AInvariant hpsi F (postState hpsi F z.raw.val e) ∧
        (attemptStepConf hpsi F z.raw.val e (F.attack.pos L)).bullet = (2 : Fin 3)) := by
  classical
  by_cases hn : NoResetSuccess F (attemptStepConf hpsi F z.raw.val e)
  · exact .inl hn
  · have hu : nextShotPosition F z.position e = L := by
      simp only [localStep, dif_neg hn] at he
      split at he
      · assumption
      · cases he
    have hl := transit_position_row hpsi F z.raw z.position (by have h := z.lower; omega)
      z.upper z.live e
    rw [hu] at hl
    exact .inr ⟨local_post_invariant hpsi F L hL z e hn, hl⟩

def localWork (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) :
    StopNode (LocalState hpsi F L) → Nat
  | .active z => z.position - L
  | .success => 0
  | .failure => 0

def localPotential (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat)
    (x : StopNode (LocalState hpsi F L)) : Nat := n * localWork hpsi F L x

private theorem local_child_le (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) (hL : 2 ≤ L)
    (z : LocalState hpsi F L) (e : Fin n) :
    localWork hpsi F L (localStep hpsi F L hL z e) ≤ z.position - L := by
  classical
  unfold localStep
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · exact Nat.sub_le_sub_right (local_position_bounds F L z.position z.lower e).2 L

private theorem local_good_drop (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) (hL : 2 ≤ L)
    (z : LocalState hpsi F L) :
    localWork hpsi F L (localStep hpsi F L hL z (F.attack.pos (z.position - 1))) + 1 ≤
      z.position - L := by
  classical
  have hlo := z.lower
  unfold localStep
  split
  · change 0 + 1 ≤ _
    omega
  · split
    · change 0 + 1 ≤ _
      omega
    · change nextShotPosition F z.position (F.attack.pos (z.position - 1)) - L + 1 ≤ _
      rw [nextShotPosition, if_pos rfl]
      omega

theorem localization_bellman (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) (hL : 2 ≤ L) :
    NatBellmanSuperSolution (localStep hpsi F L hL) 1 (localPotential hpsi F L) := by
  refine ⟨rfl, rfl, ?_⟩
  intro z
  have hr := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => localWork hpsi F L (localStep hpsi F L hL z e)) (z.position - L)
    (F.attack.pos (z.position - 1)) (local_child_le hpsi F L hL z) (local_good_drop hpsi F L hL z)
  change 1 * n + (List.ofFn (fun e => n * localWork hpsi F L (localStep hpsi F L hL z e))).sum ≤
    n * (n * (z.position - L))
  rw [Nat.one_mul, ofFn_sum_mul_left]
  have h := Nat.mul_le_mul_left n hr
  rw [Nat.mul_add, Nat.mul_one] at h
  omega

private theorem local_no_failure (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) (hL : 2 ≤ L)
    (z : LocalState hpsi F L) (e : Fin n) : localStep hpsi F L hL z e ≠ .failure := by
  classical
  unfold localStep
  split
  · intro h; cases h
  · split <;> intro h <;> cases h

/-- Half of the original scheduler words localize the real retained shot
or delete an endpoint by twice its uniform service budget. -/
theorem localization_half (hpsi : psi > 0) (F : TwoGapFrame n) (L : Nat) (hL : 2 ≤ L)
    (z : LocalState hpsi F L) :
    n ^ (2 * n * (F.attack.d - L)) ≤
      2 * successCount (localStep hpsi F L hL) (.active z) (2 * n * (F.attack.d - L)) := by
  let T := 2 * n * (F.attack.d - L)
  have hT : 0 < T := by
    have hlo := z.lower
    have hup := z.upper
    exact Nat.mul_pos (Nat.mul_pos (by decide) F.attack.ring.hn) (by omega)
  have hc := truncatedActiveCostNumerator_mul_le_of_natSuperSolution (localStep hpsi F L hL)
    1 (localPotential hpsi F L) (localization_bellman hpsi F L hL) (.active z) T
  have hp : localPotential hpsi F L (.active z) ≤ n * (F.attack.d - L) :=
    Nat.mul_le_mul_left n (Nat.sub_le_sub_right z.upper L)
  have hcost := Nat.le_trans (by simpa only [Nat.one_mul] using hc) (Nat.mul_le_mul_left (n ^ T) hp)
  have ha := two_mul_activeCount_le_pow_of_scaled_cost (localStep hpsi F L hL) (.active z)
    hT (by decide : 0 < 1) (num := n * (F.attack.d - L))
    (by simpa only [Nat.mul_one, Nat.one_mul, Nat.mul_comm] using hcost)
    (by dsimp only [T]; simp only [Nat.mul_one, Nat.mul_assoc, Nat.le_refl])
  have hf := BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure (localStep hpsi F L hL)
    (local_no_failure hpsi F L hL) z T
  have hparts := node_count_partition (localStep hpsi F L hL) (.active z) T
  change n ^ T ≤ 2 * successCount (localStep hpsi F L hL) (.active z) T
  omega

end LDSinkTwoGapRaceEntranceLocalization

#print axioms LDSinkTwoGapRaceEntranceLocalization.local_post_invariant
#print axioms LDSinkTwoGapRaceEntranceLocalization.local_active_data
#print axioms LDSinkTwoGapRaceEntranceLocalization.local_success_payload
#print axioms LDSinkTwoGapRaceEntranceLocalization.localization_bellman
#print axioms LDSinkTwoGapRaceEntranceLocalization.localization_half
