import Leader.Wu.RaceEntrance.Transit
import Leader.Wu.RaceEntrance.BirthBudget

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair LDSinkGapCleanup LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptCells LDSinkTwoGapDeletion
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapRaceEntranceTransit LDSinkTwoGapRaceEntranceFreshService

namespace LDSinkTwoGapRaceEntranceArrivalService

variable {n psi : Nat}

/-!
A fresh unique live shot reaches attack position one at cost at most
`n*(d-1)`, or a tagged endpoint is deleted earlier.  The counter is a
proof-level position projection of the actual physical bullet, with its
update proved in `RaceEntranceTransit`.  The physical target here is a
parked live shot or deletion, not the stronger recovery-clean entrance.
-/

def ArrivedOrDeleted (F : TwoGapFrame n) (C : Fin n → AgentState psi) : Prop :=
  (C (F.attack.pos 1)).bullet = (2 : Fin 3) ∨ NoResetSuccess F C

noncomputable def arrivalStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (e : Fin n) : StopNode (AState n psi) := by
  classical
  exact if ArrivedOrDeleted F (attemptStepConf hpsi F b e) then .success
    else .active (postState hpsi F b e)

structure TransitState (hpsi : psi > 0) (F : TwoGapFrame n) where
  raw : AActive hpsi F
  position : Nat
  lower : 1 < position
  upper : position ≤ F.attack.d
  live : (raw.val.conf (F.attack.pos position)).bullet = (2 : Fin 3)

private theorem transit_not_absorbed (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) (e : Fin n) :
    ¬ NoResetAbsorbedAt F z.raw.val e (attemptStepConf hpsi F z.raw.val e) := by
  intro ha
  have hb := z.raw.property.tag.parked_iff.mp ha.1
  have hpos := old_bullet_unique hpsi F z.raw 1 z.position
    (by decide) (by have h := F.attack.hd; omega)
    (by have h := z.lower; omega) z.upper (by rw [hb]; decide)
    (by rw [z.live]; decide)
  have hlo := z.lower
  omega

noncomputable def transitNext (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) (e : Fin n)
    (hn : ¬ ArrivedOrDeleted F (attemptStepConf hpsi F z.raw.val e)) :
    TransitState hpsi F := by
  classical
  let y := postState hpsi F z.raw.val e
  have hns : ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val e) := fun h => hn (.inr h)
  have hna := transit_not_absorbed hpsi F z e
  have hraw : attemptStepRaw hpsi F z.raw.val e = .active y := by
    simp only [attemptStepRaw, if_neg hns, if_neg hna]
    rfl
  have hy : AInvariant hpsi F y := (attemptLaws_K2 hpsi F).continuation z.raw e y hraw
  have hr := transit_unique_row hpsi F z.raw z.position z.lower z.upper z.live e
  have hu : 1 < nextShotPosition F z.position e := by
    have hp := hr.1
    by_cases hle : 1 < nextShotPosition F z.position e
    · exact hle
    · have he : nextShotPosition F z.position e = 1 := by omega
      have hb := hr.2.2.1
      rw [he] at hb
      exact (hn (.inl hb)).elim
  exact ⟨⟨y, hy⟩, nextShotPosition F z.position e, hu, hr.2.1, hr.2.2.1⟩

noncomputable def transitStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) (e : Fin n) : StopNode (TransitState hpsi F) := by
  classical
  exact if h : ArrivedOrDeleted F (attemptStepConf hpsi F z.raw.val e) then .success
    else .active (transitNext hpsi F z e h)

def transitWork (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (TransitState hpsi F) → Nat
  | .active z => z.position - 1
  | .success => 0
  | .failure => 0

def transitPotential (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (TransitState hpsi F)) : Nat := n * transitWork hpsi F x

private theorem transitWork_child_le (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) (e : Fin n) :
    transitWork hpsi F (transitStep hpsi F z e) ≤ transitWork hpsi F (.active z) := by
  classical
  unfold transitStep
  split
  · exact Nat.zero_le _
  · change nextShotPosition F z.position e - 1 ≤ z.position - 1
    unfold nextShotPosition
    split <;> omega

private theorem transitWork_good_drop (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) :
    transitWork hpsi F (transitStep hpsi F z (F.attack.pos (z.position - 1))) + 1 ≤
      transitWork hpsi F (.active z) := by
  classical
  have hlo := z.lower
  unfold transitStep
  split
  · change 0 + 1 ≤ z.position - 1
    omega
  · change nextShotPosition F z.position (F.attack.pos (z.position - 1)) - 1 + 1 ≤
      z.position - 1
    rw [nextShotPosition, if_pos rfl]
    omega

theorem transit_bellman (hpsi : psi > 0) (F : TwoGapFrame n) :
    NatBellmanSuperSolution (transitStep hpsi F) 1 (transitPotential hpsi F) := by
  refine ⟨rfl, rfl, ?_⟩
  intro z
  have hr := LDSinkGapCleanup.ofFn_sum_lt n
    (fun e => transitWork hpsi F (transitStep hpsi F z e))
    (transitWork hpsi F (.active z)) (F.attack.pos (z.position - 1))
    (transitWork_child_le hpsi F z) (transitWork_good_drop hpsi F z)
  change 1 * n + (List.ofFn (fun e : Fin n =>
    n * transitWork hpsi F (transitStep hpsi F z e))).sum ≤
      n * (n * transitWork hpsi F (.active z))
  rw [Nat.one_mul, ofFn_sum_mul_left]
  have hs := Nat.mul_le_mul_left n hr
  rw [Nat.mul_add, Nat.mul_one] at hs
  omega

theorem transit_truncated_cost (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) (T : Nat) :
    truncatedActiveCostNumerator (transitStep hpsi F) (.active z) T ≤
      n ^ T * (n * (F.attack.d - 1)) := by
  have hc := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (transitStep hpsi F) 1 (transitPotential hpsi F)
    (transit_bellman hpsi F) (.active z) T
  have hp : transitPotential hpsi F (.active z) ≤ n * (F.attack.d - 1) := by
    apply Nat.mul_le_mul_left
    exact Nat.sub_le_sub_right z.upper 1
  exact Nat.le_trans (by simpa only [Nat.one_mul] using hc)
    (Nat.mul_le_mul_left (n ^ T) hp)

private theorem transit_no_failure (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) (e : Fin n) : transitStep hpsi F z e ≠ .failure := by
  classical
  unfold transitStep
  split <;> intro he <;> cases he

theorem transit_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) :
    n ^ (2 * n * (F.attack.d - 1)) ≤
      2 * successCount (transitStep hpsi F) (.active z) (2 * n * (F.attack.d - 1)) := by
  let T := 2 * n * (F.attack.d - 1)
  have hp : 0 < T := by
    have hn := F.attack.ring.hn
    have hd := F.attack.hd
    exact Nat.mul_pos (Nat.mul_pos (by decide) hn) (by omega)
  have hc := transit_truncated_cost hpsi F z T
  have hactive := two_mul_activeCount_le_pow_of_scaled_cost
    (transitStep hpsi F) (.active z) hp (by decide : 0 < 1)
    (num := n * (F.attack.d - 1))
    (by simpa only [Nat.one_mul, Nat.mul_comm] using hc)
    (by dsimp only [T]; simp only [Nat.mul_one, Nat.mul_assoc, Nat.le_refl])
  have hf := BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
    (transitStep hpsi F) (transit_no_failure hpsi F) z T
  have hparts := node_count_partition (transitStep hpsi F) (.active z) T
  change n ^ T ≤ 2 * successCount (transitStep hpsi F) (.active z) T
  omega

def transitRel (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (TransitState hpsi F) → StopNode (AState n psi) → Prop
  | .failure, _ => True
  | _, .success => True
  | .active z, .active b => z.raw.val.conf = b.conf
  | _, _ => False

private theorem transitRel_success (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (TransitState hpsi F)) : transitRel hpsi F x .success := by
  cases x <;> trivial

private theorem transitRel_active_next (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : TransitState hpsi F) (b : AState n psi) (he : z.raw.val.conf = b.conf)
    (e : Fin n) :
    transitRel hpsi F (transitStep hpsi F z e) (arrivalStep hpsi F b e) := by
  classical
  have hc : attemptStepConf hpsi F z.raw.val e = attemptStepConf hpsi F b e := by
    simp only [attemptStepConf_eq_sinkStepC, he]
  unfold arrivalStep
  by_cases hs : ArrivedOrDeleted F (attemptStepConf hpsi F b e)
  · rw [if_pos hs]
    exact transitRel_success hpsi F _
  · rw [if_neg hs]
    have hns : ¬ ArrivedOrDeleted F (attemptStepConf hpsi F z.raw.val e) := by
      simpa only [hc] using hs
    unfold transitStep
    rw [dif_neg hns]
    exact hc

/-- The proof counter and reinitialized ghost erase to the same physical
configuration on every edge; no physical field or scheduler time is reset. -/
theorem transit_simulation (hpsi : psi > 0) (F : TwoGapFrame n) :
    SuccessSimulation (transitStep hpsi F) (arrivalStep hpsi F) (transitRel hpsi F) where
  terminal := by
    intro x y h
    cases x with
    | failure => exact Nat.zero_le _
    | active z => exact Nat.zero_le _
    | success =>
        cases y with
        | success => exact Nat.le_refl _
        | failure => exact h.elim
        | active b => exact h.elim
  next := by
    intro x y h e
    cases x with
    | failure => trivial
    | success =>
        cases y with
        | success => trivial
        | failure => exact h.elim
        | active b => exact h.elim
    | active z =>
        cases y with
        | success => exact transitRel_success hpsi F _
        | failure => exact h.elim
        | active b => exact transitRel_active_next hpsi F z b h e

/-- The fresh-shot producer can supply its certificate on an arbitrary
retained phase.  Its actual configuration reaches parked live or deletion
with half mass by `2*n*(d-1)`. -/
theorem fresh_to_arrival_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hf : AttemptEntrance hpsi F ⟨b.conf, .transit⟩) :
    n ^ (2 * n * (F.attack.d - 1)) ≤
      2 * successCount (arrivalStep hpsi F) (.active b) (2 * n * (F.attack.d - 1)) := by
  let z : TransitState hpsi F :=
    ⟨⟨⟨b.conf, .transit⟩, hf.1⟩, F.attack.d, (by have h := F.attack.hd; omega),
      Nat.le_refl _, hf.2.2⟩
  have hm := transit_half hpsi F z
  have hs := successCount_le_of_simulation (transitStep hpsi F) (arrivalStep hpsi F)
    (transitRel hpsi F) (transit_simulation hpsi F) (.active z) (.active b)
    rfl (2 * n * (F.attack.d - 1))
  exact Nat.le_trans hm (Nat.mul_le_mul_left 2 hs)

noncomputable def arrivalHandoff (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (e : Fin n) : StopNode (AState n psi) := by
  classical
  exact if NoResetSuccess F (attemptStepConf hpsi F b e) then .success
    else .active (postState hpsi F b e)

noncomputable def birthArrivalStep (hpsi : psi > 0) (F : TwoGapFrame n) :
    Sum (AState n psi) (AState n psi) → Fin n →
      StopNode (Sum (AState n psi) (AState n psi)) :=
  sequentialStep (freshStep hpsi F) (arrivalStep hpsi F) (arrivalHandoff hpsi F)

def birthArrivalRel : StopNode (Sum (AState n psi) (AState n psi)) →
    StopNode (AState n psi) → Prop
  | .failure, _ => True
  | _, .success => True
  | .active (.inl x), .active b => x = b
  | .active (.inr x), .active b => x = b
  | _, _ => False

private theorem birthArrivalRel_success
    (x : StopNode (Sum (AState n psi) (AState n psi))) :
    birthArrivalRel x .success := by
  cases x with
  | success => trivial
  | failure => trivial
  | active s => cases s <;> trivial

private theorem birthArrivalRel_race (x : StopNode (AState n psi)) :
    birthArrivalRel (inRace x) x := by
  cases x <;> trivial

private theorem birthArrivalRel_fresh_next (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (e : Fin n) :
    birthArrivalRel (birthArrivalStep hpsi F (.inl b) e) (arrivalStep hpsi F b e) := by
  classical
  unfold arrivalStep
  by_cases ha : ArrivedOrDeleted F (attemptStepConf hpsi F b e)
  · rw [if_pos ha]
    exact birthArrivalRel_success _
  · rw [if_neg ha]
    have hd : ¬ NoResetSuccess F (attemptStepConf hpsi F b e) := fun h => ha (.inr h)
    simp only [birthArrivalStep, sequentialStep, freshStep]
    by_cases hf : FreshOrDeleted hpsi F (attemptStepConf hpsi F b e)
    · rw [if_pos hf]
      simp only [arrivalHandoff, if_neg hd, inRace, birthArrivalRel]
    · rw [if_neg hf]
      rfl

/-- Eager birth-to-transit composition follows the same raw configuration
at every edge.  Any earlier parked arrival is already accepted by the target. -/
theorem birthArrival_simulation (hpsi : psi > 0) (F : TwoGapFrame n) :
    SuccessSimulation (birthArrivalStep hpsi F) (arrivalStep hpsi F) birthArrivalRel where
  terminal := by
    intro x y h
    cases x with
    | failure => exact Nat.zero_le _
    | active z => exact Nat.zero_le _
    | success =>
        cases y with
        | success => exact Nat.le_refl _
        | failure => exact h.elim
        | active b => exact h.elim
  next := by
    intro x y h e
    cases x with
    | failure => trivial
    | success =>
        cases y with
        | success => trivial
        | failure => exact h.elim
        | active b => exact h.elim
    | active z =>
        cases y with
        | success => exact birthArrivalRel_success _
        | failure => cases z <;> exact h.elim
        | active b =>
            cases z with
            | inl a =>
                change a = b at h
                subst a
                exact birthArrivalRel_fresh_next hpsi F b e
            | inr a =>
                change a = b at h
                subst a
                exact birthArrivalRel_race (arrivalStep hpsi F b e)

/-- Every fresh stopping handoff either has a deleted endpoint already or
supplies the proved physical fresh-shot predicate for the transit service. -/
private theorem arrivalHandoff_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (e : Fin n) (hf : freshStep hpsi F b e = .success) :
    n ^ (2 * n * (F.attack.d - 1)) ≤
      2 * successCount (arrivalStep hpsi F) (arrivalHandoff hpsi F b e)
        (2 * n * (F.attack.d - 1)) := by
  classical
  have htarget : FreshOrDeleted hpsi F (attemptStepConf hpsi F b e) := by
    by_cases ht : FreshOrDeleted hpsi F (attemptStepConf hpsi F b e)
    · exact ht
    · simp only [freshStep, if_neg ht] at hf
      cases hf
  unfold arrivalHandoff
  by_cases hd : NoResetSuccess F (attemptStepConf hpsi F b e)
  · rw [if_pos hd]
    simp only [successCount, treeWeight_success, successWeight, Nat.mul_one]
    omega
  · rw [if_neg hd]
    rcases htarget with hshot | hdeleted
    · exact fresh_to_arrival_half hpsi F (postState hpsi F b e) hshot
    · exact (hd hdeleted).elim

/-- Actual parked-live arrival or tagged deletion has constant mass from
every physical gap pair.  The `10*n*d` horizon includes repeated dummy
births, cleanup, fresh live birth, and actual transit.  Recovery cleanliness
at this parked arrival remains a separate entrance obligation. -/
theorem gapPair_arrival_quarter (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) :
    n ^ (10 * n * F.attack.d) ≤
      4 * successCount (arrivalStep hpsi F) (.active b) (10 * n * F.attack.d) := by
  have hbirth := LDSinkTwoGapRaceEntranceBirthBudget.fresh_birth_half hpsi F b hg
  have hseq := sequential_mass (freshStep hpsi F) (arrivalStep hpsi F)
    (arrivalHandoff hpsi F) b (2 * n * (4 * F.attack.d + 1))
    (2 * n * (F.attack.d - 1)) 2 2 hbirth (arrivalHandoff_half hpsi F)
  have hs := successCount_le_of_simulation (birthArrivalStep hpsi F)
    (arrivalStep hpsi F) birthArrivalRel (birthArrival_simulation hpsi F)
    (.active (.inl b)) (.active b) rfl
    (2 * n * (4 * F.attack.d + 1) + 2 * n * (F.attack.d - 1))
  have htime : 2 * n * (4 * F.attack.d + 1) + 2 * n * (F.attack.d - 1) =
      10 * n * F.attack.d := by
    rw [← Nat.mul_add]
    have hd : (4 * F.attack.d + 1) + (F.attack.d - 1) = 5 * F.attack.d := by
      have h := F.attack.hd
      omega
    rw [hd]
    calc
      2 * n * (5 * F.attack.d) = (2 * 5) * n * F.attack.d := by ac_rfl
      _ = 10 * n * F.attack.d := rfl
  change n ^ _ ≤ 4 * successCount (birthArrivalStep hpsi F) (.active (.inl b)) _ at hseq
  rw [htime] at hseq hs
  exact Nat.le_trans hseq (Nat.mul_le_mul_left 4 hs)

end LDSinkTwoGapRaceEntranceArrivalService

#print axioms LDSinkTwoGapRaceEntranceArrivalService.transit_bellman
#print axioms LDSinkTwoGapRaceEntranceArrivalService.transit_truncated_cost
#print axioms LDSinkTwoGapRaceEntranceArrivalService.transit_simulation
#print axioms LDSinkTwoGapRaceEntranceArrivalService.fresh_to_arrival_half
#print axioms LDSinkTwoGapRaceEntranceArrivalService.birthArrival_simulation
#print axioms LDSinkTwoGapRaceEntranceArrivalService.gapPair_arrival_quarter
