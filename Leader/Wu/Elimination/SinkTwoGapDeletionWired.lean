import Leader.Wu.Elimination.SinkTwoGapDeletion

open FiniteUniformStoppingTree
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptCells
open LDSinkTwoGapEntrance LDSinkTwoGapDeletion
open LDSinkGapCleanup LDTwoGapFrame PPLLRepair
open Classical

namespace LDSinkTwoGapDeletionWired

set_option autoImplicit false

noncomputable section

variable {n ψ : Nat}

/-! ## Exact domains and actual active reachability -/

/-- The physical successor, without a new raw interaction or configuration reset. -/
def postState (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) : AState n ψ :=
  advanceAState F x (attemptStepConf hψ F x e)

/-- Both rank fields of the unconditional K2 record, on their actual domain.
This does not generalize either field to arbitrary raw AState values. -/
theorem invariant_rank_laws_K2
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (hi : AInvariant hψ F x) :
    (∀ e : Fin n,
      rawStoppedR F (attemptStepRaw hψ F x e) ≤ R F x) ∧
    (∃ e : Fin n,
      rawStoppedR F (attemptStepRaw hψ F x e) < R F x) := by
  exact ⟨(attemptLaws_K2 hψ F).nonincrease ⟨x, hi⟩,
    (attemptLaws_K2 hψ F).strictDrop ⟨x, hi⟩⟩

/-- Reachability through actual active edges, from an explicit seed predicate. -/
inductive ActiveReach {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (Seed : S → Prop) : S → Prop where
  | base {x : S} : Seed x → ActiveReach step Seed x
  | next {x y : S} (e : Fin m) :
      ActiveReach step Seed x → step x e = .active y →
      ActiveReach step Seed y

/-- A closure theorem proves invariance for the transition it actually closes. -/
theorem ActiveReach.invariant {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (Seed P : S → Prop)
    (hseed : ∀ x, Seed x → P x)
    (hstep : ∀ x e y, P x → step x e = .active y → P y)
    (x : S) (hx : ActiveReach step Seed x) : P x := by
  induction hx with
  | base hs => exact hseed _ hs
  | next e _ he ih => exact hstep _ e _ ih he

/-- Reachability for the stopped attempt, not for its failure-reactivating
entrance wrapper. Raw failures have no active successors in this relation. -/
abbrev AttemptReach (hψ : ψ > 0) (F : TwoGapFrame n) :=
  ActiveReach (attemptStepRaw hψ F) (AInvariant hψ F)

/-- This is the unconditional reachability consequence of K2 continuation. -/
theorem attemptReach_invariant
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (hx : AttemptReach hψ F x) : AInvariant hψ F x := by
  exact ActiveReach.invariant
    (attemptStepRaw hψ F) (AInvariant hψ F) (AInvariant hψ F)
    (fun _ hi => hi)
    (fun y e z hi he =>
      (attemptLaws_K2 hψ F).continuation ⟨y, hi⟩ e z he) x hx

/-- Absorption decrease on every state reachable before the attempt stops. -/
theorem absorption_drop_on_attemptReach
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (hx : AttemptReach hψ F x) (e : Fin n)
    (hf : attemptStepRaw hψ F x e = .failure) :
    R F (postState hψ F x e) < R F x := by
  exact absorption_drop_on_invariant hψ F x e
    (attemptReach_invariant hψ F x hx) hf

/-- The entrance's real active reachability includes reactivated failures. -/
abbrev EntranceReach (hψ : ψ > 0) (F : TwoGapFrame n) :=
  ActiveReach (entranceStep hψ F) (AInvariant hψ F)

/-! ## Identify the additional entrance edges -/

theorem entrance_normal_form
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n) :
    entranceStep hψ F x e =
      if EntranceSuccess F (attemptStepConf hψ F x e) then .success
      else .active (postState hψ F x e) := by
  classical
  by_cases hE : EntranceSuccess F (attemptStepConf hψ F x e)
  · simp [entranceStep, hE]
  · have hs : ¬ NoResetSuccess F (attemptStepConf hψ F x e) :=
      fun hs => hE (Or.inr hs)
    by_cases ha : NoResetAbsorbedAt F x e (attemptStepConf hψ F x e) <;>
      simp [entranceStep, hE, attemptStepRaw, hs, ha,
        reactivateFailure, postState]

theorem entrance_active_data_wired
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x y : AState n ψ) (e : Fin n)
    (hy : entranceStep hψ F x e = .active y) :
    ¬ EntranceSuccess F (attemptStepConf hψ F x e) ∧
      y = postState hψ F x e := by
  classical
  rw [entrance_normal_form] at hy
  by_cases hE : EntranceSuccess F (attemptStepConf hψ F x e)
  · rw [if_pos hE] at hy
    cases hy
  · rw [if_neg hE] at hy
    exact ⟨hE, (StopNode.active.inj hy).symm⟩

/-- Every entrance continuation is either a raw active continuation or a
reactivated raw failure. The latter is not covered by AttemptClosed. -/
theorem entrance_active_source_cases
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x y : AState n ψ) (e : Fin n)
    (hy : entranceStep hψ F x e = .active y) :
    attemptStepRaw hψ F x e = .active y ∨
      (attemptStepRaw hψ F x e = .failure ∧
        y = postState hψ F x e) := by
  classical
  have hd := entrance_active_data_wired hψ F x y e hy
  have hs : ¬ NoResetSuccess F (attemptStepConf hψ F x e) :=
    fun hs => hd.1 (Or.inr hs)
  by_cases ha : NoResetAbsorbedAt F x e (attemptStepConf hψ F x e)
  · exact Or.inr
      ⟨(attemptStepRaw_failure_iff hψ F x e).mpr ⟨hs, ha⟩, hd.2⟩
  · have hr : attemptStepRaw hψ F x e = .active (postState hψ F x e) := by
      simp [attemptStepRaw, hs, ha, postState]
    exact Or.inl (hr.trans (congrArg StopNode.active hd.2.symm))

/-- An invariant can first be lost along entrance reachability only on a
reactivated absorption. K2 continuation proves the other branch outright. -/
theorem entrance_first_loss_is_failure
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x y : AState n ψ) (e : Fin n)
    (hi : AInvariant hψ F x)
    (hy : entranceStep hψ F x e = .active y)
    (hout : ¬ AInvariant hψ F y) :
    attemptStepRaw hψ F x e = .failure := by
  rcases entrance_active_source_cases hψ F x y e hy with hr | hr
  · exact (hout ((attemptLaws_K2 hψ F).continuation ⟨x, hi⟩ e y hr)).elim
  · exact hr.1

/-- A precise obstruction to asserting absorption closure. If the failed
attempt's post-state no longer has the parked live bullet, the old invariant
is false there: advanceAState keeps parked, while parked_iff requires live.
The post-bullet premise is explicit; this is not a new kernel-clearing claim. -/
theorem failure_post_not_invariant_of_not_live
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n)
    (hf : attemptStepRaw hψ F x e = .failure)
    (hb : (attemptStepConf hψ F x e (F.attack.pos 1)).bullet ≠ (2 : Fin 3)) :
    ¬ AInvariant hψ F (postState hψ F x e) := by
  have hp : x.phase = .parked :=
    ((attemptStepRaw_failure_iff hψ F x e).mp hf).2.1
  intro hi
  have hp' : (postState hψ F x e).phase = .parked := by
    simp [postState, advanceAState, advanceAPhase, hp]
  exact hb (hi.tag.parked_iff.mp hp')

/-! ## All entrance rank facts on the invariant domain are discharged -/

theorem entrance_nonincrease_on_invariant
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (hi : AInvariant hψ F x) (e : Fin n) :
    rawStoppedR F (entranceStep hψ F x e) ≤ R F x := by
  classical
  by_cases hE : EntranceSuccess F (attemptStepConf hψ F x e)
  · rw [entrance_normal_form, if_pos hE]
    exact Nat.zero_le _
  · have hy : entranceStep hψ F x e = .active (postState hψ F x e) := by
      rw [entrance_normal_form, if_neg hE]
    rw [hy]
    rcases entrance_active_source_cases hψ F x (postState hψ F x e) e hy
      with hr | hr
    · have hl := (attemptLaws_K2 hψ F).nonincrease ⟨x, hi⟩ e
      rw [hr] at hl
      exact hl
    · exact Nat.le_of_lt (absorption_drop_on_invariant hψ F x e hi hr.1)

theorem entrance_strictDrop_on_invariant
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (hi : AInvariant hψ F x) :
    ∃ e : Fin n, rawStoppedR F (entranceStep hψ F x e) < R F x := by
  classical
  obtain ⟨e, he⟩ := (attemptLaws_K2 hψ F).strictDrop ⟨x, hi⟩
  refine ⟨e, ?_⟩
  by_cases hE : EntranceSuccess F (attemptStepConf hψ F x e)
  · rw [entrance_normal_form, if_pos hE]
    exact R_pos F x
  · have hy : entranceStep hψ F x e = .active (postState hψ F x e) := by
      rw [entrance_normal_form, if_neg hE]
    rw [hy]
    rcases entrance_active_source_cases hψ F x (postState hψ F x e) e hy
      with hr | hr
    · rw [hr] at he
      exact he
    · exact absorption_drop_on_invariant hψ F x e hi hr.1

/-- REMAINING REACHABLE-RANK OBLIGATION, NOT A PROVED K2 INSTANCE.
No premise is required at unreachable states or invariant reachable states.
The missing facts concern only the actual entrance process after it has left
AInvariant. This avoids the old global RawAttemptRankLaws and the global
AbsorptionOutsideInvariant, without pretending that raw-failure reactivation
is covered by AttemptClosed. No probability or cost inequality is assumed. -/
structure ReachableEntranceRankResidual
    (hψ : ψ > 0) (F : TwoGapFrame n) : Prop where
  /-- Every raw edge from an outside-invariant reachable entrance state
  must be nonincreasing for the actual entrance classifier and current R. -/
  nonincrease : ∀ (x : AState n ψ),
    EntranceReach hψ F x → ¬ AInvariant hψ F x → ∀ e : Fin n,
      rawStoppedR F (entranceStep hψ F x e) ≤ R F x
  /-- At every such reachable state there must be at least one strict edge.
  This includes the post-absorption recovery states, not only fresh attempts. -/
  strictDrop : ∀ (x : AState n ψ),
    EntranceReach hψ F x → ¬ AInvariant hψ F x →
      ∃ e : Fin n, rawStoppedR F (entranceStep hψ F x e) < R F x

/-- A genuine proof of entrance-reachable invariance would make the new
residual vacuous. The antecedent is not supplied by AttemptClosed alone. -/
theorem reachableRankResidual_of_reachable_invariant
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hclosed : ∀ x, EntranceReach hψ F x → AInvariant hψ F x) :
    ReachableEntranceRankResidual hψ F := by
  constructor
  · intro x hx hout e
    exact (hout (hclosed x hx)).elim
  · intro x hx hout
    exact (hout (hclosed x hx)).elim

/-! ## Bellman and half mass on actual reachable entrance runs -/

private theorem sum_slack {m r : Nat} (f : Fin m → Nat)
    (hle : ∀ e, f e ≤ r) (hlt : ∃ e, f e < r) :
    1 + (List.ofFn f).sum ≤ m * r := by
  induction m with
  | zero =>
      obtain ⟨e, _⟩ := hlt
      exact Fin.elim0 e
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, Nat.succ_mul]
      obtain ⟨e, he⟩ := hlt
      cases e using Fin.cases with
      | zero =>
          have ht := ofFn_sum_le
            (fun i : Fin m => f i.succ) (fun _ : Fin m => r)
            (fun i => hle i.succ)
          rw [FiniteUniformStoppingTree.ofFn_sum_const] at ht
          omega
      | succ e =>
          have ht := ih (fun i : Fin m => f i.succ)
            (fun i => hle i.succ) ⟨e, he⟩
          have h0 := hle 0
          omega

/-- Bellman is proved at every actual reachable active entrance state.
No all-raw EntranceBellman theorem is asserted. -/
theorem entrance_bellman_on_reach
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hRank : ReachableEntranceRankResidual hψ F)
    (x : AState n ψ) (hx : EntranceReach hψ F x) :
    n + (List.ofFn (fun e : Fin n =>
      entrancePotential F (entranceStep hψ F x e))).sum ≤
        n * entrancePotential F (.active x) := by
  classical
  let f : Fin n → Nat := fun e => rawStoppedR F (entranceStep hψ F x e)
  have hr : (∀ e, f e ≤ R F x) ∧ (∃ e, f e < R F x) := by
    by_cases hi : AInvariant hψ F x
    · exact ⟨entrance_nonincrease_on_invariant hψ F x hi,
        entrance_strictDrop_on_invariant hψ F x hi⟩
    · exact ⟨hRank.nonincrease x hx hi, hRank.strictDrop x hx hi⟩
  have hslack := sum_slack f hr.1 hr.2
  have hp : ∀ z : StopNode (AState n ψ),
      entrancePotential F z = n * rawStoppedR F z := by
    intro z
    cases z <;> simp [entrancePotential, rawStoppedR]
  have hsum :
      (List.ofFn (fun e : Fin n =>
        entrancePotential F (entranceStep hψ F x e))).sum =
        n * (List.ofFn f).sum := by
    calc
      (List.ofFn (fun e : Fin n =>
        entrancePotential F (entranceStep hψ F x e))).sum =
          (List.ofFn (fun e : Fin n => n * f e)).sum :=
        ofFn_sum_eq _ _ (fun e => hp (entranceStep hψ F x e))
      _ = n * (List.ofFn f).sum := ofFn_sum_mul_left n f
  calc
    n + (List.ofFn (fun e : Fin n =>
      entrancePotential F (entranceStep hψ F x e))).sum =
        n * (1 + (List.ofFn f).sum) := by
      rw [hsum, Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * R F x) := Nat.mul_le_mul_left n hslack
    _ = n * entrancePotential F (.active x) := rfl

/-- Local Bellman induction needs only actual active successors. Reachability
is extended by the selected edge, including a reactivated absorption edge. -/
theorem entrance_cost_on_reach
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hRank : ReachableEntranceRankResidual hψ F)
    (x : AState n ψ) (hx : EntranceReach hψ F x) (T : Nat) :
    truncatedActiveCostNumerator (entranceStep hψ F) (.active x) T ≤
      n ^ T * entrancePotential F (.active x) := by
  induction T generalizing x with
  | zero => exact Nat.zero_le _
  | succ T ih =>
      have hchild : ∀ e : Fin n,
          truncatedActiveCostNumerator (entranceStep hψ F)
            (entranceStep hψ F x e) T ≤
          n ^ T * entrancePotential F (entranceStep hψ F x e) := by
        intro e
        cases he : entranceStep hψ F x e with
        | active y => exact ih y (ActiveReach.next e hx he)
        | success =>
            cases T <;> simp [truncatedActiveCostNumerator, entrancePotential]
        | failure =>
            cases T <;> simp [truncatedActiveCostNumerator, entrancePotential]
      calc
        truncatedActiveCostNumerator (entranceStep hψ F) (.active x) (T + 1) =
            n ^ (T + 1) + (List.ofFn (fun e : Fin n =>
              truncatedActiveCostNumerator (entranceStep hψ F)
                (entranceStep hψ F x e) T)).sum := rfl
        _ ≤ n ^ (T + 1) + (List.ofFn (fun e : Fin n =>
              n ^ T * entrancePotential F (entranceStep hψ F x e))).sum :=
          Nat.add_le_add_left (ofFn_sum_le _ _ hchild) _
        _ = n ^ T * (n + (List.ofFn (fun e : Fin n =>
              entrancePotential F (entranceStep hψ F x e))).sum) := by
          rw [ofFn_sum_mul_left, Nat.pow_succ, Nat.mul_add]
        _ ≤ n ^ T * (n * entrancePotential F (.active x)) :=
          Nat.mul_le_mul_left _ (entrance_bellman_on_reach hψ F hRank x hx)
        _ = n ^ (T + 1) * entrancePotential F (.active x) := by
          rw [Nat.pow_succ]
          ac_rfl

private theorem failureCount_zero {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S)
    (hno : ∀ s e, step s e ≠ .failure) :
    ∀ (s : S) (T : Nat), failureCount step (.active s) T = 0 := by
  intro s T
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
      change (List.ofFn (fun e : Fin m =>
        failureCount step (step s e) T)).sum = 0
      have hp : ∀ e : Fin m, failureCount step (step s e) T = 0 := by
        intro e
        cases he : step s e with
        | active y => exact ih y
        | success =>
            simp only [failureCount, treeWeight_success,
              failureWeight, Nat.mul_zero]
        | failure => exact (hno s e he).elim
      calc
        (List.ofFn (fun e : Fin m => failureCount step (step s e) T)).sum =
            (List.ofFn (fun _ : Fin m => 0)).sum := ofFn_sum_eq _ _ hp
        _ = 0 := by rw [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero]

/-- The original half-mass conclusion, now from invariant seeds and only
reachable rank laws. No global EntranceBellman premise is used. -/
theorem entrance_success_half_wired
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hRank : ReachableEntranceRankResidual hψ F)
    (x : AState n ψ) (hi : AInvariant hψ F x) :
    n ^ (32 * n * (F.recovery.d + F.attack.d)) ≤
      2 * successCount (entranceStep hψ F) (.active x)
        (32 * n * (F.recovery.d + F.attack.d)) := by
  let span := F.recovery.d + F.attack.d
  let horizon := 32 * n * span
  let cap := 16 * n * span
  have hn : 0 < n := by
    have hh := (F.attack.pos 0).isLt
    omega
  have hspan : 0 < span := by
    dsimp [span]
    have hd := F.attack.hd
    omega
  have hH : 0 < horizon :=
    Nat.mul_pos (Nat.mul_pos (by decide : 0 < 32) hn) hspan
  have hp : entrancePotential F (.active x) ≤ cap := by
    change n * R F x ≤ 16 * n * span
    calc
      n * R F x ≤ n * (16 * span) :=
        Nat.mul_le_mul_left n (R_le hψ F x hi.recovery hi.attack)
      _ = 16 * n * span := by ac_rfl
  have hc : truncatedActiveCostNumerator (entranceStep hψ F)
      (.active x) horizon ≤ n ^ horizon * cap :=
    Nat.le_trans
      (entrance_cost_on_reach hψ F hRank x (ActiveReach.base hi) horizon)
      (Nat.mul_le_mul_left (n ^ horizon) hp)
  have hs : 2 * cap ≤ horizon * 1 := by
    dsimp [cap, horizon]
    simp only [← Nat.mul_assoc, Nat.mul_one]
    exact Nat.le_refl _
  have ht := two_mul_activeCount_le_pow_of_scaled_cost
    (den := 1) (num := cap) (L := horizon)
    (entranceStep hψ F) (.active x) hH (by decide)
    (by simpa only [Nat.one_mul, Nat.mul_comm] using hc) hs
  have hpart := node_count_partition (entranceStep hψ F) (.active x) horizon
  have hf := failureCount_zero (entranceStep hψ F)
    (entranceStep_ne_failure hψ F) x horizon
  change n ^ horizon ≤ 2 * successCount (entranceStep hψ F) (.active x) horizon
  omega

/-! ## Preserve the proved eager serial composition -/

private theorem handoff_mass_wired
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A) (x : AState n ψ) (e : Fin n) :
    n ^ (4 * n) ≤
      16 * successCount D.step (raceHandoff hψ F D ready x e) (4 * n) := by
  classical
  unfold raceHandoff
  split
  · simp only [successCount, treeWeight_success, successWeight, Nat.mul_one]
    exact Nat.le_trans
      (by omega : n ^ (4 * n) ≤ 1 * n ^ (4 * n))
      (Nat.mul_le_mul_right (n ^ (4 * n)) (by decide : 1 ≤ 16))
  · exact D.mass (ready x e)

/-- The 1/32 mass for the unchanged fullStep, from invariant seeds. -/
theorem full_mass_wired
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A)
    (hRank : ReachableEntranceRankResidual hψ F)
    (x : AState n ψ) (hi : AInvariant hψ F x) :
    n ^ (32 * n * (F.recovery.d + F.attack.d) + 4 * n) ≤
      32 * successCount (fullStep hψ F D ready) (.active (.inl x))
        (32 * n * (F.recovery.d + F.attack.d) + 4 * n) := by
  exact sequential_mass (entranceStep hψ F) D.step
    (raceHandoff hψ F D ready) x
    (32 * n * (F.recovery.d + F.attack.d)) (4 * n) 2 16
    (entrance_success_half_wired hψ F hRank x hi)
    (fun y e _ => handoff_mass_wired hψ F D ready y e)

/-! ## Fix the physical process and discharge its structural fields -/

/-- Keep executing the real physical transition until NoResetSuccess. A failed
attempt continues from exactly its physical post-state. No serial ghost state
is substituted for that configuration, and RaceReady is not physical success. -/
def physicalBlockStep (hψ : ψ > 0) (F : TwoGapFrame n) :
    AState n ψ → Fin n → StopNode (AState n ψ) :=
  retryStep (attemptStepRaw hψ F) (postState hψ F)

theorem physicalBlockStep_normal_form
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n) :
    physicalBlockStep hψ F x e =
      if NoResetSuccess F (attemptStepConf hψ F x e) then .success
      else .active (postState hψ F x e) := by
  classical
  by_cases hs : NoResetSuccess F (attemptStepConf hψ F x e) <;>
    by_cases ha : NoResetAbsorbedAt F x e (attemptStepConf hψ F x e) <;>
    simp [physicalBlockStep, retryStep, attemptStepRaw, hs, ha, postState]

theorem physicalBlockStep_noFailure
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n) :
    physicalBlockStep hψ F x e ≠ .failure := by
  exact retryStep_ne_failure (attemptStepRaw hψ F) (postState hψ F) x e

theorem physicalBlockStep_active
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) (y : AState n ψ)
    (hy : physicalBlockStep hψ F x e = .active y) :
    y.conf = attemptStepConf hψ F x e := by
  classical
  rw [physicalBlockStep_normal_form] at hy
  by_cases hs : NoResetSuccess F (attemptStepConf hψ F x e)
  · rw [if_pos hs] at hy
    cases hy
  · rw [if_neg hs] at hy
    exact congrArg (fun z : AState n ψ => z.conf) (StopNode.active.inj hy).symm

theorem physicalBlockStep_success
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n)
    (hh : physicalBlockStep hψ F x e = .success) :
    NoResetSuccess F (attemptStepConf hψ F x e) := by
  classical
  rw [physicalBlockStep_normal_form] at hh
  by_cases hs : NoResetSuccess F (attemptStepConf hψ F x e)
  · exact hs
  · rw [if_neg hs] at hh
    cases hh

/-- Physical success has the three-tag interpretation, using F.shared directly. -/
theorem physicalBlockStep_deletes_one_of_three
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n)
    (hh : physicalBlockStep hψ F x e = .success) :
    (attemptStepConf hψ F x e (F.recovery.pos 0)).leader = false ∨
    (attemptStepConf hψ F x e (F.attack.pos 0)).leader = false ∨
    (attemptStepConf hψ F x e (F.attack.pos F.attack.d)).leader = false := by
  exact (success2_covers_three F (attemptStepConf hψ F x e) F.shared).mp
    (physicalBlockStep_success hψ F x e hh)

/-- ONLY THE TWO CONCRETE FIELDS REMAIN HERE.
The reachable-rank residual remains separate: it is not hidden in this record.
Rel is supplied as relation data, not as an assumed count inequality. -/
structure WiredResidual
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A)
    (Rel : StopNode (CompositeState D ψ) → StopNode (AState n ψ) → Prop) :
    Prop where
  /-- Exhibit a same-edge simulation of the entire entrance-plus-race
  source by physicalBlockStep. The relation must preserve successful leaves
  and advance under the identical edge, including both serial phases and
  handoffs. It may not charge an extra interaction or reset the configuration. -/
  simulation : SuccessSimulation
    (fullStep hψ F D ready) (physicalBlockStep hψ F) Rel
  /-- Exhibit, for EVERY physical active state, a related virtual entrance
  carrying the full AInvariant. This strengthens the old gap-only restart
  premise and covers intermediate and failed-race states as well as fresh
  starts. It is a proof reinitialization, not a physical state reset. -/
  restart : ∀ s : AState n ψ, ∃ x : AState n ψ,
    AInvariant hψ F x ∧ Rel (.active (.inl x)) (.active s)

/-- Construct the entire old concrete interface from its two remaining
concrete fields. No raw-rank or outside-invariant hypothesis is needed here. -/
def concreteInterface_wired
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A)
    (Rel : StopNode (CompositeState D ψ) → StopNode (AState n ψ) → Prop)
    (I : WiredResidual hψ F D ready Rel) :
    ConcreteDeletionInterface hψ F D ready (physicalBlockStep hψ F) where
  rel := Rel
  simulation := I.simulation
  restart := by
    intro s
    obtain ⟨x, hi, hx⟩ := I.restart s
    exact ⟨x, hi.recovery, hi.attack, hx⟩
  noFailure := physicalBlockStep_noFailure hψ F
  observe := fun x => x
  physical_active := physicalBlockStep_active hψ F
  physical_success := physicalBlockStep_success hψ F
  shared := F.shared

/-- Uniform physical block mass. The composed mass is proved from local
reachable rank laws and then transferred by the same-edge simulation. -/
theorem two_gap_block_mass_wired
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A)
    (Rel : StopNode (CompositeState D ψ) → StopNode (AState n ψ) → Prop)
    (hRank : ReachableEntranceRankResidual hψ F)
    (I : WiredResidual hψ F D ready Rel) (s : AState n ψ) :
    n ^ (32 * n * (F.recovery.d + F.attack.d) + 4 * n) ≤
      32 * successCount (physicalBlockStep hψ F) (.active s)
        (32 * n * (F.recovery.d + F.attack.d) + 4 * n) := by
  obtain ⟨x, hi, hx⟩ := I.restart s
  have hm := full_mass_wired hψ F D ready hRank x hi
  have hc := successCount_le_of_simulation
    (fullStep hψ F D ready) (physicalBlockStep hψ F) Rel I.simulation
    (.active (.inl x)) (.active s) hx
    (32 * n * (F.recovery.d + F.attack.d) + 4 * n)
  exact Nat.le_trans hm (Nat.mul_le_mul_left 32 hc)

/-- REACHABLE-DOMAIN CAPSTONE.
The old global RawAttemptRankLaws and AbsorptionOutsideInvariant are absent.
The still-unproved reachable-rank residual is explicit, in addition to the
simulation and restart fields. Omitting it is not justified by the exported
AttemptClosed theorem. This is a Nat finite-horizon bound, not a separately
formalized real-valued expectation limit. -/
theorem two_gap_deletion_cost_wired
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A)
    (Rel : StopNode (CompositeState D ψ) → StopNode (AState n ψ) → Prop)
    (hRank : ReachableEntranceRankResidual hψ F)
    (I : WiredResidual hψ F D ready Rel)
    (x : AState n ψ) (T : Nat) :
    truncatedActiveCostNumerator (physicalBlockStep hψ F) (.active x) T ≤
      n ^ T * (2 * 32 *
        (32 * n * (F.recovery.d + F.attack.d) + 4 * n)) := by
  have hb : ∀ s : AState n ψ,
      n ^ (1 * (32 * n * (F.recovery.d + F.attack.d) + 4 * n)) ≤
        32 * successCount (physicalBlockStep hψ F) (.active s)
          (1 * (32 * n * (F.recovery.d + F.attack.d) + 4 * n)) := by
    intro s
    simpa only [Nat.one_mul] using
      (two_gap_block_mass_wired hψ F D ready Rel hRank I s)
  have hc := UniformBlockRenewalCost.truncatedActiveCostNumerator_block_le
    (n := n) (q := 1)
    (K := 32 * n * (F.recovery.d + F.attack.d) + 4 * n) (q' := 32)
    (physicalBlockStep hψ F) (by decide)
    (physicalBlockStep_noFailure hψ F) hb x T
  simpa only [Nat.one_mul] using hc

#print axioms invariant_rank_laws_K2
#print axioms attemptReach_invariant
#print axioms absorption_drop_on_attemptReach
#print axioms entrance_active_source_cases
#print axioms entrance_first_loss_is_failure
#print axioms failure_post_not_invariant_of_not_live
#print axioms entrance_nonincrease_on_invariant
#print axioms entrance_strictDrop_on_invariant
#print axioms entrance_bellman_on_reach
#print axioms entrance_cost_on_reach
#print axioms entrance_success_half_wired
#print axioms full_mass_wired
#print axioms physicalBlockStep_noFailure
#print axioms physicalBlockStep_active
#print axioms physicalBlockStep_success
#print axioms physicalBlockStep_deletes_one_of_three
#print axioms concreteInterface_wired
#print axioms two_gap_block_mass_wired
#print axioms two_gap_deletion_cost_wired

end

end LDSinkTwoGapDeletionWired
