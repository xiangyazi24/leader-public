import Leader.Wu.Birth.SweepSpec

set_option autoImplicit false

namespace BirthRenewalBridge

open BirthSweepSpec
open FiniteUniformStoppingTree

/-- A designated service for a proposed rank is exactly a physical sweep edge
that strictly lowers that rank. Birth edges are handled separately. -/
def DesignatedService {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : Config m → Nat) (x : Config m) (e : Fin m) : Prop :=
  rank (sweepStep M hm x e) < rank x

/-- Exact rank plateau: there is neither an immediate birth edge nor a
rank-decreasing physical edge. -/
def RankPlateau {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : Config m → Nat) (x : Config m) : Prop :=
  ∀ e,
    ¬ BirthEvent M hm x e ∧
      ¬ DesignatedService M hm rank x e

/-- The one residual structure. `rank` and `bound` are proof data. The only
logical field says that the non-plateau region is closed under every non-birth
edge and that all such edges are rank-nonincreasing. -/
structure BirthRenewalResidual {m : Nat}
    (M : SweepModel m) (hm : 0 < m) where
  rank : Config m → Nat
  bound : Nat
  law :
    ∀ x, ¬ RankPlateau M hm rank x →
      rank x < bound ∧
        ∀ e, ¬ BirthEvent M hm x e →
          ¬ RankPlateau M hm rank (sweepStep M hm x e) ∧
            rank (sweepStep M hm x e) ≤ rank x

/-- User-facing plateau for one concrete rank certificate. -/
def Plateau {m : Nat} {M : SweepModel m} {hm : 0 < m}
    (R : BirthRenewalResidual M hm) (x : Config m) : Prop :=
  RankPlateau M hm R.rank x

/-- Every designated service lowers the proposed rank. -/
theorem designatedService_decreases
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : Config m → Nat) (x : Config m) (e : Fin m)
    (h : DesignatedService M hm rank x e) :
    rank (sweepStep M hm x e) < rank x :=
  h

/-- Non-plateau is nonvacuous: some scheduler edge is either an immediate birth
or a strict rank drop. -/
theorem exists_birth_or_designated
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (rank : Config m → Nat) (x : Config m)
    (hx : ¬ RankPlateau M hm rank x) :
    ∃ e : Fin m,
      BirthEvent M hm x e ∨ DesignatedService M hm rank x e := by
  apply Classical.byContradiction
  intro hnone
  apply hx
  intro e
  constructor
  · intro hbirth
    exact hnone ⟨e, Or.inl hbirth⟩
  · intro hdrop
    exact hnone ⟨e, Or.inr hdrop⟩

/-- A strict Nat drop consumes at least one unit of rank. -/
theorem rank_drop_consumes_one {a b : Nat} (h : b < a) :
    b + 1 ≤ a := by
  omega

/-- Exact success mass at an already absorbed success node. -/
theorem successCount_success
    {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (T : Nat) :
    successCount step (.success) T = m ^ T := by
  unfold successCount
  rw [FiniteUniformStoppingTree.treeWeight_success]
  simp [FiniteUniformStoppingTree.successWeight]

/-- A successful depth-T word has all m one-edge extensions successful. -/
theorem success_extensions
    {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (T : Nat) :
    successCount step (.success) (T + 1) =
      m * successCount step (.success) T := by
  rw [successCount_success, successCount_success, Nat.pow_succ]
  exact Nat.mul_comm _ _

/-- The active-node recurrence for success mass. -/
theorem successCount_active_succ
    {S : Type} {m : Nat}
    (step : S → Fin m → StopNode S) (state : S) (T : Nat) :
    successCount step (.active state) (T + 1) =
      (List.ofFn (fun e : Fin m =>
        successCount step (step state e) T)).sum := by
  rfl

/-- Division-free form of one designated service edge having scheduler mass
1/m: one distinguished value plus m-1 ordinary values. -/
theorem one_service_slot_sum
    {m : Nat} (a : Fin m) (f : Fin m → Nat) (c : Nat)
    (hother : ∀ e, e ≠ a → f e = c) :
    (List.ofFn f).sum = f a + (m - 1) * c :=
  PredictableTwoTargetFiniteTree.ofFn_sum_one_value_else_const
    a f c hother

/-- Active states of the protected birth window. -/
abbrev LiveConfig {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (R : BirthRenewalResidual M hm) :=
  {x : Config m // ¬ RankPlateau M hm R.rank x}

/-- Restrict `birthStep` to the non-plateau region certified by `R`.
The operational branch is on the Bool-valued birth guard itself. -/
def liveStep {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (R : BirthRenewalResidual M hm)
    (y : LiveConfig M hm R) (e : Fin m) :
    StopNode (LiveConfig M hm R) :=
  match hguard : birthGuard M hm y.1 e with
  | true => .success
  | false =>
      let hnoBirth : ¬ BirthEvent M hm y.1 e := by
        intro hbirth
        unfold BirthEvent at hbirth
        rw [hguard] at hbirth
        cases hbirth
      let hnext :
          ¬ RankPlateau M hm R.rank (sweepStep M hm y.1 e) :=
        ((R.law y.1 y.2).2 e hnoBirth).1
      .active ⟨sweepStep M hm y.1 e, hnext⟩

theorem liveStep_success
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (R : BirthRenewalResidual M hm)
    (y : LiveConfig M hm R) (e : Fin m)
    (hbirth : BirthEvent M hm y.1 e) :
    liveStep M hm R y e = .success := by
  unfold BirthEvent at hbirth
  unfold liveStep
  split
  · rfl
  · rename_i hfalse
    rw [hfalse] at hbirth
    cases hbirth

theorem liveStep_active
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (R : BirthRenewalResidual M hm)
    (y : LiveConfig M hm R) (e : Fin m)
    (hbirth : ¬ BirthEvent M hm y.1 e) :
    liveStep M hm R y e =
      .active ⟨sweepStep M hm y.1 e,
        ((R.law y.1 y.2).2 e hbirth).1⟩ := by
  have hguard : birthGuard M hm y.1 e = false := by
    cases hcase : birthGuard M hm y.1 e with
    | false =>
        rfl
    | true =>
        have hb : BirthEvent M hm y.1 e := hcase
        exact False.elim (hbirth hb)
  unfold liveStep
  split
  · rename_i htrue
    rw [htrue] at hguard
    cases hguard
  · rfl

/-- Local success-branch bridge for the original stopped process. -/
theorem birthStep_success_bridge
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m)
    (hbirth : BirthEvent M hm x e) :
    birthStep M hm x e = .success := by
  have hguard : birthGuard M hm x e = true := hbirth
  unfold birthStep
  rw [if_pos hguard]

/-- Local active-branch bridge for the original stopped process. -/
theorem birthStep_active_bridge
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (x : Config m) (e : Fin m)
    (hbirth : ¬ BirthEvent M hm x e) :
    birthStep M hm x e = .active (sweepStep M hm x e) := by
  have hguard : ¬ birthGuard M hm x e = true := by
    intro htrue
    exact hbirth htrue
  unfold birthStep
  rw [if_neg hguard]

/-- Bellman potential on the protected non-plateau process. -/
def livePotential {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (R : BirthRenewalResidual M hm) :
    StopNode (LiveConfig M hm R) → Nat
  | .success => 0
  | .failure => 0
  | .active y => m * (R.rank y.1 + 1)

theorem mul_eq_self_add_pred_mul
    (m c : Nat) (hm : 0 < m) :
    m * c = c + (m - 1) * c := by
  obtain ⟨k, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp [Nat.succ_mul, Nat.add_comm]

/-- One distinguished birth/drop edge and nonincrease on every other non-birth
edge give the exact division-free Bellman supersolution. -/
theorem livePotential_super
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (R : BirthRenewalResidual M hm) :
    NatBellmanSuperSolution (liveStep M hm R) 1
      (livePotential M hm R) := by
  refine ⟨rfl, rfl, ?_⟩
  intro y
  obtain ⟨a, hprogress⟩ :=
    exists_birth_or_designated M hm R.rank y.1 y.2
  let C := m * (R.rank y.1 + 1)
  let g : Fin m → Nat :=
    fun e => if e = a then m * R.rank y.1 else C
  have hpoint : ∀ e : Fin m,
      livePotential M hm R (liveStep M hm R y e) ≤ g e := by
    intro e
    cases hguard : birthGuard M hm y.1 e with
    | true =>
        have hbirth : BirthEvent M hm y.1 e := hguard
        rw [liveStep_success M hm R y e hbirth]
        change 0 ≤ g e
        exact Nat.zero_le _
    | false =>
        have hbirth : ¬ BirthEvent M hm y.1 e := by
          intro hb
          unfold BirthEvent at hb
          rw [hguard] at hb
          cases hb
        have hnon := ((R.law y.1 y.2).2 e hbirth).2
        rw [liveStep_active M hm R y e hbirth]
        change m * (R.rank (sweepStep M hm y.1 e) + 1) ≤ g e
        by_cases hea : e = a
        · subst e
          rcases hprogress with hnow | hdrop
          · exact False.elim (hbirth hnow)
          · have hs :
                R.rank (sweepStep M hm y.1 a) + 1 ≤ R.rank y.1 :=
              rank_drop_consumes_one
                (designatedService_decreases M hm R.rank y.1 a hdrop)
            rw [show g a = m * R.rank y.1 by simp [g]]
            exact Nat.mul_le_mul_left m hs
        · rw [show g e = C by simp [g, hea]]
          exact Nat.mul_le_mul_left m (Nat.succ_le_succ hnon)
  have hsum :
      (List.ofFn (fun e : Fin m =>
        livePotential M hm R (liveStep M hm R y e))).sum ≤
        (List.ofFn g).sum :=
    FiniteUniformStoppingTree.ofFn_sum_le _ _ hpoint
  have hgsum :
      (List.ofFn g).sum = g a + (m - 1) * C :=
    one_service_slot_sum a g C (by
      intro e hne
      simp [g, hne])
  have hga : g a = m * R.rank y.1 := by
    simp [g]
  have hC : C = m * R.rank y.1 + m := by
    change m * (R.rank y.1 + 1) = m * R.rank y.1 + m
    rw [Nat.mul_add, Nat.mul_one]
  change
    1 * m +
      (List.ofFn (fun e : Fin m =>
        livePotential M hm R (liveStep M hm R y e))).sum ≤
      m * (m * (R.rank y.1 + 1))
  rw [Nat.one_mul]
  calc
    m + (List.ofFn (fun e : Fin m =>
        livePotential M hm R (liveStep M hm R y e))).sum ≤
        m + (List.ofFn g).sum := Nat.add_le_add_left hsum m
    _ = m + (m * R.rank y.1 + (m - 1) * C) := by
      rw [hgsum, hga]
    _ = C + (m - 1) * C := by
      rw [hC]
      ac_rfl
    _ = m * C := (mul_eq_self_add_pred_mul m C hm).symm
    _ = m * (m * (R.rank y.1 + 1)) := by
      rfl

/-- Uniform potential cap used by the block theorem. -/
def birthBudget {m : Nat} {M : SweepModel m} {hm : 0 < m}
    (R : BirthRenewalResidual M hm) : Nat :=
  m * R.bound

/-- Explicit state-uniform renewal horizon. -/
def birthHorizon {m : Nat} {M : SweepModel m} {hm : 0 < m}
    (R : BirthRenewalResidual M hm) : Nat :=
  2 * birthBudget R

/-- The protected step has no failure child. -/
theorem liveStep_ne_failure
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (R : BirthRenewalResidual M hm) :
    ∀ y e, liveStep M hm R y e ≠ .failure := by
  intro y e
  cases hguard : birthGuard M hm y.1 e with
  | true =>
      have hbirth : BirthEvent M hm y.1 e := hguard
      rw [liveStep_success M hm R y e hbirth]
      intro hfalse
      cases hfalse
  | false =>
      have hbirth : ¬ BirthEvent M hm y.1 e := by
        intro hb
        unfold BirthEvent at hb
        rw [hguard] at hb
        cases hb
      rw [liveStep_active M hm R y e hbirth]
      intro hfalse
      cases hfalse

/-- The protected subtype and the original process have identical success
counts from corresponding non-plateau active states. -/
theorem live_successCount_eq_birth
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (R : BirthRenewalResidual M hm)
    (y : LiveConfig M hm R) :
    ∀ T,
      successCount (liveStep M hm R) (.active y) T =
        successCount (birthStep M hm) (.active y.1) T := by
  intro T
  revert y
  induction T with
  | zero =>
      intro y
      rfl
  | succ T ih =>
      intro y
      rw [successCount_active_succ, successCount_active_succ]
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      cases hguard : birthGuard M hm y.1 e with
      | true =>
          have hbirth : BirthEvent M hm y.1 e := hguard
          rw [liveStep_success M hm R y e hbirth,
            birthStep_success_bridge M hm y.1 e hbirth,
            successCount_success, successCount_success]
      | false =>
          have hbirth : ¬ BirthEvent M hm y.1 e := by
            intro hb
            unfold BirthEvent at hb
            rw [hguard] at hb
            cases hb
          have hnext := ((R.law y.1 y.2).2 e hbirth).1
          rw [liveStep_active M hm R y e hbirth,
            birthStep_active_bridge M hm y.1 e hbirth]
          exact ih ⟨sweepStep M hm y.1 e, hnext⟩

/-- Half-mass bound on the protected process. -/
theorem live_birth_mass
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (R : BirthRenewalResidual M hm)
    (y : LiveConfig M hm R) :
    m ^ birthHorizon R ≤
      2 * successCount (liveStep M hm R) (.active y)
        (birthHorizon R) := by
  let H := birthHorizon R
  have hsuper := livePotential_super M hm R
  have hbound := (R.law y.1 y.2).1
  have hsucc : R.rank y.1 + 1 ≤ R.bound :=
    rank_drop_consumes_one hbound
  have hpotential :
      livePotential M hm R (.active y) ≤ birthBudget R := by
    change m * (R.rank y.1 + 1) ≤ m * R.bound
    exact Nat.mul_le_mul_left m hsucc
  have hboundPos : 0 < R.bound :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hbound
  have hbudgetPos : 0 < birthBudget R := by
    change 0 < m * R.bound
    exact Nat.mul_pos hm hboundPos
  have hHpos : 0 < H := by
    change 0 < 2 * birthBudget R
    exact Nat.mul_pos (Nat.succ_pos 1) hbudgetPos
  have hcost0 :=
    FiniteUniformStoppingTree.truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (liveStep M hm R) 1 (livePotential M hm R) hsuper
      (.active y) H
  have hcost :
      1 * truncatedActiveCostNumerator
          (liveStep M hm R) (.active y) H ≤
        birthBudget R * m ^ H := by
    calc
      1 * truncatedActiveCostNumerator
          (liveStep M hm R) (.active y) H ≤
          m ^ H * livePotential M hm R (.active y) := hcost0
      _ ≤ m ^ H * birthBudget R :=
        Nat.mul_le_mul_left _ hpotential
      _ = birthBudget R * m ^ H := Nat.mul_comm _ _
  have hactive :
      2 * activeCount (liveStep M hm R) (.active y) H ≤ m ^ H := by
    apply FiniteUniformStoppingTree.two_mul_activeCount_le_pow_of_scaled_cost
      (liveStep M hm R) (.active y)
      (den := 1) (num := birthBudget R) (L := H)
    · exact hHpos
    · exact Nat.succ_pos 0
    · exact hcost
    · change 2 * birthBudget R ≤ birthHorizon R * 1
      rw [Nat.mul_one]
      unfold birthHorizon
      exact Nat.le_refl _
  have hfailure :
      failureCount (liveStep M hm R) (.active y) H = 0 :=
    BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
      (liveStep M hm R) (liveStep_ne_failure M hm R) y H
  have hpartition :=
    FiniteUniformStoppingTree.node_count_partition
      (liveStep M hm R) (.active y) H
  change
    m ^ H ≤ 2 * successCount (liveStep M hm R) (.active y) H
  omega

/-- The requested nonvacuous bridge to the original birth process.
H = 2 * m * R.bound, c = 2, and the plateau exclusion is explicit. -/
theorem birth_mass
    {m : Nat} (M : SweepModel m) (hm : 0 < m)
    (R : BirthRenewalResidual M hm)
    (x : Config m) (hx : ¬ Plateau R x) :
    m ^ birthHorizon R ≤
      2 * successCount (birthStep M hm) (.active x)
        (birthHorizon R) := by
  let y : LiveConfig M hm R := ⟨x, hx⟩
  have hmass := live_birth_mass M hm R y
  have heq :=
    live_successCount_eq_birth M hm R y (birthHorizon R)
  rw [heq] at hmass
  exact hmass

end BirthRenewalBridge

#print axioms BirthRenewalBridge.designatedService_decreases
#print axioms BirthRenewalBridge.exists_birth_or_designated
#print axioms BirthRenewalBridge.rank_drop_consumes_one
#print axioms BirthRenewalBridge.successCount_success
#print axioms BirthRenewalBridge.success_extensions
#print axioms BirthRenewalBridge.successCount_active_succ
#print axioms BirthRenewalBridge.one_service_slot_sum
#print axioms BirthRenewalBridge.liveStep_success
#print axioms BirthRenewalBridge.liveStep_active
#print axioms BirthRenewalBridge.birthStep_success_bridge
#print axioms BirthRenewalBridge.birthStep_active_bridge
#print axioms BirthRenewalBridge.mul_eq_self_add_pred_mul
#print axioms BirthRenewalBridge.livePotential_super
#print axioms BirthRenewalBridge.liveStep_ne_failure
#print axioms BirthRenewalBridge.live_successCount_eq_birth
#print axioms BirthRenewalBridge.live_birth_mass
#print axioms BirthRenewalBridge.birth_mass
