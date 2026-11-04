import Leader.L3.Grant.BlockSharpBlock
import Leader.L3.Grant.BlockFamilyHitting

/-!
# G18: block renewal and expected hitting time at the sharp ratio

The block mass `4 W n^T ≤ 17 Q * mass` of `GrantBlockSharpBlock.lean` gives,
by the same restart as `GrantBlockFamilyHitting.lean`, the expected time
`(17 Q + 3)/4` from every purified, density-good configuration, and
`192 n^2 + (17 Q + 3)/4` from every purified configuration.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail

set_option autoImplicit false
set_option Elab.async false

/-- **The block failure bound.**  With `W = floor(R n / 8)`, every purified,
density-good configuration that is not yet in the G18 target survives the
next `W` letters with at most the failure ratio
`(17 Q - 4 W)/(17 Q)`.

Consumer: `grantBlockSharpEntranceCost` (the restart `grantBlockRenewalCostOfBlock`
with block length `W`). -/
theorem grantBlockSharpBlockFailure
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (hsize :
      (4096 * ((compileAdvice (ceilLogTwo n)).b + 2)) ^ 2 ≤ n)
    (R W : Nat)
    (hradius :
      (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8) :
    0 < W ∧ 4 * W ≤ 17 * grantBlockEntranceCoefficient n ∧
    ∀ x : HeadlineConfiguration n,
      headlinePurified ring x →
      defects ring x * defects ring x ≤ 4 * n →
      ¬ (headlineGrantReady ring x ∨ headlineGeneratedTarget ring x) →
      17 * grantBlockEntranceCoefficient n *
          UniformFirstHit.survivalNumerator (headlinePhysicalNext ring)
            (fun D => headlineGrantReady ring D ∨
              headlineGeneratedTarget ring D) x W ≤
        (17 * grantBlockEntranceCoefficient n - 4 * W) * n ^ W := by
  obtain ⟨_, _, hRn⟩ :=
    grantCutoffsCompiledRadiusReserves n R hn hsp hradius
  have hsq := grantCutoffsPopulationSquareFitsHeads n hn
  have hWpos : 256 ≤ W := by
    rw [hW]
    generalize R * n = z at hRn ⊢
    omega
  have hRle : R ≤ n := by
    have h1 : R ≤ 256 * R := by omega
    have h2 : 256 * R ≤ (256 * R) * (256 * R) := Nat.le_mul_self _
    have h3 : (256 * R) ^ 2 = (256 * R) * (256 * R) := Nat.pow_two _
    omega
  have hWle : W ≤ 2 ^ (compileAdvice (ceilLogTwo n)).K := by
    have h1 : W ≤ R * n := by
      rw [hW]
      exact Nat.div_le_self _ _
    have h2 : R * n ≤ n * n := Nat.mul_le_mul_right n hRle
    omega
  have hQge : 2 ^ (compileAdvice (ceilLogTwo n)).K ≤
      grantBlockEntranceCoefficient n := by
    unfold grantBlockEntranceCoefficient
    have hwf : 1 ≤ ((compileAdvice (ceilLogTwo n)).b + 2) *
        (8 * (compileAdvice (ceilLogTwo n)).b + 13) :=
      Nat.mul_pos (by omega) (by omega)
    have h3 : 1 * 2 ^ (compileAdvice (ceilLogTwo n)).K ≤
        ((compileAdvice (ceilLogTwo n)).b + 2) *
          (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
          2 ^ (compileAdvice (ceilLogTwo n)).K :=
      Nat.mul_le_mul_right _ hwf
    omega
  refine ⟨by omega, by omega, ?_⟩
  intro x hxp hxd hxnot
  have hnotready : ¬ headlineGrantReady ring x :=
    fun h => hxnot (Or.inl h)
  have hblk := grantBlockSharpBlockMassLower ring hn hsp hw hlarge x
    hxp hnotready hxd R
    (1024 * bankTrialRenewalWonCutoffThreshold n (ceilLogTwo n))
    (W + bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W *
      (1024 * bankTrialRenewalWonCutoffThreshold n (ceilLogTwo n)))
    W hsize hradius hW (Nat.le_refl _) (Nat.le_add_right _ _)
    (Nat.le_refl _)
  have hpad := grantBlockHitMassPad ring x W
    (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W *
      (1024 * bankTrialRenewalWonCutoffThreshold n (ceilLogTwo n)))
  have hadd := grantBlockSurvivalAddHit ring x W
  change 4 * W * n ^ (W + bankTrialRenewalIndexWindowCount n
        (ceilLogTwo n) W *
      (1024 * bankTrialRenewalWonCutoffThreshold n (ceilLogTwo n))) ≤
    17 * grantBlockEntranceCoefficient n *
      grantBlockSurrogateG18HitMass ring x
        (W + bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W *
          (1024 * bankTrialRenewalWonCutoffThreshold n
            (ceilLogTwo n))) W at hblk
  rw [hpad] at hblk
  generalize bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W *
    (1024 * bankTrialRenewalWonCutoffThreshold n (ceilLogTwo n)) = k
    at hblk
  generalize grantBlockEntranceCoefficient n = Q at hblk hQge ⊢
  generalize grantBlockSurrogateG18HitMass ring x W W = m at hblk hadd
  generalize UniformFirstHit.survivalNumerator (headlinePhysicalNext ring)
    (fun D => headlineGrantReady ring D ∨
      headlineGeneratedTarget ring D) x W = sv at hadd ⊢
  have hnk : 0 < n ^ k := Nat.pow_pos (by omega)
  have hpow : n ^ (W + k) = n ^ W * n ^ k := Nat.pow_add n W k
  have e1 : 4 * W * n ^ (W + k) = (4 * W * n ^ W) * n ^ k := by
    rw [hpow]
    ac_rfl
  have e2 : 17 * Q * (n ^ k * m) = (17 * Q * m) * n ^ k := by ac_rfl
  rw [e1, e2] at hblk
  have h1 : 4 * W * n ^ W ≤ 17 * Q * m :=
    Nat.le_of_mul_le_mul_right hblk hnk
  have hmle : m ≤ n ^ W := by omega
  have h17 : 17 * Q * m ≤ 17 * Q * n ^ W := Nat.mul_le_mul_left _ hmle
  have hnW : 0 < n ^ W := Nat.pow_pos (by omega)
  have h2W : 4 * W ≤ 17 * Q := by
    have : 4 * W * n ^ W ≤ 17 * Q * n ^ W := Nat.le_trans h1 h17
    exact Nat.le_of_mul_le_mul_right this hnW
  have e3 : 17 * Q * sv + 17 * Q * m = 17 * Q * n ^ W := by
    rw [← Nat.mul_add, hadd]
  rw [Nat.sub_mul]
  omega

/-- The expected cost of the G18 target from the closed class of purified,
density-good configurations: `n^T (17 Q + 3)/4` for every horizon `T`.

Consumer: `grantBlockSharpEntranceExpectedHitting`. -/
theorem grantBlockSharpEntranceCost
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (hsize :
      (4096 * ((compileAdvice (ceilLogTwo n)).b + 2)) ^ 2 ≤ n) :
    ∀ x : HeadlineConfiguration n,
      headlinePurified ring x →
      defects ring x * defects ring x ≤ 4 * n →
      ∀ T, costNumerator (headlinePhysicalNext ring)
          (fun D => headlineGrantReady ring D ∨
            headlineGeneratedTarget ring D) x T ≤
        n ^ T * ((17 * grantBlockEntranceCoefficient n + 3) / 4) := by
  obtain ⟨R, hRlow, hRhigh⟩ := grantClockIntegerRadius n
  have hradius : (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2 :=
    ⟨hRlow, hRhigh⟩
  obtain ⟨hWpos, h2W, hfail⟩ := grantBlockSharpBlockFailure
    ring hn hsp hw hlarge hsize R (R * n / 8) hradius rfl
  intro x hxp hxd T
  have hclosed : ∀ y : HeadlineConfiguration n,
      (headlinePurified ring y ∧ defects ring y * defects ring y ≤ 4 * n) →
      ∀ e, headlinePurified ring (headlinePhysicalNext ring y e) ∧
        defects ring (headlinePhysicalNext ring y e) *
          defects ring (headlinePhysicalNext ring y e) ≤ 4 * n := by
    intro y hy e
    refine ⟨headlineStagesPurifiedStep ring hn y e hy.1, ?_⟩
    have hle : defects ring (headlinePhysicalNext ring y e) ≤
        defects ring y := defects_step_le ring y e
    exact Nat.le_trans (Nat.mul_le_mul hle hle) hy.2
  have hcost := grantBlockRenewalCostOfBlock
    (headlinePhysicalNext ring)
    (fun y : HeadlineConfiguration n =>
      headlinePurified ring y ∧ defects ring y * defects ring y ≤ 4 * n)
    (fun D => headlineGrantReady ring D ∨ headlineGeneratedTarget ring D)
    hclosed (R * n / 8)
    (17 * grantBlockEntranceCoefficient n - 4 * (R * n / 8))
    (17 * grantBlockEntranceCoefficient n) hWpos
    (by omega)
    (fun y hy hny => hfail y hy.1 hy.2 hny) x ⟨hxp, hxd⟩ T
  refine Nat.le_trans hcost (Nat.mul_le_mul_left _ ?_)
  -- the rounded renewal ceiling is at most (17 Q + 1) / 2
  have hsub : 17 * grantBlockEntranceCoefficient n -
      (17 * grantBlockEntranceCoefficient n -
        4 * (R * n / 8)) = 4 * (R * n / 8) := by omega
  unfold L3.Prob.renewalCeiling
  rw [hsub]
  generalize R * n / 8 = W at hWpos h2W ⊢
  generalize grantBlockEntranceCoefficient n = Q at h2W ⊢
  have hbud : W * (17 * Q) ≤ (4 * W) * ((17 * Q + 3) / 4) := by
    have h : 17 * Q ≤ 4 * ((17 * Q + 3) / 4) := by omega
    calc
      W * (17 * Q) ≤ W * (4 * ((17 * Q + 3) / 4)) :=
        Nat.mul_le_mul_left _ h
      _ = (4 * W) * ((17 * Q + 3) / 4) := by ac_rfl
  have ha : 0 < 4 * W := by omega
  -- ceilNat z a ≤ reserve from z ≤ a * reserve
  have hq : W * (17 * Q) / (4 * W) < (17 * Q + 3) / 4 + 1 := by
    apply (Nat.div_lt_iff_lt_mul ha).2
    calc
      W * (17 * Q) ≤ (4 * W) * ((17 * Q + 3) / 4) := hbud
      _ = ((17 * Q + 3) / 4) * (4 * W) := Nat.mul_comm _ _
      _ < ((17 * Q + 3) / 4 + 1) * (4 * W) := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
  by_cases hz : W * (17 * Q) % (4 * W) = 0
  · change W * (17 * Q) / (4 * W) +
      (if W * (17 * Q) % (4 * W) = 0 then 0 else 1) ≤ _
    rw [if_pos hz]
    omega
  · have hne : W * (17 * Q) ≠ ((17 * Q + 3) / 4) * (4 * W) := by
      intro he
      apply hz
      rw [he]
      simp
    have hle : W * (17 * Q) ≤ ((17 * Q + 3) / 4) * (4 * W) := by
      calc
        W * (17 * Q) ≤ (4 * W) * ((17 * Q + 3) / 4) := hbud
        _ = ((17 * Q + 3) / 4) * (4 * W) := Nat.mul_comm _ _
    have hlt : W * (17 * Q) < ((17 * Q + 3) / 4) * (4 * W) := by omega
    have hqstrict : W * (17 * Q) / (4 * W) < (17 * Q + 3) / 4 :=
      (Nat.div_lt_iff_lt_mul ha).2 hlt
    change W * (17 * Q) / (4 * W) +
      (if W * (17 * Q) % (4 * W) = 0 then 0 else 1) ≤ _
    rw [if_neg hz]
    omega

/-- **The G16 stage.**  From every purified, density-good configuration the
expected number of physical interactions until the G18 target
(`headlineGrantReady ∨ headlineGeneratedTarget`) is at most
`(17 Q + 3)/4`, `Q = (b+2)(8b+13) 2^K`.

Consumer: `grantBlockSharpLeaderlessExpectedHitting`. -/
theorem grantBlockSharpEntranceExpectedHitting
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (hsize :
      (4096 * ((compileAdvice (ceilLogTwo n)).b + 2)) ^ 2 ≤ n)
    (x : HeadlineConfiguration n)
    (hxp : headlinePurified ring x)
    (hxd : defects ring x * defects ring x ≤ 4 * n) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlineGrantReady ring D ∨
        headlineGeneratedTarget ring D) x
      (((17 * grantBlockEntranceCoefficient n + 3) / 4 : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) _ (by omega : 0 < n) x _).2
  exact grantBlockSharpEntranceCost ring hn hsp hw hlarge hsize x hxp hxd

/-- Strengthening the target on a closed carrier costs nothing.

Consumer: `grantBlockSharpLeaderlessExpectedHitting`. -/
private theorem sharpCostTargetOnClosed {m : Nat} {S : Type}
    (next : S → Fin m → S) (I P Q : S → Prop)
    (hstep : ∀ x, I x → ∀ e, I (next x e))
    (hstop : ∀ x, I x → Q x → P x) :
    ∀ T x, I x →
      costNumerator next P x T ≤ costNumerator next Q x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x hx
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro x hx
      by_cases hp : P x
      · rw [costNumerator_terminal next P x hp (T + 1)]
        exact Nat.zero_le _
      · have hq : ¬ Q x := by
          intro h
          exact hp (hstop x hx h)
        rw [costNumerator_succ next P x hp T,
          costNumerator_succ next Q x hq T]
        exact Nat.add_le_add_left
          (ofFn_sum_le
            (fun e : Fin m => costNumerator next P (next x e) T)
            (fun e : Fin m => costNumerator next Q (next x e) T)
            (fun e => ih (next x e) (hstep x hx e))) _

/-- **The G16 stage composed with the density entrance.**  From every
purified configuration, the expected time to the G18 target is at most
`192 n^2 + (17 Q + 3)/4`: the density entrance
(`headlineStagesGrantDensityEntrance`, `192 n^2`) reaches a density-good
configuration or the target, purification persists, and the block renewal
finishes.

Consumer: `grantLeaderlessSpatialClause` (GrantLeaderlessSpatial.lean). -/
theorem grantBlockSharpLeaderlessExpectedHitting
    {n : Nat} (ring : DirectedRing n) (hn : 16 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (hsize :
      (4096 * ((compileAdvice (ceilLogTwo n)).b + 2)) ^ 2 ≤ n)
    (C : HeadlineConfiguration n)
    (hpurified : headlinePurified ring C) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlineGrantReady ring D ∨
        headlineGeneratedTarget ring D) C
      ((192 * n ^ 2 +
        (17 * grantBlockEntranceCoefficient n + 3) / 4 : Nat) : Rat) := by
  have hn5 : 5 ≤ n := by omega
  have hnpos : 0 < n := by omega
  let P : HeadlineConfiguration n → Prop := fun D =>
    headlineGrantReady ring D ∨ headlineGeneratedTarget ring D
  let A : HeadlineConfiguration n → Prop := fun D =>
    headlinePurified ring D ∧ defects ring D * defects ring D ≤ 4 * n
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) P hnpos C _).2
  apply Prob.costNumerator_stage_le (headlinePhysicalNext ring) C A P
  · intro T
    have hentrance := (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (headlinePhysicalNext ring) _ hnpos C (192 * n ^ 2)).1
      (headlineStagesGrantDensityEntrance ring hn C) T
    refine Nat.le_trans ?_ hentrance
    exact sharpCostTargetOnClosed (headlinePhysicalNext ring)
      (fun D => headlinePurified ring D)
      (fun D => A D ∨ P D)
      (fun D => (defects ring D * defects ring D ≤ 4 * n) ∨
        headlineGrantReady ring D ∨ headlineGeneratedTarget ring D)
      (fun y hy e => headlineStagesPurifiedStep ring hn5 y e hy)
      (fun y hy hq => by
        rcases hq with hd | hr
        · exact Or.inl ⟨hy, hd⟩
        · exact Or.inr hr)
      T C hpurified
  · intro y hy T
    exact grantBlockSharpEntranceCost ring hn5 hsp hw hlarge hsize y hy.1 hy.2 T

end L3

#print axioms L3.grantBlockSharpBlockFailure
#print axioms L3.grantBlockSharpEntranceCost
#print axioms L3.grantBlockSharpEntranceExpectedHitting
#print axioms L3.grantBlockSharpLeaderlessExpectedHitting
