import Leader.L3.Grant.BlockFamilyBlock
import Leader.L3.ProbStages
import Leader.L3.DensityTail

/-!
# G16: block renewal, the expected hitting time of the G16 stage

`grantBlockFamilyBlockMassLower` is the per-window bound (C.19): at every
purified, density-good, grant-free entrance the G18 target is hit in the first
`W` letters with probability at least `(2/17) W / Q`, `Q = (b+2)(8b+13) 2^K`.
The block renewal turns it into `E[hitting time] ≤ (17 Q + 1)/2`:

* the set `I` of purified, density-good configurations is closed under a
  physical step (`headlineStagesPurifiedStep`, `defects_step_le`);
* a failed block ends in `I` again, with the defect count still at most the
  entrance's, so the same bound holds at the next block with a new family
  (`grantBlockRenewalCostOfBlock`; no independence of the blocks is used);
* the density entrance (`headlineStagesGrantDensityEntrance`) and the block
  renewal compose by the full-history strong Markov inequality
  (`costNumerator_stage_le`).
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail

set_option autoImplicit false
set_option Elab.async false

/-! ### Restart with a general failure ratio -/

/-- Barrier predicate of the restart: target reached or carrier left.

Consumer: `grantBlockRenewalCostOfBlock`. -/
private def famRestartGood {S : Type}
    (I P : S → Prop) (x : S) : Prop :=
  P x ∨ ¬ I x

/-- Absorbing barrier step.

Consumer: `grantBlockRenewalCostOfBlock`. -/
private noncomputable def famRestartNext {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (x : S) (e : Fin n) : S := by
  classical
  exact if famRestartGood I P x then x else next x e

/-- The barrier is closed.

Consumer: `grantBlockRenewalCostOfBlock`. -/
private theorem famRestartGoodClosed {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop) :
    ∀ x e, famRestartGood I P x →
      famRestartGood I P (famRestartNext next I P x e) := by
  classical
  intro x e hx
  change famRestartGood I P
    (if famRestartGood I P x then x else next x e)
  rw [if_pos hx]
  exact hx

/-- On the carrier the barrier is the target.

Consumer: `grantBlockRenewalCostOfBlock`. -/
private theorem famRestartGoodAtIn {S : Type}
    (I P : S → Prop) (x : S) (hx : I x) :
    famRestartGood I P x ↔ P x := by
  constructor
  · intro h
    cases h with
    | inl hp => exact hp
    | inr hnot => exact False.elim (hnot hx)
  · intro hp
    exact Or.inl hp

/-- Barrier miss mass equals survival numerator on the carrier.

Consumer: `grantBlockRenewalCostOfBlock`. -/
private theorem famRestartWordEq {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (hc : ∀ x, I x → ∀ e, I (next x e)) :
    ∀ T x, I x →
      wordSum (famRestartNext next I P)
        (miss (famRestartGood I P)) x T =
      UniformFirstHit.survivalNumerator next P x T := by
  classical
  have hgood := famRestartGoodClosed next I P
  intro T
  induction T with
  | zero =>
      intro x hx
      by_cases hp : P x
      · rw [wordSum_zero,
          UniformFirstHit.survivalNumerator_of_target next P x hp 0]
        simp [miss, famRestartGood, hp]
      · rw [wordSum_zero,
          UniformFirstHit.survivalNumerator_zero_of_not next P x hp]
        simp [miss, famRestartGood, hp, hx]
  | succ T ih =>
      intro x hx
      by_cases hp : P x
      · have hg : famRestartGood I P x := Or.inl hp
        rw [miss_zero (famRestartNext next I P)
          (famRestartGood I P) hgood x hg (T + 1),
          UniformFirstHit.survivalNumerator_of_target next P x hp (T + 1)]
      · have hg : ¬ famRestartGood I P x := by
          intro hh
          exact hp ((famRestartGoodAtIn I P x hx).mp hh)
        rw [wordSum_succ,
          UniformFirstHit.survivalNumerator_succ_of_not next P x hp T]
        apply ofFn_sum_eq
        intro e
        have hstep : famRestartNext next I P x e = next x e := by
          unfold famRestartNext
          exact if_neg hg
        rw [hstep]
        exact ih (next x e) (hc x hx e)

/-- The barrier does not change the first-hit cost on the carrier.

Consumer: `grantBlockRenewalCostOfBlock`. -/
private theorem famRestartCostEq {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (hc : ∀ x, I x → ∀ e, I (next x e)) :
    ∀ T x, I x →
      costNumerator next P x T =
      costNumerator (famRestartNext next I P)
        (famRestartGood I P) x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x hx
      simp only [costNumerator_zero]
  | succ T ih =>
      intro x hx
      by_cases hp : P x
      · have hg : famRestartGood I P x := Or.inl hp
        rw [costNumerator_terminal next P x hp (T + 1),
          costNumerator_terminal (famRestartNext next I P)
            (famRestartGood I P) x hg (T + 1)]
      · have hg : ¬ famRestartGood I P x := by
          intro hh
          exact hp ((famRestartGoodAtIn I P x hx).mp hh)
        rw [costNumerator_succ next P x hp T,
          costNumerator_succ (famRestartNext next I P)
            (famRestartGood I P) x hg T]
        exact congrArg (fun z : Nat => n ^ (T + 1) + z)
          (ofFn_sum_eq _ _ (fun e => by
            have hstep : famRestartNext next I P x e =
                next x e := by
              unfold famRestartNext
              exact if_neg hg
            rw [hstep]
            exact ih (next x e) (hc x hx e)))

/-- **Uniform first-hit restart with a general failure ratio.**  On a closed
carrier `I`, a block of `B` letters that misses `P` with probability at most
`num/den` from every live state gives `E[time] ≤ renewalCeiling B num den`.
The target `P` is not assumed absorbing, and consecutive blocks are not
assumed independent.

Consumer: `grantBlockEntranceCost`. -/
theorem grantBlockRenewalCostOfBlock {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P : S → Prop)
    (hc : ∀ x, I x → ∀ e, I (next x e))
    (B num den : Nat) (hB : 0 < B) (hrho : num < den)
    (hblock : ∀ x, I x → ¬ P x →
      den * UniformFirstHit.survivalNumerator next P x B ≤
        num * n ^ B) :
    ∀ x, I x → ∀ T,
      costNumerator next P x T ≤
        n ^ T * L3.Prob.renewalCeiling B num den := by
  classical
  intro x hx T
  have hgood : ∀ y e, famRestartGood I P y →
      famRestartGood I P (famRestartNext next I P y e) :=
    famRestartGoodClosed next I P
  have hb : ∀ y,
      den * wordSum (famRestartNext next I P)
        (miss (famRestartGood I P)) y B ≤ num * n ^ B := by
    intro y
    by_cases hg : famRestartGood I P y
    · rw [miss_zero (famRestartNext next I P)
        (famRestartGood I P) hgood y hg B]
      simp
    · have hy : I y := by
        by_cases hi : I y
        · exact hi
        · exact False.elim (hg (Or.inr hi))
      have hp : ¬ P y := by
        intro hpy
        exact hg (Or.inl hpy)
      rw [famRestartWordEq next I P hc B y hy]
      exact hblock y hy hp
  calc
    costNumerator next P x T =
        costNumerator (famRestartNext next I P)
          (famRestartGood I P) x T :=
      famRestartCostEq next I P hc T x hx
    _ ≤ n ^ T * L3.Prob.renewalCeiling B num den :=
      L3.Density.costNumerator_of_block
        (famRestartNext next I P) (famRestartGood I P) B num den
        hB hrho hgood hb x T

/-! ### The G18 hit mass of one window is the complement of the survival
numerator -/

/-- Scheduler sums only read words of the right length.

Consumer: `grantBlockSurvivalAddHit`. -/
private theorem famScheduleSumCongr {n : Nat} (L : Nat)
    (f g : List (Fin n) → Nat)
    (h : ∀ w : List (Fin n), w.length = L → f w = g w) :
    Prob.scheduleSum n L f = Prob.scheduleSum n L g := by
  change FixedSpanRenewalPayload.wordSum n L f =
    FixedSpanRenewalPayload.wordSum n L g
  rw [← FixedSpanRenewalPayload.rawWord_sum n L f,
    ← FixedSpanRenewalPayload.rawWord_sum n L g]
  exact ofFn_sum_eq _ _
    (fun i => h _ (FixedSpanRenewalPayload.rawWord_length n L i))

/-- First-letter step of the prefix-hit event.

Consumer: `famSurvivalWordHit`. -/
private theorem famHitExistsCons {n : Nat} (ring : DirectedRing n)
    (P : HeadlineConfiguration n → Prop)
    (x : HeadlineConfiguration n) (e : Fin n) (es : List (Fin n))
    (hP : ¬ P x) :
    (∃ pre suffix : List (Fin n),
        e :: es = pre ++ suffix ∧ P (Counter.Word ring pre x)) ↔
      (∃ pre suffix : List (Fin n),
        es = pre ++ suffix ∧
          P (Counter.Word ring pre (headlinePhysicalNext ring x e))) := by
  constructor
  · rintro ⟨pre, suffix, h, hpre⟩
    cases pre with
    | nil => exact absurd hpre hP
    | cons a pre' =>
        have h1 : e = a ∧ es = pre' ++ suffix := by
          injection h with h1 h2
          exact ⟨h1, h2⟩
        obtain ⟨h1, h2⟩ := h1
        subst h1
        exact ⟨pre', suffix, h2, hpre⟩
  · rintro ⟨pre, suffix, h, hpre⟩
    exact ⟨e :: pre, suffix, by rw [h]; rfl, hpre⟩

/-- Survival indicator plus prefix-hit indicator is one.

Consumer: `grantBlockSurvivalAddHit`. -/
private theorem famSurvivalWordHit {n : Nat} (ring : DirectedRing n)
    (P : HeadlineConfiguration n → Prop) :
    ∀ (w : List (Fin n)) (x : HeadlineConfiguration n),
      UniformFirstHit.survivalWord (headlinePhysicalNext ring) P x w +
        (if (∃ pre suffix : List (Fin n),
            w = pre ++ suffix ∧ P (Counter.Word ring pre x))
          then 1 else 0) = 1 := by
  intro w
  induction w with
  | nil =>
      intro x
      by_cases hP : P x
      · have hex : ∃ pre suffix : List (Fin n),
            ([] : List (Fin n)) = pre ++ suffix ∧
              P (Counter.Word ring pre x) := ⟨[], [], rfl, hP⟩
        rw [if_pos hex]
        simp [UniformFirstHit.survivalWord, hP]
      · have hex : ¬ ∃ pre suffix : List (Fin n),
            ([] : List (Fin n)) = pre ++ suffix ∧
              P (Counter.Word ring pre x) := by
          rintro ⟨pre, suffix, h, hpre⟩
          have hpre0 : pre = [] := (List.append_eq_nil_iff.mp h.symm).1
          subst hpre0
          exact hP hpre
        rw [if_neg hex]
        simp [UniformFirstHit.survivalWord, hP]
  | cons e es ih =>
      intro x
      by_cases hP : P x
      · have hex : ∃ pre suffix : List (Fin n),
            e :: es = pre ++ suffix ∧
              P (Counter.Word ring pre x) := ⟨[], e :: es, rfl, hP⟩
        rw [if_pos hex]
        simp [UniformFirstHit.survivalWord, hP]
      · have hiff := famHitExistsCons ring P x e es hP
        have hs : UniformFirstHit.survivalWord
              (headlinePhysicalNext ring) P x (e :: es) =
            UniformFirstHit.survivalWord
              (headlinePhysicalNext ring) P
              (headlinePhysicalNext ring x e) es := by
          simp [UniformFirstHit.survivalWord, hP]
        rw [hs]
        have hih := ih (headlinePhysicalNext ring x e)
        by_cases hex : ∃ pre suffix : List (Fin n),
            es = pre ++ suffix ∧
              P (Counter.Word ring pre (headlinePhysicalNext ring x e))
        · rw [if_pos (hiff.mpr hex)]
          rw [if_pos hex] at hih
          exact hih
        · rw [if_neg (fun h => hex (hiff.mp h))]
          rw [if_neg hex] at hih
          exact hih

/-- One window: the survivors and the G18 hits of a length-`W` word
partition the `n^W` words.

Consumer: `grantBlockEntranceBlockFailure`. -/
theorem grantBlockSurvivalAddHit {n : Nat} (ring : DirectedRing n)
    (x : HeadlineConfiguration n) (W : Nat) :
    UniformFirstHit.survivalNumerator (headlinePhysicalNext ring)
        (fun D => headlineGrantReady ring D ∨
          headlineGeneratedTarget ring D) x W +
      grantBlockSurrogateG18HitMass ring x W W = n ^ W := by
  unfold grantBlockSurrogateG18HitMass UniformFirstHit.survivalNumerator
  rw [← Density.schedule_sum_add W]
  have hpt : ∀ w : List (Fin n), w.length = W →
      UniformFirstHit.survivalWord (headlinePhysicalNext ring)
          (fun D => headlineGrantReady ring D ∨
            headlineGeneratedTarget ring D) x w +
        (if GrantBlockSurrogateG18HitWithin ring x W w then 1 else 0) =
      1 := by
    intro w hw
    have hiff : GrantBlockSurrogateG18HitWithin ring x W w ↔
        ∃ pre suffix : List (Fin n), w = pre ++ suffix ∧
          (fun D => headlineGrantReady ring D ∨
            headlineGeneratedTarget ring D) (Counter.Word ring pre x) := by
      unfold GrantBlockSurrogateG18HitWithin
      rw [List.take_of_length_le (Nat.le_of_eq hw)]
    by_cases hh : GrantBlockSurrogateG18HitWithin ring x W w
    · have hex := hiff.mp hh
      have := famSurvivalWordHit ring
        (fun D => headlineGrantReady ring D ∨
          headlineGeneratedTarget ring D) w x
      rw [if_pos hex] at this
      rw [if_pos hh]
      exact this
    · have hex : ¬ ∃ pre suffix : List (Fin n), w = pre ++ suffix ∧
          (fun D => headlineGrantReady ring D ∨
            headlineGeneratedTarget ring D) (Counter.Word ring pre x) :=
        fun h => hh (hiff.mpr h)
      have := famSurvivalWordHit ring
        (fun D => headlineGrantReady ring D ∨
          headlineGeneratedTarget ring D) w x
      rw [if_neg hex] at this
      rw [if_neg hh]
      exact this
  rw [famScheduleSumCongr W _ (fun _ => 1) hpt]
  exact (Density.schedule_sum_const W 1).trans (Nat.mul_one _)

/-- A first-`W`-letters function sums to a padded one-window sum.

Consumer: `grantBlockHitMassPad`. -/
private theorem famSchedulePrefix {n : Nat} :
    ∀ (W L : Nat) (f : List (Fin n) → Nat),
      Prob.scheduleSum n (W + L)
          (fun word => f (word.take W)) =
        n ^ L * Prob.scheduleSum n W f := by
  intro W
  induction W with
  | zero =>
      intro L f
      have hf :
          (fun word : List (Fin n) => f (word.take 0)) =
            (fun _ => f []) := rfl
      rw [hf, Density.schedule_sum_const,
        bankTrialProbabilityScheduleSumZero]
      simp only [Nat.zero_add]
  | succ W ih =>
      intro L f
      have hsum : (W + 1) + L = (W + L) + 1 := by omega
      rw [hsum, bankTrialProbabilityScheduleSumFirst,
        bankTrialProbabilityScheduleSumFirst]
      calc
        (List.ofFn (fun e : Fin n =>
          Prob.scheduleSum n (W + L)
            (fun word => f ((e :: word).take (W + 1))))).sum =
          (List.ofFn (fun e : Fin n =>
            n ^ L * Prob.scheduleSum n W
              (fun word => f (e :: word)))).sum := by
                apply ofFn_sum_eq
                intro e
                change Prob.scheduleSum n (W + L)
                  (fun word => f (e :: word.take W)) =
                  n ^ L * Prob.scheduleSum n W
                    (fun word => f (e :: word))
                exact ih L (fun word => f (e :: word))
        _ = n ^ L * (List.ofFn (fun e : Fin n =>
            Prob.scheduleSum n W
              (fun word => f (e :: word)))).sum :=
          ofFn_sum_mul_left (n ^ L) _

/-- The G18 hit mass at a longer horizon is the one-window mass padded with
free letters.

Consumer: `grantBlockEntranceBlockFailure`. -/
theorem grantBlockHitMassPad {n : Nat} (ring : DirectedRing n)
    (x : HeadlineConfiguration n) (W k : Nat) :
    grantBlockSurrogateG18HitMass ring x (W + k) W =
      n ^ k * grantBlockSurrogateG18HitMass ring x W W := by
  unfold grantBlockSurrogateG18HitMass
  have hfun : (fun word : List (Fin n) =>
        if GrantBlockSurrogateG18HitWithin ring x W word then 1 else 0) =
      (fun word : List (Fin n) =>
        if GrantBlockSurrogateG18HitWithin ring x W (word.take W)
          then 1 else 0) := by
    funext word
    have htt : (word.take W).take W = word.take W := by
      rw [List.take_take, Nat.min_self]
    have hiff : GrantBlockSurrogateG18HitWithin ring x W word ↔
        GrantBlockSurrogateG18HitWithin ring x W (word.take W) := by
      unfold GrantBlockSurrogateG18HitWithin
      rw [htt]
    by_cases hh : GrantBlockSurrogateG18HitWithin ring x W word
    · rw [if_pos hh, if_pos (hiff.mp hh)]
    · rw [if_neg hh, if_neg (fun h => hh (hiff.mpr h))]
  exact (congrArg (fun F => Prob.scheduleSum n (W + k) F) hfun).trans
    (famSchedulePrefix W k
      (fun w : List (Fin n) =>
        if GrantBlockSurrogateG18HitWithin ring x W w then 1 else 0))

/-! ### The block failure bound -/

/-- The block coefficient `Q = (b+2)(8b+13) 2^K` of the C.19 bound. -/
def grantBlockEntranceCoefficient (n : Nat) : Nat :=
  ((compileAdvice (ceilLogTwo n)).b + 2) *
    (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
    2 ^ (compileAdvice (ceilLogTwo n)).K

/-- **The block failure bound.**  With `W = floor(R n / 8)`, every purified,
density-good configuration that is not yet in the G18 target survives the
next `W` letters with at most the failure ratio
`(17 Q - 2 W)/(17 Q)`.

Consumer: `grantBlockEntranceCost` (the restart `grantBlockRenewalCostOfBlock`
with block length `W`). -/
theorem grantBlockEntranceBlockFailure
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
    0 < W ∧ 2 * W ≤ 17 * grantBlockEntranceCoefficient n ∧
    ∀ x : HeadlineConfiguration n,
      headlinePurified ring x →
      defects ring x * defects ring x ≤ 4 * n →
      ¬ (headlineGrantReady ring x ∨ headlineGeneratedTarget ring x) →
      17 * grantBlockEntranceCoefficient n *
          UniformFirstHit.survivalNumerator (headlinePhysicalNext ring)
            (fun D => headlineGrantReady ring D ∨
              headlineGeneratedTarget ring D) x W ≤
        (17 * grantBlockEntranceCoefficient n - 2 * W) * n ^ W := by
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
  have hblk := grantBlockFamilyBlockMassLower ring hn hsp hw hlarge x
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
  change 2 * W * n ^ (W + bankTrialRenewalIndexWindowCount n
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
  have e1 : 2 * W * n ^ (W + k) = (2 * W * n ^ W) * n ^ k := by
    rw [hpow]
    ac_rfl
  have e2 : 17 * Q * (n ^ k * m) = (17 * Q * m) * n ^ k := by ac_rfl
  rw [e1, e2] at hblk
  have h1 : 2 * W * n ^ W ≤ 17 * Q * m :=
    Nat.le_of_mul_le_mul_right hblk hnk
  have hmle : m ≤ n ^ W := by omega
  have h17 : 17 * Q * m ≤ 17 * Q * n ^ W := Nat.mul_le_mul_left _ hmle
  have hnW : 0 < n ^ W := Nat.pow_pos (by omega)
  have h2W : 2 * W ≤ 17 * Q := by
    have : 2 * W * n ^ W ≤ 17 * Q * n ^ W := Nat.le_trans h1 h17
    exact Nat.le_of_mul_le_mul_right this hnW
  have e3 : 17 * Q * sv + 17 * Q * m = 17 * Q * n ^ W := by
    rw [← Nat.mul_add, hadd]
  rw [Nat.sub_mul]
  omega

/-- The expected cost of the G18 target from the closed class of purified,
density-good configurations: `n^T (17 Q + 1)/2` for every horizon `T`.

Consumer: `grantBlockEntranceExpectedHitting`. -/
theorem grantBlockEntranceCost
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
        n ^ T * ((17 * grantBlockEntranceCoefficient n + 1) / 2) := by
  obtain ⟨R, hRlow, hRhigh⟩ := grantClockIntegerRadius n
  have hradius : (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2 :=
    ⟨hRlow, hRhigh⟩
  obtain ⟨hWpos, h2W, hfail⟩ := grantBlockEntranceBlockFailure
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
    (17 * grantBlockEntranceCoefficient n - 2 * (R * n / 8))
    (17 * grantBlockEntranceCoefficient n) hWpos
    (by omega)
    (fun y hy hny => hfail y hy.1 hy.2 hny) x ⟨hxp, hxd⟩ T
  refine Nat.le_trans hcost (Nat.mul_le_mul_left _ ?_)
  -- the rounded renewal ceiling is at most (17 Q + 1) / 2
  have hsub : 17 * grantBlockEntranceCoefficient n -
      (17 * grantBlockEntranceCoefficient n -
        2 * (R * n / 8)) = 2 * (R * n / 8) := by omega
  unfold L3.Prob.renewalCeiling
  rw [hsub]
  generalize R * n / 8 = W at hWpos h2W ⊢
  generalize grantBlockEntranceCoefficient n = Q at h2W ⊢
  have hbud : W * (17 * Q) ≤ (2 * W) * ((17 * Q + 1) / 2) := by
    have h : 17 * Q ≤ 2 * ((17 * Q + 1) / 2) := by omega
    calc
      W * (17 * Q) ≤ W * (2 * ((17 * Q + 1) / 2)) :=
        Nat.mul_le_mul_left _ h
      _ = (2 * W) * ((17 * Q + 1) / 2) := by ac_rfl
  have ha : 0 < 2 * W := by omega
  -- ceilNat z a ≤ reserve from z ≤ a * reserve
  have hq : W * (17 * Q) / (2 * W) < (17 * Q + 1) / 2 + 1 := by
    apply (Nat.div_lt_iff_lt_mul ha).2
    calc
      W * (17 * Q) ≤ (2 * W) * ((17 * Q + 1) / 2) := hbud
      _ = ((17 * Q + 1) / 2) * (2 * W) := Nat.mul_comm _ _
      _ < ((17 * Q + 1) / 2 + 1) * (2 * W) := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
  by_cases hz : W * (17 * Q) % (2 * W) = 0
  · change W * (17 * Q) / (2 * W) +
      (if W * (17 * Q) % (2 * W) = 0 then 0 else 1) ≤ _
    rw [if_pos hz]
    omega
  · have hne : W * (17 * Q) ≠ ((17 * Q + 1) / 2) * (2 * W) := by
      intro he
      apply hz
      rw [he]
      simp
    have hle : W * (17 * Q) ≤ ((17 * Q + 1) / 2) * (2 * W) := by
      calc
        W * (17 * Q) ≤ (2 * W) * ((17 * Q + 1) / 2) := hbud
        _ = ((17 * Q + 1) / 2) * (2 * W) := Nat.mul_comm _ _
    have hlt : W * (17 * Q) < ((17 * Q + 1) / 2) * (2 * W) := by omega
    have hqstrict : W * (17 * Q) / (2 * W) < (17 * Q + 1) / 2 :=
      (Nat.div_lt_iff_lt_mul ha).2 hlt
    change W * (17 * Q) / (2 * W) +
      (if W * (17 * Q) % (2 * W) = 0 then 0 else 1) ≤ _
    rw [if_neg hz]
    omega

/-- **The G16 stage.**  From every purified, density-good configuration the
expected number of physical interactions until the G18 target
(`headlineGrantReady ∨ headlineGeneratedTarget`) is at most
`(17 Q + 1)/2`, `Q = (b+2)(8b+13) 2^K`.

Consumer: `grantBlockLeaderlessEntranceExpectedHitting`. -/
theorem grantBlockEntranceExpectedHitting
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
      (((17 * grantBlockEntranceCoefficient n + 1) / 2 : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) _ (by omega : 0 < n) x _).2
  exact grantBlockEntranceCost ring hn hsp hw hlarge hsize x hxp hxd

/-- Strengthening the target on a closed carrier costs nothing.

Consumer: `grantBlockLeaderlessEntranceExpectedHitting`. -/
private theorem famCostTargetOnClosed {m : Nat} {S : Type}
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
`192 n^2 + (17 Q + 1)/2`: the density entrance
(`headlineStagesGrantDensityEntrance`, `192 n^2`) reaches a density-good
configuration or the target, purification persists, and the block renewal
finishes.

Consumer: `StageGrantLeaderlessClock` (HeadlineStages.lean:265), through
`stageFirstGrant_of_leaderless_clock`.  This is the expected-time clause of
`StageGrantLeaderlessClock` for the spatial band (`16 ≤ n`, `useSmall = false`,
nonalias, `hsize`), with the bound `192 n^2 + (17 Q + 1)/2` instead of
`headlinePermitRate n * n^2`.  Still missing for the literal consumer: the
comparison of the two bounds (the ledger's `34 f w (A+1)` against `17 Q / 2`
needs a union constant better than the Lean C.17 `min(N, 2S) ≤ 4U`), and the
band `useSmall = true` / small `n` (G17). -/
theorem grantBlockLeaderlessEntranceExpectedHitting
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
        (17 * grantBlockEntranceCoefficient n + 1) / 2 : Nat) : Rat) := by
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
    exact famCostTargetOnClosed (headlinePhysicalNext ring)
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
    exact grantBlockEntranceCost ring hn5 hsp hw hlarge hsize y hy.1 hy.2 T

end L3

#print axioms L3.grantBlockRenewalCostOfBlock
#print axioms L3.grantBlockSurvivalAddHit
#print axioms L3.grantBlockHitMassPad
#print axioms L3.grantBlockEntranceBlockFailure
#print axioms L3.grantBlockEntranceCost
#print axioms L3.grantBlockEntranceExpectedHitting
#print axioms L3.grantBlockLeaderlessEntranceExpectedHitting
