import Leader.PPL.Elim.TransferGeometry
import Leader.PPL.Elim.LocalDeletionCounting
import Leader.PPL.Elim.TransferArith

/-!
The scale attempt carries its current physical PB configuration. A retry
returns the reached configuration itself; its fuel is reset only when the next
attempt starts. The remaining obligation is the finite-word comparison of
this kernel's retry mass and cost with the literal row-E process.
-/

namespace PPL.Convergence.LDTransfer

open PPL.Convergence.LDLocal
open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A configuration is at or below the indicated 23/24 leader scale. -/
def atOrBelowScale {n : Nat} (h : Nat)
    (C : Config n) : Prop :=
  PPL.Elim.leaderCount C * 23 ^ h ≤ 24 ^ h

/-- The integer block budget corresponding to the scale ceiling. -/
def scaleBlock (c n h : Nat) : Nat :=
  ((16 * c * n * n * 23 ^ h + 24 ^ h - 1) / 24 ^ h) + 1

private theorem contract_reaches_scale (h s t : Nat)
    (hupper : s * 23 ^ (h + 1) ≤ 24 ^ (h + 1))
    (hcontract : 24 * t < 23 * s) :
    t * 23 ^ h ≤ 24 ^ h := by
  have hp : 0 < 23 ^ h := Nat.pow_pos (by decide)
  have hm := Nat.mul_lt_mul_of_pos_right hcontract hp
  have hchain : 24 * (t * 23 ^ h) < 24 * 24 ^ h := by
    calc
      24 * (t * 23 ^ h) = (24 * t) * 23 ^ h := by ac_rfl
      _ < (23 * s) * 23 ^ h := hm
      _ = s * 23 ^ (h + 1) := by simp [Nat.pow_succ]; ac_rfl
      _ ≤ 24 ^ (h + 1) := hupper
      _ = 24 * 24 ^ h := by simp [Nat.pow_succ]; ac_rfl
  omega

private theorem scaleBlock_horizon (c n h s : Nat)
    (hnot : ¬s * 23 ^ h ≤ 24 ^ h) :
    16 * c * n * n ≤ s * scaleBlock c n h := by
  let p := 23 ^ h
  let q := 24 ^ h
  let A := 16 * c * n * n
  let y := A * p + q - 1
  have hp : 0 < p := Nat.pow_pos (by decide)
  have hq : 0 < q := Nat.pow_pos (by decide)
  have hy : A * p ≤ y := by dsimp [y]; omega
  have hmod : y % q < q := Nat.mod_lt _ hq
  have hdecomp : y % q + q * (y / q) = y := Nat.mod_add_div y q
  have hyceil : y ≤ q * (y / q) + q := by omega
  have hceil : A * p ≤ (y / q + 1) * q := by
    calc
      A * p ≤ y := hy
      _ ≤ q * (y / q) + q := hyceil
      _ = (y / q + 1) * q := by rw [Nat.add_mul]; ac_rfl
  have hratio : q ≤ s * p := by
    dsimp [p, q] at *
    omega
  have hmult := Nat.mul_le_mul_left (y / q + 1) hratio
  have hscaled : A * p ≤ (s * (y / q + 1)) * p := by
    calc
      A * p ≤ (y / q + 1) * q := hceil
      _ ≤ (y / q + 1) * (s * p) := hmult
      _ = (s * (y / q + 1)) * p := by ac_rfl
  have hout := Nat.le_of_mul_le_mul_right hscaled hp
  simpa [A, p, q, y, scaleBlock, Nat.mul_assoc] using hout

/-- States admissible for every attempt carry the actual PB and upper-scale
invariants; retry validity is therefore structural. -/
def ScaleSurvivor {n : Nat} (ring : DirectedRing n) (h : Nat) : Type :=
  { D : Config n // PPL.Elim.PB ring D ∧
      PPL.Elim.leaderCount D * 23 ^ (h + 1) ≤ 24 ^ (h + 1) }

/-- Literal row-E step lifted to an admissible reached state. -/
def scaleSurvivorStep {n : Nat} (ring : DirectedRing n) (h : Nat)
    (hPBStep : PBStepClosure) (s : ScaleSurvivor ring h) (e : Fin n) :
    ScaleSurvivor ring h :=
  ⟨stepE ring s.val e, by
    constructor
    · exact hPBStep ring s.val e s.property.1
    · have hm := PPL.Elim.leaderCount_step_le ring s.val e
      have hm' := Nat.mul_le_mul_right (23 ^ (h + 1)) hm
      exact Nat.le_trans hm' s.property.2⟩

/-- The q=3 attempt kernel. The second component is the remaining number of
physical letters in this attempt, and `.retry s'` keeps the reached `s'`. -/
noncomputable def scaleRetryKernel {n : Nat} (ring : DirectedRing n)
    (h : Nat) (hPBStep : PBStepClosure) (B : Nat) :
    RetryKernel (ScaleSurvivor ring h × Nat) (ScaleSurvivor ring h) n := by
  classical
  exact
    { start := fun s => (s, B)
      step := fun a e =>
        let s' := scaleSurvivorStep ring h hPBStep a.1 e
        if atOrBelowScale h s'.val then
          .success
        else if a.2 ≤ 1 then
          .retry s'
        else
          .active (s', a.2 - 1)
      valid := fun _ => True
      retry_valid := by
        intro a e s' _
        trivial }

/-- The repeated kernel never undercounts raw first-hit cost: each retry
starts from the reached state, while target states have zero raw cost. -/
private theorem rawCost_le_repeatActive {n : Nat}
    (ring : DirectedRing n) (h : Nat) (hPBStep : PBStepClosure)
    (B : Nat) (s : ScaleSurvivor ring h) (fuel : Nat) (T : Nat) :
    costNumerator (stepE ring) (atOrBelowScale h) s.val T ≤
      repeatCostActive (scaleRetryKernel ring h hPBStep B) (s, fuel) T := by
  induction T generalizing s fuel with
  | zero => simp [repeatCostActive]
  | succ T ih =>
      by_cases ht : atOrBelowScale h s.val
      · rw [costNumerator_terminal (stepE ring) (atOrBelowScale h) s.val ht]
        exact Nat.zero_le _
      · rw [costNumerator_succ (stepE ring) (atOrBelowScale h) s.val ht]
        simp only [repeatCostActive]
        apply Nat.add_le_add_left
        apply ofFn_sum_le
        intro e
        let s' := scaleSurvivorStep ring h hPBStep s e
        have hval : s'.val = stepE ring s.val e := rfl
        by_cases hs' : atOrBelowScale h s'.val
        · have hz := costNumerator_terminal
            (stepE ring) (atOrBelowScale h) s'.val hs' T
          simp [scaleRetryKernel, s', hs', ← hval, hz]
        · by_cases hf : fuel ≤ 1
          · have hi := ih s' B
            simpa [scaleRetryKernel, s', hs', hf, ← hval] using hi
          · have hi := ih s' (fuel - 1)
            simpa [scaleRetryKernel, s', hs', hf, ← hval] using hi

private theorem attemptCost_success {A S : Type} {n : Nat}
    (K : RetryKernel A S n) (T : Nat) :
    attemptCostNumerator K .success T = 0 := by
  cases T <;> rfl

private theorem attemptCost_retry {A S : Type} {n : Nat}
    (K : RetryKernel A S n) (s : S) (T : Nat) :
    attemptCostNumerator K (.retry s) T = 0 := by
  cases T <;> rfl

/-- One attempt can charge at most its current positive fuel. Its terminal
retry branch costs no additional scheduler letters. -/
private theorem attemptCost_le_fuel {n : Nat}
    (ring : DirectedRing n) (h : Nat) (hPBStep : PBStepClosure)
    (B : Nat) (s : ScaleSurvivor ring h) (fuel : Nat)
    (hpos : 1 ≤ fuel) (T : Nat) :
    attemptCostNumerator (scaleRetryKernel ring h hPBStep B)
        (.active (s, fuel)) T ≤ n ^ T * fuel := by
  induction T generalizing s fuel with
  | zero => simp [attemptCostNumerator]
  | succ T ih =>
      simp only [attemptCostNumerator]
      by_cases hf : fuel ≤ 1
      · have hchild (e : Fin n) :
            attemptCostNumerator (scaleRetryKernel ring h hPBStep B)
              ((scaleRetryKernel ring h hPBStep B).step (s, fuel) e) T = 0 := by
          let s' := scaleSurvivorStep ring h hPBStep s e
          by_cases hs' : atOrBelowScale h s'.val
          · simp [scaleRetryKernel, s', hs', attemptCost_success]
          · simp [scaleRetryKernel, s', hs', hf, attemptCost_retry]
        rw [ofFn_sum_eq _ (fun _ : Fin n => 0) hchild, ofFn_sum_const]
        simp only [Nat.mul_zero, Nat.add_zero]
        exact Nat.le_mul_of_pos_right _ (by omega)
      · have hchild (e : Fin n) :
            attemptCostNumerator (scaleRetryKernel ring h hPBStep B)
                ((scaleRetryKernel ring h hPBStep B).step (s, fuel) e) T ≤
              n ^ T * (fuel - 1) := by
          let s' := scaleSurvivorStep ring h hPBStep s e
          by_cases hs' : atOrBelowScale h s'.val
          · simp [scaleRetryKernel, s', hs', attemptCost_success]
          · have hfpos : 1 ≤ fuel - 1 := by omega
            have hi := ih s' (fuel - 1) hfpos
            simpa [scaleRetryKernel, s', hs', hf] using hi
        have hsum := ofFn_sum_le
          (fun e : Fin n =>
            attemptCostNumerator (scaleRetryKernel ring h hPBStep B)
              ((scaleRetryKernel ring h hPBStep B).step (s, fuel) e) T)
          (fun _ : Fin n => n ^ T * (fuel - 1)) hchild
        rw [ofFn_sum_const] at hsum
        have hpow : n * (n ^ T * (fuel - 1)) =
            n ^ (T + 1) * (fuel - 1) := by
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        calc
          n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                attemptCostNumerator (scaleRetryKernel ring h hPBStep B)
                  ((scaleRetryKernel ring h hPBStep B).step (s, fuel) e) T)).sum ≤
              n ^ (T + 1) + n * (n ^ T * (fuel - 1)) :=
                Nat.add_le_add_left hsum _
          _ = n ^ (T + 1) * fuel := by
            rw [hpow]
            have hf' : 1 + (fuel - 1) = fuel := by omega
            calc
              n ^ (T + 1) + n ^ (T + 1) * (fuel - 1) =
                  n ^ (T + 1) * (1 + (fuel - 1)) := by
                    simp [Nat.mul_add]
              _ = n ^ (T + 1) * fuel := by rw [hf']

/-- The raw endpoint mass of non-target states, computed on reached subtype
states so every recursive call retains the PB/upper-scale invariant. -/
noncomputable def scaleMissMass {n : Nat} (ring : DirectedRing n)
    (h : Nat) (hPBStep : PBStepClosure)
    (s : ScaleSurvivor ring h) (T : Nat) : Nat := by
  classical
  exact wordSum (scaleSurvivorStep ring h hPBStep)
    (fun z => if atOrBelowScale h z.val then 0 else 1) s T

private theorem scaleWordSum_eq_raw {n : Nat}
    (ring : DirectedRing n) (h : Nat) (hPBStep : PBStepClosure)
    (w : Config n → Nat) (s : ScaleSurvivor ring h) (T : Nat) :
    wordSum (scaleSurvivorStep ring h hPBStep)
        (fun z => w z.val) s T =
      wordSum (stepE ring) w s.val T := by
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
      rw [wordSum_succ, wordSum_succ]
      apply ofFn_sum_eq
      intro e
      simpa [scaleSurvivorStep] using
        ih (scaleSurvivorStep ring h hPBStep s e)

private theorem wordSum_weight_congr {S : Type} {n : Nat}
    (next : S → Fin n → S) (w v : S → Nat)
    (hw : ∀ z, w z = v z) (s : S) (T : Nat) :
    wordSum next w s T = wordSum next v s T := by
  induction T generalizing s with
  | zero => exact hw s
  | succ T ih =>
      rw [wordSum_succ, wordSum_succ]
      apply ofFn_sum_eq
      intro e
      exact ih (next s e)

private theorem scaleMissMass_eq_raw {n : Nat}
    (ring : DirectedRing n) (h : Nat) (hPBStep : PBStepClosure)
    (s : ScaleSurvivor ring h) (T : Nat) :
    scaleMissMass ring h hPBStep s T =
      hitMass (stepE ring) (fun D => ¬atOrBelowScale h D) s.val T := by
  classical
  induction T generalizing s with
  | zero =>
      by_cases ht : atOrBelowScale h s.val <;>
        simp [scaleMissMass, hitMass, ht]
  | succ T ih =>
      unfold scaleMissMass hitMass
      rw [wordSum_succ, wordSum_succ]
      apply ofFn_sum_eq
      intro e
      simpa [scaleSurvivorStep, scaleMissMass, hitMass] using
        ih (scaleSurvivorStep ring h hPBStep s e)

private theorem pb_leaderCount_pos {n : Nat}
    (ring : DirectedRing n) (C : Config n)
    (hPB : PPL.Elim.PB ring C) :
    0 < PPL.Elim.leaderCount C := by
  obtain ⟨i, hi⟩ := hPB.1
  change 0 < (List.ofFn
    (fun j : Fin n => if (C j).leader then 1 else 0)).sum
  have hmem : 1 ∈ (List.ofFn
      (fun j : Fin n => if (C j).leader then 1 else 0)) := by
    rw [List.mem_ofFn]
    exact ⟨i, by simp [hi]⟩
  by_cases hpos : 0 < (List.ofFn
      (fun j : Fin n => if (C j).leader then 1 else 0)).sum
  · exact hpos
  · have hz : (List.ofFn
        (fun j : Fin n => if (C j).leader then 1 else 0)).sum = 0 := by omega
    have hall := List.sum_eq_zero_iff_forall_eq_nat.mp hz
    have hone := hall 1 hmem
    omega

private theorem count_two_of_not_scale {n : Nat}
    (ring : DirectedRing n) (h : Nat) (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (hnot : ¬atOrBelowScale h C) :
    2 ≤ PPL.Elim.leaderCount C := by
  have hpos := pb_leaderCount_pos ring C hPB
  have hpow : 23 ^ h ≤ 24 ^ h := Nat.pow_le_pow_left (by decide) h
  unfold atOrBelowScale at hnot
  by_cases htwo : 2 ≤ PPL.Elim.leaderCount C
  · exact htwo
  · have hone : PPL.Elim.leaderCount C = 1 := by omega
    rw [hone] at hnot
    simp only [Nat.one_mul] at hnot
    omega

private theorem contractMass_le_scaleMass {n : Nat}
    (ring : DirectedRing n) (h : Nat) (C : Config n)
    (hupper : PPL.Elim.leaderCount C * 23 ^ (h + 1) ≤ 24 ^ (h + 1))
    (T : Nat) :
    hitMass (stepE ring)
        (fun D => 24 * PPL.Elim.leaderCount D <
          23 * PPL.Elim.leaderCount C) C T ≤
      hitMass (stepE ring) (atOrBelowScale h) C T := by
  classical
  let s := PPL.Elim.leaderCount C
  have hclosed : ∀ D : Config n, ∀ e : Fin n,
      PPL.Elim.leaderCount D ≤ s →
      PPL.Elim.leaderCount (stepE ring D e) ≤ s := by
    intro D e hD
    exact Nat.le_trans (PPL.Elim.leaderCount_step_le ring D e) hD
  unfold hitMass
  apply wordSum_mono_on (stepE ring)
    (fun D => PPL.Elim.leaderCount D ≤ s) hclosed
  · intro D hD
    by_cases hc : 24 * PPL.Elim.leaderCount D < 23 * s
    · have ht : atOrBelowScale h D :=
        contract_reaches_scale h s _ hupper hc
      simp [hc, ht, s]
    · simp [hc, s]
  · exact Nat.le_refl _

private theorem scaleHitMiss_partition {n : Nat}
    (ring : DirectedRing n) (h : Nat) (C : Config n) (T : Nat) :
    hitMass (stepE ring) (atOrBelowScale h) C T +
      hitMass (stepE ring) (fun D => ¬atOrBelowScale h D) C T = n ^ T := by
  classical
  unfold hitMass
  rw [← wordSum_add]
  calc
    _ = wordSum (stepE ring) (fun _ => 1) C T := by
      apply wordSum_weight_congr
      intro D
      by_cases ht : atOrBelowScale h D <;> simp [ht]
    _ = n ^ T := by simp [wordSum_const]

private theorem scaleMissMass_bound {c n : Nat}
    (hLD : LDStatement c) (hc : 1 ≤ c)
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (h : Nat) (hPBStep : PBStepClosure)
    (s : ScaleSurvivor ring h) :
    3 * scaleMissMass ring h hPBStep s (scaleBlock c n h) ≤
      2 * n ^ scaleBlock c n h := by
  classical
  let B := scaleBlock c n h
  change 3 * scaleMissMass ring h hPBStep s B ≤ 2 * n ^ B
  by_cases ht : atOrBelowScale h s.val
  · have hclosed : ∀ D : Config n, ∀ e : Fin n,
        atOrBelowScale h D → atOrBelowScale h (stepE ring D e) := by
      intro D e hD
      unfold atOrBelowScale at *
      exact Nat.le_trans
        (Nat.mul_le_mul_right (23 ^ h)
          (PPL.Elim.leaderCount_step_le ring D e)) hD
    have hmiss : hitMass (stepE ring)
        (fun D => ¬atOrBelowScale h D) s.val B = 0 := by
      unfold hitMass
      have hzero := wordSum_mono_on (stepE ring)
        (atOrBelowScale h) hclosed
        (fun D : Config n => if ¬atOrBelowScale h D then 1 else 0)
        (fun _ => 0)
        (by intro D hD; simp [hD]) B s.val ht
      have hz : wordSum (stepE ring) (fun _ : Config n => 0) s.val B = 0 := by
        simp [wordSum_const]
      rw [hz] at hzero
      calc
        _ = wordSum (stepE ring)
            (fun D : Config n => if ¬atOrBelowScale h D then 1 else 0)
            s.val B := by
              apply wordSum_weight_congr
              intro D
              by_cases hD : atOrBelowScale h D <;> simp [hD]
        _ = 0 := by omega
    rw [scaleMissMass_eq_raw, hmiss]
    omega
  · have hs : 2 ≤ PPL.Elim.leaderCount s.val :=
      count_two_of_not_scale ring h s.val s.property.1 ht
    have hH : 16 * c * n * n ≤
        PPL.Elim.leaderCount s.val * B :=
      scaleBlock_horizon c n h (PPL.Elim.leaderCount s.val) ht
    have hcontract := one_block_contract_mass_geometry hLD hc hn
      ring s.val s.property.1 rfl hs hH
    have hmono := contractMass_le_scaleMass ring h s.val s.property.2 B
    have hpart := scaleHitMiss_partition ring h s.val B
    rw [scaleMissMass_eq_raw]
    omega

private theorem retryCount_before_fuel {n : Nat}
    (ring : DirectedRing n) (h : Nat) (hPBStep : PBStepClosure)
    (B : Nat) (s : ScaleSurvivor ring h)
    (fuel T : Nat) (hshort : T < fuel) :
    retryCount (scaleRetryKernel ring h hPBStep B)
      (.active (s, fuel)) T = 0 := by
  induction T generalizing s fuel with
  | zero => rfl
  | succ T ih =>
      have hf : ¬fuel ≤ 1 := by omega
      simp only [retryCount]
      have hz :
          (List.ofFn (fun e : Fin n =>
            retryCount (scaleRetryKernel ring h hPBStep B)
              ((scaleRetryKernel ring h hPBStep B).step (s, fuel) e) T)).sum =
          (List.ofFn (fun _ : Fin n => 0)).sum := by
        apply ofFn_sum_eq
        intro e
        let s' := scaleSurvivorStep ring h hPBStep s e
        by_cases hs' : atOrBelowScale h s'.val
        · simp [scaleRetryKernel, s', hs', retryCount]
        · have ht : T < fuel - 1 := by omega
          simpa [scaleRetryKernel, s', hs', hf] using ih s' (fuel - 1) ht
      rw [ofFn_sum_const] at hz
      simpa using hz

private theorem retryCount_after_fuel {n : Nat}
    (ring : DirectedRing n) (h : Nat) (hPBStep : PBStepClosure)
    (B : Nat) (fuel : Nat) (hpos : 1 ≤ fuel) :
    ∀ (s : ScaleSurvivor ring h) (T : Nat), fuel ≤ T →
      retryCount (scaleRetryKernel ring h hPBStep B)
        (.active (s, fuel)) T ≤
          scaleMissMass ring h hPBStep s fuel * n ^ (T - fuel) := by
  induction fuel with
  | zero => omega
  | succ k ih =>
      intro s T hT
      cases T with
      | zero => omega
      | succ T =>
          classical
          simp only [retryCount]
          by_cases hk : k = 0
          · subst k
            have hchild (e : Fin n) :
                retryCount (scaleRetryKernel ring h hPBStep B)
                    ((scaleRetryKernel ring h hPBStep B).step (s, 1) e) T ≤
                  (if atOrBelowScale h
                      (scaleSurvivorStep ring h hPBStep s e).val then 0 else 1) *
                    n ^ T := by
              let s' := scaleSurvivorStep ring h hPBStep s e
              by_cases hs' : atOrBelowScale h s'.val
              · simp [scaleRetryKernel, s', hs', retryCount]
              · simp [scaleRetryKernel, s', hs', retryCount]
            have hsum := ofFn_sum_le _ _ hchild
            have hsum' :
                (List.ofFn (fun e : Fin n =>
                  retryCount (scaleRetryKernel ring h hPBStep B)
                    ((scaleRetryKernel ring h hPBStep B).step (s, 1) e) T)).sum ≤
                n ^ T * (List.ofFn (fun e : Fin n =>
                  if atOrBelowScale h
                    (scaleSurvivorStep ring h hPBStep s e).val then 0 else 1)).sum := by
              simpa [Nat.mul_comm, ofFn_sum_mul_left] using hsum
            simpa [scaleMissMass, wordSum_succ, Nat.mul_comm] using hsum'
          · have hkpos : 1 ≤ k := by omega
            have hkt : k ≤ T := by omega
            have hchild (e : Fin n) :
                retryCount (scaleRetryKernel ring h hPBStep B)
                    ((scaleRetryKernel ring h hPBStep B).step (s, k + 1) e) T ≤
                  scaleMissMass ring h hPBStep
                    (scaleSurvivorStep ring h hPBStep s e) k *
                    n ^ (T - k) := by
              let s' := scaleSurvivorStep ring h hPBStep s e
              by_cases hs' : atOrBelowScale h s'.val
              · simp [scaleRetryKernel, s', hs', retryCount]
              · have hi := ih hkpos s' T hkt
                simpa [scaleRetryKernel, s', hs', show ¬k + 1 ≤ 1 by omega]
                  using hi
            have hsum := ofFn_sum_le _ _ hchild
            have hsum' :
                (List.ofFn (fun e : Fin n =>
                  retryCount (scaleRetryKernel ring h hPBStep B)
                    ((scaleRetryKernel ring h hPBStep B).step (s, k + 1) e) T)).sum ≤
                n ^ (T - k) * (List.ofFn (fun e : Fin n =>
                  scaleMissMass ring h hPBStep
                    (scaleSurvivorStep ring h hPBStep s e) k)).sum := by
              simpa [Nat.mul_comm, ofFn_sum_mul_left] using hsum
            simpa [scaleMissMass, wordSum_succ, Nat.mul_comm,
              show T + 1 - (k + 1) = T - k by omega] using hsum'

/-- The exact planned Lemma-4 conclusion, kept independent of the kernel
implementation. -/
def ScaleCostStatement (c : Nat) : Prop :=
  ∀ (hPBStep : PBStepClosure) (hLD : LDStatement c) (hc : 1 ≤ c)
    {n : Nat} (hn : 2 ≤ n) (ring : DirectedRing n)
    (h : Nat) (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (hupper :
      PPL.Elim.leaderCount C * 23 ^ (h + 1) ≤ 24 ^ (h + 1)),
    ∀ T : Nat,
      costNumerator (stepE ring) (atOrBelowScale h) C T ≤
        n ^ T * (3 * scaleBlock c n h)

/-- Lemma 4: the first hitting cost of the next leader scale is bounded by
three literal q=3 attempts of length `scaleBlock`. Every retry begins at the
configuration reached by its preceding physical word. -/
theorem scale_cost {c : Nat}
    (hPBStep : PBStepClosure) (hLD : LDStatement c) (hc : 1 ≤ c)
    {n : Nat} (hn : 2 ≤ n) (ring : DirectedRing n)
    (h : Nat) (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (hupper :
      PPL.Elim.leaderCount C * 23 ^ (h + 1) ≤ 24 ^ (h + 1)) :
    ∀ T : Nat,
      costNumerator (stepE ring) (atOrBelowScale h) C T ≤
        n ^ T * (3 * scaleBlock c n h) := by
  let B := scaleBlock c n h
  let K := scaleRetryKernel ring h hPBStep B
  let s : ScaleSurvivor ring h := ⟨C, hPB, hupper⟩
  have hB : 1 ≤ B := by
    dsimp [B, scaleBlock]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hcost : ∀ t : ScaleSurvivor ring h, K.valid t → ∀ T,
      attemptCostNumerator K (.active (K.start t)) T ≤ n ^ T * B := by
    intro t _ T
    simpa [K, scaleRetryKernel] using
      attemptCost_le_fuel ring h hPBStep B t B hB T
  have hretry : ∀ t : ScaleSurvivor ring h, K.valid t → ∀ T,
      3 * retryCount K (.active (K.start t)) T ≤ 2 * n ^ T := by
    intro t _ T
    change 3 * retryCount (scaleRetryKernel ring h hPBStep B)
      (.active (t, B)) T ≤ 2 * n ^ T
    by_cases hshort : T < B
    · rw [retryCount_before_fuel ring h hPBStep B t B T hshort]
      omega
    · have hlate := retryCount_after_fuel ring h hPBStep B B hB
        t T (by omega)
      have hmass := scaleMissMass_bound hLD hc hn ring h hPBStep t
      have hmass' : 3 * scaleMissMass ring h hPBStep t B ≤ 2 * n ^ B :=
        hmass
      calc
        3 * retryCount (scaleRetryKernel ring h hPBStep B)
            (.active (t, B)) T ≤
          3 * (scaleMissMass ring h hPBStep t B * n ^ (T - B)) :=
            Nat.mul_le_mul_left 3 hlate
        _ = (3 * scaleMissMass ring h hPBStep t B) * n ^ (T - B) := by
          ac_rfl
        _ ≤ (2 * n ^ B) * n ^ (T - B) :=
          Nat.mul_le_mul_right (n ^ (T - B)) hmass'
        _ = 2 * n ^ T := by
          have hBT : B + (T - B) = T := by omega
          calc
            (2 * n ^ B) * n ^ (T - B) = 2 * n ^ (B + (T - B)) := by
              rw [Nat.pow_add]
              ac_rfl
            _ = 2 * n ^ T := by rw [hBT]
  intro T
  have hrepeat := retry_cost_of_retry_mass K 3 B (by decide)
    hcost hretry s (by trivial) T
  have hraw := rawCost_le_repeatActive ring h hPBStep B s B T
  change costNumerator (stepE ring) (atOrBelowScale h) C T ≤
    n ^ T * (3 * B)
  exact Nat.le_trans hraw (by simpa [K, repeatCostNumerator,
    scaleRetryKernel] using hrepeat)

#print axioms PPL.Convergence.LDTransfer.scale_cost

end PPL.Convergence.LDTransfer
