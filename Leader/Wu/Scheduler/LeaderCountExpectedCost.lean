import Leader.Core.LeaderCountDyadicTail
import Leader.Wu.Scheduler.FixedSpanRenewalPayload

/-!
# Finite raw-scheduler leader-count costs

This is a conditional consumer of uniform physical deletion mass on a closed,
positive-count domain. The scheduler and every continuing state are the given
raw transition. Complete blocks may have different horizons at different
counts; unfinished prefixes are charged interaction by interaction. No
one-interaction reserve drift or termination premise is used.
-/

namespace LeaderCountExpectedCost

open FiniteUniformStoppingTree LeaderCountDyadicTail
open FixedSpanRenewalPayload (PayloadOutcome)

set_option autoImplicit false

/-- Stop charging exactly when the actual count is one. -/
def haltAt {S : Type} (count : S → Nat) (x : S) : PayloadOutcome S :=
  if count x = 1 then .success x else .retry x

/-- Each payload contains the given physical successor, without modification. -/
def physicalPayload {S : Type} {n : Nat}
    (step : S → Fin n → S) (count : S → Nat) (x : S) (e : Fin n) :
    PayloadOutcome S := haltAt count (step x e)

/-- Exact finite numerator of all charged active prefixes, denominator `n^T`. -/
def chargedPrefixNumerator {S : Type} {n : Nat}
    (step : S → Fin n → S) (count : S → Nat) (x : S) (T : Nat) : Nat :=
  truncatedActiveCostNumerator
    (FixedSpanRenewalPayload.macroStep (physicalPayload step count))
    (FixedSpanRenewalPayload.erasePayload (haltAt count x)) T

@[simp] theorem chargedPrefix_zero {S : Type} {n : Nat}
    (step : S → Fin n → S) (count : S → Nat) (x : S) :
    chargedPrefixNumerator step count x 0 = 0 := by
  unfold chargedPrefixNumerator
  cases FixedSpanRenewalPayload.erasePayload (haltAt count x) <;> rfl

theorem chargedPrefix_terminal {S : Type} {n : Nat}
    (step : S → Fin n → S) (count : S → Nat) (x : S)
    (hx : count x = 1) (T : Nat) :
    chargedPrefixNumerator step count x T = 0 := by
  cases T <;> simp [chargedPrefixNumerator, haltAt, hx,
    FixedSpanRenewalPayload.erasePayload, truncatedActiveCostNumerator]

/-- The numerator is the existing literal raw-word cost sum, including partial
active prefixes. Successful payloads retain the actual first-success state. -/
theorem chargedPrefix_eq_rawWordCost {S : Type} {n : Nat}
    (step : S → Fin n → S) (count : S → Nat) (x : S) (T : Nat) :
    chargedPrefixNumerator step count x T =
      FixedSpanRenewalPayload.wordSum n T
        (FixedSpanRenewalPayload.rawWordCost (physicalPayload step count)
          (haltAt count x)) :=
  (FixedSpanRenewalPayload.wordSum_cost_eq
    (physicalPayload step count) (haltAt count x) T).symm

/-- A horizon of length `T` charges at most `T` on each of its `n^T` words. -/
theorem chargedPrefix_le_horizon {S : Type} {n : Nat}
    (step : S → Fin n → S) (count : S → Nat) (x : S) (T : Nat) :
    chargedPrefixNumerator step count x T ≤ n ^ T * T := by
  by_cases hx : count x = 1
  · rw [chargedPrefix_terminal step count x hx T]
    exact Nat.zero_le _
  · have h := FixedSpanRenewalPayload.block_cost_le_horizon
      (physicalPayload step count) T x
    rw [FixedSpanRenewalPayload.block_cost_eq] at h
    simpa [chargedPrefixNumerator, haltAt, hx,
      FixedSpanRenewalPayload.erasePayload] using h

/-- Charge the current raw interaction when the actual count exceeds one,
then continue from its actual successor. Positivity makes count one absorbing
for this observable, even though other physical fields can keep changing. -/
theorem chargedPrefix_succ_on {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e)) (count : S → Nat)
    (hpos : ∀ x, P x → 1 ≤ count x)
    (hstep : ∀ x e, P x → count (step x e) ≤ count x)
    (x : S) (hx : P x) (T : Nat) :
    chargedPrefixNumerator step count x (T + 1) =
      n ^ (T + 1) * binMiss 1 (count x) +
        (List.ofFn (fun e : Fin n =>
          chargedPrefixNumerator step count (step x e) T)).sum := by
  by_cases hterminal : count x = 1
  · have he (e : Fin n) : count (step x e) = 1 := by
      have := hpos (step x e) (hclosed x e hx)
      have := hstep x e hx
      omega
    rw [chargedPrefix_terminal step count x hterminal (T + 1)]
    simp only [hterminal, binMiss, Nat.le_refl, ↓reduceIte, Nat.mul_zero,
      Nat.zero_add]
    rw [ofFn_sum_eq _ _ (fun e => chargedPrefix_terminal step count
      (step x e) (he e) T), ofFn_sum_const]
    simp
  · have hactive : ¬ count x ≤ 1 := by have := hpos x hx; omega
    simp only [binMiss, if_neg hactive, Nat.mul_one]
    unfold chargedPrefixNumerator
    simp only [haltAt, if_neg hterminal, FixedSpanRenewalPayload.erasePayload,
      truncatedActiveCostNumerator]
    rfl

/-- Exact denominator-aware cut at an arbitrary full raw prefix. The suffix
sum uses the actual endpoint of each prefix, also after skipped levels. -/
theorem chargedPrefix_horizon_add {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e)) (count : S → Nat)
    (hpos : ∀ x, P x → 1 ≤ count x)
    (hstep : ∀ x e, P x → count (step x e) ≤ count x) :
    ∀ h u x, P x →
      chargedPrefixNumerator step count x (h + u) =
        n ^ u * chargedPrefixNumerator step count x h +
          wordSum step (fun y => chargedPrefixNumerator step count y u) x h := by
  intro h
  induction h with
  | zero => intro u x hx; simp
  | succ h ih =>
      intro u x hx
      rw [Nat.succ_add,
        chargedPrefix_succ_on step P hclosed count hpos hstep x hx,
        chargedPrefix_succ_on step P hclosed count hpos hstep x hx,
        wordSum_succ]
      rw [ofFn_sum_eq _ _ (fun e => ih u (step x e) (hclosed x e hx)),
        ofFn_sum_add, ofFn_sum_mul_left]
      simp only [Nat.mul_add, Nat.pow_succ, Nat.pow_add]
      ac_rfl

/-- Sum of level horizons over exactly levels `3,...,k`; a ghost tariff. -/
def levelSum (H : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => levelSum H k + if 3 ≤ k + 1 then H (k + 1) else 0

/-- Reserve zero at counts zero and one; count two has only the final tariff. -/
def levelReserve (H : Nat → Nat) (Q Q2 H2 k : Nat) : Nat :=
  Q * levelSum H k + if 2 ≤ k then Q2 * H2 else 0

/-- The current full raw horizon: the two-leader horizon or the higher-level one. -/
def blockHorizon (H : Nat → Nat) (H2 k : Nat) : Nat :=
  if k = 2 then H2 else H k

/-- Reciprocal mass tariff at the actual current count. -/
def blockTariff (Q Q2 k : Nat) : Nat := if k = 2 then Q2 else Q

@[simp] theorem levelReserve_zero (H : Nat → Nat) (Q Q2 H2 : Nat) :
    levelReserve H Q Q2 H2 0 = 0 := by simp [levelReserve, levelSum]

@[simp] theorem levelReserve_one (H : Nat → Nat) (Q Q2 H2 : Nat) :
    levelReserve H Q Q2 H2 1 = 0 := by simp [levelReserve, levelSum]

@[simp] theorem levelReserve_two (H : Nat → Nat) (Q Q2 H2 : Nat) :
    levelReserve H Q Q2 H2 2 = Q2 * H2 := by simp [levelReserve, levelSum]

theorem levelSum_mono (H : Nat → Nat) {i j : Nat} (hij : i ≤ j) :
    levelSum H i ≤ levelSum H j := by
  induction j generalizing i with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact Nat.le_refl _
  | succ j ih =>
      by_cases h : i ≤ j
      · exact Nat.le_trans (ih h) (by rw [levelSum]; omega)
      · have : i = j + 1 := by omega
        subst i; exact Nat.le_refl _

theorem levelReserve_mono (H : Nat → Nat) (Q Q2 H2 : Nat)
    {i j : Nat} (hij : i ≤ j) :
    levelReserve H Q Q2 H2 i ≤ levelReserve H Q Q2 H2 j := by
  have hsum := Nat.mul_le_mul_left Q (levelSum_mono H hij)
  unfold levelReserve
  by_cases hi : 2 ≤ i
  · have hj : 2 ≤ j := by omega
    simp only [if_pos hi, if_pos hj]
    omega
  · simp only [if_neg hi, Nat.add_zero]
    exact Nat.le_trans hsum (Nat.le_add_right _ _)

theorem levelReserve_succ (H : Nat → Nat) (Q Q2 H2 k : Nat)
    (hk : 2 ≤ k) :
    levelReserve H Q Q2 H2 (k + 1) =
      Q * H (k + 1) + levelReserve H Q Q2 H2 k := by
  have hk' : 2 ≤ k + 1 := by omega
  have hk'' : 3 ≤ k + 1 := by omega
  simp only [levelReserve, levelSum, if_pos hk, if_pos hk', if_pos hk'',
    Nat.mul_add]
  ac_rfl

/-- Every strict count drop pays the whole current level tariff, including
multi-level drops. No merge rank or renewable credit is used. -/
theorem strict_drop_charge (H : Nat → Nat) (Q Q2 H2 k l : Nat)
    (hk : 2 ≤ k) (hlk : l < k) :
    blockTariff Q Q2 k * blockHorizon H H2 k +
        levelReserve H Q Q2 H2 l ≤ levelReserve H Q Q2 H2 k := by
  by_cases htwo : k = 2
  · subst k
    have hl : l = 0 ∨ l = 1 := by omega
    rcases hl with rfl | rfl <;>
      simp [blockTariff, blockHorizon]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hm : 2 ≤ m := by omega
    have hlm : l ≤ m := by omega
    have hmono := levelReserve_mono H Q Q2 H2 hlm
    rw [levelReserve_succ H Q Q2 H2 m hm]
    simp only [blockTariff, blockHorizon, if_neg htwo]
    exact Nat.add_le_add_left hmono _

theorem horizon_le_reserve (H : Nat → Nat) (Q Q2 H2 k : Nat)
    (hQ : 1 ≤ Q) (hQ2 : 1 ≤ Q2) (hk : 2 ≤ k) :
    blockHorizon H H2 k ≤ levelReserve H Q Q2 H2 k := by
  have h := strict_drop_charge H Q Q2 H2 k 0 hk (by omega)
  simp only [levelReserve_zero, Nat.add_zero] at h
  have hq : 1 ≤ blockTariff Q Q2 k := by
    unfold blockTariff; split <;> assumption
  have hle : blockHorizon H H2 k ≤
      blockTariff Q Q2 k * blockHorizon H H2 k := by
    simpa using Nat.mul_le_mul_right (blockHorizon H H2 k) hq
  exact Nat.le_trans hle h

/-- The recursive tariff is precisely the finite sum over levels `3,...,k`. -/
theorem levelSum_eq_sum_range (H : Nat → Nat) (k : Nat) :
    levelSum H k =
      ((List.range (k + 1)).map (fun j => if 3 ≤ j then H j else 0)).sum := by
  induction k with
  | zero => simp [levelSum]
  | succ k ih =>
      rw [levelSum, List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero, ih]

/-- Positive strict-deletion mass rules out a zero block horizon by itself. -/
theorem block_horizon_pos_of_mass {S : Type} {n : Nat}
    (step : S → Fin n → S) (count : S → Nat) (x : S) (q h : Nat)
    (hmass : n ^ h ≤ q * wordSum step
      (fun y => if count y < count x then 1 else 0) x h) : 0 < h := by
  by_cases hzero : h = 0
  · simp [hzero] at hmass
  · omega

/-- Actual full-block residual. The reserve is compared only after the
complete, count-dependent horizon, and its endpoint is the raw physical state.
The block cost includes every unfinished active prefix within that horizon. -/
theorem full_block_residual {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e)) (count : S → Nat)
    (hstep : ∀ x e, P x → count (step x e) ≤ count x)
    (H : Nat → Nat) (Q Q2 H2 : Nat) (x : S) (hx : P x)
    (hk : 2 ≤ count x)
    (hmass : n ^ blockHorizon H H2 (count x) ≤
      blockTariff Q Q2 (count x) * wordSum step
        (fun y => if count y < count x then 1 else 0) x
        (blockHorizon H H2 (count x))) :
    chargedPrefixNumerator step count x (blockHorizon H H2 (count x)) +
        wordSum step (fun y => levelReserve H Q Q2 H2 (count y)) x
          (blockHorizon H H2 (count x)) ≤
      n ^ blockHorizon H H2 (count x) * levelReserve H Q Q2 H2 (count x) := by
  let h := blockHorizon H H2 (count x)
  let q := blockTariff Q Q2 (count x)
  let V := fun y => levelReserve H Q Q2 H2 (count y)
  let drop := fun y => if count y < count x then 1 else 0
  have hbounded : ∀ y e, P y ∧ count y ≤ count x →
      P (step y e) ∧ count (step y e) ≤ count x := by
    intro y e hy
    exact ⟨hclosed y e hy.1, Nat.le_trans (hstep y e hy.1) hy.2⟩
  have hrow : ∀ y, P y ∧ count y ≤ count x →
      (q * h) * drop y + V y ≤ V x := by
    intro y hy
    by_cases hd : count y < count x
    · simpa [q, h, V, drop, hd] using
        strict_drop_charge H Q Q2 H2 (count x) (count y) hk hd
    · have he : count y = count x := by omega
      simp [V, drop, he]
  have hres := wordSum_mono_on step (fun y => P y ∧ count y ≤ count x)
    hbounded (fun y => (q * h) * drop y + V y) (fun _ => V x)
    hrow h x ⟨hx, Nat.le_refl _⟩
  rw [wordSum_add, wordSum_mul, wordSum_const] at hres
  have hpay : n ^ h * h ≤ (q * h) * wordSum step drop x h := by
    have hm := Nat.mul_le_mul_right h hmass
    simpa only [h, q, drop, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm
  exact Nat.le_trans
    (Nat.add_le_add_right (Nat.le_trans
      (chargedPrefix_le_horizon step count x h) hpay) _) hres

/-- Finite strong induction on the raw horizon. Every block restarts at its
actual endpoint. A prefix shorter than its current block is charged at its
actual length; no future closure or independent-trial premise is present. -/
theorem chargedPrefix_le_reserve_on_closed_domain {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e)) (count : S → Nat)
    (hpos : ∀ x, P x → 1 ≤ count x)
    (hstep : ∀ x e, P x → count (step x e) ≤ count x)
    (H : Nat → Nat) (Q Q2 H2 : Nat) (hQ : 1 ≤ Q) (hQ2 : 1 ≤ Q2)
    (hmass : ∀ x, P x → 3 ≤ count x → n ^ H (count x) ≤
      Q * wordSum step (fun y => if count y < count x then 1 else 0) x (H (count x)))
    (htwo : ∀ x, P x → count x = 2 → n ^ H2 ≤
      Q2 * wordSum step (fun y => if count y < count x then 1 else 0) x H2) :
    ∀ T x, P x → chargedPrefixNumerator step count x T ≤
      n ^ T * levelReserve H Q Q2 H2 (count x) := by
  intro T
  induction T using Nat.strongRecOn with
  | ind T ih =>
      intro x hx
      by_cases hterminal : count x = 1
      · rw [chargedPrefix_terminal step count x hterminal T]
        exact Nat.zero_le _
      · have hk : 2 ≤ count x := by have := hpos x hx; omega
        let h := blockHorizon H H2 (count x)
        let q := blockTariff Q Q2 (count x)
        let V := fun y => levelReserve H Q Q2 H2 (count y)
        have hm : n ^ h ≤ q * wordSum step
            (fun y => if count y < count x then 1 else 0) x h := by
          by_cases htwo' : count x = 2
          · simpa [h, q, blockHorizon, blockTariff, htwo'] using htwo x hx htwo'
          · simpa [h, q, blockHorizon, blockTariff, htwo'] using
              hmass x hx (by omega)
        have hp : 0 < h := block_horizon_pos_of_mass step count x q h hm
        by_cases hshort : T < h
        · exact Nat.le_trans (chargedPrefix_le_horizon step count x T)
            (Nat.mul_le_mul_left _ (Nat.le_trans (Nat.le_of_lt hshort)
              (horizon_le_reserve H Q Q2 H2 (count x) hQ hQ2 hk)))
        · have hle : h ≤ T := by omega
          have hsplit : T = h + (T - h) := by omega
          have hu : T - h < T := by omega
          have hsuffix :
              wordSum step (fun y => chargedPrefixNumerator step count y (T - h)) x h ≤
                n ^ (T - h) * wordSum step V x h := by
            rw [← wordSum_mul]
            exact wordSum_mono_on step P hclosed _ _
              (fun y hy => ih (T - h) hu y hy) h x hx
          have hres := full_block_residual step P hclosed count hstep
            H Q Q2 H2 x hx hk hm
          calc
            chargedPrefixNumerator step count x T =
                n ^ (T - h) * chargedPrefixNumerator step count x h +
                  wordSum step (fun y => chargedPrefixNumerator step count y (T - h)) x h := by
              exact (congrArg (chargedPrefixNumerator step count x) hsplit).trans
                (chargedPrefix_horizon_add step P hclosed count hpos hstep h (T - h) x hx)
            _ ≤ n ^ (T - h) *
                (chargedPrefixNumerator step count x h + wordSum step V x h) := by
              rw [Nat.mul_add]
              exact Nat.add_le_add_left hsuffix _
            _ ≤ n ^ (T - h) * (n ^ h * V x) := Nat.mul_le_mul_left _ hres
            _ = n ^ (h + (T - h)) * V x := by
              rw [Nat.pow_add]
              ac_rfl
            _ = n ^ T * V x := by rw [← hsplit]

/-- Exact finite expected-cost numerator, with the cumulative level tariff.
The result is conditional on physical closure, positive nonincreasing count,
and uniform actual block mass; it is not a producer of those properties. -/
theorem chargedPrefix_le_level_tariff {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e)) (count : S → Nat)
    (hpos : ∀ x, P x → 1 ≤ count x)
    (hstep : ∀ x e, P x → count (step x e) ≤ count x)
    (H : Nat → Nat) (Q Q2 H2 : Nat) (hQ : 1 ≤ Q) (hQ2 : 1 ≤ Q2)
    (hmass : ∀ x, P x → 3 ≤ count x → n ^ H (count x) ≤
      Q * wordSum step (fun y => if count y < count x then 1 else 0) x (H (count x)))
    (htwo : ∀ x, P x → count x = 2 → n ^ H2 ≤
      Q2 * wordSum step (fun y => if count y < count x then 1 else 0) x H2)
    (T : Nat) (x : S) (hx : P x) :
    chargedPrefixNumerator step count x T ≤
      n ^ T * (Q * levelSum H (count x) + Q2 * H2) := by
  apply Nat.le_trans (chargedPrefix_le_reserve_on_closed_domain step P hclosed
    count hpos hstep H Q Q2 H2 hQ hQ2 hmass htwo T x hx)
  apply Nat.mul_le_mul_left
  unfold levelReserve
  split <;> omega

/-- The logarithmic factor in the existing final-tail interface is at least
two. The integer numerator argument does not need a ring-size lower bound. -/
theorem two_le_final_factor (n : Nat) : 2 ≤ 2 ^ logSlack n := by
  have h : 1 ≤ logSlack n := by unfold logSlack; omega
  simpa using Nat.pow_le_pow_right (by decide : 0 < 2) h

/-- The existing final-tail premise supplies `Q2=2`, `H2=F`. At an actual
two-leader start, strict-drop and surviving-bad word counts partition `n^F`.
All endpoint comparisons are derived on the closed nonincreasing domain. -/
theorem two_leader_mass_of_final_tail {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e)) (count : S → Nat)
    (hstep : ∀ x e, P x → count (step x e) ≤ count x) (F : Nat)
    (hfinal : ∀ x, P x → count x ≤ 2 →
      2 ^ logSlack n * wordSum step (fun y => binMiss 1 (count y)) x F ≤ n ^ F)
    (x : S) (hx : P x) (htwo : count x = 2) :
    n ^ F ≤ 2 * wordSum step
      (fun y => if count y < count x then 1 else 0) x F := by
  let drop := fun y => if count y < 2 then 1 else 0
  let bad := fun y => binMiss 1 (count y)
  have hbounded : ∀ y e, P y ∧ count y ≤ 2 →
      P (step y e) ∧ count (step y e) ≤ 2 := by
    intro y e hy
    exact ⟨hclosed y e hy.1, Nat.le_trans (hstep y e hy.1) hy.2⟩
  have hpartition : ∀ y, P y ∧ count y ≤ 2 → drop y + bad y = 1 := by
    intro y hy
    unfold drop bad binMiss
    split <;> split <;> omega
  have hupper := wordSum_mono_on step (fun y => P y ∧ count y ≤ 2)
    hbounded (fun y => drop y + bad y) (fun _ => 1)
    (fun y hy => Nat.le_of_eq (hpartition y hy)) F x ⟨hx, by omega⟩
  have hlower := wordSum_mono_on step (fun y => P y ∧ count y ≤ 2)
    hbounded (fun _ => 1) (fun y => drop y + bad y)
    (fun y hy => Nat.le_of_eq (hpartition y hy).symm) F x ⟨hx, by omega⟩
  have heq := Nat.le_antisymm hupper hlower
  rw [wordSum_add, wordSum_const, Nat.mul_one] at heq
  have hbad : 2 * wordSum step bad x F ≤ n ^ F :=
    Nat.le_trans (Nat.mul_le_mul_right _ (two_le_final_factor n))
      (hfinal x hx (by omega))
  rw [htwo]
  change n ^ F ≤ 2 * wordSum step drop x F
  omega

/-- Expected-cost companion to `leader_count_whp_on_closed_domain`, using
its actual final-tail signature to derive the entire two-leader tariff. -/
theorem chargedPrefix_le_tariff_from_final_tail {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e)) (count : S → Nat)
    (hpos : ∀ x, P x → 1 ≤ count x)
    (hstep : ∀ x e, P x → count (step x e) ≤ count x)
    (H : Nat → Nat) (Q F : Nat) (hQ : 1 ≤ Q)
    (hmass : ∀ x, P x → 3 ≤ count x → n ^ H (count x) ≤
      Q * wordSum step (fun y => if count y < count x then 1 else 0) x (H (count x)))
    (hfinal : ∀ x, P x → count x ≤ 2 →
      2 ^ logSlack n * wordSum step (fun y => binMiss 1 (count y)) x F ≤ n ^ F)
    (T : Nat) (x : S) (hx : P x) :
    chargedPrefixNumerator step count x T ≤
      n ^ T * (Q * levelSum H (count x) + 2 * F) :=
  chargedPrefix_le_level_tariff step P hclosed count hpos hstep
    H Q 2 F hQ (by decide) hmass
    (two_leader_mass_of_final_tail step P hclosed count hstep F hfinal) T x hx

/-- With the physical initial count at most `n`, the tariff is bounded by
the explicit sum over ring levels `3,...,n`, at every finite raw horizon. -/
theorem chargedPrefix_le_ring_tariff_from_final_tail {S : Type} {n : Nat}
    (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e)) (count : S → Nat)
    (hpos : ∀ x, P x → 1 ≤ count x)
    (hstep : ∀ x e, P x → count (step x e) ≤ count x)
    (H : Nat → Nat) (Q F : Nat) (hQ : 1 ≤ Q)
    (hmass : ∀ x, P x → 3 ≤ count x → n ^ H (count x) ≤
      Q * wordSum step (fun y => if count y < count x then 1 else 0) x (H (count x)))
    (hfinal : ∀ x, P x → count x ≤ 2 →
      2 ^ logSlack n * wordSum step (fun y => binMiss 1 (count y)) x F ≤ n ^ F)
    (T : Nat) (x : S) (hx : P x) (hcount : count x ≤ n) :
    chargedPrefixNumerator step count x T ≤
      n ^ T * (Q *
        ((List.range (n + 1)).map (fun k => if 3 ≤ k then H k else 0)).sum + 2 * F) := by
  rw [← levelSum_eq_sum_range]
  exact Nat.le_trans (chargedPrefix_le_tariff_from_final_tail step P hclosed
    count hpos hstep H Q F hQ hmass hfinal T x hx)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (levelSum_mono H hcount)) _))

/-! A finite scheduler example. These rows test the consumer; they are not
an implementation of K2. The count is positive, progress skips levels, every
interaction changes a control bit, and retries remain possible indefinitely. -/

abbrev DelayedState := Fin 4 × Bool

def delayedCount (x : DelayedState) : Nat := x.1.val + 1

/-- A false control bit must first become true. Only edge zero at a true bit
deletes, jumping directly to count one; all other edges retain the count. -/
def delayedStep (x : DelayedState) (e : Fin 4) : DelayedState :=
  if x.2 then (if e.val = 0 then (0, false) else (x.1, false)) else (x.1, true)

def delayedStart : DelayedState := (3, false)

theorem delayed_count_positive (x : DelayedState) : 1 ≤ delayedCount x := by
  unfold delayedCount
  omega

theorem delayed_count_nonincreasing (x : DelayedState) (e : Fin 4) :
    delayedCount (delayedStep x e) ≤ delayedCount x := by
  unfold delayedStep
  split
  · split <;> simp [delayedCount]
  · exact Nat.le_refl _

/-- Four of sixteen literal length-two words strictly delete, at either
control bit and every nonterminal count. This mass is derived from the rows. -/
theorem delayed_drop_mass (x : DelayedState) (hx : 2 ≤ delayedCount x) :
    wordSum delayedStep
      (fun y => if delayedCount y < delayedCount x then 1 else 0) x 2 = 4 := by
  rcases x with ⟨k, b⟩
  change 2 ≤ k.val + 1 at hx
  have hd : 0 < k.val := by omega
  cases b <;> simp [wordSum_succ, List.ofFn_succ, delayedStep, delayedCount, hd]

/-- The higher levels use different full horizons, `H(k)=k`. Padding uses
the same real rows and count monotonicity, without resampling an entrance. -/
theorem delayed_level_mass (x : DelayedState) (hx : 3 ≤ delayedCount x) :
    4 ^ delayedCount x ≤ 4 * wordSum delayedStep
      (fun y => if delayedCount y < delayedCount x then 1 else 0) x (delayedCount x) := by
  apply pad_deletion_mass delayedStep delayedCount delayed_count_nonincreasing
    x 4 2 (delayedCount x) (by omega)
  rw [delayed_drop_mass x (by omega)]
  decide

/-- Fully discharged example, all horizons: `Q=Q2=4`, `H(k)=k`, `H2=2`,
initial count four, hence tariff `4*(3+4)+4*2=36`. -/
theorem delayed_all_horizons (T : Nat) :
    chargedPrefixNumerator delayedStep delayedCount delayedStart T ≤ 4 ^ T * 36 := by
  have h := chargedPrefix_le_level_tariff delayedStep (fun _ => True)
    (fun _ _ _ => True.intro) delayedCount (fun x _ => delayed_count_positive x)
    (fun x e _ => delayed_count_nonincreasing x e) (fun k => k) 4 4 2
    (by decide) (by decide) (fun x _ hx => delayed_level_mass x hx)
    (fun x _ hx => by rw [delayed_drop_mass x (by omega)]; decide)
    T delayedStart True.intro
  exact h

/-- Concrete unfinished prefixes at the initial horizon-four block. -/
theorem delayed_partial_prefix_costs :
    chargedPrefixNumerator delayedStep delayedCount delayedStart 1 = 4 ∧
    chargedPrefixNumerator delayedStep delayedCount delayedStart 3 = 176 := by
  decide

/-- The actual example can skip directly from four leaders to one. -/
theorem delayed_skip_levels :
    delayedCount delayedStart = 4 ∧
    delayedCount (delayedStep (delayedStep delayedStart 1) 0) = 1 := by
  decide

/-- This reserve fails the naive raw one-step Bellman row: the first
interaction always incurs cost and leaves the count (thus reserve) unchanged. -/
theorem delayed_one_step_reserve_fails :
    ¬ chargedPrefixNumerator delayedStep delayedCount delayedStart 1 +
        wordSum delayedStep (fun y => levelReserve (fun k => k) 4 4 2
          (delayedCount y)) delayedStart 1 ≤
      4 * levelReserve (fun k => k) 4 4 2 (delayedCount delayedStart) := by
  decide

/-- Edge one supplies an actual surviving word at every finite horizon. -/
theorem delayed_miss_positive : ∀ T x, 2 ≤ delayedCount x →
    1 ≤ wordSum delayedStep (fun y => binMiss 1 (delayedCount y)) x T := by
  intro T
  induction T with
  | zero =>
      intro x hx
      have h : ¬ delayedCount x ≤ 1 := by omega
      simp [binMiss, h]
  | succ T ih =>
      intro x hx
      have hkeep : delayedCount (delayedStep x (1 : Fin 4)) = delayedCount x := by
        rcases x with ⟨k, b⟩
        cases b <;> simp [delayedStep, delayedCount]
      have hh := ih (delayedStep x (1 : Fin 4)) (by omega)
      simp only [wordSum_succ, List.ofFn_succ, List.ofFn_zero,
        List.sum_cons, List.sum_nil]
      simp only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl]
      omega

/-- The already-checked dyadic example discharges the final-tail consumer too:
`H(k)=1`, `Q=4`, `F=64`, hence `4*(1+1)+2*64=136` from four leaders. -/
theorem existing_toy_final_tail_cost (T : Nat) :
    chargedPrefixNumerator toyStep toyCount (3, false) T ≤ 4 ^ T * 136 := by
  have h := chargedPrefix_le_tariff_from_final_tail toyStep (fun _ => True)
    (fun _ _ _ => True.intro) toyCount (fun x _ => by unfold toyCount; omega)
    (fun x e _ => toy_count_nonincreasing x e) (fun _ => 1) 4 64 (by decide)
    (fun x _ hx => by rw [toy_drop_mass x (by omega)]; decide)
    (fun x _ hx => toy_final_tail x hx) T (3, false) True.intro
  exact h

end LeaderCountExpectedCost
