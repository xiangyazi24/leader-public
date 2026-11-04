import Leader.L3.Bank.RepairDigitCohortTail
import Leader.L3.Bank.RepairDigitLedger

/-!
# R10c entry: the simultaneous block clock (Lemma e-max, repair.tex 4195-4239)

Research notes: research/lean-l3/ledgers/R10c-worker-notes.md.

`StructuralCut → EntryCut 0` is not a zero-cost inclusion: `EntryCut 0` asks every
interior writer pair for a pinned window (`WinInvD ∧ UseReach`), entered from a packed settled
cohort (`winInvDEntry`'s `CohortSettling R 0`), while the structural cut only records first
strict receipts.  The entry is a separately charged stage, and its cost must be the cost of
the LAST pair, not the sum over the `K ≈ n / R` pairs: the sum `K · 32 n R ≈ 32 n²` does not fit
the 201 budget.

This module proves the simultaneous clock on the literal uniform scheduler words, with no
independence assumption (all pairs read the same letters):

* `entryMissAll`, `entryWordSumOfFn`: the miss of "every pair done" is at most the sum of the
  per-pair misses (union bound inside one block).
* `entrySimultaneousCost`: on a closed class, if each persistent per-pair goal misses a block of
  `M` letters with mass at most `1 / (4K)`, all `K` goals are met at expected cost
  `renewalCeiling M 1 4` (block restart, `costNumerator_of_block`).
* `entryTailBlock`: a per-pair dyadic tail `2^M miss ≤ (2n-1)^M Φ` with `Φ ≤ W` and
  `4 K W ≤ 2^q` gives the `1 / (4K)` miss at `M = 2 n q`.
* `entryGridsCharge`: `K` real pairs each dominating a clean `r × r` grid
  (`gridDominationMiss`) are all done at doubled cost `6 n (5 r + 2 + k)` with `K ≤ 2^k`:
  the `log K` of Lemma e-max is the `k`, paid once, not `K` times.
-/

namespace L3.DigitEntryClose

set_option autoImplicit false

open L3.CohortTail
open FiniteUniformStoppingTree
open LeaderCountDyadicTail
open K2ArbitraryElimination.FiniteAccounting

/-! ### Finite sums -/

/-- Consumer: `entryMissAll`. -/
theorem entryTermLe : ∀ {m : Nat} (f : Fin m → Nat) (i : Fin m), f i ≤ (List.ofFn f).sum
  | 0, _, i => i.elim0
  | _ + 1, f, i => by
      rw [List.ofFn_succ, List.sum_cons]
      cases i using Fin.cases with
      | zero => exact Nat.le_add_right _ _
      | succ k =>
          have := entryTermLe (fun j => f j.succ) k
          omega

/-- Consumer: `entrySimultaneousCost`. -/
theorem entrySumLe : ∀ {m : Nat} (f : Fin m → Nat) (B : Nat),
    (∀ i, f i ≤ B) → (List.ofFn f).sum ≤ m * B
  | 0, _, _, _ => by simp
  | m + 1, f, B, h => by
      rw [List.ofFn_succ, List.sum_cons, Nat.succ_mul]
      have h1 := entrySumLe (fun i => f i.succ) B (fun i => h i.succ)
      have h2 := h 0
      omega

/-! ### The union bound inside one block -/

/-- The miss of "every goal met" is at most the number of missed goals.
Consumer: `entrySimultaneousCost`. -/
theorem entryMissAll {S : Type} {K : Nat} (Good : Fin K → S → Prop) (x : S) :
    miss (fun y => ∀ i, Good i y) x ≤ (List.ofFn fun i => miss (Good i) x).sum := by
  classical
  by_cases h : ∀ i, Good i x
  · unfold miss
    rw [if_pos h]
    exact Nat.zero_le _
  · have hex : ∃ i, ¬ Good i x := Classical.byContradiction fun hno =>
      h fun i => Classical.byContradiction fun hi => hno ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    have h1 : miss (fun y => ∀ i, Good i y) x ≤ 1 := miss_le_one _ x
    have h2 : miss (Good i) x = 1 := by
      unfold miss
      rw [if_neg hi]
    have h3 := entryTermLe (fun j => miss (Good j) x) i
    omega

/-- Word sums of a finite sum of weights.  Consumer: `entrySimultaneousCost`. -/
theorem entryWordSumOfFn {S : Type} {n : Nat} (step : S → Fin n → S) :
    ∀ {K : Nat} (w : Fin K → S → Nat) (x : S) (T : Nat),
      wordSum step (fun y => (List.ofFn fun i => w i y).sum) x T =
        (List.ofFn fun i => wordSum step (w i) x T).sum
  | 0, w, x, T => by
      have h := wordSum_const step 0 x T
      simp only [List.ofFn_zero, List.sum_nil, Nat.mul_zero] at h ⊢
      exact h
  | K + 1, w, x, T => by
      have hf : (fun y => (List.ofFn fun i : Fin (K + 1) => w i y).sum) =
          fun y => w 0 y + (List.ofFn fun i : Fin K => w i.succ y).sum := by
        funext y
        rw [List.ofFn_succ, List.sum_cons]
      rw [hf, wordSum_add, entryWordSumOfFn step (fun i => w i.succ) x T,
        List.ofFn_succ, List.sum_cons]

/-! ### The simultaneous block clock -/

/-- Lemma e-max on a closed class: persistent per-pair goals, each missing a block of `M`
letters with mass at most `1 / (4K)`, are all met at expected cost `renewalCeiling M 1 4`.
Consumer: `entryGridsCharge`. -/
theorem entrySimultaneousCost {S : Type} {n K : Nat} (next : S → Fin n → S)
    (P : S → Prop) (Good : Fin K → S → Prop) (M : Nat) (hM : 0 < M) (hK : 0 < K)
    (hcl : ∀ x e, P x → P (next x e))
    (hc : ∀ i x e, Good i x → Good i (next x e))
    (hb : ∀ i x, P x → 4 * K * wordSum next (miss (Good i)) x M ≤ n ^ M) :
    ∀ x, P x → ∀ T,
      costNumerator next (fun y => ∀ i, Good i y) x T ≤
        n ^ T * L3.Prob.renewalCeiling M 1 4 := by
  intro x hx T
  have hall : ∀ y, P y →
      4 * wordSum next (miss (fun y => ∀ i, Good i y)) y M ≤ 1 * n ^ M := by
    intro y hy
    have hmono := wordSum_mono_on next (fun _ => True) (fun _ _ _ => True.intro)
      (miss (fun y => ∀ i, Good i y))
      (fun y => (List.ofFn fun i => miss (Good i) y).sum)
      (fun y _ => entryMissAll Good y) M y True.intro
    rw [entryWordSumOfFn] at hmono
    have hsum : K * (4 * (List.ofFn fun i => wordSum next (miss (Good i)) y M).sum) ≤
        K * n ^ M := by
      have h1 : K * (4 * (List.ofFn fun i => wordSum next (miss (Good i)) y M).sum) =
          (List.ofFn fun i => 4 * K * wordSum next (miss (Good i)) y M).sum := by
        rw [ofFn_sum_mul_left]
        ac_rfl
      rw [h1]
      exact entrySumLe _ _ (fun i => hb i y hy)
    have h2 := Nat.le_of_mul_le_mul_left hsum hK
    omega
  have h := L3.Density.costNumerator_of_block (classNext next P hcl)
    (fun y => ∀ i, Good i y.1) M 1 4 hM (by decide)
    (fun y e hy i => hc i y.1 e (hy i))
    (fun y => by
      have hm := classMiss next P (fun y => ∀ i, Good i y) hcl M y
      rw [hm]
      exact hall y.1 y.2) ⟨x, hx⟩ T
  have hcost := classCost next P (fun y => ∀ i, Good i y) hcl T ⟨x, hx⟩
  rw [hcost] at h
  exact h

/-- A per-pair dyadic tail at `M = 2 n q` with potential at most `W` and `4 K W ≤ 2^q`
gives a miss of at most `1 / (4K)`.  Consumer: `entryGridsCharge`. -/
theorem entryTailBlock {n K q W Φ miss : Nat} (hn : 0 < n)
    (htail : 2 ^ (2 * n * q) * miss ≤ (2 * n - 1) ^ (2 * n * q) * Φ)
    (hΦ : Φ ≤ W) (hq : 4 * K * W ≤ 2 ^ q) :
    4 * K * miss ≤ n ^ (2 * n * q) := by
  have hh := halfLifePow n q hn
  have h2n : (2 * n) ^ (2 * n * q) = 2 ^ (2 * n * q) * n ^ (2 * n * q) := Nat.mul_pow _ _ _
  rw [h2n] at hh
  have hA : 0 < 2 ^ (2 * n * q) := Nat.two_pow_pos _
  generalize 2 ^ (2 * n * q) = A at htail hh hA
  generalize n ^ (2 * n * q) = N at hh ⊢
  generalize (2 * n - 1) ^ (2 * n * q) = D at htail hh
  have hX : A * (2 ^ q * miss) ≤ A * (N * W) :=
    calc
      A * (2 ^ q * miss) = 2 ^ q * (A * miss) := Nat.mul_left_comm _ _ _
      _ ≤ 2 ^ q * (D * Φ) := Nat.mul_le_mul_left _ htail
      _ = (2 ^ q * D) * Φ := (Nat.mul_assoc _ _ _).symm
      _ ≤ (A * N) * Φ := Nat.mul_le_mul_right _ hh
      _ ≤ (A * N) * W := Nat.mul_le_mul_left _ hΦ
      _ = A * (N * W) := Nat.mul_assoc _ _ _
  have hY := Nat.le_of_mul_le_mul_left hX hA
  by_cases hW : W = 0
  · subst hW
    have hm : 2 ^ q * miss = 0 := by simpa using hY
    have hpos : 0 < 2 ^ q := Nat.two_pow_pos _
    have : miss = 0 := by
      rcases Nat.mul_eq_zero.mp hm with h | h
      · omega
      · exact h
    subst this
    simp
  · have hWpos : 0 < W := Nat.pos_of_ne_zero hW
    have hZ : W * (4 * K * miss) ≤ W * N :=
      calc
        W * (4 * K * miss) = (4 * K * W) * miss := by ac_rfl
        _ ≤ 2 ^ q * miss := Nat.mul_le_mul_right _ hq
        _ ≤ N * W := hY
        _ = W * N := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left hZ hWpos

/-- The doubled block ceiling at `M = 2 n q` is at most `6 n q`.
Consumer: `entryGridsCharge`. -/
theorem entryCeilingLe (n q : Nat) (hnq : 3 ≤ n * q) :
    2 * L3.Prob.renewalCeiling (2 * n * q) 1 4 ≤ 6 * n * q := by
  unfold L3.Prob.renewalCeiling L3.Prob.ceilNat
  have h1 : 2 * n * q * 4 = 8 * (n * q) := by ac_rfl
  have h2 : 6 * n * q = 6 * (n * q) := by ac_rfl
  rw [h1, h2]
  generalize n * q = m at hnq ⊢
  have : (4 : Nat) - 1 = 3 := rfl
  rw [this]
  split <;> omega

/-! ### K real pairs over clean grids -/

/-- Lemma e-max for `K` real pairs, each dominating a clean `r × r` grid on its own closed
class (`gridDominationMiss`): all `K` persistent goals are met at doubled cost
`6 n (5 r + 2 + k)` once `K ≤ 2^k`.  A single pair (`gridDominationCharge`) costs `32 n r`;
here the `K` pairs together cost `30 n r + 6 n (k + 2)`, with no independence assumption.
Consumer: the R10c entry stage (`EntryCut 0` from the structural cut, BlockEntry). -/
theorem entryGridsCharge {S : Type} {n K : Nat} (next : S → Fin n → S)
    (P Good : Fin K → S → Prop) (r k : Nat) (hn : 0 < n) (hr : 0 < r) (hK : 0 < K)
    (hk : K ≤ 2 ^ k) (letter : Fin K → Nat → Nat → Fin n)
    (proj : Fin K → S → Nat → Nat)
    (hcl : ∀ i x e, P i x → P i (next x e))
    (hc : ∀ i x e, Good i x → Good i (next x e))
    (hdom : ∀ i x e, P i x → ¬ Good i x →
      rowsLe r (gridStep r (letter i) (proj i x) e) (proj i (next x e)))
    (hgood : ∀ i x, P i x → gridDone r r (proj i x) → Good i x) :
    ∀ x, (∀ i, P i x) → ∀ T,
      2 * costNumerator next (fun y => ∀ i, Good i y) x T ≤
        n ^ T * (6 * n * (5 * r + 2 + k)) := by
  intro x hx T
  have hq : 4 * K * (r * 2 ^ (4 * r)) ≤ 2 ^ (5 * r + 2 + k) := by
    have hr2 : r ≤ 2 ^ r := Nat.le_of_lt Nat.lt_two_pow_self
    have he : 2 ^ (5 * r + 2 + k) = 4 * 2 ^ k * (2 ^ r * 2 ^ (4 * r)) := by
      rw [show 5 * r + 2 + k = 2 + k + (r + 4 * r) by omega, Nat.pow_add, Nat.pow_add,
        Nat.pow_add]
    rw [he]
    have h1 : K * (r * 2 ^ (4 * r)) ≤ 2 ^ k * (2 ^ r * 2 ^ (4 * r)) :=
      Nat.mul_le_mul hk (Nat.mul_le_mul_right _ hr2)
    calc 4 * K * (r * 2 ^ (4 * r)) = 4 * (K * (r * 2 ^ (4 * r))) := by ac_rfl
      _ ≤ 4 * (2 ^ k * (2 ^ r * 2 ^ (4 * r))) := Nat.mul_le_mul_left 4 h1
      _ = 4 * 2 ^ k * (2 ^ r * 2 ^ (4 * r)) := by ac_rfl
  have hb : ∀ i y, (∀ j, P j y) →
      4 * K * wordSum next (miss (Good i)) y (2 * n * (5 * r + 2 + k)) ≤
        n ^ (2 * n * (5 * r + 2 + k)) := by
    intro i y hy
    have hdm := gridDominationMiss next (P i) (Good i) (hcl i) (hc i) r r (letter i)
      (proj i) (hdom i) (hgood i) (2 * n * (5 * r + 2 + k)) y (proj i y) (hy i)
      (fun _ _ => Nat.le_refl _)
    have ht := gridTail (n := n) r r (letter i) (2 * n * (5 * r + 2 + k)) (proj i y)
    have hpot := gridPotential_le r r (proj i y)
    have hpot' : gridPotential r r (proj i y) ≤ r * 2 ^ (4 * r) := by
      rw [show 2 * (r + r) = 4 * r by omega] at hpot
      omega
    have hblock := entryTailBlock (K := K) hn ht hpot' hq
    exact Nat.le_trans (Nat.mul_le_mul_left _ hdm) hblock
  have hM : 0 < 2 * n * (5 * r + 2 + k) := Nat.mul_pos (Nat.mul_pos (by decide) hn) (by omega)
  have hcost := entrySimultaneousCost next (fun y => ∀ j, P j y) Good
    (2 * n * (5 * r + 2 + k)) hM hK (fun y e hy j => hcl j y e (hy j)) hc hb x hx T
  have hceil := entryCeilingLe n (5 * r + 2 + k) (by
    have : 7 ≤ 5 * r + 2 + k := by omega
    have := Nat.mul_le_mul hn this
    omega)
  calc 2 * costNumerator next (fun y => ∀ i, Good i y) x T
      ≤ 2 * (n ^ T * L3.Prob.renewalCeiling (2 * n * (5 * r + 2 + k)) 1 4) :=
        Nat.mul_le_mul_left 2 hcost
    _ = n ^ T * (2 * L3.Prob.renewalCeiling (2 * n * (5 * r + 2 + k)) 1 4) := by ac_rfl
    _ ≤ n ^ T * (6 * n * (5 * r + 2 + k)) := by
        apply Nat.mul_le_mul_left
        have h6 : 6 * n * (5 * r + 2 + k) = 6 * n * (5 * r + 2 + k) := rfl
        exact Nat.le_trans hceil (Nat.le_of_eq h6)

/-! ### The entry charge inside the 201 budget -/

open L3.RenewalReferenceClock in
/-- The six charges (boundary, first zero, structural, entry, wave, comparison) fit the 201
budget.  The entry charge is `entryGridsCharge` for the `valueBlocks n ≤ n ≤ 2^(ceilLogTwo n)`
writer pairs of span `digitSpan = 2^t - 1`, with `k = ceilLogTwo n`.  It is a sixth charge, not
part of the structural one: `2 (ν_s + P_s) + 6 (5 R + 2 + k) ≤ 6 ν_s < n`.
Consumer: the R10c digit half-stage composition (`bankRepairDigitPreDrainHalfOfThreeClocks`
with the entry stage inserted). -/
theorem entryLedgerFit {n : Nat} (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n +
        bankRepairDigitStructuralMicroCharge n +
        6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) +
        bankRepairDigitValueWaveMicroCharge n + bankRepairDigitComparisonMicroCharge n ≤
      201 * n ^ 2 := by
  have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
  have ht : (compileAdvice (ceilLogTwo n)).t = ceilLogTwo (ceilLogTwo n) :=
    compileAdvice_t_large _ (by omega)
  have hs7 : 7 ≤ ceilLogTwo (ceilLogTwo n) := bankRepairDigitWidthBank hbank
  have hsix := bankRepairDigitNuSixOfGrowth bankRepairDigitNuGrowthProved
    (ceilLogTwo (ceilLogTwo n)) hs7
  have hpop := bankRepairDigitPopulationLower hn hbank
  have hP := bankRepairDigitPairUpperLeNu (ceilLogTwo (ceilLogTwo n))
  have hL : ceilLogTwo n ≤ 2 ^ ceilLogTwo (ceilLogTwo n) :=
    (ceilLogTwo_spec (ceilLogTwo n) (by omega)).2
  have heq : bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n +
        bankRepairDigitStructuralMicroCharge n + bankRepairDigitValueWaveMicroCharge n +
        bankRepairDigitComparisonMicroCharge n =
      2 * (bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) +
        bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n))) * n + 200 * n ^ 2 := by
    unfold bankRepairDigitBoundaryMicroCharge bankRepairDigitFirstZeroMicroCharge
      bankRepairDigitStructuralMicroCharge bankRepairDigitValueWaveMicroCharge
      bankRepairDigitComparisonMicroCharge bankRepairDigitNu
    simp only [Nat.mul_add, Nat.add_mul]
    ac_rfl
  -- the pair numerator dominates the entry numerator
  have hPlow : 6 * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) ≤
      2 * bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n)) := by
    unfold digitSpan
    rw [ht]
    unfold bankRepairDigitPairUpper bankRepairDigitPairEnvelope bankRepairDigitRadius
      bankRepairDigitExponent
    generalize hsv : ceilLogTwo (ceilLogTwo n) = s at hs7 hL ⊢
    have h2s : 2 ^ s = 2 * 2 ^ (s - 1) := by
      rw [show s = (s - 1) + 1 by omega, Nat.pow_succ]
      simp only [Nat.add_sub_cancel]
      ac_rfl
    generalize hr : 2 ^ s - 1 = r
    generalize hE : 2 ^ (s - 1) = E at h2s
    have hE2 : ceilLogTwo n ≤ 2 * E := by omega
    have hrs : 2 ^ s - 1 = r := hr
    generalize ha : 12 * r ^ 4 + 40 * r ^ 3 + 18 * r ^ 2 + 36 * r + 10 = a
    have ha1 : 36 * r + 10 ≤ a := by omega
    have hab1 : a * 3 ≤ a * (E + 3) := Nat.mul_le_mul_left a (by omega)
    have hab2 : 10 * (E + 3) ≤ a * (E + 3) := Nat.mul_le_mul_right (E + 3) (by omega)
    have hexp : 4 * a * (E + 3) = 4 * (a * (E + 3)) := by ac_rfl
    rw [hexp]
    omega
  have hbound : 2 * (bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) +
        bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n))) +
      6 * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) ≤ n := by
    omega
  have hmul := Nat.mul_le_mul_right n hbound
  rw [Nat.add_mul] at hmul
  have hsq : n ^ 2 = n * n := Nat.pow_two n
  have hentry : 6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) =
      6 * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) * n := by
    ac_rfl
  omega

end L3.DigitEntryClose

#print axioms L3.DigitEntryClose.entrySimultaneousCost
#print axioms L3.DigitEntryClose.entryTailBlock
#print axioms L3.DigitEntryClose.entryGridsCharge
#print axioms L3.DigitEntryClose.entryLedgerFit
