import Leader.L3.Bank.RepairDigitPacketMomentWide
import Leader.L3.Bank.RepairDigitPacketMomentAfter

/-!
# Lemma e-max: the per-attempt loop for every register length `r ≥ 3`

`L3.PacketMomentWide.attemptLoopWide` closes the attempt loop at `E[z^τ] ≤ 6` at the headline
width `N = n (2C + 1)`, but its phase factor `widePow` (`w^k ≤ 167/100` for `k ≤ C`) splits `C`
letters into 32 blocks of `C/32 + 1` letters, each `≤ 127/125` by Bernoulli; that needs
`127 (C/32 + 1) ≤ 2 (2C + 1)`, i.e. `C ≥ 4000`. On SMALL the register length is `r = 3` for
`ceilLogTwo n ≤ 4` (`C_3 = 442`), where the split of `C` letters fails.

The split is needed only for the budgets the loop uses, not for `C`. Here the block length is
`⌈k/32⌉ = (k + 31)/32` of the budget `k` itself:

* `widePowBlock`: `127 ⌈k/32⌉ ≤ 2 (2C + 1)` gives `w^k ≤ 167/100` at `N ≥ n (2C + 1)`, any `C ≥ 1`;
* `attemptLoopBlock`: the loop closes at `6` with that condition on `B_p` and `B_s`,
  `B_s ≤ C`, `11 B_a ≤ 2C + 1` and `C ≥ 21` (for `N ≥ 42 n`);
* `blockOfLarge`, `attemptLoopLarge`: for `C ≥ 4000` every `k ≤ C` fits, so `attemptLoopWide`'s
  statement is a corollary;
* `prepBlockFit`: the preparation budget `B_p = 2R⁴ + 4R³ + 8R² + 12R + 8` fits at `C_R` for every
  `R ≥ 3` (`64 (2C_R + 1) - 127 (B_p + 31) = 2R⁴ + 516R³ - 632R² - 116R - 4377 ≥ 3681`);
  `finishBlockFit`: the finish budget `R + 1`; `pairClockMid`: `C_r ≥ 21` for `r ≥ 1`;
  with `L3.PacketMomentAfter.afterBudgetShort` (`11 (2R² + 8R + 5) ≤ 2C_R + 1`, `R ≥ 3`) all budgets
  of the attempt except the audit receipts fit at `C_R` for every `R ≥ 3`.

At `R = 3`: `B_p = 386 = 0.87 C_3`, `⌈386/32⌉ = 13`, `127 · 13 = 1651 ≤ 1770`; no budget term is too
large.
-/

namespace L3.WidthPacketMoment

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open L3.PairMoment
open L3.PacketMoment
open L3.PacketMomentRelease
open L3.PacketMomentHorizon
open L3.PacketMomentFive
open L3.PacketMomentU
open L3.PacketMomentV
open L3.PacketMomentWide
open L3.PacketMomentAfter
open L3.RenewalReferenceClock

/-- **The phase factor from the block split of the budget**: with `⌈k/32⌉` letters per block,
`127 ⌈k/32⌉ ≤ 2 (2C + 1)` and `N ≥ n (2C + 1)`, `w^k ≤ 167/100` (`w = N/(N-n)`): 32 blocks, each
`≤ 127/125` by Bernoulli, and `(127/125)^32 ≤ 167/100`. Consumer: `attemptLoopBlock`. -/
theorem widePowBlock (N n C k : Nat) (hn : 1 ≤ n) (hC : 1 ≤ C) (hN : n * (2 * C + 1) ≤ N)
    (hk : 127 * ((k + 31) / 32) ≤ 2 * (2 * C + 1)) : 100 * N ^ k ≤ 167 * (N - n) ^ k := by
  have hnN : n < N := by
    have : n * 2 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  let j := (k + 31) / 32
  have hj32 : k ≤ j * 32 := by omega
  have hjb : 127 * (j * n) ≤ 2 * N := by
    have h2 : 127 * j * n ≤ 2 * (2 * C + 1) * n := Nat.mul_le_mul_right n hk
    have h3 : 2 * (2 * C + 1) * n = 2 * (n * (2 * C + 1)) := by
      rw [Nat.mul_comm n, Nat.mul_assoc]
    rw [← Nat.mul_assoc]
    omega
  have hb := blockPow N n j hnN hjb
  have hb32 : (125 * N ^ j) ^ 32 ≤ (127 * (N - n) ^ j) ^ 32 := Nat.pow_le_pow_left hb 32
  rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hb32
  have hnum : 100 * 127 ^ 32 ≤ 167 * 125 ^ 32 := by decide
  have hm : 100 * N ^ (j * 32) ≤ 167 * (N - n) ^ (j * 32) := by
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 125 ^ 32 by decide)
    calc 125 ^ 32 * (100 * N ^ (j * 32)) = 100 * (125 ^ 32 * N ^ (j * 32)) :=
          Nat.mul_left_comm _ _ _
      _ ≤ 100 * (127 ^ 32 * (N - n) ^ (j * 32)) := Nat.mul_le_mul_left _ hb32
      _ = (100 * 127 ^ 32) * (N - n) ^ (j * 32) := by rw [Nat.mul_assoc]
      _ ≤ (167 * 125 ^ 32) * (N - n) ^ (j * 32) := Nat.mul_le_mul_right _ hnum
      _ = 125 ^ 32 * (167 * (N - n) ^ (j * 32)) := by
          rw [Nat.mul_comm 167, Nat.mul_assoc]
  exact ratioMono N n k (j * 32) 100 167 hnN hj32 hm

/-- **The per-attempt loop closes at `6` for every pair clock `C ≥ 21`**, when the preparation
and success budgets fit the block split (`127 ⌈B/32⌉ ≤ 2(2C + 1)`, and `B_s ≤ C`) and the post-race
budget satisfies `11 B_a ≤ 2C + 1`. Consumer: the per-pair moment of Lemma e-max at the band
reference (`C = C_r`, budgets by `prepBlockFit`, `finishBlockFit`, `afterBudgetShort`). -/
theorem attemptLoopBlock {S : Type} {n : Nat} (next : S → Fin n → S) (P A Q : S → Prop)
    (N C Bp Bs Ba : Nat) (hn : 2 ≤ n) (hC : 21 ≤ C) (hN : n * (2 * C + 1) ≤ N)
    (hBs : Bs ≤ C) (hBpb : 127 * ((Bp + 31) / 32) ≤ 2 * (2 * C + 1))
    (hBsb : 127 * ((Bs + 31) / 32) ≤ 2 * (2 * C + 1)) (hBa : 11 * Ba ≤ 2 * C + 1)
    (hprep : ∀ x, A x → MomentBoundQ next Q N (N ^ Bp) ((N - n) ^ Bp) x)
    (hQ : ∀ y, Q y → P y ∨ MomentBoundQ next P N (N ^ Bs) ((N - n) ^ Bs) y ∨
      ∃ (Pend : S → Prop) (ea eb : Fin n), Pend y ∧ ea ≠ eb ∧
        (∀ x, Pend x → ¬ P x → ∀ e, e ≠ ea → e ≠ eb → Pend (next x e)) ∧
        (∀ x, Pend x → ¬ P x → MomentBoundQ next P N (N ^ Ba) ((N - n) ^ Ba) (next x ea)) ∧
        (∀ x, Pend x → ¬ P x → A (next x eb))) :
    ∀ x, A x → MomentBoundQ next P N (6 * (N - n) ^ C) ((N - n) ^ C) x := by
  have hBa' : Ba ≤ C := by omega
  have h42 : 42 * n ≤ N := by
    have : n * 42 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  have hnN : n < N := by omega
  have hD : 0 < (N - n) ^ C := Nat.pow_pos (by omega)
  refine attemptLoop next P A Q N (N ^ Bp) ((N - n) ^ Bp)
    (N ^ Bs * (N - n) ^ (C - Bs)) (N ^ Ba * (N - n) ^ (C - Ba)) (6 * (N - n) ^ C) ((N - n) ^ C)
    hn (by omega) (Nat.pow_pos (by omega)) hD ?_ ?_ (by omega) hprep ?_ ?_
  · rw [show (N - n) ^ C = (N - n) ^ Bs * (N - n) ^ (C - Bs) by
      rw [← Nat.pow_add, show Bs + (C - Bs) = C by omega]]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.sub_le N n) _)
  · rw [show (N - n) ^ C = (N - n) ^ Ba * (N - n) ^ (C - Ba) by
      rw [← Nat.pow_add, show Ba + (C - Ba) = C by omega]]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.sub_le N n) _)
  · intro y hy
    rcases hQ y hy with hp | hs | ⟨Pend, ea, eb, h1, h2, h3, h4, h5⟩
    · exact Or.inl hp
    · exact Or.inr (Or.inl (boundCommon next P N Bs C hBs y hnN hs))
    · exact Or.inr (Or.inr ⟨Pend, ea, eb, h1, h2, h3,
        fun x hx hnp => boundCommon next P N Ba C hBa' _ hnN (h4 x hx hnp), h5⟩)
  · exact hcloseWide N n _ _ _ _ _ h42
      (widePowBlock N n C Bp (by omega) (by omega) hN hBpb)
      (scaledWide N n Ba C 10 11 hBa' (shortPow N n C Ba (by omega) (by omega) hN hBa))
      (scaledWide N n Bs C 100 167 hBs (widePowBlock N n C Bs (by omega) (by omega) hN hBsb))

/-- **For `C ≥ 4000` every budget `k ≤ C` fits the block split.** Consumer:
`attemptLoopLarge`. -/
theorem blockOfLarge (C k : Nat) (hC : 4000 ≤ C) (hk : k ≤ C) :
    127 * ((k + 31) / 32) ≤ 2 * (2 * C + 1) := by
  omega

/-- **The large-clock loop as a corollary**: the statement of
`L3.PacketMomentWide.attemptLoopWide` from `attemptLoopBlock`. Consumer: the BANK per-pair moment
(`C_r ≥ 4000` there), as `attemptLoopWide`. -/
theorem attemptLoopLarge {S : Type} {n : Nat} (next : S → Fin n → S) (P A Q : S → Prop)
    (N C Bp Bs Ba : Nat) (hn : 2 ≤ n) (hC : 4000 ≤ C) (hN : n * (2 * C + 1) ≤ N)
    (hBp : Bp ≤ C) (hBs : Bs ≤ C) (hBa : 11 * Ba ≤ 2 * C + 1)
    (hprep : ∀ x, A x → MomentBoundQ next Q N (N ^ Bp) ((N - n) ^ Bp) x)
    (hQ : ∀ y, Q y → P y ∨ MomentBoundQ next P N (N ^ Bs) ((N - n) ^ Bs) y ∨
      ∃ (Pend : S → Prop) (ea eb : Fin n), Pend y ∧ ea ≠ eb ∧
        (∀ x, Pend x → ¬ P x → ∀ e, e ≠ ea → e ≠ eb → Pend (next x e)) ∧
        (∀ x, Pend x → ¬ P x → MomentBoundQ next P N (N ^ Ba) ((N - n) ^ Ba) (next x ea)) ∧
        (∀ x, Pend x → ¬ P x → A (next x eb))) :
    ∀ x, A x → MomentBoundQ next P N (6 * (N - n) ^ C) ((N - n) ^ C) x :=
  attemptLoopBlock next P A Q N C Bp Bs Ba hn (by omega) hN hBs
    (blockOfLarge C Bp hC hBp) (blockOfLarge C Bs hC hBs) hBa hprep hQ

/-- **The pair clock is at least `21`** for `r ≥ 1` (width `N ≥ 42 n` at `N = n (2C_r + 1)`).
Consumer: `attemptLoopBlock` at the band reference. -/
theorem pairClockMid (r : Nat) (hr : 1 ≤ r) : 21 ≤ bankRepairDigitPairClock r := by
  unfold bankRepairDigitPairClock
  have h4 : 1 ≤ r ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- **The preparation budget fits the block split at `C_R` for every `R ≥ 3`**:
`127 ⌈B_p/32⌉ ≤ 2 (2C_R + 1)`, `B_p = uBudget R + 2R + (R+2)(2R+2)`. Consumer:
`attemptLoopBlock` at the band reference (`hBpb`). -/
theorem prepBlockFit (R : Nat) (hR : 3 ≤ R) :
    127 * ((uBudget R + 2 * R + (R + 2) * vK R + 31) / 32) ≤
      2 * (2 * bankRepairDigitPairClock R + 1) := by
  have key : 127 * (uBudget R + 2 * R + (R + 2) * vK R + 31) ≤
      64 * (2 * bankRepairDigitPairClock R + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, R = t + 3 := ⟨R - 3, by omega⟩
    unfold uBudget uK vK bankRepairDigitPairClock
    grind
  generalize uBudget R + 2 * R + (R + 2) * vK R = B at key ⊢
  generalize bankRepairDigitPairClock R = C at key ⊢
  omega

/-- **The finish budget fits the block split** at `C_R`: `127 ⌈(R+1)/32⌉ ≤ 2 (2C_R + 1)`.
Consumer: `attemptLoopBlock` at the band reference (the finish part of `hBsb`). -/
theorem finishBlockFit (R : Nat) (hR : 2 ≤ R) :
    127 * ((R + 1 + 31) / 32) ≤ 2 * (2 * bankRepairDigitPairClock R + 1) := by
  have key : 127 * (R + 1 + 31) ≤ 64 * (2 * bankRepairDigitPairClock R + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, R = t + 2 := ⟨R - 2, by omega⟩
    unfold bankRepairDigitPairClock
    grind
  generalize bankRepairDigitPairClock R = C at key ⊢
  omega

end L3.WidthPacketMoment

#print axioms L3.WidthPacketMoment.widePowBlock
#print axioms L3.WidthPacketMoment.attemptLoopBlock
#print axioms L3.WidthPacketMoment.blockOfLarge
#print axioms L3.WidthPacketMoment.attemptLoopLarge
#print axioms L3.WidthPacketMoment.pairClockMid
#print axioms L3.WidthPacketMoment.prepBlockFit
#print axioms L3.WidthPacketMoment.finishBlockFit
