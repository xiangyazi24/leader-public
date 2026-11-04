import Leader.L3.Bank.RepairDigitPacketMomentFive
import Leader.L3.Bank.RepairDigitPacketMomentPrep

/-!
# Lemma e-max: the per-attempt loop at the headline width `N = n (2 C_r + 1)`

`L3.PacketMomentFive.attemptLoopFive` needs `5 B n ≤ N`, but the headline fixes
`N = widthPairMomentWidth n = n (2 C_r + 1)` (`C_r = bankRepairDigitPairClock r`, `r` the
register length `R` of the BANK pairs), and the preparation budget of one attempt is
`B_p = uBudget R + 2R + (R+2)(2R+2) = 2R^4 + 4R^3 + 8R^2 + 12R + 8 > (2 C_r + 1)/5`. Here the
loop is closed at the actual width:

* `prepBudgetLe`: `B_p ≤ C_r` for `R ≥ 2` (`C_r - B_p = 4R^3 - 5R^2 - R - 4`);
* `widePow`: for `k ≤ C`, `C ≥ 4000` and `n (2C + 1) ≤ N`, the phase factor
  `w^k = (N/(N-n))^k ≤ 167/100` (Bernoulli on 32 blocks of `⌈C/32⌉` letters, each
  `≤ 127/125`, and `(127/125)^32 ≤ 1.67`; the true value is `≤ e^{1/2} ≈ 1.6487`);
* `hcloseWide`: `attemptLoop` closes with `c = 6 D` when the post-race success budget
  satisfies `11 B_a ≤ 2C + 1` (`w^{B_a} ≤ 11/10`): `(167/100)(1/2 + ε)(11/10 + 6) ≤ 6` and
  `(167/100)^2 ≤ 6`;
* `attemptLoopWide`: from the attempt class, `E[z^τ] ≤ 6`, for `B_p, B_s ≤ C`,
  `11 B_a ≤ 2C + 1`, `C ≥ 4000`, `N ≥ n (2C + 1)`. With `E[z^T] ≤ 40` per pair, the moment of the
  phases before the first attempt may be up to `40/6`.
-/

namespace L3.PacketMomentWide

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open K2ArbitraryElimination.FiniteAccounting
open L3.PairMoment
open L3.PacketMoment
open L3.PacketMomentRelease
open L3.PacketMomentHorizon
open L3.PacketMomentFive
open L3.PacketMomentU
open L3.PacketMomentV
open L3.RenewalReferenceClock

/-- **The preparation budget fits the pair clock**: `uBudget R + 2R + (R+2)(2R+2) ≤ C_R` for
`R ≥ 2`. Consumer: `attemptLoopWide` at the BANK pair (`R = r`). -/
theorem prepBudgetLe (R : Nat) (hR : 2 ≤ R) :
    uBudget R + 2 * R + (R + 2) * vK R ≤ bankRepairDigitPairClock R := by
  obtain ⟨t, rfl⟩ : ∃ t, R = t + 2 := ⟨R - 2, by omega⟩
  unfold uBudget uK vK bankRepairDigitPairClock
  grind

/-- **The pair clock is at least `4000`** for `r ≥ 7`. Consumer: `attemptLoopWide` at the BANK
pair. -/
theorem pairClockLarge (r : Nat) (hr : 7 ≤ r) : 4000 ≤ bankRepairDigitPairClock r := by
  unfold bankRepairDigitPairClock
  have h : 7 ^ 4 ≤ r ^ 4 := Nat.pow_le_pow_left hr 4
  have h7 : 7 ^ 4 = 2401 := rfl
  omega

/-- A phase-factor bound for `m` letters holds for `k ≤ m` letters. Consumer: `widePow`. -/
theorem ratioMono (N n k m p q : Nat) (hn : n < N) (hk : k ≤ m) (h : p * N ^ m ≤ q * (N - n) ^ m) :
    p * N ^ k ≤ q * (N - n) ^ k := by
  have hpos : 0 < (N - n) ^ (m - k) := Nat.pow_pos (by omega)
  have e1 : N ^ m = N ^ k * N ^ (m - k) := by rw [← Nat.pow_add, show k + (m - k) = m by omega]
  have e2 : (N - n) ^ m = (N - n) ^ k * (N - n) ^ (m - k) := by
    rw [← Nat.pow_add, show k + (m - k) = m by omega]
  have h3 : (N - n) ^ (m - k) ≤ N ^ (m - k) := Nat.pow_le_pow_left (Nat.sub_le N n) _
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc p * N ^ k * (N - n) ^ (m - k) ≤ p * N ^ k * N ^ (m - k) := Nat.mul_le_mul_left _ h3
    _ = p * N ^ m := by rw [e1, Nat.mul_assoc]
    _ ≤ q * (N - n) ^ m := h
    _ = q * (N - n) ^ k * (N - n) ^ (m - k) := by rw [e2, Nat.mul_assoc]

/-- One block of `j` letters, `127 j n ≤ 2 N`: `w^j ≤ 127/125`. Consumer: `widePow`. -/
theorem blockPow (N n j : Nat) (hn : n < N) (hj : 127 * (j * n) ≤ 2 * N) :
    125 * N ^ j ≤ 127 * (N - n) ^ j := by
  have h := bernoulliNat N n j
  have h1 : 125 * N ≤ 127 * (N - j * n) := by omega
  refine Nat.le_of_mul_le_mul_right ?_ (show 0 < N by omega)
  calc 125 * N ^ j * N = N ^ j * (125 * N) := by rw [Nat.mul_comm 125, Nat.mul_assoc]
    _ ≤ N ^ j * (127 * (N - j * n)) := Nat.mul_le_mul_left _ h1
    _ = 127 * (N ^ j * (N - j * n)) := Nat.mul_left_comm _ _ _
    _ ≤ 127 * ((N - n) ^ j * N) := Nat.mul_le_mul_left _ h
    _ = 127 * (N - n) ^ j * N := by rw [Nat.mul_assoc]

/-- **Every phase factor of at most `C` letters is at most `167/100`** at width
`N ≥ n (2C + 1)`, `C ≥ 4000`. Consumer: `attemptLoopWide`. -/
theorem widePow (N n C k : Nat) (hn : 1 ≤ n) (hC : 4000 ≤ C) (hN : n * (2 * C + 1) ≤ N)
    (hk : k ≤ C) : 100 * N ^ k ≤ 167 * (N - n) ^ k := by
  have hnN : n < N := by
    have : n * 2 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  let j := C / 32 + 1
  have hj32 : C ≤ 32 * j := by omega
  have hjb : 127 * (j * n) ≤ 2 * N := by
    have h1 : 127 * j ≤ 2 * (2 * C + 1) := by omega
    have h2 : 127 * j * n ≤ 2 * (2 * C + 1) * n := Nat.mul_le_mul_right n h1
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
  exact ratioMono N n k (j * 32) 100 167 hnN (by omega) hm

/-- The post-race success factor: `11 B_a ≤ 2C + 1` gives `w^{B_a} ≤ 11/10`. Consumer:
`attemptLoopWide`. -/
theorem shortPow (N n C k : Nat) (hn : 1 ≤ n) (hC : 1 ≤ C) (hN : n * (2 * C + 1) ≤ N) (hk : 11 * k ≤ 2 * C + 1) :
    10 * N ^ k ≤ 11 * (N - n) ^ k := by
  have h := bernoulliNat N n k
  have hkn : 11 * (k * n) ≤ N := by
    have h2 : 11 * k * n ≤ (2 * C + 1) * n := Nat.mul_le_mul_right n hk
    rw [Nat.mul_comm (2 * C + 1)] at h2
    rw [← Nat.mul_assoc]
    omega
  have hnN : n < N := by
    have : n * 2 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  have h1 : 10 * N ≤ 11 * (N - k * n) := by
    generalize k * n = m at hkn ⊢
    omega
  refine Nat.le_of_mul_le_mul_right ?_ (show 0 < N by omega)
  calc 10 * N ^ k * N = N ^ k * (10 * N) := by rw [Nat.mul_comm 10, Nat.mul_assoc]
    _ ≤ N ^ k * (11 * (N - k * n)) := Nat.mul_le_mul_left _ h1
    _ = 11 * (N ^ k * (N - k * n)) := Nat.mul_left_comm _ _ _
    _ ≤ 11 * ((N - n) ^ k * N) := Nat.mul_le_mul_left _ h
    _ = 11 * (N - n) ^ k * N := by rw [Nat.mul_assoc]

/-- A scaled factor `N^k (N-n)^{C-k}` against `(N-n)^C`. Consumer: `attemptLoopWide`. -/
theorem scaledWide (N n k C p q : Nat) (hk : k ≤ C) (h : p * N ^ k ≤ q * (N - n) ^ k) :
    p * (N ^ k * (N - n) ^ (C - k)) ≤ q * (N - n) ^ C := by
  calc p * (N ^ k * (N - n) ^ (C - k)) = (p * N ^ k) * (N - n) ^ (C - k) := by
        rw [Nat.mul_assoc]
    _ ≤ (q * (N - n) ^ k) * (N - n) ^ (C - k) := Nat.mul_le_mul_right _ h
    _ = q * (N - n) ^ C := by
        rw [Nat.mul_assoc, ← Nat.pow_add, show k + (C - k) = C by omega]

/-- **The closing inequality of the loop with `c = 6 D`** at width `N ≥ 42 n`. Consumer:
`attemptLoopWide`. -/
theorem hcloseWide (N n a1 b1 Fa Fs D : Nat) (hn : 42 * n ≤ N) (h1 : 100 * a1 ≤ 167 * b1)
    (ha : 10 * Fa ≤ 11 * D) (hs : 100 * Fs ≤ 167 * D) :
    a1 * max (N * (Fa + 6 * D)) (Fs * (2 * N - n)) ≤ 6 * D * (b1 * (2 * N - n)) := by
  have hF : 10 * (Fa + 6 * D) ≤ 71 * D := by omega
  rcases Nat.le_total (N * (Fa + 6 * D)) (Fs * (2 * N - n)) with hm | hm
  · rw [Nat.max_eq_right hm]
    have e : 10000 * (a1 * (Fs * (2 * N - n))) ≤ 10000 * (6 * D * (b1 * (2 * N - n))) := by
      calc 10000 * (a1 * (Fs * (2 * N - n))) = (100 * a1) * (100 * Fs) * (2 * N - n) := by
            simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ ≤ (167 * b1) * (167 * D) * (2 * N - n) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 hs)
        _ = 27889 * (b1 * D * (2 * N - n)) := by
            simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ ≤ 60000 * (b1 * D * (2 * N - n)) := Nat.mul_le_mul_right _ (by omega)
        _ = 10000 * (6 * D * (b1 * (2 * N - n))) := by
            simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    exact Nat.le_of_mul_le_mul_left e (by omega)
  · rw [Nat.max_eq_left hm]
    have hK : 11857 * N ≤ 6000 * (2 * N - n) := by omega
    have e : 1000 * (a1 * (N * (Fa + 6 * D))) ≤ 1000 * (6 * D * (b1 * (2 * N - n))) := by
      calc 1000 * (a1 * (N * (Fa + 6 * D))) = (100 * a1) * N * (10 * (Fa + 6 * D)) := by
            simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ ≤ (167 * b1) * N * (71 * D) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ h1) hF
        _ = b1 * D * (11857 * N) := by
            simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ ≤ b1 * D * (6000 * (2 * N - n)) := Nat.mul_le_mul_left _ hK
        _ = 1000 * (6 * D * (b1 * (2 * N - n))) := by
            simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    exact Nat.le_of_mul_le_mul_left e (by omega)

/-- **The per-attempt loop at the headline width closes at `6`.** One attempt from the class
`A` reaches `Q` with moment `w^{B_p}`; at `Q` the target holds, or a success continuation with
moment `w^{B_s}` starts, or a race starts whose winning letter has a success continuation with
moment `w^{B_a}` and whose losing letter returns to `A`. With `B_p, B_s ≤ C`, `11 B_a ≤ 2C + 1`,
`C ≥ 4000` and `N ≥ n (2C + 1)`, `E[z^τ] ≤ 6` from every state of `A`. Consumer: the per-pair
moment of Lemma e-max (`E[z^{T_pair}] ≤ 40`, `WidthStrictPairMoment`), at `C = C_r`
(`prepBudgetLe`, `pairClockLarge`). -/
theorem attemptLoopWide {S : Type} {n : Nat} (next : S → Fin n → S) (P A Q : S → Prop)
    (N C Bp Bs Ba : Nat) (hn : 2 ≤ n) (hC : 4000 ≤ C) (hN : n * (2 * C + 1) ≤ N)
    (hBp : Bp ≤ C) (hBs : Bs ≤ C) (hBa : 11 * Ba ≤ 2 * C + 1)
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
  · exact hcloseWide N n _ _ _ _ _ h42 (widePow N n C Bp (by omega) hC hN hBp)
      (scaledWide N n Ba C 10 11 hBa' (shortPow N n C Ba (by omega) (by omega) hN hBa))
      (scaledWide N n Bs C 100 167 hBs (widePow N n C Bs (by omega) hC hN hBs))

end L3.PacketMomentWide

#print axioms L3.PacketMomentWide.prepBudgetLe
#print axioms L3.PacketMomentWide.pairClockLarge
#print axioms L3.PacketMomentWide.widePow
#print axioms L3.PacketMomentWide.hcloseWide
#print axioms L3.PacketMomentWide.attemptLoopWide
