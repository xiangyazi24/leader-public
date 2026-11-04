import Leader.L3.Bank.RepairDigitPacketMomentHorizon
import Leader.L3.Bank.RepairDigitPacketMomentRelease

/-!
# Lemma e-max: the per-attempt loop closes below five

repair.tex, Lemma e-max: the per-pair moment `M = E[z^{T_pair}]` must stay below a fixed
constant for the simultaneous clock. With `w = N/(N-n)` and every phase budget `k ≤ B`,
choosing `5 B n ≤ N` makes every phase factor `w^k ≤ 5/4` (`bernoulliFive`: Bernoulli's
inequality `(1 - n/N)^k ≥ 1 - k n/N` in integers), and the race weight `N/(2N-n) ≤ 5/9`. Then
`attemptLoop` closes with `c = 3 D`: `(5/4)(5/9)(5/4 + 3) = 425/144 ≤ 3` and
`(5/4)(5/4) ≤ 3` (`hcloseFive`). `attemptLoopFive`: from the attempt class, `E[z^τ] ≤ 3 < 5`,
for any preparation budget `B_p`, success budget `B_s` and post-race success budget `B_a`
(all `≤ B`).
-/

namespace L3.PacketMomentFive

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open K2ArbitraryElimination.FiniteAccounting
open L3.PairMoment
open L3.PacketMoment
open L3.PacketMomentRelease
open L3.PacketMomentHorizon

/-- **Bernoulli's inequality in integers**: `N^k (N - k n) ≤ (N - n)^k N`. Consumer:
`bernoulliFive`. -/
theorem bernoulliNat (N m : Nat) : ∀ k, N ^ k * (N - k * m) ≤ (N - m) ^ k * N
  | 0 => by simp
  | k + 1 => by
      have ih := bernoulliNat N m k
      by_cases hk : (k + 1) * m ≤ N
      · have e1 : (N - m) * (N - k * m) ≥ N * (N - (k + 1) * m) := by
          have h1 : (N - m) * (N - k * m) = N * (N - (k + 1) * m) + k * m * m := by
            have : k * m + m = (k + 1) * m := by rw [Nat.succ_mul]
            have hN1 : m ≤ N := Nat.le_trans (Nat.le_mul_of_pos_left m (by omega)) hk
            obtain ⟨d, hd⟩ : ∃ d, N = (k + 1) * m + d := ⟨N - (k + 1) * m, by omega⟩
            rw [hd, show (k + 1) * m + d - m = k * m + d by rw [Nat.succ_mul]; omega,
              show (k + 1) * m + d - k * m = m + d by rw [Nat.succ_mul]; omega,
              show (k + 1) * m + d - (k + 1) * m = d by omega]
            simp only [Nat.succ_mul, Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm,
              Nat.mul_assoc]
            omega
          omega
        calc N ^ (k + 1) * (N - (k + 1) * m) = N ^ k * (N * (N - (k + 1) * m)) := by
              rw [Nat.pow_succ, Nat.mul_assoc]
          _ ≤ N ^ k * ((N - m) * (N - k * m)) := Nat.mul_le_mul_left _ e1
          _ = (N - m) * (N ^ k * (N - k * m)) := Nat.mul_left_comm _ _ _
          _ ≤ (N - m) * ((N - m) ^ k * N) := Nat.mul_le_mul_left _ ih
          _ = (N - m) ^ (k + 1) * N := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (N - m)]
      · rw [show N - (k + 1) * m = 0 by omega, Nat.mul_zero]
        exact Nat.zero_le _

/-- **Every phase factor is at most `5/4`** when `5 k n ≤ N`. Consumer: `hcloseFive`. -/
theorem bernoulliFive (N n k : Nat) (hN : 5 * (k * n) ≤ N) : 4 * N ^ k ≤ 5 * (N - n) ^ k := by
  have h := bernoulliNat N n k
  by_cases hN0 : N = 0
  · subst hN0
    cases k with
    | zero => simp
    | succ k => simp
  have h1 : 4 * N ≤ 5 * (N - k * n) := by omega
  have h2 : N ^ k * (4 * N) ≤ N ^ k * (5 * (N - k * n)) := Nat.mul_le_mul_left _ h1
  have h3 : (4 * N ^ k) * N ≤ (5 * (N - n) ^ k) * N := by
    calc (4 * N ^ k) * N = N ^ k * (4 * N) := by
          rw [Nat.mul_comm 4, Nat.mul_assoc]
      _ ≤ N ^ k * (5 * (N - k * n)) := h2
      _ = 5 * (N ^ k * (N - k * n)) := Nat.mul_left_comm _ _ _
      _ ≤ 5 * ((N - n) ^ k * N) := Nat.mul_le_mul_left _ h
      _ = (5 * (N - n) ^ k) * N := by rw [Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_right h3 (by omega)

/-- The scaled phase weight `N^k (N-n)^{B-k}` against its denominator `(N-n)^B`. Consumer:
`hcloseFive`. -/
theorem scaledFive (N n k B : Nat) (hk : k ≤ B) (hN : 5 * (k * n) ≤ N) :
    4 * (N ^ k * (N - n) ^ (B - k)) ≤ 5 * (N - n) ^ B := by
  have h := bernoulliFive N n k hN
  calc 4 * (N ^ k * (N - n) ^ (B - k)) = (4 * N ^ k) * (N - n) ^ (B - k) := by
        rw [Nat.mul_assoc]
    _ ≤ (5 * (N - n) ^ k) * (N - n) ^ (B - k) := Nat.mul_le_mul_right _ h
    _ = 5 * (N - n) ^ B := by
        rw [Nat.mul_assoc, ← Nat.pow_add, show k + (B - k) = B by omega]

/-- A moment `w^k` in the common denominator `(N-n)^B`. Consumer: `attemptLoopFive`. -/
theorem boundCommon {S : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop) (N k B : Nat)
    (hk : k ≤ B) (x : S) (hn : n < N) (h : MomentBoundQ next P N (N ^ k) ((N - n) ^ k) x) :
    MomentBoundQ next P N (N ^ k * (N - n) ^ (B - k)) ((N - n) ^ B) x := by
  refine momentQCross next P N _ _ _ _ x (Nat.pow_pos (by omega)) ?_ h
  rw [Nat.mul_assoc, ← Nat.pow_add, show B - k + k = B by omega]
  exact Nat.le_refl _

/-- **The closing inequality of the loop with `c = 3 D`.** Consumer: `attemptLoopFive`. -/
theorem hcloseFive (N n a1 b1 Fa Fs D : Nat) (hn : 5 * n ≤ N) (h1 : 4 * a1 ≤ 5 * b1)
    (ha : 4 * Fa ≤ 5 * D) (hs : 4 * Fs ≤ 5 * D) :
    a1 * max (N * (Fa + 3 * D)) (Fs * (2 * N - n)) ≤ 3 * D * (b1 * (2 * N - n)) := by
  have hK : 9 * N ≤ 5 * (2 * N - n) := by omega
  have hF : 4 * (Fa + 3 * D) ≤ 17 * D := by omega
  rcases Nat.le_total (N * (Fa + 3 * D)) (Fs * (2 * N - n)) with hm | hm
  · rw [Nat.max_eq_right hm]
    -- 16 a1 Fs K ≤ 25 b1 D K ≤ 48 b1 D K
    have e : 16 * (a1 * (Fs * (2 * N - n))) ≤ 16 * (3 * D * (b1 * (2 * N - n))) := by
      calc 16 * (a1 * (Fs * (2 * N - n))) = (4 * a1) * (4 * Fs) * (2 * N - n) := by
            simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ ≤ (5 * b1) * (5 * D) * (2 * N - n) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 hs)
        _ ≤ 16 * (3 * D * (b1 * (2 * N - n))) := by
            have : (5 * b1) * (5 * D) * (2 * N - n) = 25 * (b1 * D * (2 * N - n)) := by
              simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            rw [this]
            have : 16 * (3 * D * (b1 * (2 * N - n))) = 48 * (b1 * D * (2 * N - n)) := by
              simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            rw [this]
            exact Nat.mul_le_mul_right _ (by omega)
    exact Nat.le_of_mul_le_mul_left e (by omega)
  · rw [Nat.max_eq_left hm]
    -- 144 a1 N F ≤ 425 b1 K D ≤ 432 b1 K D
    have e : 144 * (a1 * (N * (Fa + 3 * D))) ≤ 144 * (3 * D * (b1 * (2 * N - n))) := by
      calc 144 * (a1 * (N * (Fa + 3 * D))) = (4 * a1) * (9 * N) * (4 * (Fa + 3 * D)) := by
            simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ ≤ (5 * b1) * (5 * (2 * N - n)) * (17 * D) :=
            Nat.mul_le_mul (Nat.mul_le_mul h1 hK) hF
        _ ≤ 144 * (3 * D * (b1 * (2 * N - n))) := by
            have : (5 * b1) * (5 * (2 * N - n)) * (17 * D) = 425 * (b1 * D * (2 * N - n)) := by
              simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            rw [this]
            have : 144 * (3 * D * (b1 * (2 * N - n))) = 432 * (b1 * D * (2 * N - n)) := by
              simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            rw [this]
            exact Nat.mul_le_mul_right _ (by omega)
    exact Nat.le_of_mul_le_mul_left e (by omega)

/-- **The per-attempt loop closes at `3 < 5`.** One attempt from the class `A` reaches `Q` with
moment `w^{B_p}`; at `Q` the target holds, or a success continuation with moment `w^{B_s}`
starts, or a race starts whose winning letter has a success continuation with moment `w^{B_a}`
and whose losing letter returns to `A`. With every budget `≤ B` and `5 B n ≤ N`,
`E[z^τ] ≤ 3` from every state of `A`. Consumer: the per-pair moment of Lemma e-max
(`M < 5`). -/
theorem attemptLoopFive {S : Type} {n : Nat} (next : S → Fin n → S) (P A Q : S → Prop)
    (N B Bp Bs Ba : Nat) (hn : 2 ≤ n) (hN : 5 * (B * n) ≤ N) (hB : 1 ≤ B)
    (hBp : Bp ≤ B) (hBs : Bs ≤ B) (hBa : Ba ≤ B)
    (hprep : ∀ x, A x → MomentBoundQ next Q N (N ^ Bp) ((N - n) ^ Bp) x)
    (hQ : ∀ y, Q y → P y ∨ MomentBoundQ next P N (N ^ Bs) ((N - n) ^ Bs) y ∨
      ∃ (Pend : S → Prop) (ea eb : Fin n), Pend y ∧ ea ≠ eb ∧
        (∀ x, Pend x → ¬ P x → ∀ e, e ≠ ea → e ≠ eb → Pend (next x e)) ∧
        (∀ x, Pend x → ¬ P x → MomentBoundQ next P N (N ^ Ba) ((N - n) ^ Ba) (next x ea)) ∧
        (∀ x, Pend x → ¬ P x → A (next x eb))) :
    ∀ x, A x → MomentBoundQ next P N (3 * (N - n) ^ B) ((N - n) ^ B) x := by
  have hnN : n < N := by
    have : 5 * n ≤ 5 * (B * n) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left n hB)
    omega
  have h5 : 5 * n ≤ N := by
    have : 5 * n ≤ 5 * (B * n) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left n hB)
    omega
  have hk : ∀ k, k ≤ B → 5 * (k * n) ≤ N := fun k hk =>
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk)) hN
  have hD : 0 < (N - n) ^ B := Nat.pow_pos (by omega)
  refine attemptLoop next P A Q N (N ^ Bp) ((N - n) ^ Bp)
    (N ^ Bs * (N - n) ^ (B - Bs)) (N ^ Ba * (N - n) ^ (B - Ba)) (3 * (N - n) ^ B) ((N - n) ^ B)
    hn (by omega) (Nat.pow_pos (by omega)) hD ?_ ?_ (by omega) hprep ?_ ?_
  · rw [show (N - n) ^ B = (N - n) ^ Bs * (N - n) ^ (B - Bs) by
      rw [← Nat.pow_add, show Bs + (B - Bs) = B by omega]]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.sub_le N n) _)
  · rw [show (N - n) ^ B = (N - n) ^ Ba * (N - n) ^ (B - Ba) by
      rw [← Nat.pow_add, show Ba + (B - Ba) = B by omega]]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.sub_le N n) _)
  · intro y hy
    rcases hQ y hy with hp | hs | ⟨Pend, ea, eb, h1, h2, h3, h4, h5⟩
    · exact Or.inl hp
    · exact Or.inr (Or.inl (boundCommon next P N Bs B hBs y hnN hs))
    · exact Or.inr (Or.inr ⟨Pend, ea, eb, h1, h2, h3,
        fun x hx hnp => boundCommon next P N Ba B hBa _ hnN (h4 x hx hnp), h5⟩)
  · exact hcloseFive N n _ _ _ _ _ h5 (bernoulliFive N n Bp (hk Bp hBp))
      (scaledFive N n Ba B hBa (hk Ba hBa)) (scaledFive N n Bs B hBs (hk Bs hBs))

end L3.PacketMomentFive

#print axioms L3.PacketMomentFive.bernoulliNat
#print axioms L3.PacketMomentFive.bernoulliFive
#print axioms L3.PacketMomentFive.hcloseFive
#print axioms L3.PacketMomentFive.attemptLoopFive
