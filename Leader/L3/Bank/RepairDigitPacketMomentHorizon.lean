import Leader.L3.Bank.RepairDigitPacketMoment

/-!
# Exponential moments up to a horizon, and the renewal loop of one race per attempt

The renewal trial of Lemma e-packet (repair.tex, "If the incoming edge wins, declare failure
immediately … the actual successor still satisfies the reached-state invariant, so `U + r`
returns to packet-only") feeds the moment of the attempt class back into itself: the failure
continuation of the race has the moment that is being bounded. The bound is closed by induction
on the horizon: the failure successor is one letter later, so its bound is needed only one
horizon lower.

* `MomentUpTo next P N a b x T`: `E[z^{min(τ,t)}] ≤ a / b` for every truncation `t ≤ T`.
* `momentSeqUpTo`: `momentSeq` with the bounds at the first hit needed only up to the same
  horizon.
* `raceMomentUpTo`: `raceMoment` with the post-race bounds up to `T` giving the race bound up
  to `T + 1`.
* `momentLoop`: a bound that passes from horizon `T` (uniformly on a class) to `T + 1` holds at
  every horizon.
* **`attemptLoop`**: one attempt from the class `A` reaches `Q` with moment `a₁/b₁`; at `Q` the
  target is hit, or a success continuation with moment `F_s/D` starts, or a race between two
  distinct letters starts whose winning letter `e_a` leads to a success continuation with moment
  `F_a/D` and whose losing letter `e_b` returns to `A`. If
  `a₁ · max(N (F_a + c), F_s (2N - n)) ≤ c · b₁ (2N - n)`, then `E[z^τ] ≤ c / D` from `A`
  (the paper's `M` with `y/2 = N/(2N-n) ≤ w/2`).
-/

namespace L3.PacketMomentHorizon

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open L3.PairMoment
open L3.PacketMoment

section Horizon

variable {S : Type} {n : Nat}

/-- **The moment bound up to a horizon.** Consumer: every lemma below. -/
def MomentUpTo (next : S → Fin n → S) (P : S → Prop) (N a b : Nat) (x : S) (T : Nat) : Prop :=
  ∀ t, t ≤ T → b * momentNumerator next P N x t ≤ a * (n ^ t * (N - 1) ^ t)

/-- A full bound holds up to every horizon. Consumer: `attemptLoop`. -/
theorem upToOfBound (next : S → Fin n → S) (P : S → Prop) (N a b : Nat) (x : S)
    (h : MomentBoundQ next P N a b x) (T : Nat) : MomentUpTo next P N a b x T :=
  fun t _ => h t

/-- Cross-multiplied comparison up to a horizon. Consumer: `attemptLoop`. -/
theorem upToCross (next : S → Fin n → S) (P : S → Prop) (N a b a' b' : Nat) (x : S) (T : Nat)
    (hb : 0 < b) (h1 : a * b' ≤ a' * b) (h : MomentUpTo next P N a b x T) :
    MomentUpTo next P N a' b' x T := by
  intro t ht
  have h2 := h t ht
  refine Nat.le_of_mul_le_mul_left ?_ hb
  calc b * (b' * momentNumerator next P N x t) = b' * (b * momentNumerator next P N x t) :=
        Nat.mul_left_comm _ _ _
    _ ≤ b' * (a * (n ^ t * (N - 1) ^ t)) := Nat.mul_le_mul_left _ h2
    _ = (a * b') * (n ^ t * (N - 1) ^ t) := by
        rw [← Nat.mul_assoc, Nat.mul_comm b' a]
    _ ≤ (a' * b) * (n ^ t * (N - 1) ^ t) := Nat.mul_le_mul_right _ h1
    _ = b * (a' * (n ^ t * (N - 1) ^ t)) := by
        rw [Nat.mul_comm a' b, Nat.mul_assoc]

/-- **Strong Markov composition up to a horizon.** Consumer: `momentSeqUpTo`. -/
theorem momentSeqCoreUpTo (next : S → Fin n → S) (P Q : S → Prop) (N a2 b2 T : Nat)
    (hba : b2 ≤ a2) (hQ : ∀ y, Q y → MomentUpTo next P N a2 b2 y T) :
    ∀ t, t ≤ T → ∀ y, b2 * momentNumerator next P N y t ≤ a2 * momentNumerator next Q N y t := by
  intro t
  induction t with
  | zero =>
    intro _ y
    rw [momentNumeratorZero, momentNumeratorZero]
    simpa using hba
  | succ t ih =>
    intro ht y
    by_cases hq : Q y
    · rw [momentNumeratorTerminal next Q N y hq]
      exact hQ y hq (t + 1) ht
    · by_cases hp : P y
      · rw [momentNumeratorTerminal next P N y hp]
        exact Nat.le_trans (Nat.mul_le_mul_right _ hba)
          (Nat.mul_le_mul_left _ (momentNumeratorGe next Q N (t + 1) y))
      · rw [momentNumeratorSucc next P N y hp, momentNumeratorSucc next Q N y hq]
        have h1 := sumLe (fun e => b2 * momentNumerator next P N (next y e) t)
          (fun e => a2 * momentNumerator next Q N (next y e) t)
          (fun e => ih (by omega) (next y e))
        rw [sumMulLeft, sumMulLeft] at h1
        calc b2 * (N * (List.ofFn fun e => momentNumerator next P N (next y e) t).sum)
            = N * (b2 * (List.ofFn fun e => momentNumerator next P N (next y e) t).sum) := by
              rw [Nat.mul_left_comm]
          _ ≤ N * (a2 * (List.ofFn fun e => momentNumerator next Q N (next y e) t).sum) :=
              Nat.mul_le_mul_left N h1
          _ = a2 * (N * (List.ofFn fun e => momentNumerator next Q N (next y e) t).sum) := by
              rw [Nat.mul_left_comm]

/-- **Moments multiply across a first hit, up to a horizon.** Consumer: `attemptLoop`. -/
theorem momentSeqUpTo (next : S → Fin n → S) (P Q : S → Prop) (N a1 b1 a2 b2 T : Nat) (x : S)
    (hba : b2 ≤ a2) (hQ : ∀ y, Q y → MomentUpTo next P N a2 b2 y T)
    (hx : MomentUpTo next Q N a1 b1 x T) :
    MomentUpTo next P N (a1 * a2) (b1 * b2) x T := by
  intro t ht
  have h1 := momentSeqCoreUpTo next P Q N a2 b2 T hba hQ t ht x
  have h2 := hx t ht
  calc b1 * b2 * momentNumerator next P N x t
      = b1 * (b2 * momentNumerator next P N x t) := Nat.mul_assoc _ _ _
    _ ≤ b1 * (a2 * momentNumerator next Q N x t) := Nat.mul_le_mul_left _ h1
    _ = a2 * (b1 * momentNumerator next Q N x t) := Nat.mul_left_comm _ _ _
    _ ≤ a2 * (a1 * (n ^ t * (N - 1) ^ t)) := Nat.mul_le_mul_left _ h2
    _ = a1 * a2 * (n ^ t * (N - 1) ^ t) := by
        rw [← Nat.mul_assoc, Nat.mul_comm a2 a1]

/-- **The fair race up to a horizon**: post-race bounds up to `T` give the race bound up to
`T + 1`. Consumer: `attemptLoop`. -/
theorem raceMomentUpTo (next : S → Fin n → S) (P Pend : S → Prop) (N D Fa Fb T : Nat)
    (a b : Fin n) (hab : a ≠ b) (hn : 2 ≤ n) (hN : n ≤ N) (hFa : D ≤ Fa) (hFb : D ≤ Fb)
    (hclosed : ∀ x, Pend x → ¬ P x → ∀ e, e ≠ a → e ≠ b → Pend (next x e))
    (ha : ∀ x, Pend x → ¬ P x → MomentUpTo next P N Fa D (next x a) T)
    (hb : ∀ x, Pend x → ¬ P x → MomentUpTo next P N Fb D (next x b) T) :
    ∀ x, Pend x → MomentUpTo next P N (N * (Fa + Fb)) ((2 * N - n) * D) x (T + 1) := by
  have hconst : (2 * N - n) * D ≤ N * (Fa + Fb) := by
    calc (2 * N - n) * D ≤ (2 * N) * D := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = N * (D + D) := by rw [Nat.mul_comm 2 N, Nat.mul_assoc, Nat.two_mul]
      _ ≤ N * (Fa + Fb) := Nat.mul_le_mul_left _ (Nat.add_le_add hFa hFb)
  intro x hx t ht
  induction t generalizing x with
  | zero =>
    rw [momentNumeratorZero]
    simpa using hconst
  | succ t ih =>
    by_cases hp : P x
    · rw [momentNumeratorTerminal next P N x hp]
      exact Nat.mul_le_mul_right _ hconst
    · rw [momentNumeratorSucc next P N x hp, xSucc]
      have hs := sumTwoLe (fun e => (2 * N - n) * D * momentNumerator next P N (next x e) t)
        a b hab (N * (Fa + Fb) * (n ^ t * (N - 1) ^ t))
        (fun e h1 h2 => ih (next x e) (hclosed x hx hp e h1 h2) (by omega))
      have hA : (2 * N - n) * D * momentNumerator next P N (next x a) t ≤
          (2 * N - n) * (Fa * (n ^ t * (N - 1) ^ t)) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (ha x hx hp t (by omega))
      have hB : (2 * N - n) * D * momentNumerator next P N (next x b) t ≤
          (2 * N - n) * (Fb * (n ^ t * (N - 1) ^ t)) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (hb x hx hp t (by omega))
      rw [sumMulLeft] at hs
      have e1 : 2 * N - n + (n - 2) * N = n * (N - 1) := by
        rw [Nat.sub_mul, Nat.mul_sub_one]
        have : 2 * N ≤ n * N := Nat.mul_le_mul_right N hn
        have : n ≤ n * N := Nat.le_mul_of_pos_right n (by omega)
        omega
      obtain ⟨X, hXd⟩ : ∃ X, X = n ^ t * (N - 1) ^ t := ⟨_, rfl⟩
      obtain ⟨sm, hsd⟩ : ∃ sm, sm = (List.ofFn fun e => momentNumerator next P N (next x e) t).sum :=
        ⟨_, rfl⟩
      rw [← hXd] at hs hA hB ⊢
      rw [← hsd] at hs ⊢
      calc (2 * N - n) * D * (N * sm) = N * ((2 * N - n) * D * sm) := by
            rw [Nat.mul_left_comm]
        _ ≤ N * ((2 * N - n) * (Fa * X) + (2 * N - n) * (Fb * X) +
              (n - 2) * (N * (Fa + Fb) * X)) :=
            Nat.mul_le_mul_left N (Nat.le_trans hs (Nat.add_le_add_right
              (Nat.add_le_add hA hB) _))
        _ = N * (Fa + Fb) * ((2 * N - n + (n - 2) * N) * X) := by
            simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm,
              Nat.mul_assoc]
        _ = N * (Fa + Fb) * (n * (N - 1) * X) := by rw [e1]

/-- **The horizon induction.** Consumer: `attemptLoop`. -/
theorem momentLoop (next : S → Fin n → S) (P A : S → Prop) (N c d : Nat) (hdc : d ≤ c)
    (hstep : ∀ T, (∀ y, A y → MomentUpTo next P N c d y T) →
      ∀ x, A x → MomentUpTo next P N c d x (T + 1)) :
    ∀ x, A x → MomentBoundQ next P N c d x := by
  have hall : ∀ T, ∀ y, A y → MomentUpTo next P N c d y T := by
    intro T
    induction T with
    | zero =>
      intro y _ t ht
      rw [Nat.le_zero.mp ht, momentNumeratorZero]
      simpa using hdc
    | succ T ih => exact hstep T ih
  intro x hx T
  exact hall T x hx T (Nat.le_refl _)

/-- **The renewal loop of one race per attempt.** From the attempt class `A` the first hit of `Q`
has moment `a₁/b₁`. At a `Q` state the target holds, or a success continuation with moment
`F_s/D` starts, or a race starts: a pending class closed under every letter but two distinct race
letters, the winning letter `e_a` with a success continuation of moment `F_a/D`, the losing letter
`e_b` back into `A`. If `a₁ · max(N (F_a + c), F_s (2N - n)) ≤ c · b₁ (2N - n)`, then
`E[z^τ] ≤ c / D` from every state of `A`. Consumer: the per-pair moment of Lemma e-packet
(`E[z^{T_pair}]`, Lemma e-max). -/
theorem attemptLoop (next : S → Fin n → S) (P A Q : S → Prop) (N a1 b1 Fs Fa c D : Nat)
    (hn : 2 ≤ n) (hN : n ≤ N) (hb1 : 0 < b1) (hD : 0 < D)
    (hDFs : D ≤ Fs) (hDFa : D ≤ Fa) (hDc : D ≤ c)
    (hprep : ∀ x, A x → MomentBoundQ next Q N a1 b1 x)
    (hQ : ∀ y, Q y → P y ∨ MomentBoundQ next P N Fs D y ∨
      ∃ (Pend : S → Prop) (ea eb : Fin n), Pend y ∧ ea ≠ eb ∧
        (∀ x, Pend x → ¬ P x → ∀ e, e ≠ ea → e ≠ eb → Pend (next x e)) ∧
        (∀ x, Pend x → ¬ P x → MomentBoundQ next P N Fa D (next x ea)) ∧
        (∀ x, Pend x → ¬ P x → A (next x eb)))
    (hclose : a1 * max (N * (Fa + c)) (Fs * (2 * N - n)) ≤ c * (b1 * (2 * N - n))) :
    ∀ x, A x → MomentBoundQ next P N c D x := by
  have hK : 0 < 2 * N - n := by omega
  refine momentLoop next P A N c D hDc fun T ih x hx => ?_
  have hm1 : N * (Fa + c) ≤ max (N * (Fa + c)) (Fs * (2 * N - n)) := Nat.le_max_left _ _
  have hm2 : Fs * (2 * N - n) ≤ max (N * (Fa + c)) (Fs * (2 * N - n)) := Nat.le_max_right _ _
  have hba : (2 * N - n) * D ≤ max (N * (Fa + c)) (Fs * (2 * N - n)) := by
    rw [Nat.mul_comm]; exact Nat.le_trans (Nat.mul_le_mul_right _ hDFs) hm2
  have hQ' : ∀ y, Q y → MomentUpTo next P N (max (N * (Fa + c)) (Fs * (2 * N - n)))
      ((2 * N - n) * D) y (T + 1) := by
    intro y hy
    rcases hQ y hy with hp | hs | ⟨Pend, ea, eb, hpy, hab, hcl, hwa, hwb⟩
    · intro t _
      rw [momentNumeratorTerminal next P N y hp]
      exact Nat.mul_le_mul_right _ hba
    · refine upToCross next P N Fs D _ _ y (T + 1) hD ?_ (upToOfBound next P N Fs D y hs _)
      calc Fs * ((2 * N - n) * D) = Fs * (2 * N - n) * D := by rw [Nat.mul_assoc]
        _ ≤ _ := Nat.mul_le_mul_right _ hm2
    · have hr := raceMomentUpTo next P Pend N D Fa c T ea eb hab hn hN hDFa hDc hcl
        (fun z hz hnp => upToOfBound next P N Fa D _ (hwa z hz hnp) T)
        (fun z hz hnp => ih _ (hwb z hz hnp)) y hpy
      refine upToCross next P N _ _ _ _ y (T + 1) (Nat.mul_pos hK hD) ?_ hr
      exact Nat.mul_le_mul_right _ hm1
  have hs := momentSeqUpTo next P Q N a1 b1 _ _ (T + 1) x hba hQ'
    (upToOfBound next Q N a1 b1 x (hprep x hx) _)
  refine upToCross next P N _ _ c D x (T + 1) (Nat.mul_pos hb1 (Nat.mul_pos hK hD)) ?_ hs
  calc a1 * max (N * (Fa + c)) (Fs * (2 * N - n)) * D
      ≤ c * (b1 * (2 * N - n)) * D := Nat.mul_le_mul_right _ hclose
    _ = c * (b1 * ((2 * N - n) * D)) := by
        simp only [Nat.mul_assoc]

end Horizon

end L3.PacketMomentHorizon

#print axioms L3.PacketMomentHorizon.momentSeqUpTo
#print axioms L3.PacketMomentHorizon.raceMomentUpTo
#print axioms L3.PacketMomentHorizon.momentLoop
#print axioms L3.PacketMomentHorizon.attemptLoop
