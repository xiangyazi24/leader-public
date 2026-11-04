import Leader.L3.Width.DigitPairMoment

/-!
# Exponential moments of first-hit times: potentials, composition, the fair race

Generic tools beside `L3.PairMoment.MomentBound` for the per-pair moment of Lemma e-max
(repair.tex 1421-1465). Notation: `z = N / (N-1)`, `X_T = n^T (N-1)^T`, and
`momentNumerator next P N x T = X_T · E[z^{min(τ,T)}]` (`L3.PairMoment`).

* `MomentBoundQ next P N a b x`: `E[z^τ] ≤ a / b` (every truncation); `momentBoundOfQ` gives
  the integer form `MomentBound` when `a ≤ A b`; `momentQMono` weakens it.
* `momentNumeratorSucc`, `momentNumeratorTerminal`, `momentNumeratorGe`: the one-step recursion
  `M(x, T+1) = N Σ_e M(next x e, T)` off the target, `M = X_T` on it, `M ≥ X_T`.
* `momentOfLyapunov`: a function `g ≥ D` with `N Σ_e g(next x e) ≤ n (N-1) g(x)` off the target
  gives `E[z^τ] ≤ g(x) / D` (the one-step supermartingale criterion, on an invariant set).
* **`momentOfPotential`**: a potential that never rises and drops on a nominated edge (so with
  probability `≥ 1/n` per step) gives `E[z^τ] ≤ w^{Φ x}`, `w = N / (N - n)`. With
  `N = n (2C+1)` this is the paper's `w = 1 + 1/(2C)` per obligation (`momentOfPotentialPair`).
* `momentSeq` (strong Markov at a first hit): `E[z^{τ_P}] ≤ (a₁/b₁)(a₂/b₂)` from a moment
  `a₁/b₁` to `Q` and a moment `a₂/b₂` from every `Q` state to `P`.
* **`raceMoment`** (the failure factorization): a pending class closed under every letter but
  two distinct race letters `a`, `b`; if after `a` the moment to `P` is at most `F_a / D` and
  after `b` at most `F_b / D`, uniformly over the attained states, then from every pending state
  `E[z^τ] ≤ N (F_a + F_b) / ((2N - n) D) ≤ (w/2)(F_a + F_b)/D` (`raceMomentHalf`). Each outcome
  enters with weight `N / (2N - n) ≤ w / 2`: the race wait is geometric with success `2/n`, and
  each edge wins it with probability `1/2` independently of the wait. This is the one-step
  (Markov) form of `L3.DigitPacketRace.raceFair`; with `F_b` the success continuation and `F_a`
  the failure continuation it is `E[z^D 1_fail] ≤ (y/2)(…)` of the paper.
-/

namespace L3.PacketMoment

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FixedSpanRenewalPayload
open L3.PairMoment

/-! ### Finite sums -/

/-- Pointwise equal summands. Consumer: `momentNumeratorSucc`, `wordSumMul`. -/
theorem sumEqFn {m : Nat} (f g : Fin m → Nat) (h : ∀ i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  rw [show f = g from funext h]

/-- One summand extracted. Consumer: `sumOneLe`, `sumTwoLe`. -/
theorem sumPointFn {m : Nat} (H : Fin m → Nat) (j : Fin m) :
    (List.ofFn H).sum = H j + (List.ofFn fun i => if i = j then 0 else H i).sum := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    cases j using Fin.cases with
    | zero =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons, if_pos rfl]
      have : (List.ofFn fun i : Fin m => if i.succ = (0 : Fin (m + 1)) then 0 else H i.succ) =
          List.ofFn fun i => H i.succ :=
        congrArg List.ofFn (funext fun i => if_neg (Fin.succ_ne_zero i))
      rw [this]
      omega
    | succ j =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
        ih (fun i => H i.succ) j, if_neg (Fin.succ_ne_zero j).symm]
      have : (List.ofFn fun i : Fin m => if i.succ = j.succ then 0 else H i.succ) =
          List.ofFn fun i => if i = j then 0 else H i.succ :=
        congrArg List.ofFn (funext fun i => by simp only [Fin.succ_inj])
      rw [this]
      omega

/-- A sum with one distinguished summand and the others bounded. Consumer:
`momentOfPotential`. -/
theorem sumOneLe {m : Nat} (h : Fin m → Nat) (c : Fin m) (M : Nat)
    (hr : ∀ e, e ≠ c → h e ≤ M) : (List.ofFn h).sum ≤ h c + (m - 1) * M := by
  rw [sumPointFn h c]
  have h1 := sumLe (fun e => if e = c then 0 else h e) (fun e => if e = c then 0 else M)
    (fun e => by
      by_cases he : e = c
      · rw [if_pos he, if_pos he]; exact Nat.le_refl _
      · rw [if_neg he, if_neg he]; exact hr e he)
  have h2 := sumPointFn (fun _ : Fin m => M) c
  rw [sumConst] at h2
  have h3 : (m - 1) * M = m * M - M := Nat.sub_one_mul m M
  omega

/-- A sum with two distinguished summands and the others bounded. Consumer: `raceMoment`. -/
theorem sumTwoLe {m : Nat} (h : Fin m → Nat) (a b : Fin m) (hab : a ≠ b) (M : Nat)
    (hr : ∀ e, e ≠ a → e ≠ b → h e ≤ M) : (List.ofFn h).sum ≤ h a + h b + (m - 2) * M := by
  have hba : b ≠ a := fun e => hab e.symm
  rw [sumPointFn h a, sumPointFn (fun e => if e = a then 0 else h e) b, if_neg hba]
  have h1 := sumLe (fun e => if e = b then 0 else (if e = a then 0 else h e))
    (fun e => if e = b then 0 else (if e = a then 0 else M))
    (fun e => by
      by_cases e1 : e = b
      · rw [if_pos e1, if_pos e1]; exact Nat.le_refl _
      · by_cases e2 : e = a
        · rw [if_neg e1, if_neg e1, if_pos e2, if_pos e2]; exact Nat.le_refl _
        · rw [if_neg e1, if_neg e1, if_neg e2, if_neg e2]; exact hr e e2 e1)
  have h2 := sumPointFn (fun _ : Fin m => M) a
  rw [sumConst, sumPointFn (fun e => if e = a then 0 else M) b, if_neg hba] at h2
  have h3 : (m - 2) * M = m * M - 2 * M := Nat.sub_mul m 2 M
  omega

/-! ### Word sums and the moment recursion -/

section Moment

variable {S : Type} {n : Nat}

/-- Constant factors leave word sums. Consumer: `momentNumeratorSucc`. -/
theorem wordSumMul (c : Nat) : ∀ (T : Nat) (f : List (Fin n) → Nat),
    wordSum n T (fun u => c * f u) = c * wordSum n T f := by
  intro T
  induction T with
  | zero => intro f; rfl
  | succ T ih =>
    intro f
    rw [wordSum_succ, wordSum_succ, sumEqFn _ _ (fun e => ih (fun u => f (e :: u)))]
    exact sumMulLeft c _

/-- Word sums of a function of the length. Consumer: `momentNumeratorTerminal`. -/
theorem wordSumLen : ∀ (T : Nat) (f : Nat → Nat),
    wordSum n T (fun u => f u.length) = n ^ T * f T := by
  intro T
  induction T with
  | zero => intro f; show f 0 = n ^ 0 * f 0; rw [Nat.pow_zero, Nat.one_mul]
  | succ T ih =>
    intro f
    rw [wordSum_succ, sumEqFn (fun e => wordSum n T fun u => f (e :: u).length)
      (fun _ => n ^ T * f (T + 1)) (fun e => ih (fun m => f (m + 1))),
      sumConst, Nat.pow_succ]
    rw [Nat.mul_comm (n ^ T) n, Nat.mul_assoc]

/-- `X_{T+1} = n (N-1) X_T`. Consumer: every recursion below. -/
theorem xSucc (N T : Nat) :
    n ^ (T + 1) * (N - 1) ^ (T + 1) = n * (N - 1) * (n ^ T * (N - 1) ^ T) := by
  rw [Nat.pow_succ, Nat.pow_succ]
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- One letter off the target multiplies the word weight by `N`. Consumer:
`momentNumeratorSucc`. -/
theorem momentWordCons (next : S → Fin n → S) (P : S → Prop) (N : Nat) (x : S) (hx : ¬ P x)
    (e : Fin n) (u : List (Fin n)) :
    momentWord next P N x (e :: u) = N * momentWord next P N (next x e) u := by
  have hc := costWord_le_length next P (next x e) u
  unfold momentWord
  rw [costWordCons next P x e u hx, List.length_cons,
    show u.length + 1 - (1 + costWord next P (next x e) u) =
      u.length - costWord next P (next x e) u by omega, Nat.pow_add, Nat.pow_one,
    Nat.mul_assoc]

/-- On the target the word weight is `(N-1)^L`. Consumer: `momentNumeratorTerminal`. -/
theorem momentWordTerminal (next : S → Fin n → S) (P : S → Prop) (N : Nat) (x : S) (hx : P x)
    (u : List (Fin n)) : momentWord next P N x u = (N - 1) ^ u.length := by
  unfold momentWord
  rw [costWord_terminal next P x hx u, Nat.pow_zero, Nat.one_mul, Nat.sub_zero]

/-- Consumer: `momentOfLyapunov`, `momentSeq`, `raceMoment`. -/
theorem momentNumeratorZero (next : S → Fin n → S) (P : S → Prop) (N : Nat) (x : S) :
    momentNumerator next P N x 0 = 1 := by
  show momentWord next P N x [] = 1
  have h := Nat.le_zero.mp (costWord_le_length next P x [])
  unfold momentWord
  rw [h]
  rfl

/-- **The moment recursion** off the target. Consumer: `momentOfLyapunov`, `momentSeq`,
`raceMoment`. -/
theorem momentNumeratorSucc (next : S → Fin n → S) (P : S → Prop) (N : Nat) (x : S)
    (hx : ¬ P x) (T : Nat) :
    momentNumerator next P N x (T + 1) =
      N * (List.ofFn fun e => momentNumerator next P N (next x e) T).sum := by
  unfold momentNumerator
  rw [wordSum_succ, sumEqFn _ (fun e => N * wordSum n T (momentWord next P N (next x e)))
    (fun e => by
      rw [show (fun u => momentWord next P N x (e :: u)) =
        fun u => N * momentWord next P N (next x e) u from
          funext (momentWordCons next P N x hx e)]
      exact wordSumMul N T _)]
  exact sumMulLeft N _

/-- On the target the moment numerator is `X_T`. Consumer: `momentOfLyapunov`, `momentSeq`. -/
theorem momentNumeratorTerminal (next : S → Fin n → S) (P : S → Prop) (N : Nat) (x : S)
    (hx : P x) (T : Nat) : momentNumerator next P N x T = n ^ T * (N - 1) ^ T := by
  unfold momentNumerator
  rw [show momentWord next P N x = fun u => (N - 1) ^ u.length from
    funext (momentWordTerminal next P N x hx)]
  exact wordSumLen T (fun m => (N - 1) ^ m)

/-- `E[z^{min(τ,T)}] ≥ 1`. Consumer: `momentSeq`. -/
theorem momentNumeratorGe (next : S → Fin n → S) (P : S → Prop) (N : Nat) :
    ∀ T x, n ^ T * (N - 1) ^ T ≤ momentNumerator next P N x T := by
  intro T
  induction T with
  | zero => intro x; rw [momentNumeratorZero]; simp
  | succ T ih =>
    intro x
    by_cases hx : P x
    · rw [momentNumeratorTerminal next P N x hx]; exact Nat.le_refl _
    · rw [momentNumeratorSucc next P N x hx, xSucc]
      have h1 := sumLe (fun _ : Fin n => n ^ T * (N - 1) ^ T)
        (fun e => momentNumerator next P N (next x e) T) (fun e => ih (next x e))
      rw [sumConst] at h1
      calc n * (N - 1) * (n ^ T * (N - 1) ^ T)
          = (N - 1) * (n * (n ^ T * (N - 1) ^ T)) := by
            rw [Nat.mul_comm n (N - 1), Nat.mul_assoc]
        _ ≤ N * (n * (n ^ T * (N - 1) ^ T)) := Nat.mul_le_mul_right _ (Nat.sub_le N 1)
        _ ≤ N * _ := Nat.mul_le_mul_left N h1

/-! ### Rational moment bounds -/

/-- `E[z^τ] ≤ a / b`, `z = N/(N-1)`, for the first hit of `P` from `x` (every truncation).
Consumer: `momentBoundOfQ` and every lemma below. -/
def MomentBoundQ (next : S → Fin n → S) (P : S → Prop) (N a b : Nat) (x : S) : Prop :=
  ∀ T, b * momentNumerator next P N x T ≤ a * (n ^ T * (N - 1) ^ T)

/-- The integer form. Consumer: `L3.PairMoment.simultaneousOfMoments` through the per-pair
moment. -/
theorem momentBoundOfQ (next : S → Fin n → S) (P : S → Prop) (N a b A : Nat) (x : S)
    (hb : 0 < b) (hab : a ≤ A * b) (h : MomentBoundQ next P N a b x) :
    MomentBound next P N A x := by
  intro T
  have h1 := h T
  have h2 : a * (n ^ T * (N - 1) ^ T) ≤ b * (A * (n ^ T * (N - 1) ^ T)) := by
    calc a * (n ^ T * (N - 1) ^ T) ≤ A * b * (n ^ T * (N - 1) ^ T) := Nat.mul_le_mul_right _ hab
      _ = b * (A * (n ^ T * (N - 1) ^ T)) := by
        rw [Nat.mul_comm A b, Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans h1 h2) hb

/-- Weakening. Consumer: `raceMomentHalf`. -/
theorem momentQMono (next : S → Fin n → S) (P : S → Prop) (N a b a' b' : Nat) (x : S)
    (ha : a ≤ a') (hb : b' ≤ b) (h : MomentBoundQ next P N a b x) :
    MomentBoundQ next P N a' b' x := fun T =>
  Nat.le_trans (Nat.mul_le_mul_right _ hb)
    (Nat.le_trans (h T) (Nat.mul_le_mul_right _ ha))

/-! ### The one-step criterion -/

/-- **Lyapunov criterion for exponential moments.** On a set `I` closed off the target, a
function `g ≥ D` with `N Σ_e g(next x e) ≤ n (N-1) g(x)` off the target bounds the moment:
`E[z^τ] ≤ g(x) / D`. Consumer: `momentOfPotential`. -/
theorem momentOfLyapunov (next : S → Fin n → S) (P I : S → Prop) (N D : Nat) (g : S → Nat)
    (hclosed : ∀ x, I x → ¬ P x → ∀ e, I (next x e)) (hge : ∀ x, I x → D ≤ g x)
    (hstep : ∀ x, I x → ¬ P x →
      N * (List.ofFn fun e => g (next x e)).sum ≤ n * (N - 1) * g x) :
    ∀ x, I x → MomentBoundQ next P N (g x) D x := by
  intro x hx T
  induction T generalizing x with
  | zero =>
    rw [momentNumeratorZero]
    simpa using hge x hx
  | succ T ih =>
    by_cases hp : P x
    · rw [momentNumeratorTerminal next P N x hp]
      exact Nat.mul_le_mul_right _ (hge x hx)
    · rw [momentNumeratorSucc next P N x hp, xSucc]
      have h1 := sumLe (fun e => D * momentNumerator next P N (next x e) T)
        (fun e => g (next x e) * (n ^ T * (N - 1) ^ T))
        (fun e => ih (next x e) (hclosed x hx hp e))
      rw [sumMulLeft] at h1
      have h2 : (List.ofFn fun e => g (next x e) * (n ^ T * (N - 1) ^ T)).sum =
          (List.ofFn fun e => g (next x e)).sum * (n ^ T * (N - 1) ^ T) := by
        rw [sumEqFn _ (fun e => (n ^ T * (N - 1) ^ T) * g (next x e))
          (fun e => Nat.mul_comm _ _), sumMulLeft, Nat.mul_comm]
      rw [h2] at h1
      have h3 := hstep x hx hp
      calc D * (N * (List.ofFn fun e => momentNumerator next P N (next x e) T).sum)
          = N * (D * (List.ofFn fun e => momentNumerator next P N (next x e) T).sum) := by
            rw [Nat.mul_left_comm]
        _ ≤ N * ((List.ofFn fun e => g (next x e)).sum * (n ^ T * (N - 1) ^ T)) :=
            Nat.mul_le_mul_left N h1
        _ = (N * (List.ofFn fun e => g (next x e)).sum) * (n ^ T * (N - 1) ^ T) := by
            rw [Nat.mul_assoc]
        _ ≤ (n * (N - 1) * g x) * (n ^ T * (N - 1) ^ T) := Nat.mul_le_mul_right _ h3
        _ = g x * (n * (N - 1) * (n ^ T * (N - 1) ^ T)) := by
            rw [Nat.mul_comm (n * (N - 1)) (g x), Nat.mul_assoc]

/-- The scaled weight `N^k (N-n)^{B-k}` is monotone in `k ≤ B`. Consumer:
`momentOfPotential`. -/
theorem potWMono (N m B k k' : Nat) (h1 : k ≤ k') (h2 : k' ≤ B) :
    N ^ k * (N - m) ^ (B - k) ≤ N ^ k' * (N - m) ^ (B - k') := by
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + d := ⟨k' - k, by omega⟩
  have hB : B - k = (B - (k + d)) + d := by omega
  rw [hB, Nat.pow_add, Nat.pow_add]
  have hp : (N - m) ^ d ≤ N ^ d := Nat.pow_le_pow_left (Nat.sub_le N m) d
  calc N ^ k * ((N - m) ^ (B - (k + d)) * (N - m) ^ d)
      = (N ^ k * (N - m) ^ (B - (k + d))) * (N - m) ^ d := by rw [Nat.mul_assoc]
    _ ≤ (N ^ k * (N - m) ^ (B - (k + d))) * N ^ d := Nat.mul_le_mul_left _ hp
    _ = N ^ k * N ^ d * (N - m) ^ (B - (k + d)) := by
      rw [Nat.mul_assoc, Nat.mul_comm ((N - m) ^ _) (N ^ d), ← Nat.mul_assoc]

/-- **A potential gives a geometric moment.** A potential that never rises off the target and
drops by at least one on a nominated edge (probability `≥ 1/n` per step) gives
`E[z^τ] ≤ w^{Φ x}`, `w = N/(N-n)`, from every state. Consumer: every obligation phase of
Lemma e-packet in the per-pair moment (release, the settled-empty cut, the renewal preparation,
the post-race completions). -/
theorem momentOfPotential (next : S → Fin n → S) (P : S → Prop) (N : Nat) (Φ : S → Nat)
    (chosen : S → Fin n) (hn : 1 ≤ n) (hN : n ≤ N)
    (hdrop : ∀ x, ¬ P x → Φ (next x (chosen x)) + 1 ≤ Φ x)
    (hnoninc : ∀ x, ¬ P x → ∀ e, Φ (next x e) ≤ Φ x) (x : S) :
    MomentBoundQ next P N (N ^ Φ x) ((N - n) ^ Φ x) x := by
  have key := momentOfLyapunov next P (fun y => Φ y ≤ Φ x) N ((N - n) ^ Φ x)
    (fun y => N ^ Φ y * (N - n) ^ (Φ x - Φ y))
    (fun y hy hp e => Nat.le_trans (hnoninc y hp e) hy)
    (fun y hy => by
      have h := potWMono N n (Φ x) 0 (Φ y) (Nat.zero_le _) hy
      simpa using h)
    (fun y hy hp => by
      have hd := hdrop y hp
      obtain ⟨φ, hφ⟩ : ∃ φ, Φ y = φ + 1 := ⟨Φ y - 1, by omega⟩
      have hs := sumOneLe (fun e => N ^ Φ (next y e) * (N - n) ^ (Φ x - Φ (next y e)))
        (chosen y) (N ^ Φ y * (N - n) ^ (Φ x - Φ y))
        (fun e _ => potWMono N n (Φ x) _ _ (hnoninc y hp e) hy)
      have hc := potWMono N n (Φ x) (Φ (next y (chosen y))) φ (by omega) (by omega)
      have hN1 : N ^ Φ y = N ^ φ * N := by rw [hφ, Nat.pow_succ]
      -- K = N^φ (N-n)^{B-φ-1}
      have hB : Φ x - φ = (Φ x - Φ y) + 1 := by omega
      rw [hB, Nat.pow_succ] at hc
      rw [hN1] at hs
      have hsum : N * (List.ofFn fun e =>
          N ^ Φ (next y e) * (N - n) ^ (Φ x - Φ (next y e))).sum ≤
          N * (N ^ φ * ((N - n) ^ (Φ x - Φ y) * (N - n)) +
            (n - 1) * (N ^ φ * N * (N - n) ^ (Φ x - Φ y))) :=
        Nat.mul_le_mul_left N (Nat.le_trans hs (Nat.add_le_add_right hc _))
      refine Nat.le_trans hsum (Nat.le_of_eq ?_)
      rw [hN1]
      have e1 : N - n + (n - 1) * N = n * (N - 1) := by
        rw [Nat.sub_one_mul, Nat.mul_sub_one]
        have : n ≤ n * N := Nat.le_mul_of_pos_right n (by omega)
        have : N ≤ n * N := Nat.le_mul_of_pos_left N (by omega)
        omega
      calc N * (N ^ φ * ((N - n) ^ (Φ x - Φ y) * (N - n)) +
            (n - 1) * (N ^ φ * N * (N - n) ^ (Φ x - Φ y)))
          = (N ^ φ * N * (N - n) ^ (Φ x - Φ y)) * (N - n + (n - 1) * N) := by
            simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ = n * (N - 1) * (N ^ φ * N * (N - n) ^ (Φ x - Φ y)) := by
            rw [e1, Nat.mul_comm])
    x (Nat.le_refl _)
  simpa using key

/-- The paper's form: with `N = n (2C+1)` each unit of potential costs the factor
`w = (2C+1)/(2C)`. Consumer: the per-pair moment (`w^{A_r} < 8`, `y = w^{C_r}`). -/
theorem momentOfPotentialPair (next : S → Fin n → S) (P : S → Prop) (C : Nat) (Φ : S → Nat)
    (chosen : S → Fin n) (hn : 1 ≤ n)
    (hdrop : ∀ x, ¬ P x → Φ (next x (chosen x)) + 1 ≤ Φ x)
    (hnoninc : ∀ x, ¬ P x → ∀ e, Φ (next x e) ≤ Φ x) (x : S) :
    MomentBoundQ next P (n * (2 * C + 1)) ((2 * C + 1) ^ Φ x) ((2 * C) ^ Φ x) x := by
  have h := momentOfPotential next P (n * (2 * C + 1)) Φ chosen hn
    (Nat.le_mul_of_pos_right n (by omega)) hdrop hnoninc x
  have e1 : n * (2 * C + 1) - n = n * (2 * C) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
  rw [e1, Nat.mul_pow, Nat.mul_pow] at h
  intro T
  have hpos : 0 < n ^ Φ x := Nat.pow_pos (by omega)
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  have := h T
  calc n ^ Φ x * ((2 * C) ^ Φ x * momentNumerator next P (n * (2 * C + 1)) x T)
      = n ^ Φ x * (2 * C) ^ Φ x * momentNumerator next P (n * (2 * C + 1)) x T := by
        rw [Nat.mul_assoc]
    _ ≤ n ^ Φ x * (2 * C + 1) ^ Φ x * (n ^ T * (n * (2 * C + 1) - 1) ^ T) := this
    _ = n ^ Φ x * ((2 * C + 1) ^ Φ x * (n ^ T * (n * (2 * C + 1) - 1) ^ T)) := by
        rw [Nat.mul_assoc]

/-! ### Composition at a first hit -/

/-- **Strong Markov composition.** If every `Q` state has moment at most `a₂/b₂` to `P`
(`b₂ ≤ a₂`), then from every state the moment to `P` is at most `a₂/b₂` times the moment to
`Q`, truncation by truncation. Consumer: `momentSeq`. -/
theorem momentSeqCore (next : S → Fin n → S) (P Q : S → Prop) (N a2 b2 : Nat)
    (hba : b2 ≤ a2) (hQ : ∀ y, Q y → MomentBoundQ next P N a2 b2 y) :
    ∀ T y, b2 * momentNumerator next P N y T ≤ a2 * momentNumerator next Q N y T := by
  intro T
  induction T with
  | zero =>
    intro y
    rw [momentNumeratorZero, momentNumeratorZero]
    simpa using hba
  | succ T ih =>
    intro y
    by_cases hq : Q y
    · rw [momentNumeratorTerminal next Q N y hq]
      exact hQ y hq (T + 1)
    · by_cases hp : P y
      · rw [momentNumeratorTerminal next P N y hp]
        exact Nat.le_trans (Nat.mul_le_mul_right _ hba)
          (Nat.mul_le_mul_left _ (momentNumeratorGe next Q N (T + 1) y))
      · rw [momentNumeratorSucc next P N y hp, momentNumeratorSucc next Q N y hq]
        have h1 := sumLe (fun e => b2 * momentNumerator next P N (next y e) T)
          (fun e => a2 * momentNumerator next Q N (next y e) T) (fun e => ih (next y e))
        rw [sumMulLeft, sumMulLeft] at h1
        calc b2 * (N * (List.ofFn fun e => momentNumerator next P N (next y e) T).sum)
            = N * (b2 * (List.ofFn fun e => momentNumerator next P N (next y e) T).sum) := by
              rw [Nat.mul_left_comm]
          _ ≤ N * (a2 * (List.ofFn fun e => momentNumerator next Q N (next y e) T).sum) :=
              Nat.mul_le_mul_left N h1
          _ = a2 * (N * (List.ofFn fun e => momentNumerator next Q N (next y e) T).sum) := by
              rw [Nat.mul_left_comm]

/-- **Moments multiply across a first hit**: `E[z^{τ_P}] ≤ (a₁/b₁)(a₂/b₂)`. Consumer: the
per-pair moment (preparation, then attempts; pre-race obligations, then the race). -/
theorem momentSeq (next : S → Fin n → S) (P Q : S → Prop) (N a1 b1 a2 b2 : Nat) (x : S)
    (hba : b2 ≤ a2) (hQ : ∀ y, Q y → MomentBoundQ next P N a2 b2 y)
    (hx : MomentBoundQ next Q N a1 b1 x) :
    MomentBoundQ next P N (a1 * a2) (b1 * b2) x := by
  intro T
  have h1 := momentSeqCore next P Q N a2 b2 hba hQ T x
  have h2 := hx T
  calc b1 * b2 * momentNumerator next P N x T
      = b1 * (b2 * momentNumerator next P N x T) := Nat.mul_assoc _ _ _
    _ ≤ b1 * (a2 * momentNumerator next Q N x T) := Nat.mul_le_mul_left _ h1
    _ = a2 * (b1 * momentNumerator next Q N x T) := Nat.mul_left_comm _ _ _
    _ ≤ a2 * (a1 * (n ^ T * (N - 1) ^ T)) := Nat.mul_le_mul_left _ h2
    _ = a1 * a2 * (n ^ T * (N - 1) ^ T) := by
        rw [← Nat.mul_assoc, Nat.mul_comm a2 a1]

/-! ### The fair race -/

/-- **The failure factorization (fair race, one-step form).** A pending class closed off the
target under every letter except two distinct race letters `a` and `b`; after `a` the moment to
the target is at most `F_a / D`, after `b` at most `F_b / D`, uniformly over the attained
states. Then from every pending state `E[z^τ] ≤ N (F_a + F_b) / ((2N - n) D)`: each outcome
enters with weight `N/(2N-n)`, the moment of a geometric race wait with success `2/n` times the
winning probability `1/2`. Consumer: `raceMomentHalf`, the per-pair moment (renewal trial). -/
theorem raceMoment (next : S → Fin n → S) (P Pend : S → Prop) (N D Fa Fb : Nat) (a b : Fin n)
    (hab : a ≠ b) (hn : 2 ≤ n) (hN : n ≤ N) (hFa : D ≤ Fa) (hFb : D ≤ Fb)
    (hclosed : ∀ x, Pend x → ¬ P x → ∀ e, e ≠ a → e ≠ b → Pend (next x e))
    (ha : ∀ x, Pend x → ¬ P x → MomentBoundQ next P N Fa D (next x a))
    (hb : ∀ x, Pend x → ¬ P x → MomentBoundQ next P N Fb D (next x b)) :
    ∀ x, Pend x → MomentBoundQ next P N (N * (Fa + Fb)) ((2 * N - n) * D) x := by
  have hconst : (2 * N - n) * D ≤ N * (Fa + Fb) := by
    calc (2 * N - n) * D ≤ (2 * N) * D := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = N * (D + D) := by rw [Nat.mul_comm 2 N, Nat.mul_assoc, Nat.two_mul]
      _ ≤ N * (Fa + Fb) := Nat.mul_le_mul_left _ (Nat.add_le_add hFa hFb)
  intro x hx T
  induction T generalizing x with
  | zero =>
    rw [momentNumeratorZero]
    simpa using hconst
  | succ T ih =>
    by_cases hp : P x
    · rw [momentNumeratorTerminal next P N x hp]
      exact Nat.mul_le_mul_right _ hconst
    · rw [momentNumeratorSucc next P N x hp, xSucc]
      have hs := sumTwoLe (fun e => (2 * N - n) * D * momentNumerator next P N (next x e) T)
        a b hab (N * (Fa + Fb) * (n ^ T * (N - 1) ^ T))
        (fun e h1 h2 => ih (next x e) (hclosed x hx hp e h1 h2))
      have hA : (2 * N - n) * D * momentNumerator next P N (next x a) T ≤
          (2 * N - n) * (Fa * (n ^ T * (N - 1) ^ T)) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (ha x hx hp T)
      have hB : (2 * N - n) * D * momentNumerator next P N (next x b) T ≤
          (2 * N - n) * (Fb * (n ^ T * (N - 1) ^ T)) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (hb x hx hp T)
      rw [sumMulLeft] at hs
      have e1 : 2 * N - n + (n - 2) * N = n * (N - 1) := by
        rw [Nat.sub_mul, Nat.mul_sub_one]
        have : 2 * N ≤ n * N := Nat.mul_le_mul_right N hn
        have : n ≤ n * N := Nat.le_mul_of_pos_right n (by omega)
        omega
      obtain ⟨X, hXd⟩ : ∃ X, X = n ^ T * (N - 1) ^ T := ⟨_, rfl⟩
      obtain ⟨sm, hsd⟩ : ∃ sm, sm = (List.ofFn fun e => momentNumerator next P N (next x e) T).sum :=
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

/-- The race factorization with the paper's `w/2`: `E[z^τ] ≤ (w/2)(F_a + F_b)/D`,
`w = N/(N-n)`. Consumer: the per-pair moment (`E[z^D 1_fail] ≤ y/2`). -/
theorem raceMomentHalf (next : S → Fin n → S) (P Pend : S → Prop) (N D Fa Fb : Nat)
    (a b : Fin n) (hab : a ≠ b) (hn : 2 ≤ n) (hN : n ≤ N) (hFa : D ≤ Fa) (hFb : D ≤ Fb)
    (hclosed : ∀ x, Pend x → ¬ P x → ∀ e, e ≠ a → e ≠ b → Pend (next x e))
    (ha : ∀ x, Pend x → ¬ P x → MomentBoundQ next P N Fa D (next x a))
    (hb : ∀ x, Pend x → ¬ P x → MomentBoundQ next P N Fb D (next x b)) (x : S)
    (hx : Pend x) :
    MomentBoundQ next P N (N * (Fa + Fb)) (2 * (N - n) * D) x :=
  momentQMono next P N _ _ _ _ x (Nat.le_refl _) (Nat.mul_le_mul_right _ (by omega))
    (raceMoment next P Pend N D Fa Fb a b hab hn hN hFa hFb hclosed ha hb x hx)

end Moment

end L3.PacketMoment

#print axioms L3.PacketMoment.sumOneLe
#print axioms L3.PacketMoment.sumTwoLe
#print axioms L3.PacketMoment.momentNumeratorSucc
#print axioms L3.PacketMoment.momentNumeratorTerminal
#print axioms L3.PacketMoment.momentNumeratorGe
#print axioms L3.PacketMoment.momentBoundOfQ
#print axioms L3.PacketMoment.momentOfLyapunov
#print axioms L3.PacketMoment.momentOfPotential
#print axioms L3.PacketMoment.momentOfPotentialPair
#print axioms L3.PacketMoment.momentSeq
#print axioms L3.PacketMoment.raceMoment
#print axioms L3.PacketMoment.raceMomentHalf
