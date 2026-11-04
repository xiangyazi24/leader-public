import Leader.Wu.Birth.LeafBoost

set_option autoImplicit false

/-! # Two-stage escape: reach a class, then escape from it

Stage one: from every `Good` state, at most a `(Q₁-1)/Q₁` fraction of the words of length `B₁` stay `Good` and
avoid the class `R` at every prefix endpoint (`avoidCount`).  Stage two: from every `Good` state in `R`, at most a
`(Q₂-1)/Q₂` fraction of the words of length `B₂` stay `Good` (`aliveCount`).  Then from every `Good` state at most a
`(Q₁ Q₂ - 1)/(Q₁ Q₂)` fraction of the words of length `B₁ + B₂` stay `Good` (`two_stage_escape`).  The proof is a
first-letter induction on `Q₂ * aliveCount x (k + B₂) ≤ n^B₂ * ((Q₂ - 1) n^k + avoidCount x k)`
(`two_stage_core`), using that words entering `R` are charged the stage-two mass after padding (`alive_pad`).
For B6: `R` = configurations with a ready train window, stage two = the proved window chain mass, stage one = the
open ready-window mass; with `BirthLeafBoost.escape_boost` the product mass `1/(Q₁ Q₂)` gives the leaf at horizon
`3 Q₁ Q₂ (B₁ + B₂)`.
-/

namespace BirthTwoStageEscape

open BirthLeaderlessBirthMassRenewal FiniteUniformStoppingTree

variable {S : Type} {n : Nat}

theorem wordSum_zero' : ∀ T : Nat, FixedSpanRenewalPayload.wordSum n T (fun _ => 0) = 0
  | 0 => by unfold FixedSpanRenewalPayload.wordSum; simp [allSchedules]
  | T + 1 => by
      rw [FixedSpanRenewalPayload.wordSum_succ]
      have h : (fun _ : Fin n => FixedSpanRenewalPayload.wordSum n T (fun _ => 0)) = (fun _ => 0) := by
        funext e; exact wordSum_zero' T
      simp only [h]
      rw [ofFn_sum_const]
      simp

theorem wordSum_le_pow : ∀ (T : Nat) (f : List (Fin n) → Nat), (∀ u, f u ≤ 1) →
    FixedSpanRenewalPayload.wordSum n T f ≤ n ^ T
  | 0, f, h => by
      unfold FixedSpanRenewalPayload.wordSum
      simp [allSchedules]
      exact h []
  | T + 1, f, h => by
      rw [FixedSpanRenewalPayload.wordSum_succ]
      calc (List.ofFn (fun e : Fin n => FixedSpanRenewalPayload.wordSum n T (fun u => f (e :: u)))).sum
          ≤ (List.ofFn (fun _ : Fin n => n ^ T)).sum :=
            ofFn_sum_le _ _ (fun e => wordSum_le_pow T _ (fun u => h (e :: u)))
        _ = n ^ (T + 1) := by rw [ofFn_sum_const, Nat.pow_succ, Nat.mul_comm]

/-! ## Alive counts -/

theorem aliveCount_not_good (step : S → Fin n → S) (Good : S → Prop) (x : S) (hx : ¬ Good x) (T : Nat) :
    aliveCount step Good x T = 0 := by
  unfold aliveCount
  have h : aliveBit step Good x = fun _ => 0 := by
    funext u
    classical
    unfold aliveBit
    have : ¬ AliveAlong step Good x u := fun h => hx (aliveAlong_good h)
    simp [this]
  rw [h, wordSum_zero']

theorem aliveCount_succ (step : S → Fin n → S) (Good : S → Prop) (x : S) (hx : Good x) (T : Nat) :
    aliveCount step Good x (T + 1) = (List.ofFn (fun e : Fin n => aliveCount step Good (step x e) T)).sum := by
  unfold aliveCount
  rw [FixedSpanRenewalPayload.wordSum_succ]
  apply ofFn_sum_eq
  intro e
  have h : (fun u => aliveBit step Good x (e :: u)) = aliveBit step Good (step x e) := by
    funext u
    classical
    unfold aliveBit
    simp [AliveAlong, hx]
  rw [h]

theorem aliveCount_le_pow (step : S → Fin n → S) (Good : S → Prop) (x : S) (T : Nat) :
    aliveCount step Good x T ≤ n ^ T :=
  wordSum_le_pow T _ (fun u => aliveBit_le_one step Good x u)

/-- Staying alive for `T + m` letters requires staying alive for the first `T`. -/
theorem alive_pad (step : S → Fin n → S) (Good : S → Prop) (m : Nat) :
    ∀ (T : Nat) (x : S), aliveCount step Good x (T + m) ≤ aliveCount step Good x T * n ^ m
  | 0, x => by
      by_cases hx : Good x
      · have h0 : aliveCount step Good x 0 = 1 := by
          unfold aliveCount FixedSpanRenewalPayload.wordSum
          classical
          simp [allSchedules, aliveBit, AliveAlong, hx]
        rw [h0, Nat.one_mul, Nat.zero_add]
        exact aliveCount_le_pow step Good x m
      · rw [aliveCount_not_good step Good x hx, aliveCount_not_good step Good x hx]
        simp
  | T + 1, x => by
      by_cases hx : Good x
      · rw [show T + 1 + m = (T + m) + 1 by omega, aliveCount_succ step Good x hx, aliveCount_succ step Good x hx]
        calc (List.ofFn (fun e : Fin n => aliveCount step Good (step x e) (T + m))).sum
            ≤ (List.ofFn (fun e : Fin n => n ^ m * aliveCount step Good (step x e) T)).sum :=
              ofFn_sum_le _ _ (fun e => by rw [Nat.mul_comm]; exact alive_pad step Good m T (step x e))
          _ = n ^ m * (List.ofFn (fun e : Fin n => aliveCount step Good (step x e) T)).sum := ofFn_sum_mul_left _ _
          _ = _ := Nat.mul_comm _ _
      · rw [aliveCount_not_good step Good x hx, aliveCount_not_good step Good x hx]
        simp

/-! ## Avoiding a class -/

/-- Every prefix endpoint is `Good` and outside `R`. -/
def AvoidAlong (step : S → Fin n → S) (Good R : S → Prop) (x : S) : List (Fin n) → Prop
  | [] => Good x ∧ ¬ R x
  | e :: u => (Good x ∧ ¬ R x) ∧ AvoidAlong step Good R (step x e) u

noncomputable def avoidBit (step : S → Fin n → S) (Good R : S → Prop) (x : S) (u : List (Fin n)) : Nat := by
  classical
  exact if AvoidAlong step Good R x u then 1 else 0

noncomputable def avoidCount (step : S → Fin n → S) (Good R : S → Prop) (x : S) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (avoidBit step Good R x)

theorem avoidAlong_head {step : S → Fin n → S} {Good R : S → Prop} {x : S} :
    ∀ {u : List (Fin n)}, AvoidAlong step Good R x u → Good x ∧ ¬ R x
  | [], h => h
  | _ :: _, h => h.1

theorem avoidCount_zero_of (step : S → Fin n → S) (Good R : S → Prop) (x : S) (hx : ¬ (Good x ∧ ¬ R x))
    (T : Nat) : avoidCount step Good R x T = 0 := by
  unfold avoidCount
  have h : avoidBit step Good R x = fun _ => 0 := by
    funext u
    classical
    unfold avoidBit
    have : ¬ AvoidAlong step Good R x u := fun h => hx (avoidAlong_head h)
    simp [this]
  rw [h, wordSum_zero']

theorem avoidCount_succ (step : S → Fin n → S) (Good R : S → Prop) (x : S) (hx : Good x ∧ ¬ R x) (T : Nat) :
    avoidCount step Good R x (T + 1) =
      (List.ofFn (fun e : Fin n => avoidCount step Good R (step x e) T)).sum := by
  unfold avoidCount
  rw [FixedSpanRenewalPayload.wordSum_succ]
  apply ofFn_sum_eq
  intro e
  have h : (fun u => avoidBit step Good R x (e :: u)) = avoidBit step Good R (step x e) := by
    funext u
    classical
    unfold avoidBit
    simp [AvoidAlong, hx]
  rw [h]

theorem avoidCount_zero (step : S → Fin n → S) (Good R : S → Prop) (x : S) (hx : Good x ∧ ¬ R x) :
    avoidCount step Good R x 0 = 1 := by
  unfold avoidCount FixedSpanRenewalPayload.wordSum
  classical
  simp [allSchedules, avoidBit, AvoidAlong, hx]

/-! ## The two-stage bound -/

theorem two_stage_core (step : S → Fin n → S) (Good R : S → Prop) (B₂ Q₂ : Nat) (hQ₂ : 1 ≤ Q₂)
    (h2 : ∀ x, Good x → R x → Q₂ * aliveCount step Good x B₂ ≤ (Q₂ - 1) * n ^ B₂) :
    ∀ (k : Nat) (x : S),
      Q₂ * aliveCount step Good x (k + B₂) ≤ n ^ B₂ * ((Q₂ - 1) * n ^ k + avoidCount step Good R x k)
  | 0, x => by
      rw [Nat.zero_add, Nat.pow_zero, Nat.mul_one]
      by_cases hg : Good x
      · by_cases hr : R x
        · rw [avoidCount_zero_of step Good R x (fun h => h.2 hr), Nat.add_zero, Nat.mul_comm (n ^ B₂)]
          exact h2 x hg hr
        · rw [avoidCount_zero step Good R x ⟨hg, hr⟩]
          have hb := aliveCount_le_pow step Good x B₂
          have e : Q₂ - 1 + 1 = Q₂ := by omega
          rw [e]
          rw [Nat.mul_comm (n ^ B₂)]
          exact Nat.mul_le_mul_left _ hb
      · rw [aliveCount_not_good step Good x hg]
        simp
  | k + 1, x => by
      by_cases hg : Good x
      · by_cases hr : R x
        · rw [avoidCount_zero_of step Good R x (fun h => h.2 hr), Nat.add_zero]
          have hp := alive_pad step Good (k + 1) B₂ x
          rw [show B₂ + (k + 1) = k + 1 + B₂ by omega] at hp
          have h2x := h2 x hg hr
          calc Q₂ * aliveCount step Good x (k + 1 + B₂)
              ≤ Q₂ * (aliveCount step Good x B₂ * n ^ (k + 1)) := Nat.mul_le_mul_left _ hp
            _ = (Q₂ * aliveCount step Good x B₂) * n ^ (k + 1) := by rw [Nat.mul_assoc]
            _ ≤ ((Q₂ - 1) * n ^ B₂) * n ^ (k + 1) := Nat.mul_le_mul_right _ h2x
            _ = n ^ B₂ * ((Q₂ - 1) * n ^ (k + 1)) := by
                rw [Nat.mul_comm (Q₂ - 1) (n ^ B₂), Nat.mul_assoc]
        · rw [show k + 1 + B₂ = (k + B₂) + 1 by omega, aliveCount_succ step Good x hg,
            avoidCount_succ step Good R x ⟨hg, hr⟩]
          rw [← ofFn_sum_mul_left]
          calc (List.ofFn (fun e : Fin n => Q₂ * aliveCount step Good (step x e) (k + B₂))).sum
              ≤ (List.ofFn (fun e : Fin n =>
                  n ^ B₂ * ((Q₂ - 1) * n ^ k) + n ^ B₂ * avoidCount step Good R (step x e) k)).sum :=
                ofFn_sum_le _ _ (fun e => by
                  have := two_stage_core step Good R B₂ Q₂ hQ₂ h2 k (step x e)
                  rw [Nat.mul_add] at this
                  exact this)
            _ = n * (n ^ B₂ * ((Q₂ - 1) * n ^ k)) +
                n ^ B₂ * (List.ofFn (fun e : Fin n => avoidCount step Good R (step x e) k)).sum := by
                rw [ofFn_sum_add, ofFn_sum_const, ofFn_sum_mul_left]
            _ = n ^ B₂ * ((Q₂ - 1) * n ^ (k + 1) +
                (List.ofFn (fun e : Fin n => avoidCount step Good R (step x e) k)).sum) := by
                rw [Nat.mul_add, Nat.pow_succ]
                congr 1
                simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      · rw [aliveCount_not_good step Good x hg]
        simp

theorem two_stage_escape (step : S → Fin n → S) (Good R : S → Prop) (B₁ B₂ Q₁ Q₂ : Nat)
    (hQ₁ : 1 ≤ Q₁) (hQ₂ : 1 ≤ Q₂)
    (h1 : ∀ x, Good x → Q₁ * avoidCount step Good R x B₁ ≤ (Q₁ - 1) * n ^ B₁)
    (h2 : ∀ x, Good x → R x → Q₂ * aliveCount step Good x B₂ ≤ (Q₂ - 1) * n ^ B₂) :
    UniformEscapeMass step Good (B₁ + B₂) (Q₁ * Q₂) := by
  intro x hx
  have hc := two_stage_core step Good R B₂ Q₂ hQ₂ h2 B₁ x
  have ha := h1 x hx
  generalize aliveCount step Good x (B₁ + B₂) = A at hc ⊢
  generalize avoidCount step Good R x B₁ = V at hc ha
  have hN : n ^ (B₁ + B₂) = n ^ B₂ * n ^ B₁ := by rw [Nat.pow_add, Nat.mul_comm]
  rw [hN]
  generalize n ^ B₂ = M at hc ⊢
  generalize n ^ B₁ = N at hc ha ⊢
  -- hc : Q₂ * A ≤ M * ((Q₂ - 1) * N + V), ha : Q₁ * V ≤ (Q₁ - 1) * N
  have s1 : Q₁ * (Q₂ * A) ≤ M * (Q₁ * ((Q₂ - 1) * N) + Q₁ * V) := by
    calc Q₁ * (Q₂ * A) ≤ Q₁ * (M * ((Q₂ - 1) * N + V)) := Nat.mul_le_mul_left _ hc
      _ = M * (Q₁ * ((Q₂ - 1) * N) + Q₁ * V) := by
          rw [Nat.mul_left_comm, Nat.mul_add]
  have s2 : M * (Q₁ * ((Q₂ - 1) * N) + Q₁ * V) ≤ M * (Q₁ * ((Q₂ - 1) * N) + (Q₁ - 1) * N) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left ha _)
  have e3 : Q₁ * ((Q₂ - 1) * N) + (Q₁ - 1) * N = (Q₁ * Q₂ - 1) * N := by
    have hq : Q₁ * (Q₂ - 1) + (Q₁ - 1) = Q₁ * Q₂ - 1 := by
      have h' : Q₁ * (Q₂ - 1) = Q₁ * Q₂ - Q₁ := Nat.mul_sub_one Q₁ Q₂
      have hle : Q₁ ≤ Q₁ * Q₂ := Nat.le_mul_of_pos_right Q₁ hQ₂
      omega
    rw [← Nat.mul_assoc, ← Nat.add_mul, hq]
  rw [e3] at s2
  calc Q₁ * Q₂ * A = Q₁ * (Q₂ * A) := Nat.mul_assoc _ _ _
    _ ≤ M * ((Q₁ * Q₂ - 1) * N) := Nat.le_trans s1 s2
    _ = (Q₁ * Q₂ - 1) * (M * N) := by rw [Nat.mul_left_comm]

end BirthTwoStageEscape
