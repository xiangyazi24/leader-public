import Leader.L4.Height.Trial
import Leader.L4.Height.Couple

namespace L4.Height

open Classical

/-- Replace an opposing active side by its prescribed mate. -/
def steerEdge {α : Type} {n : Nat}
    (active preferred : α → Fin n → Bool)
    (mate : α → Fin n → Fin n)
    (x : α) (e : Fin n) : Fin n :=
  if active x e && !preferred x e then mate x e else e

/-- Steering is recomputed at the state reached by the emitted label. -/
def steerWord {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (active preferred : α → Fin n → Bool)
    (mate : α → Fin n → Fin n) :
    α → List (Fin n) → List (Fin n)
  | _, [] => []
  | x, e :: u =>
      let f := steerEdge active preferred mate x e
      f :: steerWord next active preferred mate (next x f) u

/-- Count all prescribed active sides on the unmodified word. -/
def steeringCount {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (active : α → Fin n → Bool) :
    α → List (Fin n) → Nat
  | _, [] => 0
  | x, e :: u =>
      (active x e).toNat +
        steeringCount next active (next x e) u

/-- The number of raw one-letter preimages of an emitted label. -/
def steeringFactor {α : Type} {n : Nat}
    (active preferred : α → Fin n → Bool)
    (x : α) (e : Fin n) : Nat :=
  if active x e then
    if preferred x e then 2 else 0
  else 1

/-- Multiplicity of an emitted word, with states following its letters. -/
def steeringMultiplicity {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (active preferred : α → Fin n → Bool) :
    α → List (Fin n) → Nat
  | _, [] => 1
  | x, e :: u =>
      steeringFactor active preferred x e *
        steeringMultiplicity next active preferred (next x e) u

/-- Active status is constant on each mate orbit. -/
private theorem active_mate_eq {α : Type} {n : Nat}
    (active : α → Fin n → Bool)
    (mate : α → Fin n → Fin n)
    (hMate : ∀ x e, mate x (mate x e) = e)
    (hActive : ∀ x e, active x e = true →
      active x (mate x e) = true)
    (x : α) (e : Fin n) :
    active x (mate x e) = active x e := by
  cases ha : active x e with
  | false =>
      cases hb : active x (mate x e) with
      | false =>
          rfl
      | true =>
          have hback := hActive x (mate x e) hb
          rw [hMate x e] at hback
          simp [ha] at hback
  | true =>
      simpa [ha] using hActive x e ha

/-- Exact one-letter pushforward, with multiplicity and no inequalities. -/
private theorem steerEdge_sum {α : Type} {n : Nat}
    (active preferred : α → Fin n → Bool)
    (mate : α → Fin n → Fin n)
    (hMate : ∀ x e, mate x (mate x e) = e)
    (hActive : ∀ x e, active x e = true →
      active x (mate x e) = true)
    (hSide : ∀ x e, active x e = true →
      preferred x (mate x e) = !(preferred x e))
    (x : α) (f : Fin n → Nat) :
    (List.ofFn (fun e => f (steerEdge active preferred mate x e))).sum =
      (List.ofFn (fun e =>
        steeringFactor active preferred x e * f e)).sum := by
  let bad : Fin n → Bool :=
    fun e => active x e && !preferred x e
  let good : Fin n → Bool :=
    fun e => active x e && preferred x e
  let extra : Fin n → Nat :=
    fun e => if bad e then f (mate x e) else 0
  have hbadGood : ∀ e, bad (mate x e) = good e := by
    intro e
    dsimp [bad, good]
    rw [active_mate_eq active mate hMate hActive x e]
    cases ha : active x e with
    | false =>
        simp
    | true =>
        rw [hSide x e ha]
        cases hp : preferred x e <;> simp
  have hperm :
      (List.ofFn extra).sum =
        (List.ofFn (fun e => if good e then f e else 0)).sum := by
    calc
      (List.ofFn extra).sum =
          (List.ofFn (fun e => extra (mate x e))).sum := by
            exact (Couple.sum_ofFn_relabel
              (mate x) (mate x) (hMate x) (hMate x) extra).symm
      _ = (List.ofFn (fun e =>
            if good e then f e else 0)).sum := by
              apply sum_ofFn_eq
              intro e
              change (if bad (mate x e) then
                f (mate x (mate x e)) else 0) =
                (if good e then f e else 0)
              rw [hbadGood e, hMate x e]
  calc
    (List.ofFn (fun e =>
      f (steerEdge active preferred mate x e))).sum =
        (List.ofFn (fun e =>
          (if bad e then 0 else f e) + extra e)).sum := by
            apply sum_ofFn_eq
            intro e
            change f (if bad e then mate x e else e) =
              (if bad e then 0 else f e) +
                (if bad e then f (mate x e) else 0)
            cases hb : bad e <;> simp
    _ = (List.ofFn (fun e =>
          if bad e then 0 else f e)).sum +
        (List.ofFn extra).sum := sum_ofFn_add _ extra
    _ = (List.ofFn (fun e =>
          if bad e then 0 else f e)).sum +
        (List.ofFn (fun e =>
          if good e then f e else 0)).sum := by
            rw [hperm]
    _ = (List.ofFn (fun e =>
          (if bad e then 0 else f e) +
            (if good e then f e else 0))).sum :=
              (sum_ofFn_add _ _).symm
    _ = (List.ofFn (fun e =>
          steeringFactor active preferred x e * f e)).sum := by
            apply sum_ofFn_eq
            intro e
            cases ha : active x e <;>
              cases hp : preferred x e <;>
              simp [bad, good, steeringFactor, ha, hp] <;> omega

/-- Exact pushforward identity for arbitrary natural-number word weights.
Every future state follows the emitted label, not the raw preimage. -/
theorem steerWord_pushforward {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (active preferred : α → Fin n → Bool)
    (mate : α → Fin n → Fin n)
    (hMate : ∀ x e, mate x (mate x e) = e)
    (hActive : ∀ x e, active x e = true →
      active x (mate x e) = true)
    (hSide : ∀ x e, active x e = true →
      preferred x (mate x e) = !(preferred x e)) :
    ∀ (t : Nat) (x : α) (weight : List (Fin n) → Nat),
      wordSum (fun u =>
        weight (steerWord next active preferred mate x u)) t =
      wordSum (fun v =>
        steeringMultiplicity next active preferred x v * weight v) t := by
  intro t
  induction t with
  | zero =>
      intro x weight
      simp [wordSum, steerWord, steeringMultiplicity]
  | succ t ih =>
      intro x weight
      let F : Fin n → Nat := fun e =>
        wordSum (fun v =>
          steeringMultiplicity next active preferred (next x e) v *
            weight (e :: v)) t
      calc
        wordSum (fun u =>
          weight (steerWord next active preferred mate x u)) (t + 1) =
            (List.ofFn (fun e : Fin n =>
              F (steerEdge active preferred mate x e))).sum := by
                simp only [wordSum]
                apply sum_ofFn_eq
                intro e
                change wordSum (fun v =>
                  weight (steerEdge active preferred mate x e ::
                    steerWord next active preferred mate
                      (next x (steerEdge active preferred mate x e)) v)) t =
                  F (steerEdge active preferred mate x e)
                exact ih (next x (steerEdge active preferred mate x e))
                  (fun v => weight (steerEdge active preferred mate x e :: v))
        _ = (List.ofFn (fun e : Fin n =>
              steeringFactor active preferred x e * F e)).sum :=
                steerEdge_sum active preferred mate
                  hMate hActive hSide x F
        _ = wordSum (fun v =>
              steeringMultiplicity next active preferred x v *
                weight v) (t + 1) := by
                  simp only [wordSum]
                  apply sum_ofFn_eq
                  intro e
                  simpa only [steeringMultiplicity, Nat.mul_assoc] using
                    ((wordSum_mul_left (n := n)
                      (steeringFactor active preferred x e)
                      (fun v =>
                        steeringMultiplicity next active preferred
                          (next x e) v * weight (e :: v)) t).symm)

/-- A geometric doubling identity for an additional active decision. -/
private theorem steering_pow_one_add (c : Nat) :
    2 * 2 ^ c = 2 ^ (1 + c) := by
  rw [Nat.add_comm 1 c, Nat.pow_succ, Nat.mul_comm]

/-- An output word with d active prescribed sides has at most 2^d preimages. -/
theorem steeringMultiplicity_le_pow {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (active preferred : α → Fin n → Bool) :
    ∀ (x : α) (u : List (Fin n)),
      steeringMultiplicity next active preferred x u ≤
        2 ^ steeringCount next active x u := by
  intro x u
  induction u generalizing x with
  | nil =>
      exact Nat.le_refl _
  | cons e u ih =>
      cases ha : active x e with
      | false =>
          simpa [steeringMultiplicity, steeringCount,
            steeringFactor, ha] using ih (next x e)
      | true =>
          cases hp : preferred x e with
          | false =>
              simp [steeringMultiplicity, steeringCount,
                steeringFactor, ha, hp]
          | true =>
              calc
                steeringMultiplicity next active preferred x (e :: u) =
                    2 * steeringMultiplicity next active preferred
                      (next x e) u := by
                        simp [steeringMultiplicity, steeringFactor, ha, hp]
                _ ≤ 2 * 2 ^ steeringCount next active (next x e) u :=
                  Nat.mul_le_mul_left 2 (ih (next x e))
                _ = 2 ^ steeringCount next active x (e :: u) := by
                  simpa [steeringCount, ha] using
                    (steering_pow_one_add
                      (steeringCount next active (next x e) u))

/-- Restoring every prescribed FIRST side costs at most 2^b in raw words,
where the budget counts even an active side already preferred. -/
theorem restore_prescribed_sides {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (active preferred : α → Fin n → Bool)
    (mate : α → Fin n → Fin n)
    (hMate : ∀ x e, mate x (mate x e) = e)
    (hActive : ∀ x e, active x e = true →
      active x (mate x e) = true)
    (hSide : ∀ x e, active x e = true →
      preferred x (mate x e) = !(preferred x e))
    (x : α) (E : List (Fin n) → Prop) (t b : Nat)
    (hBudget : ∀ u, u.length = t → E u →
      steeringCount next active x u ≤ b) :
    wordSum (fun u =>
      if E (steerWord next active preferred mate x u) then 1 else 0) t ≤
    2 ^ b * wordSum (fun u => if E u then 1 else 0) t := by
  have hpush := steerWord_pushforward
    next active preferred mate hMate hActive hSide t x
    (fun u => if E u then 1 else 0)
  calc
    wordSum (fun u =>
      if E (steerWord next active preferred mate x u) then 1 else 0) t =
        wordSum (fun u =>
          steeringMultiplicity next active preferred x u *
            (if E u then 1 else 0)) t := hpush
    _ ≤ wordSum (fun u =>
          2 ^ b * (if E u then 1 else 0)) t := by
            apply wordSum_mono_on_length
            intro u hu
            by_cases hE : E u
            · have hc := hBudget u hu hE
              have hm := steeringMultiplicity_le_pow
                next active preferred x u
              have hp : 2 ^ steeringCount next active x u ≤ 2 ^ b :=
                Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hc
              simpa [hE] using Nat.le_trans hm hp
            · simp [hE]
    _ = 2 ^ b *
          wordSum (fun u => if E u then 1 else 0) t := by
            exact wordSum_mul_left (n := n) (2 ^ b)
              (fun u => if E u then 1 else 0) t

end L4.Height

