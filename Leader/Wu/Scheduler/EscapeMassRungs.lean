import Leader.Wu.Birth.TwoStageEscape
import Leader.Core.GlobalGapComposition

set_option autoImplicit false

namespace ZZFirstMassBound

open BirthLeaderlessBirthMassRenewal
open FiniteUniformStoppingTree

/-! ## Enumeration smoke checks -/

/-- The existing scheduler enumeration really has the advertised denominator. -/
theorem allSchedules_cardinality (n T : Nat) :
    (allSchedules n T).length = n ^ T :=
  allSchedules_length n T

/-- Every word appearing in that enumeration really has the requested horizon. -/
theorem allSchedules_exact_length (n T : Nat) :
    ∀ u ∈ allSchedules n T, u.length = T :=
  allSchedules_schedule_length n T

/-! ## Small local helpers -/

/-- Zero-horizon `aliveCount` is one at a Good state.
This is the same kernel proof shape already used inside `BirthTwoStageEscape.alive_pad`. -/
private theorem aliveCount_zero_of_good
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (Good : S → Prop)
    (x : S) (hx : Good x) :
    aliveCount step Good x 0 = 1 := by
  unfold aliveCount FixedSpanRenewalPayload.wordSum
  classical
  simp [allSchedules, aliveBit, AliveAlong, hx]

/-- Natural predecessor times a common factor, under positivity. -/
private theorem pred_mul (m c : Nat) (hm : 0 < m) :
    m * c = c + (m - 1) * c := by
  obtain ⟨d, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp [Nat.succ_mul, Nat.add_comm]

/-- Expand the Core `List.ofFn` sum over `Fin 2`. -/
private theorem fin2_sum (f : Fin 2 → Nat) :
    (List.ofFn f).sum = f (0 : Fin 2) + f (1 : Fin 2) := by
  rw [List.ofFn_succ, List.sum_cons,
    List.ofFn_succ, List.sum_cons]
  simp

/-! ## Rung 1: every letter immediately leaves Good -/

/-- The first escaping letter already contradicts `AliveAlong` on every
nonempty word.  This proof reasons about the Prop directly; there is no `decide`. -/
theorem every_letter_escape_kills_cons
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (Good : S → Prop)
    (hEscape : ∀ y, Good y → ∀ e : Fin n, ¬ Good (step y e))
    (x : S) (hx : Good x) (e : Fin n) (u : List (Fin n)) :
    ¬ AliveAlong step Good x (e :: u) := by
  intro h
  have ht : AliveAlong step Good (step x e) u := h.2
  exact hEscape x hx e (aliveAlong_good ht)

/-- If every scheduler letter leaves `Good`, no positive-length scheduler word
is alive. -/
theorem rung1_aliveCount_zero
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (Good : S → Prop)
    (hEscape : ∀ y, Good y → ∀ e : Fin n, ¬ Good (step y e))
    (x : S) (hx : Good x) (L : Nat) (hL : 1 ≤ L) :
    aliveCount step Good x L = 0 := by
  obtain ⟨T, hT⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  subst L
  change aliveCount step Good x (T + 1) = 0
  rw [BirthTwoStageEscape.aliveCount_succ step Good x hx T]
  calc
    (List.ofFn (fun e : Fin n =>
        aliveCount step Good (step x e) T)).sum =
        (List.ofFn (fun _ : Fin n => 0)).sum := by
      apply ofFn_sum_eq
      intro e
      exact BirthTwoStageEscape.aliveCount_not_good
        step Good (step x e) (hEscape x hx e) T
    _ = n * 0 := ofFn_sum_const n 0
    _ = 0 := Nat.mul_zero n

/-- First mass bound from a protocol property rather than from another mass bound. -/
theorem rung1_uniformEscapeMass
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (Good : S → Prop)
    (hEscape : ∀ y, Good y → ∀ e : Fin n, ¬ Good (step y e))
    (L Q : Nat) (hL : 1 ≤ L) :
    UniformEscapeMass step Good L Q := by
  intro x hx
  rw [rung1_aliveCount_zero step Good hEscape x hx L hL]
  simp

/-! ## Rung 2: a two-letter scheduler with one escape and one stutter -/

inductive Rung2State where
  | good
  | bad

/-- Only the `good` state belongs to the live set. -/
def rung2Good : Rung2State → Prop
  | .good => True
  | .bad => False

/-- Scheduler letter 0 escapes; scheduler letter 1 leaves the Good state fixed.
The bad state is absorbing.  `Fin 2` is exactly the two-edge scheduler alphabet
seen by the generic mass machinery for a two-site ring. -/
def rung2Step : Rung2State → Fin 2 → Rung2State
  | .bad, _ => .bad
  | .good, e => if e.val = 0 then .bad else .good

@[simp] theorem rung2Good_good : rung2Good .good := by
  exact True.intro

@[simp] theorem rung2Good_bad : ¬ rung2Good .bad := by
  intro h
  exact h

@[simp] theorem rung2Step_good_zero :
    rung2Step .good (0 : Fin 2) = .bad := by
  rfl

@[simp] theorem rung2Step_good_one :
    rung2Step .good (1 : Fin 2) = .good := by
  rfl

/-- The two scheduler letters are exactly the requested escape/stutter pair. -/
theorem rung2_exactly_one_escape :
    (¬ rung2Good (rung2Step .good (0 : Fin 2))) ∧
      rung2Step .good (1 : Fin 2) = .good := by
  constructor
  · rw [rung2Step_good_zero]
    exact rung2Good_bad
  · exact rung2Step_good_one

/-- There is exactly one live word of every length: the all-1 word. -/
theorem rung2_aliveCount_one : ∀ L : Nat,
    aliveCount rung2Step rung2Good .good L = 1
  | 0 =>
      aliveCount_zero_of_good rung2Step rung2Good .good rung2Good_good
  | T + 1 => by
      rw [BirthTwoStageEscape.aliveCount_succ
        rung2Step rung2Good .good rung2Good_good T]
      rw [fin2_sum]
      have hbad : aliveCount rung2Step rung2Good .bad T = 0 :=
        BirthTwoStageEscape.aliveCount_not_good
          rung2Step rung2Good .bad rung2Good_bad T
      rw [rung2Step_good_zero, rung2Step_good_one,
        hbad, rung2_aliveCount_one T]

/-- The exact combinatorial spelling requested in Rung 2. -/
theorem rung2_aliveCount_exact (L : Nat) :
    aliveCount rung2Step rung2Good .good L = (2 - 1) ^ L := by
  rw [rung2_aliveCount_one L]
  simp

/-- At `n = 2`, `Q = 8`, every positive horizon satisfies the mass bound. -/
theorem rung2_uniformEscapeMass (L : Nat) (hL : 1 ≤ L) :
    UniformEscapeMass rung2Step rung2Good L 8 := by
  intro x hx
  cases x with
  | good =>
      rw [rung2_aliveCount_one L]
      obtain ⟨T, hT⟩ :=
        Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
      subst L
      rw [Nat.pow_succ]
      have hp : 0 < 2 ^ T := Nat.pow_pos (by omega)
      omega
  | bad =>
      exact hx.elim

/-! ## Rung 3: one immediate escape from every Good state -/

/-- A single immediately escaping letter at every Good state is enough.
No separately strengthened "for every prefix" hypothesis is needed: every
surviving prefix endpoint is Good, so this same hypothesis re-applies there. -/
theorem aliveCount_le_pred_pow_of_one_escape
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (Good : S → Prop)
    (hEscape : ∀ x, Good x → ∃ e : Fin n, ¬ Good (step x e)) :
    ∀ (L : Nat) (x : S), Good x →
      aliveCount step Good x L ≤ (n - 1) ^ L
  | 0, x, hx => by
      rw [aliveCount_zero_of_good step Good x hx]
      simp
  | T + 1, x, hx => by
      rw [BirthTwoStageEscape.aliveCount_succ step Good x hx T]
      obtain ⟨chosen, hchosen⟩ := hEscape x hx
      let c : Nat := (n - 1) ^ T
      let a : Fin n → Nat :=
        fun e => aliveCount step Good (step x e) T
      have hzero : a chosen = 0 := by
        dsimp [a]
        exact BirthTwoStageEscape.aliveCount_not_good
          step Good (step x chosen) hchosen T
      have hle : ∀ e : Fin n, a e ≤ c := by
        intro e
        dsimp [a, c]
        by_cases he : Good (step x e)
        · exact aliveCount_le_pred_pow_of_one_escape
            step Good hEscape T (step x e) he
        · rw [BirthTwoStageEscape.aliveCount_not_good
            step Good (step x e) he T]
          exact Nat.zero_le _
      have hpay :
          c + (List.ofFn a).sum ≤
            (List.ofFn (fun _ : Fin n => c)).sum := by
        apply GlobalGapComposition.ofFn_sum_le_of_one_pay
          c a (fun _ : Fin n => c) chosen
        · simp [hzero]
        · intro e
          exact hle e
      rw [FiniteUniformStoppingTree.ofFn_sum_const] at hpay
      have hn : 0 < n := by
        have hc := chosen.isLt
        omega
      have hsum : (List.ofFn a).sum ≤ (n - 1) * c := by
        rw [pred_mul n c hn] at hpay
        omega
      calc
        (List.ofFn (fun e : Fin n =>
            aliveCount step Good (step x e) T)).sum =
            (List.ofFn a).sum := by rfl
        _ ≤ (n - 1) * c := hsum
        _ = (n - 1) ^ (T + 1) := by
          dsimp [c]
          rw [Nat.pow_succ]
          exact Nat.mul_comm _ _

/-- Generic first-principles producer: the only remaining premise is plain
arithmetic, not another `aliveCount`/`avoidCount` mass statement. -/
theorem rung3_uniformEscapeMass
    {S : Type} {n : Nat}
    (step : S → Fin n → S) (Good : S → Prop)
    (hEscape : ∀ x, Good x → ∃ e : Fin n, ¬ Good (step x e))
    (L Q : Nat)
    (harith : Q * (n - 1) ^ L ≤ (Q - 1) * n ^ L) :
    UniformEscapeMass step Good L Q := by
  intro x hx
  calc
    Q * aliveCount step Good x L
        ≤ Q * (n - 1) ^ L :=
      Nat.mul_le_mul_left Q
        (aliveCount_le_pred_pow_of_one_escape
          step Good hEscape L x hx)
    _ ≤ (Q - 1) * n ^ L := harith

end ZZFirstMassBound

#print axioms ZZFirstMassBound.rung1_uniformEscapeMass
#print axioms ZZFirstMassBound.rung2_aliveCount_exact
#print axioms ZZFirstMassBound.rung2_uniformEscapeMass
#print axioms ZZFirstMassBound.aliveCount_le_pred_pow_of_one_escape
#print axioms ZZFirstMassBound.rung3_uniformEscapeMass
