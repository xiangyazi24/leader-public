import Leader.L4.Height.Physical
import Leader.L4.Height.Overrun

namespace L4.Height

open Classical

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Arbitrary repair cost and arbitrary trial deadline. -/
theorem post_custody_time_gen {α : Type} {N : Nat}
    (next : α → Fin N → α)
    (R Leg Cust : α → Prop)
    (rep d : Nat)
    (FailLog FailOver : α → List (Fin N) → Prop)
    (hR : ∀ x e, R x → R (next x e))
    (hLeg : ∀ x e, Leg x → Leg (next x e))
    (_hCust : ∀ x e, Cust x → Cust (next x e))
    (_hLegCust : ∀ x, Leg x → Cust x)
    (hRepair : ∀ x, Cust x →
      IIDExpectedHittingTimeAtMost next Leg x rep)
    (hLogical : ∀ x, Leg x → ¬ R x →
      4 * wordSum (fun u => if FailLog x u then 1 else 0) d ≤ N ^ d)
    (hOverrun : ∀ x, Leg x → ¬ R x →
      4 * wordSum (fun u => if FailOver x u then 1 else 0) d ≤ N ^ d)
    (hCover : ∀ x, Leg x → ∀ u, u.length = d →
      ¬ FailLog x u → ¬ FailOver x u → R (runWord next x u))
    (x : α) (hxCust : Cust x) :
    IIDExpectedHittingTimeAtMost next R x (rep + 2 * d) := by
  have hfail :
      ∀ y, Leg y → ¬ R y →
        2 * wordSum
          (fun u => if R (runWord next y u) then 0 else 1) d ≤ N ^ d := by
    intro y hyLeg hyR
    exact trial_from_two next R y (FailLog y) (FailOver y)
      (hLogical y hyLeg hyR) (hOverrun y hyLeg hyR)
      (hCover y hyLeg)
  have hRestart : ∀ y, Leg y →
      IIDExpectedHittingTimeAtMost next R y (2 * d) := by
    intro y hyLeg
    exact restart_mean next R Leg hR hLeg hfail y hyLeg
  exact expected_then_closed
    (next := next) (A := Cust) (B := Leg) (C := R)
    (a := rep) (b := 2 * d)
    hRepair hLeg hRestart x hxCust

/-
The zero-deadline form WITHOUT hd is false: choose N=1, K=d=0,
X constantly zero. All means vanish but the conclusion becomes 4 ≤ 1.
-/
/-- Corrected Markov-quarter interface: the deadline must be positive. -/
theorem overrun_of_mean {N : Nat} (X : List (Fin N) → Nat)
    (K d : Nat) (hd : 0 < d) (hKD : 4 * K ≤ d)
    (hmean : ∀ t, wordSum (fun u => Nat.min (X u) t) t ≤ K * N ^ t) :
    4 * wordSum (fun u => if d ≤ X u then 1 else 0) d ≤ N ^ d := by
  have hmark := markov_deadline X d K (hmean d)
  have hmul :
      d * (4 * wordSum (fun u => if d ≤ X u then 1 else 0) d)
        ≤ d * N ^ d := by
    calc
      d * (4 * wordSum (fun u => if d ≤ X u then 1 else 0) d)
          = 4 * (d * wordSum (fun u => if d ≤ X u then 1 else 0) d) := by
              ac_rfl
      _ ≤ 4 * (K * N ^ d) := Nat.mul_le_mul_left 4 hmark
      _ = (4 * K) * N ^ d := by ac_rfl
      _ ≤ d * N ^ d := Nat.mul_le_mul_right (N ^ d) hKD
  exact Nat.le_of_mul_le_mul_left hmul hd

/-- The 16^h logarithm is at most four bits per level. -/
private theorem log2_sixteen_pow_le (h : Nat) :
    Nat.log2 (16 ^ h) ≤ 4 * h := by
  have hpow : ∀ j : Nat, 16 ^ j = 2 ^ (4 * j) := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
        calc
          16 ^ (j + 1) = 16 ^ j * 16 := Nat.pow_succ 16 j
          _ = 2 ^ (4 * j) * 16 := by rw [ih]
          _ = 2 ^ (4 * j + 4) := by
            rw [Nat.pow_add]
          _ = 2 ^ (4 * (j + 1)) :=
            congrArg (fun q : Nat => 2 ^ q) (by omega)
  have hpos : 0 < 16 ^ h := Nat.pow_pos (by decide)
  have hlt : 16 ^ h < 2 ^ (4 * h + 1) := by
    rw [hpow, Nat.pow_succ]
    have hp : 0 < 2 ^ (4 * h) := Nat.pow_pos (by decide)
    omega
  have hlog :
      Nat.log2 (16 ^ h) < 4 * h + 1 :=
    (Nat.log2_lt (Nat.ne_of_gt hpos)).2 hlt
  omega

/-- The larger clock-mean coefficient remains within 2^28*m. -/
theorem clock_budget_gen (m h : Nat) (hm : 1 ≤ m)
    (hh : h ≤ 2 ^ 25 * m) :
    Nat.log2 (m * 3 ^ h) + Nat.log2 (16 ^ h) + 4 ≤
      2 ^ 28 * m := by
  have hold := log_mean_budget m h hm hh
  have hfour := log2_sixteen_pow_le h
  have htwice : 2 * h ≤ 2 ^ 26 * m := by
    have hh' := Nat.mul_le_mul_left 2 hh
    have heq : 2 * (2 ^ 25 * m) = 2 ^ 26 * m := by
      simp only [show (2 : Nat) ^ 25 = 33554432 by decide,
        show (2 : Nat) ^ 26 = 67108864 by decide]
      omega
    omega
  have hnum : 2 ^ 27 * m + 2 ^ 26 * m ≤ 2 ^ 28 * m := by
    simp only [show (2 : Nat) ^ 26 = 67108864 by decide,
      show (2 : Nat) ^ 27 = 134217728 by decide,
      show (2 : Nat) ^ 28 = 268435456 by decide]
    omega
  omega

/-- The corrected clock mean yields quarter overrun at the enlarged deadline. -/
theorem overrun_quarter_gen {N : Nat} (L m h : Nat)
    (X : List (Fin N) → Nat)
    (hL : 1 ≤ L) (hm : 1 ≤ m)
    (hh : h ≤ 2 ^ 25 * m)
    (hmean : ∀ t : Nat,
      wordSum (fun u => Nat.min (X u) t) t ≤
        L * (Nat.log2 (m * 3 ^ h) + Nat.log2 (16 ^ h) + 4) * N ^ t) :
    4 * wordSum
      (fun u => if 2 ^ 30 * L * m ≤ X u then 1 else 0)
      (2 ^ 30 * L * m) ≤ N ^ (2 ^ 30 * L * m) := by
  let d := 2 ^ 30 * L * m
  let K := L * (2 ^ 28 * m)
  have hclock := clock_budget_gen m h hm hh
  have hK :
      L * (Nat.log2 (m * 3 ^ h) + Nat.log2 (16 ^ h) + 4) ≤ K := by
    exact Nat.mul_le_mul_left L hclock
  have hmeanK : ∀ t,
      wordSum (fun u => Nat.min (X u) t) t ≤ K * N ^ t := by
    intro t
    exact Nat.le_trans (hmean t) (Nat.mul_le_mul_right (N ^ t) hK)
  have hd : 0 < d := by
    dsimp [d]
    have hp30 : 0 < (2 : Nat) ^ 30 := Nat.pow_pos (by decide)
    exact Nat.mul_pos (Nat.mul_pos hp30 hL) hm
  have hKD : 4 * K ≤ d := by
    dsimp [K, d]
    have hconst : (4 : Nat) * 268435456 = 1073741824 := by decide
    calc
      4 * (L * (268435456 * m))
          = (4 * 268435456) * L * m := by ac_rfl
      _ ≤ 1073741824 * L * m := by
        rw [hconst]
        exact Nat.le_refl _
  exact overrun_of_mean X K d hd hKD hmeanK

/-- Enlarged-deadline physical bound (recovery budget 16 L m). -/
theorem post_custody_quadratic_gen {α : Type} {N : Nat}
    (next : α → Fin N → α)
    (R Leg Cust : α → Prop)
    (L m bL ringN r : Nat)
    (FailLog FailOver : α → List (Fin N) → Prop)
    (hL : L = 2 ^ (5 * bL + 34) * ringN * r)
    (hmr : m * r ≤ ringN)
    (hR : ∀ x e, R x → R (next x e))
    (hLeg : ∀ x e, Leg x → Leg (next x e))
    (hCust : ∀ x e, Cust x → Cust (next x e))
    (hLegCust : ∀ x, Leg x → Cust x)
    (hRepair : ∀ x, Cust x →
      IIDExpectedHittingTimeAtMost next Leg x (16 * L * m))
    (hLogical : ∀ x, Leg x → ¬ R x →
      4 * wordSum
        (fun u => if FailLog x u then 1 else 0)
        (2 ^ 30 * L * m) ≤ N ^ (2 ^ 30 * L * m))
    (hOverrun : ∀ x, Leg x → ¬ R x →
      4 * wordSum
        (fun u => if FailOver x u then 1 else 0)
        (2 ^ 30 * L * m) ≤ N ^ (2 ^ 30 * L * m))
    (hCover : ∀ x, Leg x →
      ∀ u, u.length = 2 ^ 30 * L * m →
        ¬ FailLog x u → ¬ FailOver x u →
          R (runWord next x u))
    (x : α) (hxCust : Cust x) :
    IIDExpectedHittingTimeAtMost next R x
      (2 ^ (5 * bL + 66) * ringN ^ 2) := by
  have htime := post_custody_time_gen
    (next := next) (R := R) (Leg := Leg) (Cust := Cust)
    (rep := 16 * L * m) (d := 2 ^ 30 * L * m)
    (FailLog := FailLog) (FailOver := FailOver)
    hR hLeg hCust hLegCust hRepair hLogical hOverrun hCover x hxCust
  have hcoefficient : 16 + 2 * 2 ^ 30 ≤ 2 ^ 32 := by decide
  have hfactor :
      16 * L * m + 2 * (2 ^ 30 * L * m) =
        (16 + 2 * 2 ^ 30) * L * m := by
    simp only [Nat.add_mul]
    ac_rfl
  have hsmall :
      16 * L * m + 2 * (2 ^ 30 * L * m) ≤
      2 ^ 32 * L * m := by
    rw [hfactor]
    exact Nat.mul_le_mul_right m
      (Nat.mul_le_mul_right L hcoefficient)
  have hscale :
      2 ^ 32 * L * m ≤ 2 ^ (5 * bL + 66) * ringN ^ 2 := by
    rw [hL]
    have hexp :
        2 ^ 32 * 2 ^ (5 * bL + 34) = 2 ^ (5 * bL + 66) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hrbound :
        ringN * (m * r) ≤ ringN * ringN :=
      Nat.mul_le_mul_left ringN hmr
    have hsq : ringN ^ 2 = ringN * ringN := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    calc
      2 ^ 32 * (2 ^ (5 * bL + 34) * ringN * r) * m
          = (2 ^ 32 * 2 ^ (5 * bL + 34)) *
              (ringN * (m * r)) := by ac_rfl
      _ = 2 ^ (5 * bL + 66) * (ringN * (m * r)) := by
        rw [hexp]
      _ ≤ 2 ^ (5 * bL + 66) * (ringN * ringN) :=
        Nat.mul_le_mul_left _ hrbound
      _ = 2 ^ (5 * bL + 66) * ringN ^ 2 := by
        rw [hsq]
  exact expected_bound_mono (next := next) (target := R) (x := x)
    htime (Nat.le_trans hsmall hscale)

end L4.Height

