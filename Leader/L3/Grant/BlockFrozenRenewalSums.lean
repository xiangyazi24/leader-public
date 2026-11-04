import Leader.L3.Grant.BlockFrozenRecovery

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! Kernel-free arithmetic and stage-sum helpers of the G13 chain, copied from
the private declarations of BankTrialRenewal.lean so that the frozen chain can
use them. -/

theorem grantBlockFrozenRenewalStageScale
    (a H : Nat) (f : Nat → Nat) :
    bankTrialSuccessStageIndexSum (fun j => a * f j) H =
      a * bankTrialSuccessStageIndexSum f H := by
  induction H with
  | zero =>
      rfl
  | succ H ih =>
      change bankTrialSuccessStageIndexSum (fun j => a * f j) H +
          a * f H =
        a * (bankTrialSuccessStageIndexSum f H + f H)
      rw [ih, Nat.mul_add]

/-- Monotonicity of finite stage sums under bounds valid only
for indices j < H. -/
theorem grantBlockFrozenRenewalStageIndexMonoBelow
    (f g : Nat → Nat) :
    ∀ (H : Nat),
      (∀ j, j < H → f j ≤ g j) →
      bankTrialSuccessStageIndexSum f H ≤
        bankTrialSuccessStageIndexSum g H := by
  intro H
  induction H with
  | zero =>
      intro _
      exact Nat.le_refl _
  | succ k ih =>
      intro h
      change
        bankTrialSuccessStageIndexSum f k + f k ≤
          bankTrialSuccessStageIndexSum g k + g k
      have hsmall : ∀ j, j < k → f j ≤ g j := by
        intro j hj
        exact h j (by omega)
      exact Nat.add_le_add (ih hsmall) (h k (by omega))

/-- Distribute addition across a mapped finite Nat sum. -/
theorem grantBlockFrozenRenewalNatMapSumAdd
    {A : Type} (xs : List A) (f g : A → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

/-- Clear den^(j+1) to den^H. The only omega calculation
is on the index identity, not on any compiled large power. -/
theorem grantBlockFrozenRenewalCommonPowerLift
    (den lo win N H j mass : Nat)
    (hj : j + 1 ≤ H)
    (hmass :
      lo ^ j * win * N ≤ den ^ (j + 1) * mass) :
    N * (lo ^ j * win * den ^ (H - (j + 1))) ≤
      den ^ H * mass := by
  have hscaled :=
    Nat.mul_le_mul_right (den ^ (H - (j + 1))) hmass
  calc
    N * (lo ^ j * win * den ^ (H - (j + 1))) =
        (lo ^ j * win * N) * den ^ (H - (j + 1)) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (den ^ (j + 1) * mass) *
        den ^ (H - (j + 1)) := hscaled
    _ = (den ^ (j + 1) * den ^ (H - (j + 1))) *
        mass := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ = den ^ H * mass := by
          have hsum :
              (j + 1) + (H - (j + 1)) = H := by omega
          rw [← Nat.pow_add, hsum]

/-- The consumer window is the largest Nat W satisfying
8 * W <= R * n; this lemma uses the Euclidean remainder. -/
theorem grantBlockFrozenRenewalIndexConsumerWindowCap
    (n R W : Nat) (hW : W = R * n / 8) :
    8 * W ≤ R * n := by
  have hmod := Nat.mod_add_div (R * n) 8
  rw [hW]
  omega

/-- Elementary monotonicity of quotient floors without Nat.find. -/
theorem grantBlockFrozenRenewalIndexFloorLower
    (a f H : Nat)
    (hf : 0 < f)
    (h : H * f ≤ a) :
    H ≤ a / f := by
  by_cases hc : H ≤ a / f
  · exact hc
  · have hnext : a / f + 1 ≤ H := by omega
    have hm := Nat.mul_le_mul_right f hnext
    have hdiv : a % f + (a / f) * f = a := by
      simpa only [Nat.mul_comm] using Nat.mod_add_div a f
    have hrem : a % f < f := Nat.mod_lt a hf
    have hupper : a < (a / f + 1) * f := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    omega

theorem grantBlockFrozenRenewalIndexCostComplement
    (W C G F : Nat) (hG : G ≤ C) :
    ∀ H, C + H * F ≤ W →
      bankTrialSuccessStageIndexSum (fun j => G + j * F) H +
        bankTrialSuccessStageIndexSum
          (fun j => W - C - j * F) H ≤ W * H := by
  intro H
  induction H with
  | zero =>
      intro _
      exact Nat.zero_le _
  | succ k ih =>
      intro h
      have hstep := Nat.mul_le_mul_right F (Nat.le_succ k)
      have hsF : (k + 1) * F = k * F + F := Nat.succ_mul k F
      have hsF' : k.succ * F = k * F + F := Nat.succ_mul k F
      have hk : C + k * F ≤ W := by omega
      have hitem : G + k * F + (W - C - k * F) ≤ W := by
        omega
      have hprev := ih hk
      change
        (bankTrialSuccessStageIndexSum (fun j => G + j * F) k +
          (G + k * F)) +
        (bankTrialSuccessStageIndexSum
          (fun j => W - C - j * F) k +
          (W - C - k * F)) ≤ W * (k + 1)
      rw [Nat.mul_add, Nat.mul_one]
      omega

theorem grantBlockFrozenRenewalIndexConstantStageSum
    (a H : Nat) :
    bankTrialSuccessStageIndexSum (fun _ => a) H = H * a := by
  induction H with
  | zero => simp [bankTrialSuccessStageIndexSum]
  | succ k ih =>
      change bankTrialSuccessStageIndexSum (fun _ => a) k + a =
        (k + 1) * a
      rw [ih, Nat.add_mul]
      simp

/-- A geometric point, normalized with an opaque denominator;
only small fixed multipliers are evaluated. -/
theorem grantBlockFrozenRenewalIndexWeightedPoint
    (lo den L P H j : Nat)
    (hden : den = 1024 * L * P)
    (hj : j < H)
    (hgeo : 1023 * den ^ j ≤ 1024 * lo ^ j) :
    1046529 * den ^ H ≤
      1048576 * P *
        (lo ^ j * (1023 * L) * den ^ (H - (j + 1))) := by
  have hsum : j + (H - (j + 1)) + 1 = H := by omega
  have hpower :
      den ^ j * den ^ (H - (j + 1)) * den = den ^ H := by
    calc
      _ = den ^ (j + (H - (j + 1))) * den := by
        rw [Nat.pow_add]
      _ = den ^ (j + (H - (j + 1)) + 1) := by
        rw [Nat.pow_succ]
      _ = den ^ H := by rw [hsum]
  have hfac :
      1024 * (1023 * den) =
        1048576 * P * (1023 * L) := by
    rw [hden, show (1048576 : Nat) = 1024 * 1024 by decide]
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hscaled := Nat.mul_le_mul_left
    (1023 * den * den ^ (H - (j + 1))) hgeo
  calc
    1046529 * den ^ H =
        (1023 * den * den ^ (H - (j + 1))) *
          (1023 * den ^ j) := by
      rw [show (1046529 : Nat) = 1023 * 1023 by decide,
        ← hpower]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ ≤ (1023 * den * den ^ (H - (j + 1))) *
          (1024 * lo ^ j) := hscaled
    _ = (1024 * (1023 * den)) *
          (lo ^ j * den ^ (H - (j + 1))) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = (1048576 * P * (1023 * L)) *
          (lo ^ j * den ^ (H - (j + 1))) := by rw [hfac]
    _ = 1048576 * P *
          (lo ^ j * (1023 * L) * den ^ (H - (j + 1))) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem grantBlockFrozenRenewalIndexWeightedSum
    (lo den L P H : Nat)
    (hden : den = 1024 * L * P)
    (hgeo : ∀ j, j < H →
      1023 * den ^ j ≤ 1024 * lo ^ j) :
    1046529 * H * den ^ H ≤
      1048576 * P *
        bankTrialSuccessStageIndexSum (fun j =>
          lo ^ j * (1023 * L) *
            den ^ (H - (j + 1))) H := by
  have hs := grantBlockFrozenRenewalStageIndexMonoBelow
    (fun _ => 1046529 * den ^ H)
    (fun j => 1048576 * P *
      (lo ^ j * (1023 * L) * den ^ (H - (j + 1))))
    H (by
      intro j hj
      exact grantBlockFrozenRenewalIndexWeightedPoint
        lo den L P H j hden hj (hgeo j hj))
  rw [grantBlockFrozenRenewalIndexConstantStageSum] at hs
  rw [grantBlockFrozenRenewalStageScale] at hs
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    using hs

theorem grantBlockFrozenRenewalIndexMassLinear
    (W P N M H cost lo den L : Nat)
    (hdenpos : 0 < den)
    (hweighted :
      1046529 * H * den ^ H ≤
        1048576 * P *
          bankTrialSuccessStageIndexSum (fun j =>
            lo ^ j * (1023 * L) *
              den ^ (H - (j + 1))) H)
    (hwin :
      W * P * N *
        bankTrialSuccessStageIndexSum (fun j =>
          lo ^ j * (1023 * L) *
            den ^ (H - (j + 1))) H ≤
      den ^ H * (W * P * M + N * cost)) :
    1046529 * (W * H * N) ≤
      1048576 * (W * P * M + N * cost) := by
  have hdpos : 0 < den ^ H := Nat.pow_pos hdenpos
  have hh :
      den ^ H * (1046529 * (W * H * N)) ≤
      den ^ H * (1048576 * (W * P * M + N * cost)) := by
    calc
      den ^ H * (1046529 * (W * H * N)) =
          (W * N) * (1046529 * H * den ^ H) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ (W * N) * (1048576 * P *
          bankTrialSuccessStageIndexSum (fun j =>
            lo ^ j * (1023 * L) *
              den ^ (H - (j + 1))) H) :=
        Nat.mul_le_mul_left _ hweighted
      _ = 1048576 * (W * P * N *
          bankTrialSuccessStageIndexSum (fun j =>
            lo ^ j * (1023 * L) *
              den ^ (H - (j + 1))) H) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ 1048576 * (den ^ H *
            (W * P * M + N * cost)) :=
        Nat.mul_le_mul_left 1048576 hwin
      _ = den ^ H *
            (1048576 * (W * P * M + N * cost)) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left hh hdpos

/-- The 491/1000 sum reserve pays all 2047/1048576
geometric thinning. The fixed arithmetic margin is 4606. -/
theorem grantBlockFrozenRenewalIndexMassPayoff
    (W F H P N M cost s : Nat)
    (hW : 0 < W)
    (hFH : F * H ≤ W)
    (hS : 491 * W * W ≤ 1000 * F * s)
    (hcost : cost + s ≤ W * H)
    (hmass :
      1046529 * (W * H * N) ≤
        1048576 * (W * P * M + N * cost)) :
    51279921 * W * N ≤ 104857600 * F * P * M := by
  have hc := Nat.mul_le_mul_left N hcost
  have hcscaled : N * cost + N * s ≤ W * H * N := by
    simpa only [Nat.mul_add, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using hc
  have hbridge :
      1048576 * (N * s) ≤
        1048576 * (W * P * M) + 2047 * (W * H * N) := by
    have hcc := Nat.mul_le_mul_left 1048576 hcscaled
    simp only [Nat.mul_add] at hcc hmass
    omega
  have hgapBound :
      (1000 * F) * (2047 * (W * H * N)) ≤
        1000 * 2047 * (W * W * N) := by
    have hs := Nat.mul_le_mul_left (1000 * 2047 * W * N) hFH
    simpa only [Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hs
  have hpaid :
      491 * 1048576 * (W * W * N) ≤
        1000 * 1048576 * (W * F * P * M) +
          1000 * 2047 * (W * W * N) := by
    calc
      491 * 1048576 * (W * W * N) ≤
          (1000 * F) * (1048576 * (N * s)) := by
        have hs := Nat.mul_le_mul_left (1048576 * N) hS
        simpa only [Nat.mul_assoc, Nat.mul_left_comm,
          Nat.mul_comm] using hs
      _ ≤ (1000 * F) *
            (1048576 * (W * P * M) +
              2047 * (W * H * N)) :=
        Nat.mul_le_mul_left _ hbridge
      _ = 1000 * 1048576 * (W * F * P * M) +
            (1000 * F) * (2047 * (W * H * N)) := by
        simp only [Nat.mul_add, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ 1000 * 1048576 * (W * F * P * M) +
            1000 * 2047 * (W * W * N) :=
        Nat.add_le_add_left hgapBound _
  have hcoef :
      490 * 1046529 * (W * W * N) ≤
        1000 * 1048576 * (W * F * P * M) := by
    have hstrict :
        490 * 1046529 + 1000 * 2047 ≤
          491 * 1048576 := by decide
    have hstrictScaled := Nat.mul_le_mul_right
      (W * W * N) hstrict
    have hstrictNormal :
        (490 * 1046529) * (W * W * N) +
          (1000 * 2047) * (W * W * N) ≤
        (491 * 1048576) * (W * W * N) := by
      simpa only [Nat.add_mul, Nat.mul_assoc] using hstrictScaled
    omega
  have hcancel :
      490 * 1046529 * (W * N) ≤
        1000 * 1048576 * (F * P * M) := by
    have hh :
        W * (490 * 1046529 * (W * N)) ≤
          W * (1000 * 1048576 * (F * P * M)) := by
      simpa only [Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using hcoef
    exact Nat.le_of_mul_le_mul_left hh hW
  have hten :
      10 * (49 * 1046529 * W * N) ≤
        10 * (100 * 1048576 * F * P * M) := by
    have e1 : 10 * (49 * 1046529 * W * N) = 490 * 1046529 * (W * N) := by
      rw [show (490 : Nat) = 10 * 49 by decide]
      ac_rfl
    have e2 : 10 * (100 * 1048576 * F * P * M) =
        1000 * 1048576 * (F * P * M) := by
      rw [show (1000 : Nat) = 10 * 100 by decide]
      ac_rfl
    rw [e1, e2]
    exact hcancel
  have hfinal := Nat.le_of_mul_le_mul_left hten
    (by decide : 0 < (10 : Nat))
  have hpaper :
      49 * 1023 ^ 2 * W * N ≤
        100 * 1024 ^ 2 * F * 1 * P * M := by
    simpa only [
      show (1023 ^ 2 : Nat) = 1046529 by decide,
      show (1024 ^ 2 : Nat) = 1048576 by decide,
      Nat.mul_one, Nat.mul_assoc] using hfinal
  have hcleared :=
    (bankTrialRenewalIndexThetaSquareClearing W N F 1 P M).mp
      hpaper
  simpa only [Nat.mul_one, Nat.mul_assoc] using hcleared

/-- Pure Nat reduction with exactly the AnyH window sandwich.
Every hypothesis will be supplied by the compiled window below. -/
theorem grantBlockFrozenRenewalIndexVariableMassArithmetic
    (W F H P N M C G L lo den : Nat)
    (hW : 0 < W)
    (hF : 0 < F)
    (hfloor : H = (W - C) / F)
    (hratio : 255 * C ≤ 2 * W)
    (hlarge : 22517 ≤ H)
    (hG : G ≤ C)
    (hden : den = 1024 * L * P)
    (hdenpos : 0 < den)
    (hgeo : ∀ j, j < H →
      1023 * den ^ j ≤ 1024 * lo ^ j)
    (hwin :
      W * P * N *
        bankTrialSuccessStageIndexSum (fun j =>
          lo ^ j * (1023 * L) *
            den ^ (H - (j + 1))) H ≤
      den ^ H *
        (W * P * M + N *
          bankTrialSuccessStageIndexSum
            (fun j => G + j * F) H)) :
    51279921 * W * N ≤ 104857600 * F * P * M := by
  have hCle : C ≤ W := by omega
  have hdiv : (W - C) % F + ((W - C) / F) * F =
      W - C := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div (W - C) F
  have hHF : H * F ≤ W - C := by
    rw [hfloor]
    omega
  have hCbudget : C + H * F ≤ W := by
    have hsub := Nat.sub_add_cancel hCle
    omega
  have hFH : F * H ≤ W := by
    calc
      F * H = H * F := Nat.mul_comm _ _
      _ ≤ W - C := hHF
      _ ≤ W := Nat.sub_le _ _
  have hsum := bankTrialRenewalIndexSumStrong
    W C F H hF hratio hfloor hlarge
  have hcomp := grantBlockFrozenRenewalIndexCostComplement
    W C G F hG H hCbudget
  have hweighted := grantBlockFrozenRenewalIndexWeightedSum
    lo den L P H hden hgeo
  have hlin := grantBlockFrozenRenewalIndexMassLinear
    W P N M H
    (bankTrialSuccessStageIndexSum (fun j => G + j * F) H)
    lo den L hdenpos hweighted hwin
  exact grantBlockFrozenRenewalIndexMassPayoff
    W F H P N M
    (bankTrialSuccessStageIndexSum (fun j => G + j * F) H)
    (bankTrialSuccessStageIndexSum (fun j => W - C - j * F) H)
    hW hFH hsum hcomp hlin

end L3
#print axioms L3.grantBlockFrozenRenewalIndexVariableMassArithmetic
#print axioms L3.grantBlockFrozenRenewalStageIndexMonoBelow
