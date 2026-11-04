import Leader.PPL.Probability.LotteryTails

set_option autoImplicit false

namespace PPL.Probability

/-!
# Nat potential proof for the P_PL lottery moments

This file discharges `LotteryTailMomentArithmetic` using only natural-number
recurrences and denominator-free potential inequalities.
-/

def lotteryUpperHeadDP (k : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | T + 1, h =>
      if k ≤ h + 1 then
        3 * lotteryUpperHeadDP k T 0
      else
        lotteryUpperHeadDP k T 0 +
          lotteryUpperHeadDP k T (h + 1)

def lotteryDiscountHeadDP (k : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | T + 1, h =>
      if k ≤ h + 1 then
        3 * lotteryDiscountHeadDP k T 0
      else
        2 * lotteryDiscountHeadDP k T 0 +
          2 * lotteryDiscountHeadDP k T (h + 1)

def lotteryUpperPotential (k h : Nat) : Nat :=
  2 ^ k + 2 ^ h

def lotteryUpperGrowth (k : Nat) : Nat :=
  2 * (2 ^ k + 1)

def lotteryDownPotential (k h : Nat) : Nat :=
  2 * 2 ^ k - 2 ^ h

def lotteryDownGrowth (k : Nat) : Nat :=
  4 * 2 ^ k - 1

private theorem lotteryUpperHeadDP_eq_natDP
    (k T : Nat) (s : LotteryState) (hs : s.headRun < k) :
    lotteryNatDP k (fun u => 2 ^ u.wins) T s =
      2 ^ s.wins * lotteryUpperHeadDP k T s.headRun := by
  induction T generalizing s with
  | zero =>
      simp [lotteryNatDP, lotteryUpperHeadDP]
  | succ T ih =>
      rw [lotteryNatDP]
      by_cases hw : k ≤ s.headRun + 1
      · have hfalse : (lotteryStep k s false).headRun < k := by
          simp [lotteryStep]
          omega
        have htrue : (lotteryStep k s true).headRun < k := by
          simp [lotteryStep, hw]
          omega
        rw [ih (lotteryStep k s false) hfalse,
          ih (lotteryStep k s true) htrue]
        simp [lotteryStep, hw, lotteryUpperHeadDP,
          Nat.pow_succ, Nat.mul_add, Nat.succ_mul]
        all_goals try simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        all_goals omega
      · have hfalse : (lotteryStep k s false).headRun < k := by
          simp [lotteryStep]
          omega
        have htrue : (lotteryStep k s true).headRun < k := by
          simp [lotteryStep, hw]
          omega
        rw [ih (lotteryStep k s false) hfalse,
          ih (lotteryStep k s true) htrue]
        simp [lotteryStep, hw, lotteryUpperHeadDP,
          Nat.mul_add] <;> ac_rfl

private theorem lotteryDiscountHeadDP_eq_natDP
    (k T R : Nat) (s : LotteryState) (hs : s.headRun < k) :
    lotteryNatDP k
        (fun u => 2 ^ (T + R + s.wins - u.wins)) T s =
      2 ^ R * lotteryDiscountHeadDP k T s.headRun := by
  induction T generalizing R s with
  | zero =>
      simp [lotteryNatDP, lotteryDiscountHeadDP]
  | succ T ih =>
      rw [lotteryNatDP]
      by_cases hw : k ≤ s.headRun + 1
      · have hfalse : (lotteryStep k s false).headRun < k := by
          simp [lotteryStep]
          omega
        have htrue : (lotteryStep k s true).headRun < k := by
          simp [lotteryStep, hw]
          omega
        have hfunFalse :
            (fun u : LotteryState =>
              2 ^ (T + 1 + R + s.wins - u.wins)) =
            (fun u : LotteryState =>
              2 ^ (T + (R + 1) +
                (lotteryStep k s false).wins - u.wins)) := by
          funext u
          apply congrArg (fun z : Nat => 2 ^ z)
          simp [lotteryStep] <;> omega
        have hfunTrue :
            (fun u : LotteryState =>
              2 ^ (T + 1 + R + s.wins - u.wins)) =
            (fun u : LotteryState =>
              2 ^ (T + R +
                (lotteryStep k s true).wins - u.wins)) := by
          funext u
          apply congrArg (fun z : Nat => 2 ^ z)
          simp [lotteryStep, hw] <;> omega
        have hfalseDP :
            lotteryNatDP k
                (fun u => 2 ^ (T + 1 + R + s.wins - u.wins))
                T (lotteryStep k s false) =
              2 ^ (R + 1) * lotteryDiscountHeadDP k T 0 := by
          rw [hfunFalse]
          simpa [lotteryStep] using
            ih (R + 1) (lotteryStep k s false) hfalse
        have htrueDP :
            lotteryNatDP k
                (fun u => 2 ^ (T + 1 + R + s.wins - u.wins))
                T (lotteryStep k s true) =
              2 ^ R * lotteryDiscountHeadDP k T 0 := by
          rw [hfunTrue]
          simpa [lotteryStep, hw] using
            ih R (lotteryStep k s true) htrue
        rw [hfalseDP, htrueDP]
        simp [lotteryDiscountHeadDP, hw, Nat.pow_succ,
          Nat.mul_add, Nat.succ_mul]
        all_goals try simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        all_goals omega
      · have hfalse : (lotteryStep k s false).headRun < k := by
          simp [lotteryStep]
          omega
        have htrue : (lotteryStep k s true).headRun < k := by
          simp [lotteryStep, hw]
          omega
        have hfunFalse :
            (fun u : LotteryState =>
              2 ^ (T + 1 + R + s.wins - u.wins)) =
            (fun u : LotteryState =>
              2 ^ (T + (R + 1) +
                (lotteryStep k s false).wins - u.wins)) := by
          funext u
          apply congrArg (fun z : Nat => 2 ^ z)
          simp [lotteryStep] <;> omega
        have hfunTrue :
            (fun u : LotteryState =>
              2 ^ (T + 1 + R + s.wins - u.wins)) =
            (fun u : LotteryState =>
              2 ^ (T + (R + 1) +
                (lotteryStep k s true).wins - u.wins)) := by
          funext u
          apply congrArg (fun z : Nat => 2 ^ z)
          simp [lotteryStep, hw] <;> omega
        have hfalseDP :
            lotteryNatDP k
                (fun u => 2 ^ (T + 1 + R + s.wins - u.wins))
                T (lotteryStep k s false) =
              2 ^ (R + 1) * lotteryDiscountHeadDP k T 0 := by
          rw [hfunFalse]
          simpa [lotteryStep] using
            ih (R + 1) (lotteryStep k s false) hfalse
        have htrueDP :
            lotteryNatDP k
                (fun u => 2 ^ (T + 1 + R + s.wins - u.wins))
                T (lotteryStep k s true) =
              2 ^ (R + 1) *
                lotteryDiscountHeadDP k T (s.headRun + 1) := by
          rw [hfunTrue]
          simpa [lotteryStep, hw] using
            ih (R + 1) (lotteryStep k s true) htrue
        rw [hfalseDP, htrueDP]
        simp [lotteryDiscountHeadDP, hw, Nat.pow_succ,
          Nat.mul_add] <;> ac_rfl

private theorem upperPotential_floor (k h : Nat) :
    2 ^ k ≤ lotteryUpperPotential k h := by
  unfold lotteryUpperPotential
  exact Nat.le_add_right _ _

private theorem upperPotential_step (k h : Nat) :
    2 ^ k *
        (lotteryUpperPotential k 0 +
          lotteryUpperPotential k (h + 1)) ≤
      lotteryUpperGrowth k * lotteryUpperPotential k h := by
  have heq :
      lotteryUpperGrowth k * lotteryUpperPotential k h =
        2 ^ k *
            (lotteryUpperPotential k 0 +
              lotteryUpperPotential k (h + 1)) +
          2 ^ k + 2 ^ (h + 1) := by
    simp only [lotteryUpperGrowth, lotteryUpperPotential,
      Nat.pow_zero, Nat.pow_succ, Nat.mul_add, Nat.add_mul,
      Nat.mul_one, Nat.one_mul, Nat.two_mul]
    try simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  rw [heq]
  have hnonneg : 0 ≤ 2 ^ k + 2 ^ (h + 1) := Nat.zero_le _
  omega

private theorem upperPotential_win
    (k h : Nat) (hs : h < k) (hw : k ≤ h + 1) :
    3 * 2 ^ k * lotteryUpperPotential k 0 ≤
      lotteryUpperGrowth k * lotteryUpperPotential k h := by
  have hk : k = h + 1 := by omega
  subst k
  let x := 2 ^ h
  have hq : 2 ^ (h + 1) = 2 * x := by
    dsimp [x]
    rw [Nat.pow_succ] <;> ac_rfl
  have hv0 : lotteryUpperPotential (h + 1) 0 = 2 * x + 1 := by
    unfold lotteryUpperPotential
    rw [Nat.pow_zero, hq]
  have hvh : lotteryUpperPotential (h + 1) h = 3 * x := by
    unfold lotteryUpperPotential
    rw [hq]
    dsimp [x]
    omega
  have hg : lotteryUpperGrowth (h + 1) = 2 * (2 * x + 1) := by
    unfold lotteryUpperGrowth
    rw [hq]
  rw [hq, hv0, hvh, hg]
  exact Nat.le_of_eq (by ac_rfl)

private theorem upperHeadDP_potential
    (k T h : Nat) (hk : 1 ≤ k) (hh : h < k) :
    (2 ^ k) ^ (T + 1) * lotteryUpperHeadDP k T h ≤
      (lotteryUpperGrowth k) ^ T * lotteryUpperPotential k h := by
  induction T generalizing h with
  | zero =>
      simpa [lotteryUpperHeadDP, Nat.pow_succ] using
        upperPotential_floor k h
  | succ T ih =>
      rw [lotteryUpperHeadDP]
      by_cases hw : k ≤ h + 1
      · rw [if_pos hw]
        have hi := ih 0 (by omega)
        have hs := upperPotential_win k h hh hw
        calc
          (2 ^ k) ^ (T + 2) *
                (3 * lotteryUpperHeadDP k T 0) =
              (3 * 2 ^ k) *
                ((2 ^ k) ^ (T + 1) *
                  lotteryUpperHeadDP k T 0) := by
            rw [Nat.pow_succ] <;> ac_rfl
          _ ≤ (3 * 2 ^ k) *
                ((lotteryUpperGrowth k) ^ T *
                  lotteryUpperPotential k 0) :=
            Nat.mul_le_mul_left _ hi
          _ = (lotteryUpperGrowth k) ^ T *
                (3 * 2 ^ k * lotteryUpperPotential k 0) := by
            ac_rfl
          _ ≤ (lotteryUpperGrowth k) ^ T *
                (lotteryUpperGrowth k *
                  lotteryUpperPotential k h) :=
            Nat.mul_le_mul_left _ hs
          _ = (lotteryUpperGrowth k) ^ (T + 1) *
                lotteryUpperPotential k h := by
            rw [Nat.pow_succ] <;> ac_rfl
      · rw [if_neg hw]
        have hh1 : h + 1 < k := by omega
        have hi0 := ih 0 (by omega)
        have hi1 := ih (h + 1) hh1
        have hsum := Nat.add_le_add hi0 hi1
        have hs := upperPotential_step k h
        calc
          (2 ^ k) ^ (T + 2) *
                (lotteryUpperHeadDP k T 0 +
                  lotteryUpperHeadDP k T (h + 1)) =
              2 ^ k *
                ((2 ^ k) ^ (T + 1) *
                    lotteryUpperHeadDP k T 0 +
                  (2 ^ k) ^ (T + 1) *
                    lotteryUpperHeadDP k T (h + 1)) := by
            rw [Nat.pow_succ, Nat.mul_add]
            simp only [Nat.mul_add, Nat.add_mul]
            ac_rfl
          _ ≤ 2 ^ k *
                ((lotteryUpperGrowth k) ^ T *
                    lotteryUpperPotential k 0 +
                  (lotteryUpperGrowth k) ^ T *
                    lotteryUpperPotential k (h + 1)) :=
            Nat.mul_le_mul_left _ hsum
          _ = (lotteryUpperGrowth k) ^ T *
                (2 ^ k *
                  (lotteryUpperPotential k 0 +
                    lotteryUpperPotential k (h + 1))) := by
            rw [Nat.mul_add, Nat.mul_add]
            simp only [Nat.mul_add, Nat.add_mul]
            ac_rfl
          _ ≤ (lotteryUpperGrowth k) ^ T *
                (lotteryUpperGrowth k *
                  lotteryUpperPotential k h) :=
            Nat.mul_le_mul_left _ hs
          _ = (lotteryUpperGrowth k) ^ (T + 1) *
                lotteryUpperPotential k h := by
            rw [Nat.pow_succ] <;> ac_rfl

private theorem downPotential_floor
    (k h : Nat) (hh : h < k) :
    2 ^ k ≤ lotteryDownPotential k h := by
  have hp : 2 ^ h ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by omega) (by omega)
  unfold lotteryDownPotential
  omega

private theorem downPotential_step
    (k h : Nat) (hh : h + 1 < k) :
    2 ^ k *
        (2 * lotteryDownPotential k 0 +
          2 * lotteryDownPotential k (h + 1)) ≤
      lotteryDownGrowth k * lotteryDownPotential k h := by
  have hp : 2 ^ (h + 1) ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.pow_succ] at hp
  have hp0 : 2 ^ h ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hq : 0 < 2 ^ k := Nat.pow_pos (by omega)
  have hlin :
      2 * lotteryDownPotential k 0 +
          2 * lotteryDownPotential k (h + 1) + 2 =
        4 * lotteryDownPotential k h := by
    unfold lotteryDownPotential
    rw [Nat.pow_zero, Nat.pow_succ]
    omega
  have hvle :
      lotteryDownPotential k h ≤ 2 * 2 ^ k := by
    unfold lotteryDownPotential
    exact Nat.sub_le _ _
  have hcommon1 :
      2 ^ k *
            (2 * lotteryDownPotential k 0 +
              2 * lotteryDownPotential k (h + 1)) +
          2 * 2 ^ k =
        4 * 2 ^ k * lotteryDownPotential k h := by
    calc
      _ = 2 ^ k *
          ((2 * lotteryDownPotential k 0 +
              2 * lotteryDownPotential k (h + 1)) + 2) := by
            rw [Nat.mul_add]
            simp only [Nat.mul_add, Nat.add_mul, Nat.two_mul]
            omega
      _ = 2 ^ k * (4 * lotteryDownPotential k h) := by
            rw [hlin]
      _ = _ := by ac_rfl
  have hqpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
  have hpred : (4 * 2 ^ k - 1) + 1 = 4 * 2 ^ k := by
    omega
  have hcommon2 :
      lotteryDownGrowth k * lotteryDownPotential k h +
          lotteryDownPotential k h =
        4 * 2 ^ k * lotteryDownPotential k h := by
    unfold lotteryDownGrowth
    calc
      (4 * 2 ^ k - 1) * lotteryDownPotential k h +
            lotteryDownPotential k h =
          ((4 * 2 ^ k - 1) + 1) *
            lotteryDownPotential k h := by
              rw [Nat.add_mul, Nat.one_mul]
      _ = 4 * 2 ^ k * lotteryDownPotential k h := by
              rw [hpred]
  have hadd :
      2 ^ k *
            (2 * lotteryDownPotential k 0 +
              2 * lotteryDownPotential k (h + 1)) +
          lotteryDownPotential k h ≤
        lotteryDownGrowth k * lotteryDownPotential k h +
          lotteryDownPotential k h := by
    calc
      _ ≤ 2 ^ k *
            (2 * lotteryDownPotential k 0 +
              2 * lotteryDownPotential k (h + 1)) +
          2 * 2 ^ k :=
        Nat.add_le_add_left hvle _
      _ = 4 * 2 ^ k * lotteryDownPotential k h := hcommon1
      _ = _ := hcommon2.symm
  omega

private theorem downPotential_win
    (k h : Nat) (hs : h < k) (hw : k ≤ h + 1) :
    3 * 2 ^ k * lotteryDownPotential k 0 ≤
      lotteryDownGrowth k * lotteryDownPotential k h := by
  have hk : k = h + 1 := by omega
  subst k
  let x := 2 ^ h
  have hxpos : 0 < x := by
    dsimp [x]
    exact Nat.pow_pos (by omega)
  have hq : 2 ^ (h + 1) = 2 * x := by
    dsimp [x]
    rw [Nat.pow_succ] <;> ac_rfl
  have hv0 : lotteryDownPotential (h + 1) 0 = 4 * x - 1 := by
    unfold lotteryDownPotential
    rw [Nat.pow_zero, hq]
    omega
  have hvh : lotteryDownPotential (h + 1) h = 3 * x := by
    unfold lotteryDownPotential
    rw [hq]
    dsimp [x]
    omega
  have hg : lotteryDownGrowth (h + 1) = 8 * x - 1 := by
    unfold lotteryDownGrowth
    rw [hq]
    omega
  have hinner : 2 * (4 * x - 1) ≤ 8 * x - 1 := by
    omega
  rw [hq, hv0, hvh, hg]
  calc
    3 * (2 * x) * (4 * x - 1) =
        (3 * x) * (2 * (4 * x - 1)) := by ac_rfl
    _ ≤ (3 * x) * (8 * x - 1) :=
      Nat.mul_le_mul_left _ hinner
    _ = (8 * x - 1) * (3 * x) := by ac_rfl

private theorem discountHeadDP_potential
    (k T h : Nat) (hk : 1 ≤ k) (hh : h < k) :
    (2 ^ k) ^ (T + 1) * lotteryDiscountHeadDP k T h ≤
      (lotteryDownGrowth k) ^ T * lotteryDownPotential k h := by
  induction T generalizing h with
  | zero =>
      simpa [lotteryDiscountHeadDP, Nat.pow_succ] using
        downPotential_floor k h hh
  | succ T ih =>
      rw [lotteryDiscountHeadDP]
      by_cases hw : k ≤ h + 1
      · rw [if_pos hw]
        have hi := ih 0 (by omega)
        have hs := downPotential_win k h hh hw
        calc
          (2 ^ k) ^ (T + 2) *
                (3 * lotteryDiscountHeadDP k T 0) =
              (3 * 2 ^ k) *
                ((2 ^ k) ^ (T + 1) *
                  lotteryDiscountHeadDP k T 0) := by
            rw [Nat.pow_succ] <;> ac_rfl
          _ ≤ (3 * 2 ^ k) *
                ((lotteryDownGrowth k) ^ T *
                  lotteryDownPotential k 0) :=
            Nat.mul_le_mul_left _ hi
          _ = (lotteryDownGrowth k) ^ T *
                (3 * 2 ^ k * lotteryDownPotential k 0) := by
            ac_rfl
          _ ≤ (lotteryDownGrowth k) ^ T *
                (lotteryDownGrowth k *
                  lotteryDownPotential k h) :=
            Nat.mul_le_mul_left _ hs
          _ = (lotteryDownGrowth k) ^ (T + 1) *
                lotteryDownPotential k h := by
            rw [Nat.pow_succ] <;> ac_rfl
      · rw [if_neg hw]
        have hh1 : h + 1 < k := by omega
        have hi0 := ih 0 (by omega)
        have hi1 := ih (h + 1) hh1
        have hsum :=
          Nat.add_le_add
            (Nat.mul_le_mul_left 2 hi0)
            (Nat.mul_le_mul_left 2 hi1)
        have hs := downPotential_step k h hh1
        calc
          (2 ^ k) ^ (T + 2) *
                (2 * lotteryDiscountHeadDP k T 0 +
                  2 * lotteryDiscountHeadDP k T (h + 1)) =
              2 ^ k *
                (2 * ((2 ^ k) ^ (T + 1) *
                    lotteryDiscountHeadDP k T 0) +
                  2 * ((2 ^ k) ^ (T + 1) *
                    lotteryDiscountHeadDP k T (h + 1))) := by
            rw [Nat.pow_succ, Nat.mul_add]
            simp only [Nat.mul_add, Nat.add_mul, Nat.two_mul]
            ac_rfl
          _ ≤ 2 ^ k *
                (2 * ((lotteryDownGrowth k) ^ T *
                    lotteryDownPotential k 0) +
                  2 * ((lotteryDownGrowth k) ^ T *
                    lotteryDownPotential k (h + 1))) :=
            Nat.mul_le_mul_left _ hsum
          _ = (lotteryDownGrowth k) ^ T *
                (2 ^ k *
                  (2 * lotteryDownPotential k 0 +
                    2 * lotteryDownPotential k (h + 1))) := by
            rw [Nat.mul_add]
            simp only [Nat.mul_add, Nat.add_mul, Nat.two_mul]
            ac_rfl
          _ ≤ (lotteryDownGrowth k) ^ T *
                (lotteryDownGrowth k *
                  lotteryDownPotential k h) :=
            Nat.mul_le_mul_left _ hs
          _ = (lotteryDownGrowth k) ^ (T + 1) *
                lotteryDownPotential k h := by
            rw [Nat.pow_succ] <;> ac_rfl

private theorem addOne_pow_self_le_three_mul_pow_self
    (q : Nat) (hq : 1 ≤ q) :
    (q + 1) ^ q ≤ 3 * q ^ q := by
  have hbase :=
    addTwo_pow_self_le_eight_mul_pow_self (2 * q) (by omega)
  have hscaled :
      2 ^ (2 * q) * (q + 1) ^ (2 * q) ≤
        2 ^ (2 * q) * (8 * q ^ (2 * q)) := by
    calc
      _ = (2 * q + 2) ^ (2 * q) := by
        rw [show 2 * q + 2 = 2 * (q + 1) by omega,
          Nat.mul_pow] <;> ac_rfl
      _ ≤ 8 * (2 * q) ^ (2 * q) := hbase
      _ = _ := by
        rw [Nat.mul_pow] <;> ac_rfl
  have hcancel :
      (q + 1) ^ (2 * q) ≤ 8 * q ^ (2 * q) :=
    Nat.le_of_mul_le_mul_left hscaled (Nat.pow_pos (by omega))
  have hsq :
      ((q + 1) ^ q) * ((q + 1) ^ q) ≤
        8 * ((q ^ q) * (q ^ q)) := by
    have he : 2 * q = q + q := by omega
    rw [he, Nat.pow_add, Nat.pow_add] at hcancel
    exact hcancel
  by_cases hgood : (q + 1) ^ q ≤ 3 * q ^ q
  · exact hgood
  · have hlt : 3 * q ^ q < (q + 1) ^ q := by omega
    have hle : 3 * q ^ q ≤ (q + 1) ^ q := Nat.le_of_lt hlt
    have hsquare := Nat.mul_le_mul hle hle
    have hbad :
        9 * ((q ^ q) * (q ^ q)) ≤
          8 * ((q ^ q) * (q ^ q)) := by
      calc
        _ = (3 * q ^ q) * (3 * q ^ q) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ ((q + 1) ^ q) * ((q + 1) ^ q) := hsquare
        _ ≤ 8 * ((q ^ q) * (q ^ q)) := hsq
    have hpos : 0 < (q ^ q) * (q ^ q) :=
      Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
    omega

private theorem three_pow_close
    (a : Nat) (ha : 1 ≤ a) :
    3 ^ (4 * a + 1) ≤ 2 ^ (7 * a + 1) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 :=
    ⟨a - 1, by omega⟩
  induction b with
  | zero =>
      decide
  | succ b ih =>
      have h81 : 3 ^ 4 ≤ 2 ^ 7 := by decide
      have ih' := ih (by omega)
      have hmul := Nat.mul_le_mul ih' h81
      calc
        3 ^ (4 * (b + 2) + 1) =
            3 ^ (4 * (b + 1) + 1) * 3 ^ 4 := by
          rw [← Nat.pow_add]
          congr 1
        _ ≤ 2 ^ (7 * (b + 1) + 1) * 2 ^ 7 := hmul
        _ = 2 ^ (7 * (b + 2) + 1) := by
          rw [← Nat.pow_add]
          congr 1

private theorem upper_horizon_ratio
    (q a : Nat) (hq : 2 ≤ q) (ha : 1 ≤ a) :
    (q + 1) ^ (4 * a * q + 1) ≤
      q ^ (4 * a * q + 1) * 2 ^ (7 * a) := by
  have he := addOne_pow_self_le_three_mul_pow_self q (by omega)
  have hpow := Nat.pow_le_pow_left he (4 * a)
  have hExp : 4 * a * q = q * (4 * a) := by ac_rfl
  have hblock :
      (q + 1) ^ (4 * a * q) ≤
        3 ^ (4 * a) * q ^ (4 * a * q) := by
    calc
      (q + 1) ^ (4 * a * q) =
          ((q + 1) ^ q) ^ (4 * a) := by
        rw [hExp, Nat.pow_mul]
      _ ≤ (3 * q ^ q) ^ (4 * a) := hpow
      _ = 3 ^ (4 * a) * (q ^ q) ^ (4 * a) := by
        rw [Nat.mul_pow]
      _ = 3 ^ (4 * a) * q ^ (4 * a * q) := by
        rw [← Nat.pow_mul, ← hExp]
  have h3 := three_pow_close a ha
  have hpair : 2 * (q + 1) ≤ 3 * q := by omega
  have hcoef2 :
      2 * (3 ^ (4 * a) * (q + 1)) ≤
        2 * (2 ^ (7 * a) * q) := by
    calc
      _ = 3 ^ (4 * a) * (2 * (q + 1)) := by ac_rfl
      _ ≤ 3 ^ (4 * a) * (3 * q) :=
        Nat.mul_le_mul_left _ hpair
      _ = 3 ^ (4 * a + 1) * q := by
        rw [Nat.pow_succ] <;> ac_rfl
      _ ≤ 2 ^ (7 * a + 1) * q :=
        Nat.mul_le_mul_right q h3
      _ = 2 * (2 ^ (7 * a) * q) := by
        rw [Nat.pow_succ] <;> ac_rfl
  have hcoef :
      3 ^ (4 * a) * (q + 1) ≤ 2 ^ (7 * a) * q :=
    Nat.le_of_mul_le_mul_left hcoef2 (by omega)
  calc
    (q + 1) ^ (4 * a * q + 1) =
        (q + 1) ^ (4 * a * q) * (q + 1) := by
      rw [Nat.pow_succ]
    _ ≤ (3 ^ (4 * a) * q ^ (4 * a * q)) * (q + 1) :=
      Nat.mul_le_mul_right _ hblock
    _ = q ^ (4 * a * q) *
          (3 ^ (4 * a) * (q + 1)) := by ac_rfl
    _ ≤ q ^ (4 * a * q) * (2 ^ (7 * a) * q) :=
      Nat.mul_le_mul_left _ hcoef
    _ = q ^ (4 * a * q + 1) * 2 ^ (7 * a) := by
      rw [Nat.pow_succ] <;> ac_rfl

private theorem lotteryNatBernoulliMoment
    (a : Nat) : ∀ k,
      a ^ (k + 1) + (k + 1) * a ^ k ≤ (a + 1) ^ (k + 1)
  | 0 => by simp
  | k + 1 => by
      have ih := lotteryNatBernoulliMoment a k
      have h1 :
          (a + 1) *
                (a ^ (k + 1) + (k + 1) * a ^ k) ≤
            (a + 1) * (a + 1) ^ (k + 1) :=
        Nat.mul_le_mul_left _ ih
      have e2 :
          (a + 1) *
                (a ^ (k + 1) + (k + 1) * a ^ k) =
            a ^ (k + 1 + 1) +
              (k + 1) * a ^ (k + 1) +
              a ^ (k + 1) +
              (k + 1) * a ^ k := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_add,
          Nat.pow_succ a (k + 1)]
        have hmul :
            a * ((k + 1) * a ^ k) =
              (k + 1) * a ^ (k + 1) := by
          rw [Nat.pow_succ, Nat.mul_left_comm,
            Nat.mul_comm (a ^ k) a]
        rw [hmul, Nat.mul_comm a (a ^ (k + 1))]
        omega
      have e3 :
          (a + 1) * (a + 1) ^ (k + 1) =
            (a + 1) ^ (k + 1 + 1) := by
        rw [Nat.pow_succ (a + 1) (k + 1), Nat.mul_comm]
      rw [e2, e3] at h1
      have e4 :
          (k + 1 + 1) * a ^ (k + 1) =
            (k + 1) * a ^ (k + 1) + a ^ (k + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [e4]
      omega

private theorem two_mul_pred_pow_self_le
    (N : Nat) (hN : 1 ≤ N) :
    2 * (N - 1) ^ N ≤ N ^ N := by
  obtain ⟨a, rfl⟩ : ∃ a, N = a + 1 :=
    ⟨N - 1, by omega⟩
  have hb := lotteryNatBernoulliMoment a a
  have h2 : a ^ (a + 1) ≤ (a + 1) * a ^ a := by
    rw [Nat.pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.le_succ a)
  simp only [Nat.add_sub_cancel]
  omega

private theorem down_horizon_ratio
    (q a : Nat) (hq : 1 ≤ q) (ha : 1 ≤ a) :
    2 ^ (9 * a + 1) * (4 * q - 1) ^ (64 * a * q) ≤
      (4 * q) ^ (64 * a * q) := by
  have hhalf := two_mul_pred_pow_self_le (4 * q) (by omega)
  have hpow := Nat.pow_le_pow_left hhalf (16 * a)
  have hExp : (4 * q) * (16 * a) = 64 * a * q := by ac_rfl
  have hblock :
      2 ^ (16 * a) * (4 * q - 1) ^ (64 * a * q) ≤
        (4 * q) ^ (64 * a * q) := by
    calc
      _ = (2 * (4 * q - 1) ^ (4 * q)) ^ (16 * a) := by
        rw [Nat.mul_pow, ← Nat.pow_mul, hExp]
      _ ≤ ((4 * q) ^ (4 * q)) ^ (16 * a) := hpow
      _ = (4 * q) ^ (64 * a * q) := by
        rw [← Nat.pow_mul, hExp]
  have hsmall :
      2 ^ (9 * a + 1) ≤ 2 ^ (16 * a) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc
    2 ^ (9 * a + 1) * (4 * q - 1) ^ (64 * a * q) ≤
        2 ^ (16 * a) * (4 * q - 1) ^ (64 * a * q) :=
      Nat.mul_le_mul_right _ hsmall
    _ ≤ (4 * q) ^ (64 * a * q) := hblock

private theorem upper_moment_bound
    (k a : Nat) (hk : 1 ≤ k) (ha : 1 ≤ a) :
    2 ^ a *
        lotteryNatDP k (fun s => 2 ^ s.wins)
          (4 * a * 2 ^ k) lotteryFresh ≤
      2 ^ (4 * a * 2 ^ k + 8 * a) := by
  let H := 4 * a * 2 ^ k
  change
    2 ^ a *
        lotteryNatDP k (fun s => 2 ^ s.wins) H lotteryFresh ≤
      2 ^ (H + 8 * a)
  have hdp :=
    lotteryUpperHeadDP_eq_natDP k H lotteryFresh (by
      simp [lotteryFresh]
      omega)
  have hdp0 :
      lotteryNatDP k (fun s => 2 ^ s.wins) H lotteryFresh =
        lotteryUpperHeadDP k H 0 := by
    simpa [lotteryFresh] using hdp
  have hpot := upperHeadDP_potential k H 0 hk (by omega)
  have hpot' :
      (2 ^ k) ^ (H + 1) * lotteryUpperHeadDP k H 0 ≤
        2 ^ H * (2 ^ k + 1) ^ (H + 1) := by
    calc
      _ ≤ (lotteryUpperGrowth k) ^ H *
            lotteryUpperPotential k 0 := hpot
      _ = 2 ^ H * (2 ^ k + 1) ^ (H + 1) := by
        unfold lotteryUpperGrowth lotteryUpperPotential
        rw [Nat.pow_zero, Nat.mul_pow, Nat.pow_succ] <;> ac_rfl
  have hq2 : 2 ≤ 2 ^ k := by
    have h : 2 ^ 1 ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by omega) hk
    simpa using h
  have hratio0 := upper_horizon_ratio (2 ^ k) a hq2 ha
  have hratio :
      (2 ^ k + 1) ^ (H + 1) ≤
        (2 ^ k) ^ (H + 1) * 2 ^ (7 * a) := by
    simpa [H] using hratio0
  have hchain :
      (2 ^ k) ^ (H + 1) *
            (2 ^ a * lotteryUpperHeadDP k H 0) ≤
        (2 ^ k) ^ (H + 1) *
            (2 ^ a * 2 ^ H * 2 ^ (7 * a)) := by
    calc
      _ = 2 ^ a *
            ((2 ^ k) ^ (H + 1) *
              lotteryUpperHeadDP k H 0) := by ac_rfl
      _ ≤ 2 ^ a *
            (2 ^ H * (2 ^ k + 1) ^ (H + 1)) :=
        Nat.mul_le_mul_left _ hpot'
      _ ≤ 2 ^ a *
            (2 ^ H *
              ((2 ^ k) ^ (H + 1) * 2 ^ (7 * a))) :=
        Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ hratio)
      _ = _ := by ac_rfl
  have hcancel :
      2 ^ a * lotteryUpperHeadDP k H 0 ≤
        2 ^ a * 2 ^ H * 2 ^ (7 * a) :=
    Nat.le_of_mul_le_mul_left hchain
      (Nat.pow_pos (by omega))
  rw [hdp0]
  calc
    2 ^ a * lotteryUpperHeadDP k H 0 ≤
        2 ^ a * 2 ^ H * 2 ^ (7 * a) := hcancel
    _ = 2 ^ (H + 8 * a) := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      congr 1
      omega

private theorem lower_moment_bound
    (k a : Nat) (hk : 1 ≤ k) (ha : 1 ≤ a) :
    2 ^ a *
        lotteryNatDP k
          (fun s => 2 ^ (64 * a * 2 ^ k + 8 * a - s.wins))
          (64 * a * 2 ^ k) lotteryFresh ≤
      2 ^ (64 * a * 2 ^ k + 64 * a * 2 ^ k) := by
  let H := 64 * a * 2 ^ k
  change
    2 ^ a *
        lotteryNatDP k (fun s => 2 ^ (H + 8 * a - s.wins))
          H lotteryFresh ≤
      2 ^ (H + H)
  have hdp :=
    lotteryDiscountHeadDP_eq_natDP k H (8 * a)
      lotteryFresh (by
        simp [lotteryFresh]
        omega)
  have hdp0 :
      lotteryNatDP k (fun s => 2 ^ (H + 8 * a - s.wins))
          H lotteryFresh =
        2 ^ (8 * a) * lotteryDiscountHeadDP k H 0 := by
    simpa [lotteryFresh] using hdp
  have hpot := discountHeadDP_potential k H 0 hk (by omega)
  have hvle :
      lotteryDownPotential k 0 ≤ 2 * 2 ^ k := by
    unfold lotteryDownPotential
    exact Nat.sub_le _ _
  have hpot2 :
      (2 ^ k) ^ (H + 1) * lotteryDiscountHeadDP k H 0 ≤
        (lotteryDownGrowth k) ^ H * (2 * 2 ^ k) :=
    Nat.le_trans hpot
      (Nat.mul_le_mul_left _ hvle)
  have hqpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
  have hscaled :
      2 ^ k *
          ((2 ^ k) ^ H * lotteryDiscountHeadDP k H 0) ≤
        2 ^ k * (2 * (lotteryDownGrowth k) ^ H) := by
    calc
      _ = (2 ^ k) ^ (H + 1) *
            lotteryDiscountHeadDP k H 0 := by
        rw [Nat.pow_succ] <;> ac_rfl
      _ ≤ (lotteryDownGrowth k) ^ H * (2 * 2 ^ k) := hpot2
      _ = _ := by ac_rfl
  have hsimple :
      (2 ^ k) ^ H * lotteryDiscountHeadDP k H 0 ≤
        2 * (lotteryDownGrowth k) ^ H :=
    Nat.le_of_mul_le_mul_left hscaled hqpos
  have hratio0 := down_horizon_ratio (2 ^ k) a (by omega) ha
  have hratio :
      2 ^ (9 * a + 1) * (lotteryDownGrowth k) ^ H ≤
        (4 * 2 ^ k) ^ H := by
    simpa [lotteryDownGrowth, H] using hratio0
  have hfour :
      (4 * 2 ^ k) ^ H =
        (2 ^ k) ^ H * 2 ^ (H + H) := by
    rw [show (4 : Nat) = 2 ^ 2 by rfl, Nat.mul_pow,
      ← Nat.pow_mul]
    have he : 2 * H = H + H := by omega
    rw [he]
    ac_rfl
  have hchain :
      (2 ^ k) ^ H *
          (2 ^ (9 * a) * lotteryDiscountHeadDP k H 0) ≤
        (2 ^ k) ^ H * 2 ^ (H + H) := by
    calc
      _ = 2 ^ (9 * a) *
            ((2 ^ k) ^ H * lotteryDiscountHeadDP k H 0) := by
        ac_rfl
      _ ≤ 2 ^ (9 * a) *
            (2 * (lotteryDownGrowth k) ^ H) :=
        Nat.mul_le_mul_left _ hsimple
      _ = 2 ^ (9 * a + 1) *
            (lotteryDownGrowth k) ^ H := by
        rw [Nat.pow_succ] <;> ac_rfl
      _ ≤ (4 * 2 ^ k) ^ H := hratio
      _ = _ := hfour
  have hcancel :
      2 ^ (9 * a) * lotteryDiscountHeadDP k H 0 ≤
        2 ^ (H + H) :=
    Nat.le_of_mul_le_mul_left hchain
      (Nat.pow_pos (by omega))
  rw [hdp0]
  calc
    2 ^ a *
          (2 ^ (8 * a) * lotteryDiscountHeadDP k H 0) =
        2 ^ (9 * a) * lotteryDiscountHeadDP k H 0 := by
      have hexp : a + 8 * a = 9 * a := by omega
      rw [← Nat.mul_assoc, ← Nat.pow_add, hexp]
    _ ≤ 2 ^ (H + H) := hcancel

theorem lotteryTailMomentArithmetic : LotteryTailMomentArithmetic := by
  unfold LotteryTailMomentArithmetic
  intro k c hk hc
  have haPos : 0 < c * k :=
    Nat.mul_pos (by omega) (by omega)
  have ha : 1 ≤ c * k := by omega
  constructor
  · have h := upper_moment_bound k (c * k) hk ha
    simpa [lotteryL7Horizon, lotteryTarget, Nat.mul_assoc] using h
  · have h := lower_moment_bound k (c * k) hk ha
    simpa [lotteryL8Horizon, lotteryTarget, Nat.mul_assoc] using h

theorem lotteryCountBounds : LotteryCountBounds :=
  lotteryCountBounds_of_moments lotteryTailMomentArithmetic

#print axioms lotteryTailMomentArithmetic
#print axioms lotteryCountBounds

end PPL.Probability
