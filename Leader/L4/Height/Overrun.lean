import Leader.L4.Height.Window

namespace L4.Height

/-- The physical deadline has exactly the same expression as
    Physical.physicalDeadline. -/
def overrunDeadline (L m : Nat) : Nat := 2 ^ 29 * L * m

theorem nat_lt_two_pow_succ (n : Nat) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hp : 0 < 2 ^ (n + 1) := Nat.pow_pos (by omega)
      have hle : n + 1 ≤ 2 ^ (n + 1) := by omega
      calc
        n + 1 < 2 ^ (n + 1) * 2 := by omega
        _ = 2 ^ ((n + 1) + 1) :=
          (Nat.pow_succ 2 (n + 1)).symm

theorem level_budget (m D : Nat) (hm : 1 ≤ m) (hD : D ≤ m) :
    D + 200 + 32 * (2 ^ 19 * m) ≤ 2 ^ 25 * m := by
  have hconst : 32 * 2 ^ 19 = 2 ^ 24 := by decide
  calc
    D + 200 + 32 * (2 ^ 19 * m)
        ≤ m + 200 + 32 * (2 ^ 19 * m) := by omega
    _ = m + 200 + 2 ^ 24 * m := by
          rw [← Nat.mul_assoc, hconst]
    _ ≤ 2 ^ 25 * m := by omega

theorem three_pow_le_two_pow (h : Nat) :
    3 ^ h ≤ 2 ^ (2 * h) := by
  induction h with
  | zero => decide
  | succ h ih =>
      calc
        3 ^ (h + 1) = 3 ^ h * 3 := Nat.pow_succ 3 h
        _ ≤ 2 ^ (2 * h) * 4 :=
          Nat.mul_le_mul ih (by omega)
        _ = 2 ^ (2 * h + 2) := by
          rw [Nat.pow_add]
        _ = 2 ^ (2 * (h + 1)) :=
          congrArg (fun q : Nat => 2 ^ q) (by omega)

theorem log2_le_self (n : Nat) (hn : 1 ≤ n) :
    Nat.log2 n ≤ n := by
  have hne : n ≠ 0 := by omega
  have hp : n < 2 ^ (n + 1) := nat_lt_two_pow_succ n
  have hlog : Nat.log2 n < n + 1 := (Nat.log2_lt hne).2 hp
  omega

theorem log2_mul_le (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.log2 (a * b) ≤ Nat.log2 a + Nat.log2 b + 1 := by
  have haPos : 0 < a := by omega
  have hbPos : 0 < b := by omega
  have habPos : 0 < a * b := Nat.mul_pos haPos hbPos
  have haPow : a < 2 ^ (Nat.log2 a + 1) :=
    (Nat.log2_lt (Nat.ne_of_gt haPos)).1 (by omega)
  have hbPow : b < 2 ^ (Nat.log2 b + 1) :=
    (Nat.log2_lt (Nat.ne_of_gt hbPos)).1 (by omega)
  have hprod :
      a * b < 2 ^ (Nat.log2 a + Nat.log2 b + 2) := by
    calc
      a * b < 2 ^ (Nat.log2 a + 1) * b :=
        Nat.mul_lt_mul_of_pos_right haPow hbPos
      _ < 2 ^ (Nat.log2 a + 1) *
            2 ^ (Nat.log2 b + 1) :=
        Nat.mul_lt_mul_of_pos_left hbPow (Nat.pow_pos (by omega))
      _ = 2 ^ (Nat.log2 a + Nat.log2 b + 2) := by
        rw [← Nat.pow_add]
        exact congrArg (fun q : Nat => 2 ^ q) (by omega)
  have hlog :
      Nat.log2 (a * b) < Nat.log2 a + Nat.log2 b + 2 :=
    (Nat.log2_lt (Nat.ne_of_gt habPos)).2 hprod
  omega

/-- A four-step induction gives a useful deficit relative to 2*h.
    The +1 permits the elementary log2-of-product bound. -/
theorem log2_three_pow_le (h : Nat) :
    Nat.log2 (3 ^ h) ≤ 2 * h - h / 4 + 1 := by
  induction h using Nat.strongRecOn with
  | ind h ih =>
      by_cases hs : h < 4
      · have hh : h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 := by omega
        rcases hh with hh | hh | hh | hh
        · subst h; decide
        · subst h; decide
        · subst h; decide
        · subst h; decide
      · let k := h - 4
        have hdecomp : h = k + 4 := by
          dsimp [k]
          omega
        have hk : k < h := by
          dsimp [k]
          omega
        have hki := ih k hk
        have hpow : 3 ^ h = 3 ^ k * 3 ^ 4 := by
          rw [hdecomp, Nat.pow_add]
        have hkpos : 1 ≤ 3 ^ k := by
          have hp : 0 < 3 ^ k := Nat.pow_pos (by omega)
          omega
        have hlogmul := log2_mul_le (3 ^ k) (3 ^ 4)
          hkpos (by decide)
        have hlog81 : Nat.log2 (3 ^ 4) ≤ 6 := by
          have hp : 3 ^ 4 < 2 ^ 7 := by decide
          have hpos : 0 < 3 ^ 4 := Nat.pow_pos (by omega)
          have hz := (Nat.log2_lt (Nat.ne_of_gt hpos)).2 hp
          omega
        have hbound :
            Nat.log2 (3 ^ k * 3 ^ 4) ≤
              (2 * k - k / 4 + 1) + 7 := by
          calc
            Nat.log2 (3 ^ k * 3 ^ 4)
                ≤ Nat.log2 (3 ^ k) + Nat.log2 (3 ^ 4) + 1 :=
                  hlogmul
            _ ≤ (2 * k - k / 4 + 1) + 7 := by omega
        rw [hpow]
        have hquot : (k + 4) / 4 = k / 4 + 1 := by omega
        rw [hdecomp, hquot]
        omega

theorem log_mean_budget (m h : Nat) (hm : 1 ≤ m)
    (hh : h ≤ 2 ^ 25 * m) :
    Nat.log2 (m * 3 ^ h) + 2 * h + 4 ≤ 2 ^ 27 * m := by
  have hmLog : Nat.log2 m ≤ m := log2_le_self m hm
  have hthree := log2_three_pow_le h
  have hpowpos : 1 ≤ 3 ^ h := by
    have hp : 0 < 3 ^ h := Nat.pow_pos (by omega)
    omega
  have hprod := log2_mul_le m (3 ^ h) hm hpowpos
  have hlog :
      Nat.log2 (m * 3 ^ h) + 2 * h + 4
        ≤ m + (2 * h - h / 4 + 1) + 1 + 2 * h + 4 := by
    omega
  by_cases hlarge : 4 * (m + 6) ≤ h
  · have hdiv : m + 6 ≤ h / 4 := by omega
    have htotal :
        m + (2 * h - h / 4 + 1) + 1 + 2 * h + 4
          ≤ 4 * h := by omega
    have hfour : 4 * h ≤ 2 ^ 27 * m := by
      have hs : 4 * (2 ^ 25 * m) = 2 ^ 27 * m := by
        simp only [show 2 ^ 25 = 33554432 by decide,
          show 2 ^ 27 = 134217728 by decide]
        omega
      have hmul := Nat.mul_le_mul_left 4 hh
      omega
    omega
  · have hsmall : h ≤ 4 * (m + 6) := by omega
    have hroom : m + 4 * h + 6 ≤ 2 ^ 27 * m := by
      omega
    omega

theorem markov_deadline {N : Nat} (X : List (Fin N) → Nat)
    (d K : Nat)
    (hmean : wordSum (fun u => min (X u) d) d ≤ K * N ^ d) :
    d * wordSum (fun u => if d ≤ X u then 1 else 0) d ≤ K * N ^ d := by
  have hpoint : ∀ u, d * (if d ≤ X u then 1 else 0) ≤ min (X u) d := by
    intro u
    by_cases h : d ≤ X u
    · simp [h]
    · simp [h]
  calc
    d * wordSum (fun u => if d ≤ X u then 1 else 0) d
        = wordSum (fun u => d * (if d ≤ X u then 1 else 0)) d := by
          symm
          exact wordSum_mul_left d (fun u => if d ≤ X u then 1 else 0) d
    _ ≤ wordSum (fun u => min (X u) d) d :=
      wordSum_mono _ _ hpoint d
    _ ≤ K * N ^ d := hmean

theorem overrun_quarter {N : Nat} (L m h : Nat)
    (X : List (Fin N) → Nat)
    (hL : 1 ≤ L) (hm : 1 ≤ m)
    (hh : h ≤ 2 ^ 25 * m)
    (hmean : ∀ t : Nat,
      wordSum (fun u => min (X u) t) t ≤
        L * (Nat.log2 (m * 3 ^ h) + 2 * h + 4) * N ^ t) :
    4 * wordSum
      (fun u => if overrunDeadline L m ≤ X u then 1 else 0)
      (overrunDeadline L m) ≤ N ^ (overrunDeadline L m) := by
  let d := overrunDeadline L m
  let C := L * (2 ^ 27 * m)
  have hlog := log_mean_budget m h hm hh
  have hmeanD := hmean d
  have hK :
      L * (Nat.log2 (m * 3 ^ h) + 2 * h + 4) ≤ C := by
    dsimp [C]
    exact Nat.mul_le_mul_left L hlog
  have hmeanBound :
      wordSum (fun u => min (X u) d) d ≤ C * N ^ d := by
    calc
      wordSum (fun u => min (X u) d) d
          ≤ (L * (Nat.log2 (m * 3 ^ h) + 2 * h + 4)) * N ^ d :=
            hmeanD
      _ ≤ C * N ^ d := Nat.mul_le_mul_right (N ^ d) hK
  have hmark := markov_deadline X d C hmeanBound
  have hp : 2 ^ 29 = 4 * 2 ^ 27 := by decide
  have hd : d = 4 * C := by
    dsimp [d, overrunDeadline, C]
    calc
      2 ^ 29 * L * m = (4 * 2 ^ 27) * L * m := by rw [hp]
      _ = 4 * (L * (2 ^ 27 * m)) := by
        simp only [Nat.mul_left_comm, Nat.mul_comm]
  have hC : 0 < C := by
    dsimp [C]
    have hp27 : 0 < 2 ^ 27 := Nat.pow_pos (by omega)
    exact Nat.mul_pos hL (Nat.mul_pos hp27 hm)
  have hcancel : C * (4 *
      wordSum (fun u => if d ≤ X u then 1 else 0) d) ≤
      C * N ^ d := by
    calc
      C * (4 * wordSum (fun u => if d ≤ X u then 1 else 0) d)
          = (4 * C) * wordSum
              (fun u => if d ≤ X u then 1 else 0) d := by
                simp only [Nat.mul_assoc, Nat.mul_left_comm]
      _ = d * wordSum
              (fun u => if d ≤ X u then 1 else 0) d := by rw [← hd]
      _ ≤ C * N ^ d := hmark
  have hfinal := Nat.le_of_mul_le_mul_left hcancel hC
  simpa [d] using hfinal

end L4.Height
