import Leader.L4.Height.Drift

/-!
# Arithmetic for the height-contraction windows

This file uses the accepted `fact`, `Vpot`, `gapWindowLen`, `wordSum`, and
interface definitions imported through `L4.Height.Drift`.
-/

namespace L4.Height

set_option maxHeartbeats 8000000

/-- `ceil (10*m/k)`, written with natural-number division. -/
def gapCeil (m k : Nat) : Nat :=
  (10 * m + k - 1) / k

/-- Count qualifying consecutive triples, consuming three gaps at a time.
The first two entries of each block are the two internal gaps. -/
def qualifyingTriples (G : Nat) : List Nat → Nat
  | a :: b :: _ :: rest =>
      (if a ≤ G ∧ b ≤ G then 1 else 0) + qualifyingTriples G rest
  | _ => 0

/-- The complementary number of nonqualifying consecutive triples. -/
def failingTriples (G : Nat) : List Nat → Nat
  | a :: b :: _ :: rest =>
      (if a ≤ G ∧ b ≤ G then 0 else 1) + failingTriples G rest
  | _ => 0

/-- The elementary floor estimate used in the triple count. -/
theorem five_mul_div_three (k : Nat) (hk : 3 ≤ k) :
    k ≤ 5 * (k / 3) := by
  have hq : 1 ≤ k / 3 :=
    (Nat.one_le_div_iff (by decide : 0 < 3)).2 hk
  have hmod := Nat.mod_add_div k 3
  have hr := Nat.mod_lt k (by decide : 0 < 3)
  omega

private theorem triples_partition (G : Nat) :
    ∀ gs : List Nat,
      qualifyingTriples G gs + failingTriples G gs = gs.length / 3
  | [] => by simp [qualifyingTriples, failingTriples]
  | [a] => by simp [qualifyingTriples, failingTriples]
  | [a, b] => by simp [qualifyingTriples, failingTriples]
  | a :: b :: c :: rest => by
      have ih := triples_partition G rest
      have hdiv :
          (a :: b :: c :: rest).length / 3 = rest.length / 3 + 1 := by
        simp only [List.length_cons]
        have he : rest.length + 1 + 1 + 1 = rest.length + 3 := by omega
        rw [he]
        exact Nat.add_div_right rest.length (by decide : 0 < 3)
      by_cases h : a ≤ G ∧ b ≤ G
      · simp only [qualifyingTriples, failingTriples, if_pos h,
          Nat.zero_add]
        rw [hdiv]
        omega
      · simp only [qualifyingTriples, failingTriples, if_neg h,
          Nat.zero_add]
        rw [hdiv]
        omega

private theorem failingTriples_weight (G : Nat) :
    ∀ gs : List Nat, (G + 1) * failingTriples G gs ≤ gs.sum
  | [] => by simp [failingTriples]
  | [a] => by simp [failingTriples]
  | [a, b] => by simp [failingTriples]
  | a :: b :: c :: rest => by
      have ih := failingTriples_weight G rest
      by_cases h : a ≤ G ∧ b ≤ G
      · simp only [failingTriples, if_pos h, Nat.zero_add, List.sum_cons]
        exact Nat.le_trans ih (by omega)
      · have hlarge : G + 1 ≤ a + b := by
          by_cases ha : a ≤ G
          · have hb : G < b := by omega
            omega
          · have ha' : G < a := by omega
            omega
        simp only [failingTriples, if_neg h, List.sum_cons]
        calc
          (G + 1) * (1 + failingTriples G rest) =
              (G + 1) + (G + 1) * failingTriples G rest := by
                rw [Nat.mul_add, Nat.mul_one]
          _ ≤ (a + b) + rest.sum := Nat.add_le_add hlarge ih
          _ ≤ a + (b + (c + rest.sum)) := by omega

/-- Multiplying the natural ceiling by its denominator recovers the
unrounded numerator. -/
private theorem ceil_mul_lower (a k : Nat) (hk : 1 ≤ k) :
    a ≤ k * ((a + k - 1) / k) := by
  let q := (a + k - 1) / k
  change a ≤ k * q
  by_cases h : a ≤ k * q
  · exact h
  · have hlt : k * q < a := Nat.lt_of_not_ge h
    have hmul : (q + 1) * k ≤ a + k - 1 := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q k]
      omega
    have hq : q + 1 ≤ (a + k - 1) / k :=
      (Nat.le_div_iff_mul_le (by omega : 0 < k)).2 hmul
    have hqq : q + 1 ≤ q := by
      simpa [q] using hq
    omega

/-- Among the first `3*(k/3)` cyclically ordered anchors, at least `k/10`
consecutive triples have both internal gaps at most `ceil (10*m/k)`. -/
theorem triples_qualify (gs : List Nat) (k m : Nat)
    (hk : 3 ≤ k)
    (hlen : gs.length = k)
    (_hpos : ∀ g, g ∈ gs → 1 ≤ g)
    (hsum : gs.sum = m) :
    k ≤ 10 * qualifyingTriples (gapCeil m k) gs := by
  let G := gapCeil m k
  let good := qualifyingTriples G gs
  let bad := failingTriples G gs
  have hpart0 := triples_partition G gs
  have hpart : good + bad = k / 3 := by
    simpa [good, bad, hlen] using hpart0
  have hfive := five_mul_div_three k hk
  have htotal : k ≤ 5 * (good + bad) := by
    omega
  have hweight0 := failingTriples_weight G gs
  have hweight : (G + 1) * bad ≤ m := by
    simpa [bad, hsum] using hweight0
  have hceil : 10 * m ≤ k * G := by
    simpa [G, gapCeil] using
      (ceil_mul_lower (10 * m) k (by omega))
  have hbadBound : 10 * bad ≤ k := by
    by_cases hb : 10 * bad ≤ k
    · exact hb
    · have hlt : k < 10 * bad := Nat.lt_of_not_ge hb
      have hkpos : 0 < k := by omega
      have hscaled : 10 * ((G + 1) * bad) ≤ 10 * m :=
        Nat.mul_le_mul_left 10 hweight
      have hcycle : k * G < k * G := by
        calc
          k * G < k * (G + 1) :=
            Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self G) hkpos
          _ < (10 * bad) * (G + 1) :=
            Nat.mul_lt_mul_of_pos_right hlt (Nat.succ_pos G)
          _ = 10 * ((G + 1) * bad) := by
            ac_rfl
          _ ≤ 10 * m := hscaled
          _ ≤ k * G := hceil
      exact False.elim (Nat.lt_irrefl _ hcycle)
  change k ≤ 10 * good
  have htotal' : k ≤ 5 * good + 5 * bad := by
    simpa [Nat.mul_add] using htotal
  omega

/-- The accepted paper window has length at most `768*m/k`. -/
theorem gap_len_bound (m k : Nat) (h2 : 2 ≤ k) (hk : k ≤ m) :
    k * gapWindowLen m k ≤ 768 * m := by
  have hdiv0 := Nat.div_mul_le_self (10 * m + k - 1) k
  have hdiv :
      k * ((10 * m + k - 1) / k) ≤ 10 * m + k - 1 := by
    simpa [Nat.mul_comm] using hdiv0
  have hinner :
      k * (((10 * m + k - 1) / k) + 1) ≤ 12 * m := by
    rw [Nat.mul_add]
    omega
  calc
    k * gapWindowLen m k =
        64 * (k * (((10 * m + k - 1) / k) + 1)) := by
          unfold gapWindowLen
          ac_rfl
    _ ≤ 64 * (12 * m) := Nat.mul_le_mul_left 64 hinner
    _ = (64 * 12) * m := by rw [← Nat.mul_assoc]
    _ = 768 * m := by
      rw [show 64 * 12 = 768 by decide]

/-- Every `k` in `[1,m]` divides the accepted factorial `fact m`. -/
theorem fact_dvd (k m : Nat) (hk : 1 ≤ k) (hkm : k ≤ m) :
    k ∣ fact m := by
  induction m generalizing k with
  | zero => omega
  | succ m ih =>
      by_cases htop : k = m + 1
      · subst k
        simp only [fact]
        exact Nat.dvd_mul_right (m + 1) (fact m)
      · have hle : k ≤ m := by omega
        have hd := ih k hk hle
        simp only [fact]
        exact Nat.dvd_mul_left_of_dvd hd (m + 1)

private theorem fact_ratio_identity (m k : Nat)
    (hk : 1 ≤ k) (hkm : k ≤ m) :
    (k - 1) * (fact m / k) = fact m - fact m / k := by
  have hd := fact_dvd k m hk hkm
  have heq : k * (fact m / k) = fact m :=
    Nat.mul_div_cancel' hd
  have hsum :
      (k - 1) * (fact m / k) + fact m / k = fact m := by
    calc
      (k - 1) * (fact m / k) + fact m / k =
          ((k - 1) + 1) * (fact m / k) := by
            rw [Nat.add_mul, Nat.one_mul]
      _ = k * (fact m / k) := by
        have hkback : (k - 1) + 1 = k := by omega
        rw [hkback]
      _ = fact m := heq
  omega

private theorem fact_ratio_le_fact (m k : Nat)
    (hk : 1 ≤ k) (hkm : k ≤ m) :
    fact m / k ≤ fact m := by
  have hd := fact_dvd k m hk hkm
  calc
    fact m / k = 1 * (fact m / k) := by simp
    _ ≤ k * (fact m / k) := Nat.mul_le_mul_right _ hk
    _ = fact m := Nat.mul_div_cancel' hd

private theorem fact_ratio_antitone (m kp k : Nat)
    (hkp : 1 ≤ kp) (hpk : kp ≤ k) (hkm : k ≤ m) :
    fact m / k ≤ fact m / kp := by
  have hk : 1 ≤ k := by omega
  have hdk := fact_dvd k m hk hkm
  have hdkp := fact_dvd kp m hkp (by omega)
  have hmul : kp * (fact m / k) ≤ kp * (fact m / kp) := by
    calc
      kp * (fact m / k) ≤ k * (fact m / k) :=
        Nat.mul_le_mul_right _ hpk
      _ = fact m := Nat.mul_div_cancel' hdk
      _ = kp * (fact m / kp) := (Nat.mul_div_cancel' hdkp).symm
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

private theorem Vpot_eq_sub (m k : Nat)
    (hk : 1 ≤ k) (hkm : k ≤ m) :
    Vpot m k = 122880 * m * (fact m - fact m / k) := by
  unfold Vpot
  rw [Nat.mul_assoc, fact_ratio_identity m k hk hkm]

private theorem Vpot_mono (m kp k : Nat)
    (hkp : 1 ≤ kp) (hpk : kp ≤ k) (hkm : k ≤ m) :
    Vpot m kp ≤ Vpot m k := by
  have hk : 1 ≤ k := by omega
  have hratio := fact_ratio_antitone m kp k hkp hpk hkm
  have hkpFact := fact_ratio_le_fact m kp hkp (by omega)
  have hsub : fact m - fact m / kp ≤ fact m - fact m / k := by
    omega
  rw [Vpot_eq_sub m kp hkp (by omega), Vpot_eq_sub m k hk hkm]
  exact Nat.mul_le_mul_left _ hsub

/-- The exact factorial-scaled potential decrease. -/
theorem pot_drop (m kp k : Nat)
    (hkp : 1 ≤ kp) (hpk : kp ≤ k) (hkm : k ≤ m) :
    k * k * (Vpot m k - Vpot m kp) ≥
      122880 * m * fact m * (k - kp) := by
  have hk : 1 ≤ k := by omega
  have hdk := fact_dvd k m hk hkm
  have hdkp := fact_dvd kp m hkp (by omega)
  have hratio := fact_ratio_antitone m kp k hkp hpk hkm
  have hkpFact := fact_ratio_le_fact m kp hkp (by omega)
  have hident :
      kp * (fact m / kp - fact m / k) =
        (k - kp) * (fact m / k) := by
    calc
      kp * (fact m / kp - fact m / k) =
          kp * (fact m / kp) - kp * (fact m / k) :=
        Nat.mul_sub_left_distrib _ _ _
      _ = fact m - kp * (fact m / k) := by
        rw [Nat.mul_div_cancel' hdkp]
      _ = k * (fact m / k) - kp * (fact m / k) := by
        rw [Nat.mul_div_cancel' hdk]
      _ = (k - kp) * (fact m / k) :=
        (Nat.sub_mul _ _ _).symm
  have hstep :
      (k - kp) * (fact m / k) ≤
        k * (fact m / kp - fact m / k) := by
    rw [← hident]
    exact Nat.mul_le_mul_right _ hpk
  have hmul := Nat.mul_le_mul_left k hstep
  have hF : fact m = k * (fact m / k) :=
    (Nat.mul_div_cancel' hdk).symm
  have hcore :
      fact m * (k - kp) ≤
        k * k * (fact m / kp - fact m / k) := by
    calc
      fact m * (k - kp) =
          (k * (fact m / k)) * (k - kp) :=
        congrArg (fun x : Nat => x * (k - kp)) hF
      _ = k * ((k - kp) * (fact m / k)) := by
        ac_rfl
      _ ≤ k * (k * (fact m / kp - fact m / k)) := hmul
      _ = k * k * (fact m / kp - fact m / k) := by
        rw [Nat.mul_assoc]
  have hsubsub :
      (fact m - fact m / k) - (fact m - fact m / kp) =
        fact m / kp - fact m / k := by
    omega
  have hdiffV :
      Vpot m k - Vpot m kp =
        122880 * m * (fact m / kp - fact m / k) := by
    rw [Vpot_eq_sub m k hk hkm,
      Vpot_eq_sub m kp hkp (by omega)]
    rw [← Nat.mul_sub_left_distrib, hsubsub]
  have hscaled := Nat.mul_le_mul_left (122880 * m) hcore
  calc
    122880 * m * fact m * (k - kp) =
        (122880 * m) * (fact m * (k - kp)) := by
          rw [Nat.mul_assoc]
    _ ≤ (122880 * m) *
        (k * k * (fact m / kp - fact m / k)) := hscaled
    _ = k * k *
        (122880 * m * (fact m / kp - fact m / k)) := by
          ac_rfl
    _ = k * k * (Vpot m k - Vpot m kp) := by
      rw [hdiffV]

/-- The exact integer supermartingale inequality required by `Drift`. -/
theorem window_step_interface (m : Nat) :
    WindowStepInterface m (2 ^ m) := by
  unfold WindowStepInterface
  intro k L f hk hkm hfrange hlen hLoss
  have hpoint : ∀ u : List (Fin (2 ^ m)),
      122880 * m * fact m * (k - f u) +
          k * k * Vpot m (f u) ≤
        k * k * Vpot m k := by
    intro u
    have hu := hfrange u
    have hdrop := pot_drop m (f u) k hu.1 hu.2 hkm
    have hmono := Vpot_mono m (f u) k hu.1 hu.2 hkm
    have hadd := Nat.add_le_add_right hdrop (k * k * Vpot m (f u))
    calc
      122880 * m * fact m * (k - f u) +
          k * k * Vpot m (f u) ≤
        k * k * (Vpot m k - Vpot m (f u)) +
          k * k * Vpot m (f u) := hadd
      _ = k * k * Vpot m k := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hmono]
  have hsum0 := wordSum_mono
    (fun u : List (Fin (2 ^ m)) =>
      122880 * m * fact m * (k - f u) +
        k * k * Vpot m (f u))
    (fun _ : List (Fin (2 ^ m)) => k * k * Vpot m k)
    hpoint L
  rw [wordSum_add_fun
    (fun u : List (Fin (2 ^ m)) =>
      122880 * m * fact m * (k - f u))
    (fun u : List (Fin (2 ^ m)) =>
      k * k * Vpot m (f u)) L] at hsum0
  rw [wordSum_mul_left (122880 * m * fact m)
    (fun u : List (Fin (2 ^ m)) => k - f u) L] at hsum0
  rw [wordSum_mul_left (k * k)
    (fun u : List (Fin (2 ^ m)) => Vpot m (f u)) L] at hsum0
  rw [wordSum_const (n := 2 ^ m) (k * k * Vpot m k) L] at hsum0
  have hsum :
      122880 * m * fact m * wordSum (fun u => k - f u) L +
        k * k * wordSum (fun u => Vpot m (f u)) L ≤
      k * k * Vpot m k * (2 ^ m) ^ L := by
    calc
      122880 * m * fact m * wordSum (fun u => k - f u) L +
          k * k * wordSum (fun u => Vpot m (f u)) L ≤
        (2 ^ m) ^ L * (k * k * Vpot m k) := hsum0
      _ = k * k * Vpot m k * (2 ^ m) ^ L := by
        ac_rfl
  have hprod :
      (k * L) * (k * (2 ^ m) ^ L) ≤
        (768 * m) * (160 * wordSum (fun u => k - f u) L) :=
    Nat.mul_le_mul hlen hLoss
  have hcost0 :
      fact m * ((k * L) * (k * (2 ^ m) ^ L)) ≤
        fact m * ((768 * m) *
          (160 * wordSum (fun u => k - f u) L)) :=
    Nat.mul_le_mul_left (fact m) hprod
  have hconst : 768 * 160 = 122880 := by decide
  have hcost :
      k * k * (fact m * L * (2 ^ m) ^ L) ≤
        122880 * m * fact m * wordSum (fun u => k - f u) L := by
    calc
      k * k * (fact m * L * (2 ^ m) ^ L) =
          fact m * ((k * L) * (k * (2 ^ m) ^ L)) := by
            ac_rfl
      _ ≤ fact m * ((768 * m) *
          (160 * wordSum (fun u => k - f u) L)) := hcost0
      _ = (768 * 160) * m * fact m *
          wordSum (fun u => k - f u) L := by
            ac_rfl
      _ = 122880 * m * fact m *
          wordSum (fun u => k - f u) L := by
            rw [hconst]
  have hcombined :
      (k * k) *
          (fact m * L * (2 ^ m) ^ L +
            wordSum (fun u => Vpot m (f u)) L) ≤
        (k * k) * (Vpot m k * (2 ^ m) ^ L) := by
    calc
      (k * k) *
          (fact m * L * (2 ^ m) ^ L +
            wordSum (fun u => Vpot m (f u)) L) =
        k * k * (fact m * L * (2 ^ m) ^ L) +
          k * k * wordSum (fun u => Vpot m (f u)) L := by
            rw [Nat.mul_add]
      _ ≤ 122880 * m * fact m *
            wordSum (fun u => k - f u) L +
          k * k * wordSum (fun u => Vpot m (f u)) L :=
        Nat.add_le_add_right hcost _
      _ ≤ k * k * Vpot m k * (2 ^ m) ^ L := hsum
      _ = (k * k) * (Vpot m k * (2 ^ m) ^ L) := by
        rw [Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_left hcombined
    (Nat.mul_pos (by omega) (by omega))

private theorem potentialFactor_le (F k : Nat) :
    (k - 1) * (F / k) ≤ F := by
  have hfirst : (k - 1) * (F / k) ≤ k * (F / k) :=
    Nat.mul_le_mul_right _ (Nat.sub_le k 1)
  have hdiv : k * (F / k) ≤ F := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self F k
  exact Nat.le_trans hfirst hdiv

/-- The accepted integer potential is bounded by the scaled target constant. -/
theorem potential_bound_interface (m : Nat) :
    PotentialBoundInterface m := by
  unfold PotentialBoundInterface
  intro k hk hkm
  have hscaled := Nat.mul_le_mul_left (122880 * m)
    (potentialFactor_le (fact m) k)
  calc
    Vpot m k =
        (122880 * m) * ((k - 1) * (fact m / k)) := by
          unfold Vpot
          rw [Nat.mul_assoc]
    _ ≤ (122880 * m) * fact m := hscaled

#print axioms five_mul_div_three
#print axioms triples_qualify
#print axioms gap_len_bound
#print axioms pot_drop
#print axioms window_step_interface
#print axioms potential_bound_interface

end L4.Height
