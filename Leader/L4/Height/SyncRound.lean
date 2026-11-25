import Leader.L4.Height.SyncAlt
namespace L4.Height
open L4.Compiler.Native
variable {m : Nat}

theorem clockOf_mod_phase {M ellzero n : Nat}
    (hdiv : 32 ∣ M / 2) (hzero : ellzero % 32 = 0) :
    clockOf M (ellzero + n) % 32 = n % 32 := by
  have hp : (M / 2) % 32 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
  have hmod : (ellzero + n) % (M / 2) % 32 = (ellzero + n) % 32 :=
    Nat.mod_mod_of_dvd (ellzero + n) hdiv
  have hsum : (ellzero + n) % 32 = n % 32 := by
    rw [Nat.add_mod, hzero]
    simp
  calc
    clockOf M (ellzero + n) % 32 =
        ((M / 2) % 32 + ((ellzero + n) % (M / 2)) % 32) % 32 := by
          unfold clockOf
          rw [Nat.add_mod]
    _ = ((ellzero + n) % (M / 2)) % 32 := by simp [hp]
    _ = (ellzero + n) % 32 := hmod
    _ = n % 32 := hsum

theorem phaseStep_high_id {B j : Nat} (hj : 6 ≤ j)
    (hm : 0 < m) (bits : Fin m → Bool) (s : Fin m → Snapshot) :
    phaseStep B j hm bits s = s := by
  funext i
  simp only [phaseStep]
  cases j with
  | zero => omega
  | succ j =>
    cases j with
    | zero => omega
    | succ j =>
      cases j with
      | zero => omega
      | succ j =>
        cases j with
        | zero => omega
        | succ j =>
          cases j with
          | zero => omega
          | succ j =>
            cases j with
            | zero => omega
            | succ j => simp [phaseUpdate]

theorem phaseStep_bits_irrelevant {B j : Nat} (hj : j ≠ 1)
    (hm : 0 < m) (bits bits' : Fin m → Bool) (s : Fin m → Snapshot) :
    phaseStep B j hm bits s = phaseStep B j hm bits' s := by
  funext i
  exact phaseUpdate_delta_irrelevant B j
    (s (left hm i)) (s i) (s (right hm i)) (bits i) (bits' i) hj

theorem syncLevels_add {m : Nat} (B M ellzero : Nat) (hm : 0 < m)
    (choices : Nat → Fin m → Bool) (start : Fin m → Snapshot) (a : Nat) :
    ∀ b, syncLevels B M ellzero hm choices start (a + b) =
      syncLevels B M (ellzero + a) hm choices
        (syncLevels B M ellzero hm choices start a) b := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Nat.add_succ, syncLevels, syncLevels, ih, Nat.add_assoc]

def roundBits (choices : Nat → Fin m → Bool) (ellzero : Nat) :
    Nat → List (Fin m → Bool)
  | 0 => []
  | k + 1 => roundBits choices ellzero k ++ [choices (ellzero + 32 * k + 1)]

theorem roundBits_succ (choices : Nat → Fin m → Bool) (ellzero k : Nat) :
    roundBits choices ellzero (k + 1) =
      roundBits choices ellzero k ++ [choices (ellzero + 32 * k + 1)] := rfl

theorem runRounds_append {B : Nat} (hm : 0 < m)
    (xs ys : List (Fin m → Bool)) (s : Fin m → Snapshot) :
    runRounds B hm (xs ++ ys) s =
      runRounds B hm ys (runRounds B hm xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, runRounds]
      exact ih (logicalRound B hm x s)

theorem syncLevels_segment_period {B M ellzero : Nat}
    (hm : 0 < m) (choices : Nat → Fin m → Bool)
    (start : Fin m → Snapshot)
    (hphase : ∀ n, clockOf M (ellzero + n) % 32 = n % 32) :
    syncLevels B M ellzero hm choices start 32 =
      logicalRound B hm (choices (ellzero + 1)) start := by
  have hzero : clockOf M (ellzero + 0) % 32 = 0 := by simpa using hphase 0
  have hone : clockOf M (ellzero + 1) % 32 = 1 := by simpa using hphase 1
  have htwo : clockOf M (ellzero + 2) % 32 = 2 := by simpa using hphase 2
  have hthree : clockOf M (ellzero + 3) % 32 = 3 := by simpa using hphase 3
  have hfour : clockOf M (ellzero + 4) % 32 = 4 := by simpa using hphase 4
  have hfive : clockOf M (ellzero + 5) % 32 = 5 := by simpa using hphase 5
  have hsix : clockOf M (ellzero + 6) % 32 = 6 := by simpa using hphase 6
  have hseven : clockOf M (ellzero + 7) % 32 = 7 := by simpa using hphase 7
  have height : clockOf M (ellzero + 8) % 32 = 8 := by simpa using hphase 8
  have hnine : clockOf M (ellzero + 9) % 32 = 9 := by simpa using hphase 9
  have hten : clockOf M (ellzero + 10) % 32 = 10 := by simpa using hphase 10
  have heleven : clockOf M (ellzero + 11) % 32 = 11 := by simpa using hphase 11
  have htwelve : clockOf M (ellzero + 12) % 32 = 12 := by simpa using hphase 12
  have hthirteen : clockOf M (ellzero + 13) % 32 = 13 := by simpa using hphase 13
  have hfourteen : clockOf M (ellzero + 14) % 32 = 14 := by simpa using hphase 14
  have hfifteen : clockOf M (ellzero + 15) % 32 = 15 := by simpa using hphase 15
  have hsixteen : clockOf M (ellzero + 16) % 32 = 16 := by simpa using hphase 16
  have hseventeen : clockOf M (ellzero + 17) % 32 = 17 := by simpa using hphase 17
  have heighteen : clockOf M (ellzero + 18) % 32 = 18 := by simpa using hphase 18
  have hnineteen : clockOf M (ellzero + 19) % 32 = 19 := by simpa using hphase 19
  have htwenty : clockOf M (ellzero + 20) % 32 = 20 := by simpa using hphase 20
  have htwentyone : clockOf M (ellzero + 21) % 32 = 21 := by simpa using hphase 21
  have htwentytwo : clockOf M (ellzero + 22) % 32 = 22 := by simpa using hphase 22
  have htwentythree : clockOf M (ellzero + 23) % 32 = 23 := by simpa using hphase 23
  have htwentyfour : clockOf M (ellzero + 24) % 32 = 24 := by simpa using hphase 24
  have htwentyfive : clockOf M (ellzero + 25) % 32 = 25 := by simpa using hphase 25
  have htwentysix : clockOf M (ellzero + 26) % 32 = 26 := by simpa using hphase 26
  have htwentyseven : clockOf M (ellzero + 27) % 32 = 27 := by simpa using hphase 27
  have htwentyeight : clockOf M (ellzero + 28) % 32 = 28 := by simpa using hphase 28
  have htwentynine : clockOf M (ellzero + 29) % 32 = 29 := by simpa using hphase 29
  have hthirty : clockOf M (ellzero + 30) % 32 = 30 := by simpa using hphase 30
  have hthirtyone : clockOf M (ellzero + 31) % 32 = 31 := by simpa using hphase 31
  simp only [syncLevels]
  rw [hthirtyone, hthirty, htwentynine, htwentyeight, htwentyseven, htwentysix, htwentyfive, htwentyfour, htwentythree, htwentytwo, htwentyone, htwenty, hnineteen, heighteen, hseventeen, hsixteen, hfifteen, hfourteen, hthirteen, htwelve, heleven, hten, hnine, height, hseven, hsix, hfive, hfour, hthree, htwo, hone, hzero]
  have hidThirtyone : ∀ t, phaseStep B 31 hm (choices (ellzero + 31)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 31) (by omega) hm (choices (ellzero + 31)) t
  have hidThirty : ∀ t, phaseStep B 30 hm (choices (ellzero + 30)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 30) (by omega) hm (choices (ellzero + 30)) t
  have hidTwentynine : ∀ t, phaseStep B 29 hm (choices (ellzero + 29)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 29) (by omega) hm (choices (ellzero + 29)) t
  have hidTwentyeight : ∀ t, phaseStep B 28 hm (choices (ellzero + 28)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 28) (by omega) hm (choices (ellzero + 28)) t
  have hidTwentyseven : ∀ t, phaseStep B 27 hm (choices (ellzero + 27)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 27) (by omega) hm (choices (ellzero + 27)) t
  have hidTwentysix : ∀ t, phaseStep B 26 hm (choices (ellzero + 26)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 26) (by omega) hm (choices (ellzero + 26)) t
  have hidTwentyfive : ∀ t, phaseStep B 25 hm (choices (ellzero + 25)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 25) (by omega) hm (choices (ellzero + 25)) t
  have hidTwentyfour : ∀ t, phaseStep B 24 hm (choices (ellzero + 24)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 24) (by omega) hm (choices (ellzero + 24)) t
  have hidTwentythree : ∀ t, phaseStep B 23 hm (choices (ellzero + 23)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 23) (by omega) hm (choices (ellzero + 23)) t
  have hidTwentytwo : ∀ t, phaseStep B 22 hm (choices (ellzero + 22)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 22) (by omega) hm (choices (ellzero + 22)) t
  have hidTwentyone : ∀ t, phaseStep B 21 hm (choices (ellzero + 21)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 21) (by omega) hm (choices (ellzero + 21)) t
  have hidTwenty : ∀ t, phaseStep B 20 hm (choices (ellzero + 20)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 20) (by omega) hm (choices (ellzero + 20)) t
  have hidNineteen : ∀ t, phaseStep B 19 hm (choices (ellzero + 19)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 19) (by omega) hm (choices (ellzero + 19)) t
  have hidEighteen : ∀ t, phaseStep B 18 hm (choices (ellzero + 18)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 18) (by omega) hm (choices (ellzero + 18)) t
  have hidSeventeen : ∀ t, phaseStep B 17 hm (choices (ellzero + 17)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 17) (by omega) hm (choices (ellzero + 17)) t
  have hidSixteen : ∀ t, phaseStep B 16 hm (choices (ellzero + 16)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 16) (by omega) hm (choices (ellzero + 16)) t
  have hidFifteen : ∀ t, phaseStep B 15 hm (choices (ellzero + 15)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 15) (by omega) hm (choices (ellzero + 15)) t
  have hidFourteen : ∀ t, phaseStep B 14 hm (choices (ellzero + 14)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 14) (by omega) hm (choices (ellzero + 14)) t
  have hidThirteen : ∀ t, phaseStep B 13 hm (choices (ellzero + 13)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 13) (by omega) hm (choices (ellzero + 13)) t
  have hidTwelve : ∀ t, phaseStep B 12 hm (choices (ellzero + 12)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 12) (by omega) hm (choices (ellzero + 12)) t
  have hidEleven : ∀ t, phaseStep B 11 hm (choices (ellzero + 11)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 11) (by omega) hm (choices (ellzero + 11)) t
  have hidTen : ∀ t, phaseStep B 10 hm (choices (ellzero + 10)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 10) (by omega) hm (choices (ellzero + 10)) t
  have hidNine : ∀ t, phaseStep B 9 hm (choices (ellzero + 9)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 9) (by omega) hm (choices (ellzero + 9)) t
  have hidEight : ∀ t, phaseStep B 8 hm (choices (ellzero + 8)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 8) (by omega) hm (choices (ellzero + 8)) t
  have hidSeven : ∀ t, phaseStep B 7 hm (choices (ellzero + 7)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 7) (by omega) hm (choices (ellzero + 7)) t
  have hidSix : ∀ t, phaseStep B 6 hm (choices (ellzero + 6)) t = t := by
    intro t
    exact phaseStep_high_id (B := B) (j := 6) (by omega) hm (choices (ellzero + 6)) t
  simp only [hidThirtyone, hidThirty, hidTwentynine, hidTwentyeight, hidTwentyseven, hidTwentysix, hidTwentyfive, hidTwentyfour, hidTwentythree, hidTwentytwo, hidTwentyone, hidTwenty, hidNineteen, hidEighteen, hidSeventeen, hidSixteen, hidFifteen, hidFourteen, hidThirteen, hidTwelve, hidEleven, hidTen, hidNine, hidEight, hidSeven, hidSix]
  have hbZero : phaseStep B 0 hm (choices (ellzero + 0)) =
      phaseStep B 0 hm (choices (ellzero + 1)) := by
    funext t
    exact phaseStep_bits_irrelevant (B := B) (j := 0) (by decide)
      hm (choices (ellzero + 0)) (choices (ellzero + 1)) t
  have hbTwo : phaseStep B 2 hm (choices (ellzero + 2)) =
      phaseStep B 2 hm (choices (ellzero + 1)) := by
    funext t
    exact phaseStep_bits_irrelevant (B := B) (j := 2) (by decide)
      hm (choices (ellzero + 2)) (choices (ellzero + 1)) t
  have hbThree : phaseStep B 3 hm (choices (ellzero + 3)) =
      phaseStep B 3 hm (choices (ellzero + 1)) := by
    funext t
    exact phaseStep_bits_irrelevant (B := B) (j := 3) (by decide)
      hm (choices (ellzero + 3)) (choices (ellzero + 1)) t
  have hbFour : phaseStep B 4 hm (choices (ellzero + 4)) =
      phaseStep B 4 hm (choices (ellzero + 1)) := by
    funext t
    exact phaseStep_bits_irrelevant (B := B) (j := 4) (by decide)
      hm (choices (ellzero + 4)) (choices (ellzero + 1)) t
  have hbFive : phaseStep B 5 hm (choices (ellzero + 5)) =
      phaseStep B 5 hm (choices (ellzero + 1)) := by
    funext t
    exact phaseStep_bits_irrelevant (B := B) (j := 5) (by decide)
      hm (choices (ellzero + 5)) (choices (ellzero + 1)) t
  change
    phaseStep B 5 hm (choices (ellzero + 5))
      (phaseStep B 4 hm (choices (ellzero + 4))
        (phaseStep B 3 hm (choices (ellzero + 3))
          (phaseStep B 2 hm (choices (ellzero + 2))
            (phaseStep B 1 hm (choices (ellzero + 1))
              (phaseStep B 0 hm (choices (ellzero + 0)) start))))) =
    logicalRound B hm (choices (ellzero + 1)) start
  rw [hbFive, hbFour, hbThree, hbTwo, hbZero]
  rfl

theorem syncLevels_round {B M ellzero k : Nat}
    (hm : 0 < m) (choices : Nat → Fin m → Bool)
    (start : Fin m → Snapshot)
    (hphase : ∀ n, clockOf M (ellzero + n) % 32 = n % 32) :
    syncLevels B M ellzero hm choices start (32 * (k + 1)) =
      logicalRound B hm (choices (ellzero + 32 * k + 1))
        (syncLevels B M ellzero hm choices start (32 * k)) := by
  have hidx : 32 * (k + 1) = 32 * k + 32 := by omega
  rw [hidx]
  rw [syncLevels_add (B := B) (M := M) (ellzero := ellzero)
    (a := 32 * k) (b := 32) hm choices start]
  have hshift : ∀ n,
      clockOf M ((ellzero + 32 * k) + n) % 32 = n % 32 := by
    intro n
    have h := hphase (32 * k + n)
    have harg : ellzero + (32 * k + n) = (ellzero + 32 * k) + n := by omega
    have hmul : (32 * k + n) % 32 = n % 32 := by
      rw [Nat.add_mod]
      simp
    calc
      clockOf M ((ellzero + 32 * k) + n) % 32 =
          clockOf M (ellzero + (32 * k + n)) % 32 := by rw [← harg]
      _ = (32 * k + n) % 32 := h
      _ = n % 32 := hmul
  exact syncLevels_segment_period hm choices
    (syncLevels B M ellzero hm choices start (32 * k)) hshift

theorem syncLevels_runRounds {B M ellzero k : Nat}
    (hm : 0 < m) (choices : Nat → Fin m → Bool)
    (start : Fin m → Snapshot)
    (hphase : ∀ n, clockOf M (ellzero + n) % 32 = n % 32) :
    syncLevels B M ellzero hm choices start (32 * k) =
      runRounds B hm (roundBits choices ellzero k) start := by
  induction k with
  | zero => simp [roundBits, syncLevels, runRounds]
  | succ k ih =>
      rw [syncLevels_round hm choices start hphase]
      rw [roundBits_succ, runRounds_append, ih]
      rfl

end L4.Height

#print axioms L4.Height.clockOf_mod_phase
#print axioms L4.Height.phaseStep_high_id
#print axioms L4.Height.phaseStep_bits_irrelevant
#print axioms L4.Height.syncLevels_add
#print axioms L4.Height.syncLevels_segment_period
#print axioms L4.Height.syncLevels_round
#print axioms L4.Height.syncLevels_runRounds
