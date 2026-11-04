import Leader.Wu.Birth.ShortDoneParameterChoice


set_option autoImplicit false


namespace Q11578HScaleAudit


open BirthShortDoneParticipationLoadMass
open Q11497FeasibilityAudit


/-- The exact B5 horizon, specialized to the checked
`kappaChoice`.  Width two is intentional. -/
def roadmapTcap (n : Nat) : Nat :=
  BirthWaitClockMass.DirtyMass.horizon n 2 *
    (256 * (kappaChoice n + 1) * (Nat.log2 n + 1))


/-- Pascal monotonicity in the first argument. -/
private theorem chooseCount_step (T m : Nat) :
    chooseCount T m <= chooseCount (T + 1) m := by
  cases m with
  | zero =>
      simp [chooseCount]
  | succ m =>
      change chooseCount T (m + 1) <=
        chooseCount T m + chooseCount T (m + 1)
      omega


/-- Iterated first-argument monotonicity. -/
private theorem chooseCount_mono_first
    {a b m : Nat} (hab : a <= b) :
    chooseCount a m <= chooseCount b m := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases htop : a = b + 1
      · subst a
        exact Nat.le_refl _
      · have hab' : a <= b := by omega
        exact Nat.le_trans (ih hab') (chooseCount_step b m)


/-- Elementary central-binomial lower bound proved only from the source-local
Pascal recursion. -/
private theorem two_pow_le_choose_double (m : Nat) :
    2 ^ m <= chooseCount (2 * m) m := by
  induction m with
  | zero =>
      simp [chooseCount]
  | succ m ih =>
      have hleft :
          chooseCount (2 * m) m <=
            chooseCount (2 * m + 1) m :=
        chooseCount_step (2 * m) m
      have hright :
          chooseCount (2 * m) m <=
            chooseCount (2 * m + 1) (m + 1) := by
        change chooseCount (2 * m) m <=
          chooseCount (2 * m) m + chooseCount (2 * m) (m + 1)
        omega
      calc
        2 ^ (m + 1) = 2 * 2 ^ m := by
          rw [Nat.pow_succ]
          ac_rfl
        _ <= 2 * chooseCount (2 * m) m :=
          Nat.mul_le_mul_left 2 ih
        _ = chooseCount (2 * m) m + chooseCount (2 * m) m := by
          omega
        _ <= chooseCount (2 * m + 1) m +
              chooseCount (2 * m + 1) (m + 1) :=
          Nat.add_le_add hleft hright
        _ = chooseCount ((2 * m + 1) + 1) (m + 1) := by
          rfl
        _ = chooseCount (2 * (m + 1)) (m + 1) := by
          rw [show (2 * m + 1) + 1 = 2 * (m + 1) by omega]


/-- One extra row above the central binomial makes the lower bound strict. -/
private theorem two_pow_lt_choose_double_succ
    (m : Nat) (hm : 0 < m) :
    2 ^ m < chooseCount (2 * m + 1) m := by
  obtain ⟨j, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hpos :
      0 < chooseCount (2 * (j + 1)) j :=
    chooseCount_pos_of_le (by omega)
  have hcentral :
      2 ^ (j + 1) <=
        chooseCount (2 * (j + 1)) (j + 1) :=
    two_pow_le_choose_double (j + 1)
  change 2 ^ (j + 1) <
    chooseCount (2 * (j + 1)) j +
      chooseCount (2 * (j + 1)) (j + 1)
  omega


private theorem two_pow_lt_choose_of_large_first
    {T m : Nat} (hm : 0 < m) (hT : 2 * m + 1 <= T) :
    2 ^ m < chooseCount T m := by
  have hstrict := two_pow_lt_choose_double_succ m hm
  have hmono :
      chooseCount (2 * m + 1) m <= chooseCount T m :=
    chooseCount_mono_first hT
  exact Nat.lt_of_lt_of_le hstrict hmono


/-- The exact B5 roadmap horizon at the first ring accepted by the checked
feasibility witness and Local3 timing layer. -/
theorem roadmapTcap_four :
    roadmapTcap 4 = 73728 := by
  decide


/-- The checked timer order at n=4 is 49. -/
theorem tauChoice_four_order :
    tauChoice 4 + 1 = 49 := by
  rcases Q11497FeasibilityAudit.n4_parameters with
    ⟨_hscale, _hpsi, _hkappa, htau, _hpsi2, _hpsilt⟩
  omega


theorem fixed_site_hscale_four_fails_of_99_le
    (T : Nat) (hT : 99 <= T) :
    not (chooseCount T 49 * 2 ^ 49 <= 4 ^ 49) := by
  have hbin : 2 ^ 49 < chooseCount T 49 :=
    two_pow_lt_choose_of_large_first (by omega) (by omega)
  have hp : 0 < 2 ^ 49 := Nat.pow_pos (by omega)
  have hmul :
      2 ^ 49 * 2 ^ 49 < chooseCount T 49 * 2 ^ 49 :=
    (Nat.mul_lt_mul_right hp).2 hbin
  have hfour : 4 ^ 49 = 2 ^ 49 * 2 ^ 49 := by
    simpa using (Nat.mul_pow 2 2 49)
  have hnot :
      ¬ (chooseCount T 49 * 2 ^ 49 <= 4 ^ 49) := by
    intro hscale
    rw [hfour] at hscale
    exact (Nat.not_lt_of_ge hscale) hmul
  simp [hnot]


/-- Main concrete certificate: the checked `tauChoice` does not satisfy
the exact specialized fixed-site hscale at the B5 horizon, already for
n=4 and Q=1. -/
theorem tauChoice_four_fixed_site_hscale_fails_at_roadmapTcap :
    not (1 *
      (chooseCount (roadmapTcap 4) (tauChoice 4 + 1) *
        2 ^ (tauChoice 4 + 1)) <=
      4 ^ (tauChoice 4 + 1)) := by
  rw [roadmapTcap_four, tauChoice_four_order]
  simp only [Nat.one_mul]
  exact fixed_site_hscale_four_fails_of_99_le 73728 (by omega)


/-- The failure persists in the listed-site shape already for a one-element
list factor and Q=1. -/
theorem tauChoice_four_listed_one_site_hscale_fails_at_roadmapTcap :
    not (1 * 1 *
      (chooseCount (roadmapTcap 4) (tauChoice 4 + 1) *
        2 ^ (tauChoice 4 + 1)) <=
      4 ^ (tauChoice 4 + 1)) := by
  simpa using tauChoice_four_fixed_site_hscale_fails_at_roadmapTcap


end Q11578HScaleAudit


#print axioms Q11578HScaleAudit.roadmapTcap_four
#print axioms Q11578HScaleAudit.tauChoice_four_order
#print axioms Q11578HScaleAudit.fixed_site_hscale_four_fails_of_99_le
#print axioms Q11578HScaleAudit.tauChoice_four_fixed_site_hscale_fails_at_roadmapTcap
#print axioms Q11578HScaleAudit.tauChoice_four_listed_one_site_hscale_fails_at_roadmapTcap
