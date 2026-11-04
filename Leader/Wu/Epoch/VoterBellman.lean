import Leader.Wu.Epoch.VoterReduction

/-!
# Cubic Bellman scale of the directed-voter epoch dynamics

For a circular configuration consisting of two contiguous color domains, only
the two boundary edges change the domain length: one grows it, one shrinks it,
and the other `n-2` edge choices are self-loops.  The first-step Bellman system
for the global-interaction consensus time therefore has a quadratic solution in
the domain length and a cubic worst-case scale in `n`.

This file certifies that algebraic Bellman solution.  It does not yet construct
an infinite-horizon probability space or prove that every filtered epoch start
contains such a two-domain subsystem; those are separate bridges required for
a formal runtime lower bound.
-/

namespace PPLLEpochVoterBellman

/-- Twice the classical expected global-interaction absorption time for a lazy
unbiased domain-length walk on `{0,...,n}`.  Doubling keeps the certificate in
natural-number arithmetic: the expected time itself is
`n*x*(n-x)/2`. -/
def doubledLazyConsensusTime (n x : Nat) : Nat :=
  n * x * (n - x)

/-- Both consensus boundaries have zero remaining Bellman potential. -/
theorem doubledLazyConsensusTime_zero (n : Nat) :
    doubledLazyConsensusTime n 0 = 0 := by
  simp [doubledLazyConsensusTime]

/-- The all-one-color boundary also has zero remaining potential. -/
theorem doubledLazyConsensusTime_self (n : Nat) :
    doubledLazyConsensusTime n n = 0 := by
  simp [doubledLazyConsensusTime]

/-- Exact first-step Bellman equation at every interior domain length.  Among
`n` scheduler edges, `n-2` keep length `x`, one gives `x-1`, and one gives
`x+1`; the additive `2n` is twice one elapsed interaction across all outcomes. -/
theorem doubledLazyConsensusTime_bellman
    (n x : Nat) (hx : 0 < x) (hxn : x < n) :
    n * doubledLazyConsensusTime n x =
      2 * n + (n - 2) * doubledLazyConsensusTime n x +
        doubledLazyConsensusTime n (x - 1) +
        doubledLazyConsensusTime n (x + 1) := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
  subst x
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le
    (by omega : a + 1 + 1 ≤ n)
  subst n
  simp [doubledLazyConsensusTime]
  have h1 : a + 1 + 1 + b - a = b + 2 := by omega
  have h2 : a + 1 + 1 + b - (a + 1) = b + 1 := by omega
  rw [h1, h2]
  grind

/-- At the midpoint of an even ring, the doubled Bellman value is exactly
`2m^3`; hence the undoubled classical expectation is `m^3 = n^3/8`. -/
theorem doubledLazyConsensusTime_even_midpoint (m : Nat) :
    doubledLazyConsensusTime (2 * m) m = 2 * (m ^ 3) := by
  simp [doubledLazyConsensusTime, Nat.pow_succ]
  grind

/-- The midpoint Bellman scale dominates a simple cubic lower expression. -/
theorem doubledLazyConsensusTime_even_midpoint_cubic (m : Nat) :
    m ^ 3 ≤ doubledLazyConsensusTime (2 * m) m := by
  rw [doubledLazyConsensusTime_even_midpoint]
  omega

/-! ## Uniqueness of the finite Bellman solution -/

/-- Reduced first-step equations for twice the lazy walk's expected absorption
time.  Cancelling the `n-2` self-loop terms from the full uniform-edge equation
leaves the second-difference equation displayed here. -/
def LazyConsensusBellman (n : Nat) (E : Nat → Rat) : Prop :=
  E 0 = 0 ∧ E n = 0 ∧
    ∀ x, 0 < x → x < n →
      (2 : Rat) * E x = (2 : Rat) * (n : Nat) +
        E (x - 1) + E (x + 1)

/-- Natural-number Bellman polynomial viewed in the exact rational field. -/
def doubledLazyConsensusTimeRat (n x : Nat) : Rat :=
  (doubledLazyConsensusTime n x : Nat)

private theorem doubledLazyConsensusTime_reduced_bellman
    (n x : Nat) (hx : 0 < x) (hxn : x < n) :
    2 * doubledLazyConsensusTime n x =
      2 * n + doubledLazyConsensusTime n (x - 1) +
        doubledLazyConsensusTime n (x + 1) := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
  subst x
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le
    (by omega : a + 1 + 1 ≤ n)
  subst n
  simp [doubledLazyConsensusTime]
  have h1 : a + 1 + 1 + b - a = b + 2 := by omega
  have h2 : a + 1 + 1 + b - (a + 1) = b + 1 := by omega
  rw [h1, h2]
  grind

/-- The cubic polynomial is an actual solution of the exact finite Bellman
system, not only a heuristic drift expression. -/
theorem doubledLazyConsensusTimeRat_bellman (n : Nat) :
    LazyConsensusBellman n (doubledLazyConsensusTimeRat n) := by
  constructor
  · simp [doubledLazyConsensusTimeRat, doubledLazyConsensusTime]
  constructor
  · simp [doubledLazyConsensusTimeRat, doubledLazyConsensusTime]
  · intro x hx hxn
    have hnat := doubledLazyConsensusTime_reduced_bellman n x hx hxn
    have hrat := congrArg (fun z : Nat => (z : Rat)) hnat
    simpa [doubledLazyConsensusTimeRat] using hrat

private theorem rat_linear_step (a b z q : Rat) (hab : b + 1 = a)
    (h : 2 * (a * q) = b * q + z) : z = (a + 1) * q := by
  grind

/-- Every solution of the homogeneous second-difference equation with zero at
position zero is linear.  Strong induction avoids importing a sequence or
matrix library. -/
private theorem homogeneous_bellman_linear
    (n : Nat) (d : Nat → Rat) (h0 : d 0 = 0)
    (hrec : ∀ x, 0 < x → x < n →
      (2 : Rat) * d x = d (x - 1) + d (x + 1)) :
    ∀ x, x ≤ n → d x = (x : Rat) * d 1 := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
      intro hxn
      by_cases hx0 : x = 0
      · subst x
        simp [h0]
      by_cases hx1 : x = 1
      · subst x
        simp
      let y := x - 1
      have hypos : 0 < y := by dsimp [y]; omega
      have hylt : y < n := by dsimp [y]; omega
      have hr := hrec y hypos hylt
      have hiy := ih y (by dsimp [y]; omega) (by omega : y ≤ n)
      have hiym1 := ih (y - 1) (by dsimp [y]; omega)
        (by omega : y - 1 ≤ n)
      rw [hiy, hiym1] at hr
      have hy1 : y + 1 = x := by dsimp [y]; omega
      rw [hy1] at hr
      have hcast : (((y - 1 : Nat) : Rat) + 1) = (y : Rat) := by
        have hn : y - 1 + 1 = y := by omega
        simpa using congrArg (fun z : Nat => (z : Rat)) hn
      have hz := rat_linear_step (y : Rat) (y - 1 : Nat)
        (d x) (d 1) hcast hr
      have hycast : ((y : Rat) + 1) = (x : Rat) := by
        simpa using congrArg (fun z : Nat => (z : Rat)) hy1
      rw [← hycast]
      exact hz

/-- The finite Bellman boundary-value problem has a unique rational solution on
`0,...,n`.  Hence the displayed cubic polynomial is the only quantity that can
serve as the doubled first-step expected absorption time for this lazy chain. -/
theorem LazyConsensusBellman.unique
    (n : Nat) (hn : 0 < n) (E F : Nat → Rat)
    (hE : LazyConsensusBellman n E)
    (hF : LazyConsensusBellman n F) :
    ∀ x, x ≤ n → E x = F x := by
  let d := fun x => E x - F x
  have hd0 : d 0 = 0 := by
    dsimp [d]
    rw [hE.1, hF.1]
    grind
  have hdrec : ∀ x, 0 < x → x < n →
      (2 : Rat) * d x = d (x - 1) + d (x + 1) := by
    intro x hx hxn
    have he := hE.2.2 x hx hxn
    have hf := hF.2.2 x hx hxn
    dsimp [d]
    grind
  have hlinear := homogeneous_bellman_linear n d hd0 hdrec
  have hdn : d n = 0 := by
    dsimp [d]
    rw [hE.2.1, hF.2.1]
    grind
  have hnlin := hlinear n (by omega)
  rw [hdn] at hnlin
  have hnrat : (n : Rat) ≠ 0 := by
    have hp : (0 : Rat) < n := Rat.natCast_pos.mpr hn
    exact (Rat.ne_of_lt hp).symm
  have hd1 : d 1 = 0 := by
    rcases Rat.mul_eq_zero.mp hnlin.symm with hbad | hgood
    · exact absurd hbad hnrat
    · exact hgood
  intro x hx
  have hdx := hlinear x hx
  rw [hd1, Rat.mul_zero] at hdx
  dsimp [d] at hdx
  grind

/-- Every exact Bellman interpretation of the lazy domain-length absorption
time equals the cubic certificate. -/
theorem LazyConsensusBellman.eq_cubic
    (n : Nat) (hn : 0 < n) (E : Nat → Rat)
    (hE : LazyConsensusBellman n E) :
    ∀ x, x ≤ n → E x = doubledLazyConsensusTimeRat n x :=
  hE.unique n hn E (doubledLazyConsensusTimeRat n)
    (doubledLazyConsensusTimeRat_bellman n)

end PPLLEpochVoterBellman
