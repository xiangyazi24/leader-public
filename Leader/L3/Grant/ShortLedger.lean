import Leader.L3.Grant.ShortBound
import Leader.L3.Headline.Assembly

/-!
# G17: the ledger comparison (F.9) on the finite branch

For every `n ≥ 5` on the finite advice branch (`q = ceilLogTwo n ∈ [3, 79]`),
the coupon-collector term satisfies the dyadic bound `H(n) ≤ q n + 2^q`, and
the permit rate of the selected ledger row (the finite table for `q ≤ 32`,
the `s = 6, 7` rows of the large ledger for `33 ≤ q ≤ 79`) dominates
`H(n) + (2 (2^K + 1) + n (K-1) + 1)/2` times nothing more than `n^2`.

The row inequality is checked at the smallest `n = 2^(q-1) + 1` of each row
and carried to larger `n` by monotonicity of `P n^2 - c n`.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-! ### The dyadic bound on the harmonic term -/

/-- A block of the harmonic sum.

Consumer: `shortHarmDyadic`. -/
theorem shortHarmBlock (n a c : Nat) :
    ∀ m, (∀ k, a ≤ k → k < a + m → (n + k) / (k + 1) ≤ c) →
      shortHarm n (a + m) ≤ shortHarm n a + m * c := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro h
      have h1 := ih (fun k hk1 hk2 => h k hk1 (by omega))
      have h2 := h (a + m) (by omega) (by omega)
      rw [← Nat.add_assoc, shortHarmSucc, Nat.succ_mul]
      omega

/-- `ceil(n/b) ≤ ceil(n/a)` for `a ≤ b`.

Consumer: `shortHarmDyadic`. -/
theorem shortCeilAnti (n a b : Nat) (ha : 0 < a) (hab : a ≤ b) :
    (n + (b - 1)) / b ≤ (n + (a - 1)) / a := by
  have hb : 0 < b := by omega
  have hcov := shortCeilCovers n a ha
  have h1 : (n + (b - 1)) / b < (n + (a - 1)) / a + 1 := by
    apply (Nat.div_lt_iff_lt_mul hb).2
    have h2 : a * ((n + (a - 1)) / a) ≤ b * ((n + (a - 1)) / a) :=
      Nat.mul_le_mul_right _ hab
    have h3 : ((n + (a - 1)) / a + 1) * b =
        b * ((n + (a - 1)) / a) + b := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  omega

/-- The harmonic term at `2^i - 1`.

Consumer: `shortHarmLe`. -/
theorem shortHarmDyadic (n : Nat) (hn : 1 ≤ n) :
    ∀ i, shortHarm n (2 ^ i - 1) ≤ i * n + (2 ^ i - 1) := by
  intro i
  induction i with
  | zero => simp [shortHarm]
  | succ i ih =>
      have hp : 0 < 2 ^ i := Nat.two_pow_pos i
      have hpow : 2 ^ (i + 1) - 1 = (2 ^ i - 1) + 2 ^ i := by
        rw [Nat.pow_succ]
        omega
      rw [hpow]
      have hblock := shortHarmBlock n (2 ^ i - 1) ((n + (2 ^ i - 1)) / 2 ^ i)
        (2 ^ i) (by
          intro k hk1 hk2
          have := shortCeilAnti n (2 ^ i) (k + 1) hp (by omega)
          simpa using this)
      have hmul : (n + (2 ^ i - 1)) / 2 ^ i * 2 ^ i ≤ n + (2 ^ i - 1) :=
        Nat.div_mul_le_self _ _
      have h2 : 2 ^ i * ((n + (2 ^ i - 1)) / 2 ^ i) ≤ n + (2 ^ i - 1) := by
        rw [Nat.mul_comm]
        exact hmul
      have h3 : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by
        rw [Nat.pow_succ]
        omega
      have e : (i + 1) * n = i * n + n := by
        rw [Nat.succ_mul]
      omega

/-- **The dyadic bound** `H(n) ≤ q n + 2^q` for `1 ≤ n ≤ 2^q`.

Consumer: `shortLedgerBound`. -/
theorem shortHarmLe (n q : Nat) (hn : 1 ≤ n) (hq : n ≤ 2 ^ q) :
    shortHarm n n ≤ q * n + 2 ^ q := by
  have hp : 0 < 2 ^ q := Nat.two_pow_pos q
  have h1 := shortHarmDyadic n hn q
  have h2 := shortHarmMono n hq
  have hsucc : shortHarm n (2 ^ q) = shortHarm n (2 ^ q - 1) +
      (n + (2 ^ q - 1)) / 2 ^ q := by
    have h4 := shortHarmSucc n (2 ^ q - 1)
    rw [Nat.sub_add_cancel hp] at h4
    exact h4
  have h3 : (n + (2 ^ q - 1)) / 2 ^ q ≤ 1 := by
    have : (n + (2 ^ q - 1)) / 2 ^ q < 2 := by
      apply (Nat.div_lt_iff_lt_mul hp).2
      omega
    omega
  omega


/-! ### The ledger rows -/

/-- The compiled threshold `K = 2q + kappa` of advice `q`.

Consumer: `shortRowOk`. -/
def shortRowK (q : Nat) : Nat := 2 * q + productionKappa q

/-- The selected permit rate as a function of `q = ceilLogTwo n`: the finite
table for `q ≤ 32`, the large ledger at `s = ceilLogTwo q` above.

Consumer: `shortRowOk`. -/
def shortRowP (q : Nat) : Nat :=
  (if q ≤ 32 then headlineFiniteLedger q
   else headlineLargeLedger (ceilLogTwo q)).1

/-- The row inequality at the smallest `n = 2^(q-1) + 1` of the row `q`:
`2^(K+1) + 2^(q+1) + 3 + (2q + K - 1) N ≤ 2 P N^2`.

Consumer: `shortRowsHold`. -/
def shortRowOk (q : Nat) : Bool :=
  decide (2 ^ (shortRowK q + 1) + 2 ^ (q + 1) + 3 +
      (2 * q + shortRowK q - 1) * (2 ^ (q - 1) + 1) ≤
    2 * shortRowP q * (2 ^ (q - 1) + 1) ^ 2)

/-- **The ledger rows `q = 3 .. 79`.**  Checked row by row.

Consumer: `shortLedgerBound`. -/
theorem shortRowsHold (q : Nat) (h3 : 3 ≤ q) (h79 : q ≤ 79) :
    shortRowOk q = true := by
  have hall : (List.range 80).all
      (fun q => decide (q < 3) || shortRowOk q) = true := by decide
  rw [List.all_eq_true] at hall
  have := hall q (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h | h
  · omega
  · exact h


/-- Every selected permit rate on the finite branch is at least `1000`.

Consumer: `shortLedgerBound`. -/
theorem shortRowPLarge (q : Nat) (h3 : 3 ≤ q) (h79 : q ≤ 79) :
    1000 ≤ shortRowP q := by
  have hall : (List.range 80).all
      (fun q => decide (q < 3) || decide (1000 ≤ shortRowP q)) = true := by
    decide
  rw [List.all_eq_true] at hall
  have := hall q (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h | h
  · omega
  · exact h

/-- Monotonicity of `P n^2 - c1 n`.

Consumer: `shortLedgerBound`. -/
theorem shortLedgerMono (P N n c0 c1 : Nat) (hN : N ≤ n)
    (h : c0 + c1 * N ≤ P * N ^ 2) (hP : c1 ≤ P * (N + n)) :
    c0 + c1 * n ≤ P * n ^ 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = N + d := ⟨n - N, by omega⟩
  have h1 := Nat.mul_le_mul_right d hP
  have e : P * (N + d) ^ 2 = P * N ^ 2 + P * (N + (N + d)) * d := by
    simp only [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm]
    omega
  have e2 : c1 * (N + d) = c1 * N + c1 * d := Nat.mul_add _ _ _
  omega

/-- **The ledger comparison (F.9) on the finite branch.**  For `n ≥ 5` with
`useSmall = true`, the expected-time bound is at most
`headlinePermitRate n * n^2`.

Consumer: `grantLeaderlessShortClause` (GrantLeaderlessShort.lean). -/
theorem shortLedgerBound (n : Nat) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    shortHarm n n +
      (2 * (2 ^ (compileAdvice (ceilLogTwo n)).K + 1) +
        n * ((compileAdvice (ceilLogTwo n)).K - 1) + 1) / 2 ≤
      headlinePermitRate n * n ^ 2 := by
  have hspec := ceilLogTwo_spec n (by omega)
  have hq3 : 3 ≤ ceilLogTwo n := by
    by_cases h : 3 ≤ ceilLogTwo n
    · exact h
    · have hle : ceilLogTwo n ≤ 2 := by omega
      have hp2 := Nat.pow_le_pow_right (by decide : 0 < 2) hle
      have h4 : (2 : Nat) ^ 2 = 4 := by decide
      omega
  have hq79 : ceilLogTwo n ≤ 79 := by
    have h : (compileAdvice (ceilLogTwo n)).useSmall = true := hsmall
    unfold Compiled.useSmall at h
    exact of_decide_eq_true h
  obtain ⟨q, hqdef⟩ : ∃ q, q = ceilLogTwo n := ⟨_, rfl⟩
  rw [← hqdef] at hq3 hq79 hspec hsmall ⊢
  have hKq : (compileAdvice q).K = shortRowK q := rfl
  have hPq : headlinePermitRate n = shortRowP q := by
    unfold headlinePermitRate headlineSelectedLedger shortRowP
    rw [← hqdef]
  rw [hKq, hPq]
  have hrow := shortRowsHold q hq3 hq79
  unfold shortRowOk at hrow
  have hrow' := of_decide_eq_true hrow
  have hP1000 := shortRowPLarge q hq3 hq79
  have hK1 : 1 ≤ shortRowK q := by
    unfold shortRowK
    omega
  have hKlt : shortRowK q < 199 := by
    have := compileAdvice_K_lt_kStar q hq3 hsmall
    rw [hKq] at this
    exact this
  have hq1 : 2 ^ (q - 1) + 1 ≤ n := hspec.1
  have hn2q : n ≤ 2 ^ q := hspec.2
  have hmono := shortLedgerMono (2 * shortRowP q) (2 ^ (q - 1) + 1) n
    (2 ^ (shortRowK q + 1) + 2 ^ (q + 1) + 3)
    (2 * q + shortRowK q - 1) hq1 hrow' (by
      have h5 : 5 ≤ 2 ^ (q - 1) + 1 + n := by
        have : 1 ≤ 2 ^ (q - 1) := Nat.one_le_two_pow
        omega
      have : 2 * shortRowP q * 5 ≤ 2 * shortRowP q * (2 ^ (q - 1) + 1 + n) :=
        Nat.mul_le_mul_left _ h5
      omega)
  have hH := shortHarmLe n q (by omega) hn2q
  have h2q : 2 ^ (q + 1) = 2 * 2 ^ q := by
    rw [Nat.pow_succ]
    omega
  have h2K : 2 ^ (shortRowK q + 1) = 2 * 2 ^ shortRowK q := by
    rw [Nat.pow_succ]
    omega
  have hc1 : 2 * q + shortRowK q - 1 = 2 * q + (shortRowK q - 1) := by omega
  rw [hc1] at hmono
  have hX : (2 * (2 ^ shortRowK q + 1) + n * (shortRowK q - 1) + 1) / 2 * 2 ≤
      2 * (2 ^ shortRowK q + 1) + n * (shortRowK q - 1) + 1 := by omega
  have hexp : (2 * q + (shortRowK q - 1)) * n =
      2 * (q * n) + n * (shortRowK q - 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm]
  have hfin : 2 * (shortHarm n n +
      (2 * (2 ^ shortRowK q + 1) + n * (shortRowK q - 1) + 1) / 2) ≤
      2 * (shortRowP q * n ^ 2) := by
    have e : 2 * shortRowP q * n ^ 2 = 2 * (shortRowP q * n ^ 2) :=
      Nat.mul_assoc _ _ _
    omega
  omega

end L3

#print axioms L3.shortRowsHold
#print axioms L3.shortHarmLe
#print axioms L3.shortLedgerBound
