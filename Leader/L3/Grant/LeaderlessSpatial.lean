import Leader.L3.Grant.BlockSharpHitting
import Leader.L3.Headline.Stages
import Leader.L3.Headline.GrantProducer

/-!
# G18: `StageGrantLeaderlessClock` on the spatial band, at the ledger rate

* The compiled advice of a spatial `q = ceilLogTwo n ≥ 80` has `b = s + 11`
  and `K = 2 q + kappaDot s`, `s = ceilLogTwo q ≥ 7`.
* The ledger permit rate (`headlineLargeLedger s`) is at least
  `192 + 17 (8 s + 101)(s + 13) 2^(kappaDot s)`: the rows `s = 7 .. 16` are
  exactly that number, and for `s ≥ 17` it is `192 + 34 f w (A+1)` with
  `2^kappa < 2 (A+1)`.
* `2^(2 q) + 4 ≤ 4 n^2`, hence `192 n^2 + (17 Q + 3)/4 ≤ permit * n^2`.
* The premises of the hitting theorem (nonalias, `2 bankLeaseCap ≤ n`,
  `(4096 (b+2))^2 ≤ n`, `16 ≤ n`) follow from the compiled spatial square
  lower bound `grantClockSpatialPaperBudgetSquareLower`.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The compiled advice of a spatial `q`.

Consumer: `grantLeaderlessCoefficientLe`. -/
theorem grantLeaderlessAdviceShape (q : Nat) (hq : 80 ≤ q) :
    7 ≤ ceilLogTwo q ∧
    (compileAdvice q).b = ceilLogTwo q + 11 ∧
    (compileAdvice q).K = 2 * q + kappaDot (ceilLogTwo q) := by
  have hwidth := grantClockSpatialWidthBounds q hq
  have hs : (compileAdvice q).s = ceilLogTwo q := by
    have h7 := hwidth.1
    rw [compileAdvice_s] at h7 ⊢
    omega
  have h7 : 7 ≤ ceilLogTwo q := by
    have h := hwidth.1
    omega
  refine ⟨h7, ?_, ?_⟩
  · change (compileAdvice q).s + 11 = _
    rw [hs]
  · change 2 * q + productionKappa q = _
    unfold productionKappa
    rw [if_neg (by omega : ¬ q ≤ 32)]
    unfold paddedS sourceTOfQ
    rw [Nat.max_eq_right (by omega : 2 ≤ ceilLogTwo q)]

/-- `kappaDot s = 17` on `7 ≤ s ≤ 16`, by `ceilLogTwo_unique` (evaluating `Nat.log2` by `decide`
costs the kernel about 90 s and 7.8 GB). -/
private theorem grantLeaderlessKappaLow (s : Nat) (hs : 7 ≤ s) (h16 : s ≤ 16) :
    kappaDot s = 17 := by
  unfold kappaDot
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have h16' : (2 : Nat) ^ (17 - 1) = 65536 := rfl
  have h17 : (2 : Nat) ^ 17 = 131072 := rfl
  exact ceilLogTwo_unique 17 _ (by omega) (by rw [h16']; omega) (by rw [h17]; omega)

/-- The table rows `s = 7 .. 16`, as closed literals. -/
private theorem grantLeaderlessLedgerRowLow (s : Nat) (hs : 7 ≤ s) (h16 : s ≤ 16) :
    192 + 17 * (8 * s + 101) * (s + 13) * 2 ^ 17 ≤ (headlineLargeLedger s).1 := by
  have hcases : s = 7 ∨ s = 8 ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨
      s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

private theorem grantLeaderlessPowPred (c : Nat) (hc : 1 ≤ c) :
    2 ^ c = 2 * 2 ^ (c - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]

private theorem grantLeaderlessKappaHigh (s : Nat) (h16 : ¬ s ≤ 16) :
    kappaDot s = ceilLogTwo (557 * s + 119982) := by
  unfold kappaDot
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem grantLeaderlessLedgerHigh (s : Nat) (h16 : ¬ s ≤ 16) :
    (headlineLargeLedger s).1 =
      192 + 34 * (8 * s + 101) * (s + 13) * (557 * s + 119982) := by
  unfold headlineLargeLedger
  rw [if_neg h16]

/-- The ledger permit rate dominates `192 + 17 f w 2^kappa` for `s ≥ 7`: the
table rows `s = 7 .. 16` equal it, and for `s ≥ 17` the formula
`192 + 34 f w (A+1)` has `2^kappa < 2 (A+1)`.

Consumer: `grantLeaderlessCoefficientLe`. -/
theorem grantLeaderlessLedgerRow (s : Nat) (hs : 7 ≤ s) :
    192 + 17 * (8 * s + 101) * (s + 13) * 2 ^ kappaDot s ≤
      (headlineLargeLedger s).1 := by
  by_cases h16 : s ≤ 16
  · rw [grantLeaderlessKappaLow s hs h16]
    exact grantLeaderlessLedgerRowLow s hs h16
  · have hk := grantLeaderlessKappaHigh s h16
    have hspec := ceilLogTwo_spec (557 * s + 119982) (by omega)
    have hpos : 1 ≤ ceilLogTwo (557 * s + 119982) := by
      by_cases h0 : ceilLogTwo (557 * s + 119982) = 0
      · rw [h0] at hspec
        have := hspec.2
        simp at this
      · omega
    have hpow := grantLeaderlessPowPred _ hpos
    have hle : 2 ^ kappaDot s ≤ 2 * (557 * s + 119982) := by
      rw [hk, hpow]
      omega
    rw [grantLeaderlessLedgerHigh s h16]
    have hm := Nat.mul_le_mul_left (17 * (8 * s + 101) * (s + 13)) hle
    have e1 : 17 * (8 * s + 101) * (s + 13) * (2 * (557 * s + 119982)) =
        34 * (8 * s + 101) * (s + 13) * (557 * s + 119982) := by
      rw [show (34 : Nat) = 17 * 2 from rfl]
      ac_rfl
    omega

/-- The ledger arithmetic over opaque naturals.

Consumer: `grantLeaderlessCoefficientLe`. -/
theorem grantLeaderlessLedgerArith (n q s kappa perm : Nat)
    (hP2 : 2 ^ (2 * q) + 4 ≤ 4 * (n * n))
    (hrow : 192 + 17 * (8 * s + 101) * (s + 13) * 2 ^ kappa ≤ perm) :
    192 * n ^ 2 + (17 * ((s + 11 + 2) * (8 * (s + 11) + 13) *
      2 ^ (2 * q + kappa)) + 3) / 4 ≤ perm * n ^ 2 := by
  have hQ : (s + 11 + 2) * (8 * (s + 11) + 13) * 2 ^ (2 * q + kappa) =
      ((8 * s + 101) * (s + 13) * 2 ^ kappa) * 2 ^ (2 * q) := by
    rw [Nat.pow_add]
    have e1 : 8 * (s + 11) + 13 = 8 * s + 101 := by omega
    have e2 : s + 11 + 2 = s + 13 := by omega
    rw [e1, e2]
    ac_rfl
  rw [hQ, Nat.pow_two]
  have hV : 0 < 2 ^ kappa := Nat.two_pow_pos _
  have hY : 1 ≤ (8 * s + 101) * (s + 13) * 2 ^ kappa :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hV
  have e3 : 17 * (8 * s + 101) * (s + 13) * 2 ^ kappa =
      17 * ((8 * s + 101) * (s + 13) * 2 ^ kappa) := by ac_rfl
  rw [e3] at hrow
  generalize (8 * s + 101) * (s + 13) * 2 ^ kappa = Y at hY hrow ⊢
  generalize 2 ^ (2 * q) = P2 at hP2 ⊢
  generalize n * n = nn at hP2 ⊢
  have h1 := Nat.mul_le_mul_right nn hrow
  have h2 := Nat.mul_le_mul_left (17 * Y) hP2
  have e4 : 17 * Y * (P2 + 4) = 17 * (Y * P2) + 68 * Y := by
    rw [Nat.mul_add, Nat.mul_assoc]
    have : 17 * Y * 4 = 68 * Y := by omega
    rw [this]
  have e5 : 17 * Y * (4 * nn) = 68 * (Y * nn) := by
    calc
      17 * Y * (4 * nn) = (17 * 4) * (Y * nn) := by ac_rfl
      _ = 68 * (Y * nn) := rfl
  have e6 : (192 + 17 * Y) * nn = 192 * nn + 17 * (Y * nn) := by
    rw [Nat.add_mul, Nat.mul_assoc]
  rw [e4, e5] at h2
  rw [e6] at h1
  omega

/-- The BANK block coefficient is within the ledger permit rate: for a
spatial `n`, `192 n^2 + (17 Q + 3)/4 ≤ headlinePermitRate n * n^2`.

Consumer: `grantLeaderlessSpatialClause`. -/
theorem grantLeaderlessCoefficientLe (n : Nat) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    192 * n ^ 2 + (17 * grantBlockEntranceCoefficient n + 3) / 4 ≤
      headlinePermitRate n * n ^ 2 := by
  have hq := grantClockSpatialAdviceEighty (ceilLogTwo n) hsp
  obtain ⟨hs7, hb, hK⟩ := grantLeaderlessAdviceShape (ceilLogTwo n) hq
  have hrow := grantLeaderlessLedgerRow (ceilLogTwo (ceilLogTwo n)) hs7
  have hperm : headlinePermitRate n =
      (headlineLargeLedger (ceilLogTwo (ceilLogTwo n))).1 := by
    unfold headlinePermitRate headlineSelectedLedger
    rw [if_neg (by omega)]
  rw [hperm]
  generalize (headlineLargeLedger (ceilLogTwo (ceilLogTwo n))).1 = perm
    at hrow ⊢
  have hspec := (ceilLogTwo_spec n (by omega)).1
  have hqpos : 1 ≤ ceilLogTwo n := by omega
  have hP2 : 2 ^ (2 * ceilLogTwo n) + 4 ≤ 4 * (n * n) := by
    have hA : 2 ^ (2 * ceilLogTwo n) =
        4 * (2 ^ (ceilLogTwo n - 1) * 2 ^ (ceilLogTwo n - 1)) := by
      rw [← Nat.pow_add, show (4 : Nat) = 2 ^ 2 by decide,
        ← Nat.pow_add]
      congr 1
      omega
    have hpos : 1 ≤ 2 ^ (ceilLogTwo n - 1) := Nat.one_le_two_pow
    have hsq : (2 ^ (ceilLogTwo n - 1) + 1) *
        (2 ^ (ceilLogTwo n - 1) + 1) ≤ n * n :=
      Nat.mul_le_mul hspec hspec
    rw [hA]
    generalize 2 ^ (ceilLogTwo n - 1) = A at hpos hsq ⊢
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hsq
    omega
  have key := grantLeaderlessLedgerArith n (ceilLogTwo n)
    (ceilLogTwo (ceilLogTwo n))
    (kappaDot (ceilLogTwo (ceilLogTwo n))) perm hP2 hrow
  unfold grantBlockEntranceCoefficient
  rw [hb, hK]
  exact key

/-- The premises of the hitting theorem on the spatial band, from the
compiled spatial square lower bound and the G2 population lower bound.

Consumer: `grantLeaderlessSpatialClause`. -/
theorem grantLeaderlessSpatialPremises (n : Nat) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    16 ≤ n ∧
    (4096 * ((compileAdvice (ceilLogTwo n)).b + 2)) ^ 2 ≤ n ∧
    BankTrialLiveWindowNonalias n (ceilLogTwo n) ∧
    2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n := by
  have hpop := grantClockSpatialPopulationLower n hn hsp
  have h16 : 16 ≤ 2 ^ 79 := by decide
  have hbudget := grantClockSpatialPaperBudgetSquareLower n hn hsp
  have hsize : (4096 * ((compileAdvice (ceilLogTwo n)).b + 2)) ^ 2 ≤ n := by
    have hle : 4096 * ((compileAdvice (ceilLogTwo n)).b + 2) ≤
        256 * (1024 *
          (224 * ((compileAdvice (ceilLogTwo n)).b + 2) +
            32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
              ((compileAdvice (ceilLogTwo n)).K + 2))) := by
      omega
    exact Nat.le_trans (Nat.pow_le_pow_left hle 2) hbudget
  have hself : 4096 * ((compileAdvice (ceilLogTwo n)).b + 2) ≤
      (4096 * ((compileAdvice (ceilLogTwo n)).b + 2)) ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.le_mul_self _
  refine ⟨by omega, hsize, ?_, ?_⟩
  · change (compileAdvice (ceilLogTwo n)).b + 2 ≤ n
    omega
  · change 2 * (13 * ((compileAdvice (ceilLogTwo n)).b + 2)) ≤ n
    omega

/-- **`StageGrantLeaderlessClock` on the spatial band, at the ledger rate.**
For `useSmall = false` (equivalently `ceilLogTwo n ≥ 80`) and every purified,
leaderless, grant-free configuration, the expected number of physical
interactions to `headlineGrantReady ∨ headlineGeneratedTarget` is at most
`headlinePermitRate n * n^2`.

Consumer: `stageGrantLeaderlessClockOfSmallBand`. -/
theorem grantLeaderlessSpatialClause {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ C : HeadlineConfiguration n,
      headlinePurified ring C →
      (∀ i : Fin n, (C i).l = false) →
      (∀ i : Fin n, (C i).grant = false) →
      UniformFirstHit.ExpectedHittingTimeAtMost
        (headlinePhysicalNext ring)
        (fun D => headlineGrantReady ring D ∨
          headlineGeneratedTarget ring D)
        C ((headlinePermitRate n * n ^ 2 : Nat) : Rat) := by
  intro C hpurified _ _
  obtain ⟨h16, hsize, hw, hlarge⟩ :=
    grantLeaderlessSpatialPremises n hn hsp
  have hhit := grantBlockSharpLeaderlessExpectedHitting ring h16 hsp hw
    hlarge hsize C hpurified
  have hle := grantLeaderlessCoefficientLe n hn hsp
  have hnpos : 0 < n := by omega
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) _ hnpos C _).2
  intro T
  have hcost := (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) _ hnpos C _).1 hhit T
  exact Nat.le_trans hcost (Nat.mul_le_mul_left _ hle)

/-- `StageGrantLeaderlessClock` reduces to the SMALL band: the spatial band
is `grantLeaderlessSpatialClause`; what remains is the clause for
`useSmall = true` (the SHORT branch, G17).

Consumer: `stageFirstGrant_of_leaderless_clock` (HeadlineStages.lean). -/
theorem stageGrantLeaderlessClockOfSmallBand {n : Nat}
    (ring : DirectedRing n)
    (hshort : (compileAdvice (ceilLogTwo n)).useSmall = true →
      ∀ C : HeadlineConfiguration n,
        headlinePurified ring C →
        (∀ i : Fin n, (C i).l = false) →
        (∀ i : Fin n, (C i).grant = false) →
        UniformFirstHit.ExpectedHittingTimeAtMost
          (headlinePhysicalNext ring)
          (fun D => headlineGrantReady ring D ∨
            headlineGeneratedTarget ring D)
          C ((headlinePermitRate n * n ^ 2 : Nat) : Rat)) :
    StageGrantLeaderlessClock ring := by
  intro C hpurified hl hg
  cases hsp : (compileAdvice (ceilLogTwo n)).useSmall with
  | true => exact hshort hsp C hpurified hl hg
  | false =>
      have h80 := grantClockSpatialAdviceEighty (ceilLogTwo n) hsp
      have hn : 5 ≤ n := by
        have := ceilLogTwo_le_self n
        omega
      exact grantLeaderlessSpatialClause ring hn hsp C hpurified hl hg

end L3

#print axioms L3.grantLeaderlessAdviceShape
#print axioms L3.grantLeaderlessLedgerRow
#print axioms L3.grantLeaderlessCoefficientLe
#print axioms L3.grantLeaderlessSpatialPremises
#print axioms L3.grantLeaderlessSpatialClause
#print axioms L3.stageGrantLeaderlessClockOfSmallBand
