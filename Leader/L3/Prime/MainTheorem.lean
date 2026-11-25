import Leader.L3.MainTheorem
import Leader.L3.Prime.Statement
import Leader.L3.Prime.RenewalSharp

/-!
# L3-PRIME main theorem (`L3PRIME-TRANSFER.tex`, `thm:l3prime`)

For every `n ≥ 5` the compiled family (signed threshold `K = 2q - t_s` on `s ≥ 40000`, the original
L3 record below) satisfies the L3-PRIME headline: state count (T3.3), closed one-leader class,
expected entrance time at most `C n^2 s` with `C = 32652734400000000` (T3.4), and the block tail
(T3.5).  For `n = 4` the separate four-state rule.

The assembly proves the headline at the additive stage cost `headlineStageCost n`
(`l3HeadlineAtProved`); here `headlineStageCost n ≤ C s n^2` on every band:
* `q ≤ 32`: stage rate `≤ 158046 ≤ 2 C`;
* `6 ≤ s < 40000`: rate `≤ 20407959 s^3 ≤ C s`, since `C = 20407959 * 40000^2`;
* `s ≥ 40000`: rate `≤ 6000000 s` (`headlineLargeRate_signed`).
Core Lean only; no `sorry`, `axiom`, `native_decide`.
-/

namespace L3

set_option autoImplicit false

/-- `20407959 s^3 ≤ C s` for `s ≤ 40000`. -/
private theorem l3PrimeCubeLe (s : Nat) (hs : s ≤ 40000) :
    20407959 * s ^ 3 ≤ l3PrimeConstant * s := by
  have hsq : s * s ≤ 40000 * 40000 := Nat.mul_le_mul hs hs
  have hC : l3PrimeConstant = 20407959 * (40000 * 40000) := rfl
  have hcube : s ^ 3 = s * (s * s) := by
    rw [Nat.pow_succ, Nat.pow_two, Nat.mul_assoc]
  rw [hcube, hC]
  calc 20407959 * (s * (s * s)) = s * (20407959 * (s * s)) :=
        Nat.mul_left_comm 20407959 s (s * s)
    _ ≤ s * (20407959 * (40000 * 40000)) :=
        Nat.mul_le_mul_left s (Nat.mul_le_mul_left 20407959 hsq)
    _ = 20407959 * (40000 * 40000) * s := Nat.mul_comm _ _

/-- (T3.4) on every band: `headlineStageCost n ≤ C s n^2`. -/
theorem headlineStageCost_le_l3PrimeBound (n : Nat) (hn : 5 ≤ n) :
    headlineStageCost n ≤ l3PrimeBound n := by
  have hthree : 3 ≤ ceilLogTwo n := ceilLogTwo_ge_three n hn
  unfold headlineStageCost l3PrimeBound
  rw [compileAdvice_s]
  apply Nat.mul_le_mul_right (n ^ 2)
  by_cases hf : ceilLogTwo n ≤ 32
  · have hh := headlineFiniteRate_bound (ceilLogTwo n) hthree hf
    have heq : headlineStageRate n = headlineFiniteRate (ceilLogTwo n) := by
      simp [headlineStageRate, headlinePermitRate,
        headlineRenewalRate, headlineCheckerRate,
        headlineSelectedLedger, headlineFiniteRate, hf]
    rw [heq]
    have h2 : 2 ≤ max 2 (ceilLogTwo (ceilLogTwo n)) := Nat.le_max_left _ _
    have hC : 158046 ≤ l3PrimeConstant * 2 := by decide
    exact Nat.le_trans hh (Nat.le_trans hC (Nat.mul_le_mul_left _ h2))
  · have hs : 6 ≤ ceilLogTwo (ceilLogTwo n) :=
      ceilLogTwo_ge_six (ceilLogTwo n) (by omega)
    have hmax : max 2 (ceilLogTwo (ceilLogTwo n)) = ceilLogTwo (ceilLogTwo n) :=
      Nat.max_eq_right (by omega)
    rw [hmax]
    have heq : headlineStageRate n = headlineLargeRate (ceilLogTwo (ceilLogTwo n)) := by
      simp [headlineStageRate, headlinePermitRate,
        headlineRenewalRate, headlineCheckerRate,
        headlineSelectedLedger, headlineLargeRate, hf]
    rw [heq]
    by_cases hsig : 40000 ≤ ceilLogTwo (ceilLogTwo n)
    · have h1 := headlineLargeRate_signed _ hsig
      have hC : 6000000 ≤ l3PrimeConstant := by decide
      exact Nat.le_trans h1 (Nat.mul_le_mul_right _ hC)
    · exact Nat.le_trans (headlineLargeRate_bound _ hs)
        (l3PrimeCubeLe _ (by omega))

/-- **thm:l3prime for one ring size `n ≥ 5`.** -/
theorem l3PrimeHeadlineProved {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n) :
    L3PrimeHeadline ring := by
  have h := l3HeadlineAtMono ring (by omega)
    (L3.HeadlineCleanAssembly.l3HeadlineAtProved ring hn)
    (headlineStageCost_le_l3PrimeBound n hn)
  unfold L3HeadlineAt at h
  unfold L3PrimeHeadline
  dsimp only at h ⊢
  obtain ⟨hstates, G, hclosed, hsafe, hmean⟩ := h
  refine ⟨hstates, G, hclosed, hsafe, hmean, ?_⟩
  exact UniformFirstHit.survivalProb_blocks_of_expected
    (fun D e => (protocol (ceilLogTwo n)).step ring D e) G (by omega)
    (l3PrimeBound n) hmean

/-- **`thm:l3prime`** (`L3PRIME-TRANSFER.tex`): every `n ≥ 5` with the signed compiler, and the
separate four-state rule for `n = 4`. -/
theorem l3PrimeMainTheorem :
    (∀ {n : Nat} (ring : DirectedRing n), 5 ≤ n → L3PrimeHeadline ring) ∧
    (∀ ring : DirectedRing 4, L3FourAgentHeadline ring) :=
  ⟨fun ring hn => l3PrimeHeadlineProved ring hn, l3MainTheorem.2⟩

/-- (T3.5) for natural `alpha`, in the paper's form: with `k = alpha * ceil(log2 n)`,
`n^alpha * P(T_G > 2 C n^2 s k) ≤ 1`, since `n ≤ 2^ceil(log2 n)`.  Same `G` as the headline. -/
theorem l3PrimePolyTail {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n) :
    ∃ G : (protocol (ceilLogTwo n)).Configuration n → Prop,
      PopulationProtocol.ClosedPred (protocol (ceilLogTwo n)) ring G ∧
      (∀ C, G C → PopulationProtocol.IsSafe (protocol (ceilLogTwo n)) ring C (fun b => b)) ∧
      ∀ (C0 : (protocol (ceilLogTwo n)).Configuration n) (alpha : Nat),
        ((n ^ alpha : Nat) : Rat) *
          UniformFirstHit.survivalProb
            (fun D e => (protocol (ceilLogTwo n)).step ring D e) G C0
            (2 * l3PrimeBound n * (alpha * ceilLogTwo n)) ≤ 1 := by
  have h := l3PrimeHeadlineProved ring hn
  unfold L3PrimeHeadline at h
  dsimp only at h
  obtain ⟨_, G, hclosed, hsafe, _, htail⟩ := h
  refine ⟨G, hclosed, hsafe, ?_⟩
  intro C0 alpha
  have hn0 : 0 < n := by omega
  have ht := htail C0 (alpha * ceilLogTwo n)
  have ht' : ((2 ^ (alpha * ceilLogTwo n) : Nat) : Rat) *
      UniformFirstHit.survivalProb
        (fun D e => (protocol (ceilLogTwo n)).step ring D e) G C0
        (2 * l3PrimeBound n * (alpha * ceilLogTwo n)) ≤ 1 := by
    simpa only [Rat.natCast_pow, Rat.natCast_ofNat] using ht
  have hnat := (UniformFirstHit.survivalProb_bound_iff
    (fun D e => (protocol (ceilLogTwo n)).step ring D e) G hn0 C0 _ _).1 ht'
  apply (UniformFirstHit.survivalProb_bound_iff
    (fun D e => (protocol (ceilLogTwo n)).step ring D e) G hn0 C0 _ _).2
  have hpow : n ^ alpha ≤ 2 ^ (alpha * ceilLogTwo n) := by
    have hle : n ≤ 2 ^ ceilLogTwo n := (ceilLogTwo_spec n (by omega)).2
    calc n ^ alpha ≤ (2 ^ ceilLogTwo n) ^ alpha := Nat.pow_le_pow_left hle alpha
      _ = 2 ^ (alpha * ceilLogTwo n) := by
        rw [← Nat.pow_mul, Nat.mul_comm]
  exact Nat.le_trans (Nat.mul_le_mul_right _ hpow) hnat

end L3

#print axioms L3.headlineStageCost_le_l3PrimeBound
#print axioms L3.l3PrimeHeadlineProved
#print axioms L3.l3PrimeMainTheorem
#print axioms L3.l3PrimePolyTail
