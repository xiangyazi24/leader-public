import Leader.AAFJ.TwoBarrier.RingSixMPlusTwoRecurrence

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.N6m2ExactFamilySignedBalance

open N6m2ColoredChildTable N6m2ColoredRecurrence
open TwoEndpointColoredClock

private theorem hk3 : 0 < 3 := by decide
private theorem N_pos {m : Nat} : 0 < N m := by simp [N]
private theorem N_ne_one {m : Nat} : N m ≠ 1 := by simp [N]
private theorem N_ne_two {m : Nat} (hm : 1 ≤ m) : N m ≠ 2 := by simp [N]; omega

/-- On the sizes `6*m+2`, the exact-family selector is journal P3. -/
theorem leastNonDivisor_N {m : Nat} (hm : 1 ≤ m) :
    AAFJExactN.leastNonDivisor (N m) = 3 := by
  have hn : 0 < N m := by simp [N]
  have hs := AAFJExactN.leastNonDivisor_spec (N m) hn
  have h2dvd : 2 ∣ N m := by
    refine ⟨3 * m + 1, ?_⟩
    simp [N]
    omega
  have h3nd : ¬ 3 ∣ N m := by
    intro h
    rcases h with ⟨c, hc⟩
    simp [N] at hc
    omega
  have hle : AAFJExactN.leastNonDivisor (N m) ≤ 3 := by
    apply Nat.le_of_not_lt
    intro h
    exact h3nd (hs.2.2 3 (by omega) h)
  have hne2 : AAFJExactN.leastNonDivisor (N m) ≠ 2 := by
    intro h
    apply hs.2.1
    simpa [h] using h2dvd
  omega

/-- Therefore the large-ring exact-family protocol is definitionally the P3
protocol used by the accepted colored child table. -/
theorem protocolFor_N_eq_p3 {m : Nat} (hm : 1 ≤ m) :
    AAFJExactFamily.protocolFor (N m) N_pos =
      AAFJPK.protocol 3 hk3 := by
  have hlarge := AAFJExactFamily.protocolFor_large
    (n := N m) N_pos N_ne_one (N_ne_two hm)
  simpa only [leastNonDivisor_N hm] using hlarge

/-- Exact-family wrapper for the source-derived finite-horizon obstruction.
The first conjunct pins the selected protocol; the second is the actual
colored-tree signed-balance failure for every positive horizon. -/
theorem exactFamily_actual_colorMass_signed_balance_fails
    {m : Nat} (hm : 1 ≤ m) {T : Nat} (hT : 0 < T) :
    AAFJExactFamily.protocolFor (N m) N_pos =
        AAFJPK.protocol 3 hk3 ∧
      ¬ (((cm hm .frontAdvance (st0 hm) T : Int) -
              cm hm .rearAdvance (st0 hm) T) *
            ((N m : Int) - 2 * 3) ≤
          (cm hm .rearAdvance (st0 hm) T +
            cm hm .frontAdvance (st0 hm) T : Nat)) := by
  exact ⟨protocolFor_N_eq_p3 hm,
    actual_colorMass_signed_balance_fails hm hT⟩

end AAFJPK.N6m2ExactFamilySignedBalance
