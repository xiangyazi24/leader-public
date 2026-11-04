import Leader.AAFJ.LeastNonDivisor
import Leader.Wu.Protocol.FiniteState

/-!
# Exact parameters for the rooted polylogarithmic carrier

This module contains only the arithmetic and literal finite-product certificate
for the proposed fixed-block carrier.  It deliberately does not define a
transaction transition.

For a positive exact ring size `n`, let `k` be the least integer at least two
which does not divide `n`.  The carrier uses blocks of

`h = log2 (k - 1) + 1`

physical cells.  Minimality of `k` makes `h` divide `n`, while the existing
prefix-LCM estimate bounds `h` by an explicit iterated logarithm.
-/

namespace PPLLPolylogCarrierParameters

open AAFJExactN

set_option autoImplicit false

/-- The least nondivisor used as the weighted macro-label modulus. -/
def carrierModulus (n : Nat) : Nat := leastNonDivisor n

/-- Bit length of `carrierModulus n - 1`. -/
def carrierHeight (n : Nat) : Nat :=
  Nat.log2 (carrierModulus n - 1) + 1

/-- Explicit pointwise iterated-logarithm envelope for `carrierHeight`. -/
def explicitHeightBound (n : Nat) : Nat :=
  Nat.log2 (Nat.log2 n + 1) + 1

/-- Number of exact `carrierHeight n`-cell macroblocks. -/
def macroCount (n : Nat) : Nat := n / carrierHeight n

/-- The direct `P₂` branch is exactly the odd-size branch. -/
def OddBranch (n : Nat) : Prop := n % 2 = 1

theorem carrierHeight_pos (n : Nat) : 0 < carrierHeight n := by
  simp [carrierHeight]

theorem carrierHeight_lt_modulus {n : Nat} (hn : 0 < n) :
    carrierHeight n < carrierModulus n := by
  let k := carrierModulus n
  have hk2 : 2 ≤ k := leastNonDivisor_ge_two hn
  have hm : k - 1 ≠ 0 := by omega
  have hlog : Nat.log2 (k - 1) < k - 1 :=
    (Nat.log2_lt hm).2 Nat.lt_two_pow_self
  dsimp [carrierHeight, k, carrierModulus] at *
  omega

/-- Exact equal-block divisibility.  For height one this is trivial; otherwise
minimality of the least nondivisor supplies the divisor. -/
theorem carrierHeight_dvd {n : Nat} (hn : 0 < n) :
    carrierHeight n ∣ n := by
  by_cases h1 : carrierHeight n = 1
  · simp [h1]
  · exact dvd_of_lt_leastNonDivisor hn
      (by
        have hp := carrierHeight_pos n
        omega)
      (by simpa [carrierModulus] using carrierHeight_lt_modulus hn)

/-- `carrierHeight` bits contain every canonical residue modulo `k`. -/
theorem modulus_le_two_pow_height {n : Nat} (hn : 0 < n) :
    carrierModulus n ≤ 2 ^ carrierHeight n := by
  let k := carrierModulus n
  have hk2 : 2 ≤ k := leastNonDivisor_ge_two hn
  have hm : k - 1 ≠ 0 := by omega
  have hlt : k - 1 < 2 ^ (Nat.log2 (k - 1) + 1) :=
    (Nat.log2_lt hm).1 (by omega)
  dsimp [carrierHeight, k, carrierModulus] at *
  omega

/-- There are fewer than two full modulus intervals among the `h`-bit words,
so canonicalization needs at most one subtraction. -/
theorem two_pow_height_lt_two_mul_modulus {n : Nat} (hn : 0 < n) :
    2 ^ carrierHeight n < 2 * carrierModulus n := by
  let k := carrierModulus n
  have hk2 : 2 ≤ k := leastNonDivisor_ge_two hn
  have hm : k - 1 ≠ 0 := by omega
  have hlo : 2 ^ Nat.log2 (k - 1) ≤ k - 1 :=
    Nat.log2_self_le hm
  have heq :
      2 ^ (Nat.log2 (k - 1) + 1) =
        2 * 2 ^ Nat.log2 (k - 1) := by
    rw [show Nat.log2 (k - 1) + 1 = (Nat.log2 (k - 1)).succ by omega,
      Nat.pow_succ]
    omega
  dsimp [carrierHeight, k, carrierModulus] at *
  rw [heq]
  omega

theorem modulus_le_two_pow_height_lt_two_mul {n : Nat} (hn : 0 < n) :
    carrierModulus n ≤ 2 ^ carrierHeight n ∧
      2 ^ carrierHeight n < 2 * carrierModulus n :=
  ⟨modulus_le_two_pow_height hn,
    two_pow_height_lt_two_mul_modulus hn⟩

/-- Passing to exact equal blocks preserves the nondivisibility premise needed
by the weighted macro protocol. -/
theorem modulus_not_dvd_macroCount {n : Nat} (hn : 0 < n) :
    ¬ carrierModulus n ∣ macroCount n := by
  intro hd
  rcases hd with ⟨q, hq⟩
  have hnfac : carrierHeight n * macroCount n = n := by
    exact Nat.mul_div_cancel' (carrierHeight_dvd hn)
  apply leastNonDivisor_not_dvd hn
  refine ⟨carrierHeight n * q, ?_⟩
  calc
    n = carrierHeight n * macroCount n := hnfac.symm
    _ = carrierHeight n * (carrierModulus n * q) := by rw [hq]
    _ = carrierModulus n * (carrierHeight n * q) := by
      simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem log2_mono_pos {a b : Nat} (ha : 0 < a) (hab : a ≤ b) :
    Nat.log2 a ≤ Nat.log2 b := by
  apply (Nat.le_log2 (by omega : b ≠ 0)).2
  exact Nat.le_trans (Nat.log2_self_le (by omega : a ≠ 0)) hab

/-- Explicit form of `carrierHeight n = O(log log n)`.  The logarithmic bound
on the least nondivisor is the prefix-LCM theorem
`leastNonDivisor_le_log2_add_two`. -/
theorem carrierHeight_le_explicitHeightBound {n : Nat} (hn : 0 < n) :
    carrierHeight n ≤ explicitHeightBound n := by
  have hk2 := leastNonDivisor_ge_two hn
  have hk := leastNonDivisor_le_log2_add_two hn
  have hmpos : 0 < carrierModulus n - 1 := by
    simpa [carrierModulus] using (show 0 < leastNonDivisor n - 1 by omega)
  have hmle : carrierModulus n - 1 ≤ Nat.log2 n + 1 := by
    simpa [carrierModulus] using
      (show leastNonDivisor n - 1 ≤ Nat.log2 n + 1 by omega)
  have hmono := log2_mono_pos hmpos hmle
  simpa [carrierHeight, explicitHeightBound] using
    Nat.add_le_add_right hmono 1

theorem carrierHeight_eq_one_iff_modulus_eq_two {n : Nat} (hn : 0 < n) :
    carrierHeight n = 1 ↔ carrierModulus n = 2 := by
  have hk2 : 2 ≤ carrierModulus n := by
    simpa [carrierModulus] using leastNonDivisor_ge_two hn
  constructor
  · intro hh
    have hm : carrierModulus n - 1 ≠ 0 := by omega
    have hlog : Nat.log2 (carrierModulus n - 1) = 0 := by
      simpa [carrierHeight] using hh
    have hspec := (Nat.log2_eq_iff hm).1 hlog
    simp at hspec
    omega
  · intro hk
    have hlog : Nat.log2 1 = 0 := by decide
    simp [carrierHeight, hk, hlog]

theorem modulus_eq_two_iff_not_two_dvd {n : Nat} (hn : 0 < n) :
    carrierModulus n = 2 ↔ ¬ 2 ∣ n := by
  constructor
  · intro hk
    have hnd : ¬ carrierModulus n ∣ n := by
      simpa [carrierModulus] using leastNonDivisor_not_dvd hn
    rw [hk] at hnd
    exact hnd
  · intro hnd
    have hk2 : 2 ≤ carrierModulus n := by
      simpa [carrierModulus] using leastNonDivisor_ge_two hn
    apply Nat.le_antisymm ?_ hk2
    by_cases hle : carrierModulus n ≤ 2
    · exact hle
    · have hlt : 2 < leastNonDivisor n := by
        simpa [carrierModulus] using (show 2 < carrierModulus n by omega)
      exact False.elim
        (hnd (dvd_of_lt_leastNonDivisor hn (by omega) hlt))

theorem carrierHeight_eq_one_iff_oddBranch {n : Nat} (hn : 0 < n) :
    carrierHeight n = 1 ↔ OddBranch n := by
  rw [carrierHeight_eq_one_iff_modulus_eq_two hn,
    modulus_eq_two_iff_not_two_dvd hn]
  unfold OddBranch
  constructor
  · intro hnd
    apply (Nat.mod_two_not_eq_zero).mp
    intro hz
    exact hnd ((Nat.dvd_iff_mod_eq_zero).2 hz)
  · intro hm hd
    have hz : n % 2 = 0 := (Nat.dvd_iff_mod_eq_zero).1 hd
    have hnz : n % 2 ≠ 0 := (Nat.mod_two_not_eq_zero).mpr hm
    exact hnz hz

/-! ## Literal rooted-carrier product

The fixed component below records, in order: two digit-bank bits and their
selector; two four-bit macro banks and their selector; the unbanked physical
output bit and eight lock modes; sixteen work kinds and seven auxiliary bits.
The dynamic component records position, cursor, and the non-modularly-used
service-rank field.  This is only a carrier code, not a transition semantics.
-/

abbrev FourBits := (Bool × Bool) × (Bool × Bool)

private abbrev FixedCarrierCode :=
  (((Bool × Bool) × Bool) × ((FourBits × FourBits) × Bool)) ×
    ((Bool × Fin 8) × (Fin 16 × Fin 128))

private abbrev DynamicCarrierCode (h : Nat) :=
  (Fin h × Fin (h + 1)) × Fin (8 * h + 9)

/-- Literal Cartesian carrier proposed for the rooted transaction branch. -/
abbrev RootedCarrierCode (h : Nat) :=
  FixedCarrierCode × DynamicCarrierCode h

private def pairBoolSource : ExhaustiveList (Bool × Bool) :=
  ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool

private def fourBitsSource : ExhaustiveList FourBits :=
  ExhaustiveList.prod pairBoolSource pairBoolSource

private def fixedCarrierSource : ExhaustiveList FixedCarrierCode :=
  ExhaustiveList.prod
    (ExhaustiveList.prod
      (ExhaustiveList.prod pairBoolSource ExhaustiveList.bool)
      (ExhaustiveList.prod
        (ExhaustiveList.prod fourBitsSource fourBitsSource)
        ExhaustiveList.bool))
    (ExhaustiveList.prod
      (ExhaustiveList.prod ExhaustiveList.bool (ExhaustiveList.fin 8))
      (ExhaustiveList.prod (ExhaustiveList.fin 16)
        (ExhaustiveList.fin 128)))

private def dynamicCarrierSource (h : Nat) :
    ExhaustiveList (DynamicCarrierCode h) :=
  ExhaustiveList.prod
    (ExhaustiveList.prod (ExhaustiveList.fin h)
      (ExhaustiveList.fin (h + 1)))
    (ExhaustiveList.fin (8 * h + 9))

/-- Duplicate-free exhaustive enumeration of the literal product. -/
def rootedCarrierStates (h : Nat) : ExhaustiveList (RootedCarrierCode h) :=
  ExhaustiveList.prod fixedCarrierSource (dynamicCarrierSource h)

private theorem pairBoolSource_nodup : pairBoolSource.values.Nodup := by
  exact ExhaustiveList.values_nodup_prod _ _
    ExhaustiveList.values_nodup_bool ExhaustiveList.values_nodup_bool

private theorem fourBitsSource_nodup : fourBitsSource.values.Nodup := by
  exact ExhaustiveList.values_nodup_prod _ _
    pairBoolSource_nodup pairBoolSource_nodup

private theorem fixedCarrierSource_nodup :
    fixedCarrierSource.values.Nodup := by
  apply ExhaustiveList.values_nodup_prod
  · apply ExhaustiveList.values_nodup_prod
    · exact ExhaustiveList.values_nodup_prod _ _
        pairBoolSource_nodup ExhaustiveList.values_nodup_bool
    · exact ExhaustiveList.values_nodup_prod _ _
        (ExhaustiveList.values_nodup_prod _ _
          fourBitsSource_nodup fourBitsSource_nodup)
        ExhaustiveList.values_nodup_bool
  · apply ExhaustiveList.values_nodup_prod
    · exact ExhaustiveList.values_nodup_prod _ _
        ExhaustiveList.values_nodup_bool
        (ExhaustiveList.values_nodup_fin 8)
    · exact ExhaustiveList.values_nodup_prod _ _
        (ExhaustiveList.values_nodup_fin 16)
        (ExhaustiveList.values_nodup_fin 128)

private theorem dynamicCarrierSource_nodup (h : Nat) :
    (dynamicCarrierSource h).values.Nodup := by
  exact ExhaustiveList.values_nodup_prod _ _
    (ExhaustiveList.values_nodup_prod _ _
      (ExhaustiveList.values_nodup_fin h)
      (ExhaustiveList.values_nodup_fin (h + 1)))
    (ExhaustiveList.values_nodup_fin (8 * h + 9))

theorem rootedCarrierStates_nodup (h : Nat) :
    (rootedCarrierStates h).values.Nodup := by
  exact ExhaustiveList.values_nodup_prod _ _
    fixedCarrierSource_nodup (dynamicCarrierSource_nodup h)

private theorem fixedCarrierSource_length :
    fixedCarrierSource.values.length = 134217728 := by
  simp [fixedCarrierSource, fourBitsSource, pairBoolSource,
    ExhaustiveList.values_length_prod, ExhaustiveList.values_length_bool,
    ExhaustiveList.values_length_fin]

private theorem dynamicCarrierSource_length (h : Nat) :
    (dynamicCarrierSource h).values.length =
      h * (h + 1) * (8 * h + 9) := by
  simp [dynamicCarrierSource, ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_fin]

/-- Exact literal state count at height `h`. -/
theorem rootedCarrierStates_length (h : Nat) :
    (rootedCarrierStates h).values.length =
      134217728 * h * (h + 1) * (8 * h + 9) := by
  simp [rootedCarrierStates, ExhaustiveList.values_length_prod,
    fixedCarrierSource_length, dynamicCarrierSource_length, Nat.mul_assoc]

/-- Closed-form carrier polynomial, separated from its enumeration. -/
def rootedCarrierCountAtHeight (h : Nat) : Nat :=
  134217728 * h * (h + 1) * (8 * h + 9)

theorem rootedCarrierCountAtHeight_eq_states (h : Nat) :
    rootedCarrierCountAtHeight h =
      (rootedCarrierStates h).values.length := by
  rw [rootedCarrierStates_length]
  rfl

theorem rootedCarrierCountAtHeight_mono {a b : Nat} (hab : a ≤ b) :
    rootedCarrierCountAtHeight a ≤ rootedCarrierCountAtHeight b := by
  unfold rootedCarrierCountAtHeight
  have h0 : 134217728 * a ≤ 134217728 * b :=
    Nat.mul_le_mul_left _ hab
  have h1 : a + 1 ≤ b + 1 := Nat.add_le_add_right hab 1
  have h2 : 8 * a + 9 ≤ 8 * b + 9 := by omega
  exact Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2

/-- Exact state count of the large rooted branch at ring size `n`. -/
def rootedCarrierStateCount (n : Nat) : Nat :=
  rootedCarrierCountAtHeight (carrierHeight n)

/-- Explicit polynomial-in-iterated-logarithm envelope. -/
def rootedCarrierStateCountBound (n : Nat) : Nat :=
  rootedCarrierCountAtHeight (explicitHeightBound n)

theorem rootedCarrierStateCount_eq (n : Nat) :
    rootedCarrierStateCount n =
      134217728 * carrierHeight n * (carrierHeight n + 1) *
        (8 * carrierHeight n + 9) := rfl

theorem rootedCarrierStateCount_le_explicitBound {n : Nat} (hn : 0 < n) :
    rootedCarrierStateCount n ≤ rootedCarrierStateCountBound n := by
  exact rootedCarrierCountAtHeight_mono
    (carrierHeight_le_explicitHeightBound hn)

/-- A cubic envelope for the exact carrier polynomial.  The coefficient is
literal: `134217728 * 2 * 17 = 4563402752`. -/
theorem rootedCarrierCountAtHeight_le_cube {h : Nat} (hh : 0 < h) :
    rootedCarrierCountAtHeight h ≤ 4563402752 * h ^ 3 := by
  have hnext : h + 1 ≤ 2 * h := by omega
  have hservice : 8 * h + 9 ≤ 17 * h := by omega
  unfold rootedCarrierCountAtHeight
  calc
    134217728 * h * (h + 1) * (8 * h + 9) ≤
        134217728 * h * (2 * h) * (17 * h) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left (134217728 * h) hnext) hservice
    _ = (134217728 * 2 * 17) * (h * h * h) := by ac_rfl
    _ = 4563402752 * (h * h * h) := by rfl
    _ = 4563402752 * h ^ 3 := by simp [Nat.pow_succ]

/-- Direct literal `polyloglog(n)` state bound, with no asymptotic notation
or conversion from bits to states. -/
theorem rootedCarrierStateCount_le_explicit_cube {n : Nat} (hn : 0 < n) :
    rootedCarrierStateCount n ≤
      4563402752 * (explicitHeightBound n) ^ 3 := by
  calc
    rootedCarrierStateCount n ≤
        4563402752 * (carrierHeight n) ^ 3 :=
      rootedCarrierCountAtHeight_le_cube (carrierHeight_pos n)
    _ ≤ 4563402752 * (explicitHeightBound n) ^ 3 :=
      Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (carrierHeight_le_explicitHeightBound hn) 3)

end PPLLPolylogCarrierParameters
