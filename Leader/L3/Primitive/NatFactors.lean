import Leader.L3.Primitive.TapPoly

/-!
Primitive natural-factor arithmetic, for PrimitiveFieldGenerator
and PrimitiveTapSelection.

The unrestricted strip-prime-preservation claim is false when d
is composite; the correct versions below either require p not
to divide d or require d itself to be prime.
All other requested factor enumeration, distinct prime-power list,
Euclidean, and literal search conclusions are transcribed below.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- PrimitiveFieldGenerator: a prime is a Nat >= 2 with no
nontrivial positive proper divisor. -/
def TapNatPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- PrimitiveFieldGenerator: the literal strip result is a
divisor of the original input, for every amount of fuel. -/
theorem tapStripFactorFuelDivides (m d fuel : Nat) :
    tapStripFactorFuel m d fuel ∣ m := by
  induction fuel generalizing m with
  | zero =>
      simp [tapStripFactorFuel]
  | succ fuel ih =>
      by_cases hlow : d < 2
      · simp [tapStripFactorFuel, hlow]
      · by_cases hz : m % d = 0
        · have hstep :
              tapStripFactorFuel m d (fuel + 1) =
                tapStripFactorFuel (m / d) d fuel := by
            simp [tapStripFactorFuel, hlow, hz]
          rw [hstep]
          exact Nat.dvd_trans (ih (m / d))
            (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero hz))
        · simp [tapStripFactorFuel, hlow, hz]

/-- PrimitiveFieldGenerator: stripping a positive input by a
divisor >= 2 leaves a positive quotient at every stage. -/
theorem tapStripFactorFuelPositive (m d fuel : Nat)
    (hm : 0 < m) (hd : 2 ≤ d) :
    0 < tapStripFactorFuel m d fuel := by
  induction fuel generalizing m with
  | zero =>
      simpa [tapStripFactorFuel] using hm
  | succ fuel ih =>
      have hlow : ¬ d < 2 := by omega
      by_cases hz : m % d = 0
      · have hdvd : d ∣ m := Nat.dvd_of_mod_eq_zero hz
        have hquot : 0 < m / d := by
          apply (Nat.one_le_div_iff (by omega : 0 < d)).2
          exact Nat.le_of_dvd hm hdvd
        have hrec := ih (m / d) hquot
        simpa [tapStripFactorFuel, hlow, hz] using hrec
      · simpa [tapStripFactorFuel, hlow, hz] using hm

/-- PrimitiveFieldGenerator: if m < 2^fuel, each successful
division by d >= 2 at least halves m, so the last quotient
cannot still be divisible by d. -/
theorem tapStripFactorFuelNoDivisor (m d fuel : Nat)
    (hm : 0 < m) (hd : 2 ≤ d)
    (hbound : m < 2 ^ fuel) :
    ¬ d ∣ tapStripFactorFuel m d fuel := by
  induction fuel generalizing m with
  | zero =>
      have hlt : m < 1 := by simpa using hbound
      omega
  | succ fuel ih =>
      have hlow : ¬ d < 2 := by omega
      by_cases hz : m % d = 0
      · have hdvd : d ∣ m := Nat.dvd_of_mod_eq_zero hz
        have hquot : 0 < m / d := by
          apply (Nat.one_le_div_iff (by omega : 0 < d)).2
          exact Nat.le_of_dvd hm hdvd
        have hmul : 2 * (m / d) ≤ m := by
          have hh := Nat.mul_le_mul_right (m / d) hd
          rw [Nat.mul_div_cancel_left' hdvd] at hh
          exact hh
        have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm]
        have hqbound : m / d < 2 ^ fuel := by
          rw [hpow] at hbound
          omega
        have hrec := ih (m / d) hquot hqbound
        simpa [tapStripFactorFuel, hlow, hz] using hrec
      · have hnot : ¬ d ∣ m := by
          intro hdvd
          exact hz (Nat.mod_eq_zero_of_dvd hdvd)
        simpa [tapStripFactorFuel, hlow, hz] using hnot

/-- PrimitiveFieldGenerator: a prime not dividing d is
preserved by every strip step, including when d is composite.
A mere inequality p != d does not suffice. -/
theorem tapStripFactorFuelPreservesPrime (m d fuel p : Nat)
    (hd : 2 ≤ d) (hp : TapNatPrime p)
    (hnot : ¬ p ∣ d) :
    (p ∣ m ↔ p ∣ tapStripFactorFuel m d fuel) := by
  have hcop : Nat.Coprime p d := by
    have hgd : Nat.gcd p d ∣ p := Nat.gcd_dvd_left p d
    rcases hp.2 (Nat.gcd p d) hgd with hone | hpEq
    · exact hone
    · have hpd : p ∣ d := by
        rw [← hpEq]
        exact Nat.gcd_dvd_right p d
      exact False.elim (hnot hpd)
  induction fuel generalizing m with
  | zero =>
      simp [tapStripFactorFuel]
  | succ fuel ih =>
      have hlow : ¬ d < 2 := by omega
      by_cases hz : m % d = 0
      · have hdvd : d ∣ m := Nat.dvd_of_mod_eq_zero hz
        have heq : p ∣ m ↔ p ∣ m / d := by
          constructor
          · intro hpm
            have hprod : p ∣ d * (m / d) := by
              rw [Nat.mul_div_cancel_left' hdvd]
              exact hpm
            exact hcop.dvd_of_dvd_mul_left hprod
          · intro hquot
            exact Nat.dvd_trans hquot
              (Nat.div_dvd_of_dvd hdvd)
        calc
          (p ∣ m) ↔ p ∣ m / d := heq
          _ ↔ p ∣ tapStripFactorFuel (m / d) d fuel :=
            ih (m / d)
          _ ↔ p ∣ tapStripFactorFuel m d (fuel + 1) := by
            simp [tapStripFactorFuel, hlow, hz]
      · simp [tapStripFactorFuel, hlow, hz]

/-- PrimitiveFieldGenerator: the stated logarithmic fuel
really strips all occurrences of any divisor d >= 2.
This is the true common part of tapStripFactorComplete. -/
theorem tapStripFactorCompleteCore (m d : Nat)
    (hm : 0 < m) (hd : 2 ≤ d) :
    tapStripFactorFuel m d (Nat.log2 m + 1) ∣ m ∧
    0 < tapStripFactorFuel m d (Nat.log2 m + 1) ∧
    ¬ d ∣ tapStripFactorFuel m d (Nat.log2 m + 1) := by
  refine ⟨tapStripFactorFuelDivides m d _, ?_, ?_⟩
  · exact tapStripFactorFuelPositive m d _ hm hd
  · exact tapStripFactorFuelNoDivisor m d _
      hm hd Nat.lt_log2_self

/-- PrimitiveFieldGenerator: a repaired strip-completeness
interface. With a prime divisor d, all other primes survive. -/
theorem tapStripFactorCompletePrime (m d : Nat)
    (hm : 0 < m) (hd : TapNatPrime d) :
    tapStripFactorFuel m d (Nat.log2 m + 1) ∣ m ∧
    0 < tapStripFactorFuel m d (Nat.log2 m + 1) ∧
    (¬ d ∣ tapStripFactorFuel m d (Nat.log2 m + 1)) ∧
    (∀ p : Nat, TapNatPrime p → p ≠ d →
      (p ∣ m ↔ p ∣ tapStripFactorFuel m d (Nat.log2 m + 1))) := by
  obtain ⟨hdiv, hpos, hfree⟩ :=
    tapStripFactorCompleteCore m d hm hd.1
  refine ⟨hdiv, hpos, hfree, ?_⟩
  intro p hp hneq
  have hnot : ¬ p ∣ d := by
    intro hpd
    rcases hd.2 p hpd with hunit | hsame
    · have := hp.1
      omega
    · exact hneq hsame
  exact tapStripFactorFuelPreservesPrime
    m d (Nat.log2 m + 1) p hd.1 hp hnot


/-! The fuel-generic factor-scan soundness and completeness
invariants are proved after the independent prime-existence
and terminal-small-divisor lemmas. -/

/-- PrimitiveFieldGenerator: any Nat >= 2 has a prime divisor.
The proper-divisor branch uses strong induction on that divisor,
not the as-yet-unproved executable prime-factor list. -/
theorem tapExistsPrimeDvd (m : Nat) (hm : 2 ≤ m) :
    ∃ p : Nat, TapNatPrime p ∧ p ∣ m := by
  classical
  have hmain :
      ∀ k : Nat, 2 ≤ k →
        ∃ p : Nat, TapNatPrime p ∧ p ∣ k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro hk
        by_cases hproper :
            ∃ d : Nat, d ∣ k ∧ d ≠ 1 ∧ d ≠ k
        · obtain ⟨d, hdvd, hone, hne⟩ := hproper
          have hdpos : 0 < d :=
            Nat.pos_of_dvd_of_pos hdvd (by omega)
          have hdtwo : 2 ≤ d := by omega
          have hdlt : d < k := by
            have hle := Nat.le_of_dvd (by omega : 0 < k) hdvd
            omega
          obtain ⟨p, hp, hpk⟩ := ih d hdlt hdtwo
          exact ⟨p, hp, Nat.dvd_trans hpk hdvd⟩
        · have hprime : TapNatPrime k := by
            constructor
            · exact hk
            · intro d hdvd
              by_cases hone : d = 1
              · exact Or.inl hone
              · by_cases hself : d = k
                · exact Or.inr hself
                · exact False.elim
                    (hproper ⟨d, hdvd, hone, hself⟩)
          exact ⟨k, hprime, Nat.dvd_refl k⟩
  exact hmain m hm



/-- PrimitiveFieldGenerator: a composite integer >= 2 has
a genuine nonunit proper divisor. Consumer: detecting the
final trial-scan prime. -/
theorem tapCompositeProperDivisor (m : Nat)
    (hm : 2 ≤ m) (hnot : ¬ TapNatPrime m) :
    ∃ d : Nat, d ∣ m ∧ 2 ≤ d ∧ d < m := by
  classical
  by_cases hproper : ∃ d : Nat, d ∣ m ∧ d ≠ 1 ∧ d ≠ m
  · obtain ⟨d, hdvd, hone, hne⟩ := hproper
    have hpos : 0 < d :=
      Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hle := Nat.le_of_dvd (by omega : 0 < m) hdvd
    exact ⟨d, hdvd, by omega, by omega⟩
  · have hprime : TapNatPrime m := by
      constructor
      · exact hm
      · intro d hdvd
        by_cases hone : d = 1
        · exact Or.inl hone
        · by_cases hself : d = m
          · exact Or.inr hself
          · exact False.elim
              (hproper ⟨d, hdvd, hone, hself⟩)
    exact False.elim (hnot hprime)

/-- PrimitiveFieldGenerator: if all smaller prime divisors
have been eliminated and m < d*d, the positive residual
m must itself be prime. This is the terminal trial row.
Consumer: tapPrimeFactorsSound. -/
theorem tapPrimeOfNoSmallDivisor (m d : Nat)
    (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hbelow : m < d * d)
    (hno : ∀ p : Nat, TapNatPrime p → p < d → ¬ p ∣ m) :
    TapNatPrime m := by
  classical
  by_cases hprime : TapNatPrime m
  · exact hprime
  · obtain ⟨a, hadvd, hatwo, halt⟩ :=
      tapCompositeProperDivisor m hm hprime
    have hapos : 0 < a := by omega
    have hquotpos : 0 < m / a := by
      apply (Nat.one_le_div_iff hapos).2
      exact Nat.le_of_dvd (by omega : 0 < m) hadvd
    have hquotTwo : 2 ≤ m / a := by
      by_cases hone : m / a = 1
      · have heq : m = a := by
          calc
            m = (m / a) * a := (Nat.div_mul_cancel hadvd).symm
            _ = a := by rw [hone]; simp
        omega
      · omega
    by_cases halow : a < d
    · obtain ⟨p, hp, hpa⟩ := tapExistsPrimeDvd a hatwo
      have hpbelow : p < d := by
        have hle := Nat.le_of_dvd hapos hpa
        omega
      exact False.elim
        (hno p hp hpbelow (Nat.dvd_trans hpa hadvd))
    · have hbBelow : m / a < d := by
        by_cases hbLarge : d ≤ m / a
        · have hsq : d * d ≤ a * (m / a) :=
            Nat.mul_le_mul (by omega : d ≤ a) hbLarge
          rw [Nat.mul_div_cancel_left' hadvd] at hsq
          omega
        · omega
      obtain ⟨p, hp, hpquot⟩ :=
        tapExistsPrimeDvd (m / a) hquotTwo
      have hpbelow : p < d := by
        have hle := Nat.le_of_dvd hquotpos hpquot
        omega
      exact False.elim
        (hno p hp hpbelow
          (Nat.dvd_trans hpquot
            (Nat.div_dvd_of_dvd hadvd)))


/-- PrimitiveFieldGenerator: under a positive trial remainder
having no smaller prime divisor, every factor output by the
literal fuel-limited trial program is prime and divides the
original input. This soundness lemma does not need fuel
completeness, only the exact OLD program branches. -/
theorem tapPrimeFactorsFuelSound
    (initial m d fuel : Nat)
    (hd : 2 ≤ d) (hm : 0 < m)
    (hno : ∀ q : Nat, TapNatPrime q → q < d → ¬ q ∣ m)
    (hmdiv : m ∣ initial)
    (p : Nat) (hmem : p ∈ tapPrimeFactorsFuel m d fuel) :
    TapNatPrime p ∧ p ∣ initial := by
  have hmain :
      ∀ k x a : Nat,
        2 ≤ a → 0 < x →
        (∀ q : Nat, TapNatPrime q → q < a → ¬ q ∣ x) →
        x ∣ initial →
        ∀ z : Nat, z ∈ tapPrimeFactorsFuel x a k →
          TapNatPrime z ∧ z ∣ initial := by
    intro k
    induction k with
    | zero =>
        intro x a _ _ _ _ z hz
        simp [tapPrimeFactorsFuel] at hz
    | succ k ih =>
        intro x a ha hx hnone hxdiv z hz
        by_cases hsmall : x ≤ 1
        · simp [tapPrimeFactorsFuel, hsmall] at hz
        · have hxtwo : 2 ≤ x := by omega
          by_cases hterminal : x < a * a
          · have hprime :=
              tapPrimeOfNoSmallDivisor
                x a hxtwo ha hterminal hnone
            have heq : z = x := by
              simpa [tapPrimeFactorsFuel, hsmall, hterminal]
                using hz
            rw [heq]
            exact ⟨hprime, hxdiv⟩
          · by_cases hzero : x % a = 0
            · have hadvd : a ∣ x := Nat.dvd_of_mod_eq_zero hzero
              have haprime : TapNatPrime a := by
                by_cases hprime : TapNatPrime a
                · exact hprime
                · obtain ⟨b, hbdiv, hbtwo, hblt⟩ :=
                    tapCompositeProperDivisor a ha hprime
                  obtain ⟨q, hq, hqb⟩ :=
                    tapExistsPrimeDvd b hbtwo
                  have hqlt : q < a := by
                    have hle := Nat.le_of_dvd (by omega : 0 < b) hqb
                    omega
                  have hqx : q ∣ x :=
                    Nat.dvd_trans (Nat.dvd_trans hqb hbdiv) hadvd
                  exact False.elim (hnone q hq hqlt hqx)
              have hbranch :
                  z = a ∨
                    z ∈ tapPrimeFactorsFuel
                      (tapStripFactorFuel x a (Nat.log2 x + 1))
                      (a + 1) k := by
                simpa [tapPrimeFactorsFuel, hsmall,
                  hterminal, hzero] using hz
              rcases hbranch with heq | htail
              · rw [heq]
                exact ⟨haprime, Nat.dvd_trans hadvd hxdiv⟩
              · obtain ⟨hstrip, hpos, hfree⟩ :=
                  tapStripFactorCompleteCore x a hx ha
                have hnoneNext :
                    ∀ q : Nat, TapNatPrime q →
                      q < a + 1 →
                      ¬ q ∣ tapStripFactorFuel
                        x a (Nat.log2 x + 1) := by
                  intro q hq hqa hqstrip
                  by_cases hless : q < a
                  · exact hnone q hq hless
                      (Nat.dvd_trans hqstrip hstrip)
                  · have heq : q = a := by omega
                    rw [heq] at hqstrip
                    exact hfree hqstrip
                exact ih
                  (tapStripFactorFuel x a (Nat.log2 x + 1))
                  (a + 1) (by omega : 2 ≤ a + 1)
                  hpos hnoneNext
                  (Nat.dvd_trans hstrip hxdiv)
                  z htail
            · have hnotDvd : ¬ a ∣ x := by
                intro hadvd
                exact hzero (Nat.mod_eq_zero_of_dvd hadvd)
              have hnoneNext :
                  ∀ q : Nat, TapNatPrime q → q < a + 1 →
                    ¬ q ∣ x := by
                intro q hq hqa hqx
                by_cases hless : q < a
                · exact hnone q hq hless hqx
                · have heq : q = a := by omega
                  rw [heq] at hqx
                  exact hnotDvd hqx
              have htail :
                  z ∈ tapPrimeFactorsFuel x (a + 1) k := by
                simpa [tapPrimeFactorsFuel, hsmall,
                  hterminal, hzero] using hz
              exact ih x (a + 1) (by omega : 2 ≤ a + 1)
                hx hnoneNext hxdiv z htail
  exact hmain fuel m d hd hm hno hmdiv p hmem

/-- PrimitiveFieldGenerator: every member actually emitted by
the complete literal factor search is a prime divisor. -/
theorem tapPrimeFactorsSound (m p : Nat)
    (hm : 2 ≤ m)
    (hmem : p ∈ tapPrimeFactors m) :
    TapNatPrime p ∧ p ∣ m := by
  have hno :
      ∀ q : Nat, TapNatPrime q → q < 2 → ¬ q ∣ m := by
    intro q hq hlt _
    have := hq.1
    omega
  unfold tapPrimeFactors at hmem
  exact tapPrimeFactorsFuelSound m m 2 m
    (by decide : 2 ≤ 2) (by omega : 0 < m)
    hno (Nat.dvd_refl m) p hmem


/-- PrimitiveFieldGenerator: if a trial call has no remaining
smaller prime divisor, every chosen prime p dividing the
current residual and at or above d appears in the literal
remaining factor list, provided the unchanged fuel margin
M+2 <= d+fuel holds. The margin is exact at the initial
call (m,2,m) and survives every trial increment. -/
theorem tapPrimeFactorsFuelComplete
    (M m d fuel p : Nat)
    (hM : 2 ≤ M)
    (hm : 0 < m) (hmdvd : m ∣ M)
    (hd : 2 ≤ d)
    (hno : ∀ q : Nat, TapNatPrime q → q < d → ¬ q ∣ m)
    (hp : TapNatPrime p) (hpm : p ∣ m)
    (hpd : d ≤ p)
    (hmargin : M + 2 ≤ d + fuel) :
    p ∈ tapPrimeFactorsFuel m d fuel := by
  have hmain :
      ∀ k x a : Nat,
        0 < x → x ∣ M → 2 ≤ a →
        (∀ q : Nat, TapNatPrime q → q < a → ¬ q ∣ x) →
        TapNatPrime p → p ∣ x → a ≤ p →
        M + 2 ≤ a + k →
        p ∈ tapPrimeFactorsFuel x a k := by
    intro k
    induction k with
    | zero =>
        intro x a hx hxM ha hnone hprime hpx hap hmargin
        have hple := Nat.le_of_dvd hx hpx
        have hxle := Nat.le_of_dvd (by omega : 0 < M) hxM
        omega
    | succ k ih =>
        intro x a hx hxM ha hnone hprime hpx hap hmargin
        have hminor : ¬ x ≤ 1 := by
          have hple := Nat.le_of_dvd hx hpx
          omega
        have hxtwo : 2 ≤ x := by omega
        by_cases hterminal : x < a * a
        · have hresprime :=
            tapPrimeOfNoSmallDivisor
              x a hxtwo ha hterminal hnone
          have hpeq : p = x := by
            rcases hresprime.2 p hpx with hone | hsame
            · omega
            · exact hsame
          have hmember :
              p ∈ [x] := by
            simp [hpeq]
          simpa [tapPrimeFactorsFuel, hminor, hterminal]
            using hmember
        · by_cases hz : x % a = 0
          · have hadvd : a ∣ x :=
              Nat.dvd_of_mod_eq_zero hz
            have haa : a < a * a := by
              have hmul := Nat.mul_le_mul_right a ha
              omega
            have hnoA :
                ∀ q : Nat, TapNatPrime q → q < a → ¬ q ∣ a := by
              intro q hq hqlt hqa
              exact hnone q hq hqlt
                (Nat.dvd_trans hqa hadvd)
            have hprimeA :=
              tapPrimeOfNoSmallDivisor
                a a ha ha haa hnoA
            by_cases hpeq : p = a
            · have hmem : p ∈ a ::
                  tapPrimeFactorsFuel
                    (tapStripFactorFuel x a (Nat.log2 x + 1))
                    (a + 1) k := by
                simp [hpeq]
              simpa [tapPrimeFactorsFuel,
                hminor, hterminal, hz] using hmem
            · have hnotPDivA : ¬ p ∣ a := by
                intro hpA
                rcases hprimeA.2 p hpA with hone | heq
                · omega
                · exact hpeq heq
              have hstrip := tapStripFactorCompleteCore
                x a hx ha
              obtain ⟨hstripDiv, hstripPos, hstripFree⟩ :=
                hstrip
              have hpstrip :
                  p ∣ tapStripFactorFuel
                    x a (Nat.log2 x + 1) :=
                (tapStripFactorFuelPreservesPrime
                  x a (Nat.log2 x + 1) p
                  ha hprime hnotPDivA).1 hpx
              have hnoNext :
                  ∀ q : Nat, TapNatPrime q → q < a + 1 →
                    ¬ q ∣ tapStripFactorFuel
                      x a (Nat.log2 x + 1) := by
                intro q hq hqa hqstrip
                by_cases hless : q < a
                · exact hnone q hq hless
                    (Nat.dvd_trans hqstrip hstripDiv)
                · have heq : q = a := by omega
                  rw [heq] at hqstrip
                  exact hstripFree hqstrip
              have hmember :=
                ih
                  (tapStripFactorFuel x a (Nat.log2 x + 1))
                  (a + 1)
                  hstripPos
                  (Nat.dvd_trans hstripDiv hxM)
                  (by omega : 2 ≤ a + 1)
                  hnoNext hprime hpstrip
                  (by omega : a + 1 ≤ p)
                  (by omega : M + 2 ≤ a + 1 + k)
              have hbranch :
                  p ∈ a ::
                    tapPrimeFactorsFuel
                      (tapStripFactorFuel x a (Nat.log2 x + 1))
                      (a + 1) k := by
                exact List.mem_cons_of_mem a hmember
              simpa [tapPrimeFactorsFuel,
                hminor, hterminal, hz] using hbranch
          · have hnotDvd : ¬ a ∣ x := by
              intro hadvd
              exact hz (Nat.mod_eq_zero_of_dvd hadvd)
            have hneq : p ≠ a := by
              intro heq
              rw [heq] at hpx
              exact hnotDvd hpx
            have hnoNext :
                ∀ q : Nat, TapNatPrime q → q < a + 1 →
                  ¬ q ∣ x := by
              intro q hq hqa hqx
              by_cases hless : q < a
              · exact hnone q hq hless hqx
              · have heq : q = a := by omega
                rw [heq] at hqx
                exact hnotDvd hqx
            have hmember :=
              ih x (a + 1) hx hxM
                (by omega : 2 ≤ a + 1)
                hnoNext hprime hpx
                (by omega : a + 1 ≤ p)
                (by omega : M + 2 ≤ a + 1 + k)
            simpa [tapPrimeFactorsFuel,
              hminor, hterminal, hz] using hmember
  exact hmain fuel m d hm hmdvd hd hno
    hp hpm hpd hmargin

/-- PrimitiveFieldGenerator: every prime divisor of m
is reached by the exact literal trial search with its
specified fuel m; no unbounded scan is substituted. -/
theorem tapPrimeFactorsComplete (m p : Nat)
    (hm : 2 ≤ m)
    (hp : TapNatPrime p) (hpm : p ∣ m) :
    p ∈ tapPrimeFactors m := by
  have hno :
      ∀ q : Nat, TapNatPrime q → q < 2 → ¬ q ∣ m := by
    intro q hq hlt _
    have := hq.1
    omega
  unfold tapPrimeFactors
  exact tapPrimeFactorsFuelComplete m m 2 m p
    hm (by omega : 0 < m) (Nat.dvd_refl m)
    (by decide : 2 ≤ 2) hno hp hpm hp.1
    (by omega : m + 2 ≤ 2 + m)

/-- PrimitiveFieldGenerator: a proper divisor d of m misses
a prime p dividing the quotient m / d, and removing p
still leaves a multiple of d. This supplies the number-
theoretic part of tapProperDivisorFactor, independently
of the as-yet-unproved literal factor-list membership. -/
theorem tapProperDivisorComplementPrime (m d : Nat)
    (hm : 0 < m) (hdvd : d ∣ m) (hproper : d < m) :
    ∃ p : Nat, TapNatPrime p ∧ p ∣ m ∧ d ∣ m / p := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hm
  have hquotpos : 0 < m / d := by
    apply (Nat.one_le_div_iff hdpos).2
    exact Nat.le_of_dvd hm hdvd
  have hquotTwo : 2 ≤ m / d := by
    by_cases hqone : m / d = 1
    · have heq : m = d := by
        calc
          m = (m / d) * d := (Nat.div_mul_cancel hdvd).symm
          _ = d := by rw [hqone]; simp
      omega
    · omega
  obtain ⟨p, hp, hpquot⟩ :=
    tapExistsPrimeDvd (m / d) hquotTwo
  have hpdivm : p ∣ m :=
    Nat.dvd_trans hpquot (Nat.div_dvd_of_dvd hdvd)
  have hmult : d * p ∣ m :=
    (Nat.dvd_div_iff_mul_dvd hdvd).1 hpquot
  have hmult' : p * d ∣ m := by
    rw [Nat.mul_comm]
    exact hmult
  exact ⟨p, hp, hpdivm,
    (Nat.dvd_div_iff_mul_dvd hpdivm).2 hmult'⟩

/-! The exact proper-divisor factor-list membership theorem
follows below from this complement prime and from the proved
literal finite-fuel factor-list completeness theorem. -/


/-- PrimitiveFieldGenerator: for every proper positive divisor
d of m, a literal enumerated prime factor of m can be removed
without destroying the divisibility by d. -/
theorem tapProperDivisorFactor (m d : Nat)
    (hm : 0 < m) (hdvd : d ∣ m) (hproper : d < m) :
    ∃ p : Nat, p ∈ tapPrimeFactors m ∧ d ∣ m / p := by
  obtain ⟨p, hp, hpdiv, hddiv⟩ :=
    tapProperDivisorComplementPrime m d hm hdvd hproper
  have hmtwo : 2 ≤ m := by
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hm
    omega
  exact ⟨p, tapPrimeFactorsComplete m p hmtwo hp hpdiv,
    hddiv⟩

/-- PrimitiveFieldGenerator: split the complete positive
power of one specified prime from a positive integer. -/
theorem tapPrimePowerSplit (m p : Nat)
    (hm : 2 ≤ m) (hp : TapNatPrime p) (hpm : p ∣ m) :
    ∃ e r : Nat,
      1 ≤ e ∧ m = p ^ e * r ∧ ¬ p ∣ r := by
  have hp2 := hp.1
  have hmain :
      ∀ k : Nat, 0 < k → p ∣ k →
        ∃ e r : Nat,
          1 ≤ e ∧ k = p ^ e * r ∧ ¬ p ∣ r := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro hk hpk
        have hquot : 0 < k / p := by
          apply (Nat.one_le_div_iff (by omega : 0 < p)).2
          exact Nat.le_of_dvd hk hpk
        have hlt : k / p < k :=
          Nat.div_lt_self hk (by omega : 1 < p)
        by_cases hmore : p ∣ k / p
        · obtain ⟨e, r, he, hsplit, hfree⟩ :=
            ih (k / p) hlt hquot hmore
          refine ⟨e + 1, r, by omega, ?_, hfree⟩
          calc
            k = p * (k / p) := by
              rw [Nat.mul_comm]
              exact (Nat.div_mul_cancel hpk).symm
            _ = p * (p ^ e * r) := by rw [hsplit]
            _ = p ^ (e + 1) * r := by
              rw [Nat.pow_succ,
                Nat.mul_comm (p ^ e) p, Nat.mul_assoc]
        · refine ⟨1, k / p, by omega, ?_, hmore⟩
          calc
            k = p * (k / p) := by
              rw [Nat.mul_comm]
              exact (Nat.div_mul_cancel hpk).symm
            _ = p ^ 1 * (k / p) := by simp
  exact hmain m (by omega) hpm


/-- Literal product of pairwise distinct Nat prime powers.
Consumer: PrimitiveFieldGenerator, factor decomposition. -/
def tapNatPrimePowerProduct : List (Nat × Nat) → Nat
  | [] => 1
  | (p, e) :: rest => p ^ e * tapNatPrimePowerProduct rest

/-- Every listed prime power divides the product of its
literal list, using only List membership and multiplication.
Consumer: PrimitiveFieldGenerator, distinct-bases proof. -/
theorem tapNatPrimePowerMemberDivides
    (l : List (Nat × Nat)) (x : Nat × Nat)
    (hx : x ∈ l) :
    x.1 ^ x.2 ∣ tapNatPrimePowerProduct l := by
  induction l with
  | nil =>
      cases hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with hhead | htail
      · subst y
        change x.1 ^ x.2 ∣
          x.1 ^ x.2 * tapNatPrimePowerProduct ys
        exact Nat.dvd_mul_right _ _
      · change x.1 ^ x.2 ∣
          y.1 ^ y.2 * tapNatPrimePowerProduct ys
        exact Nat.dvd_mul_left_of_dvd (ih htail) _

/-- PrimitiveFieldGenerator: every positive natural number
is a product of prime powers with genuinely distinct bases.
This strong induction uses the maximal prime-power split,
not the unproved executable trial-divisor enumeration. -/
theorem tapPrimePowerList (m : Nat) (hm : 1 ≤ m) :
    ∃ l : List (Nat × Nat),
      tapNatPrimePowerProduct l = m ∧
      (∀ x : Nat × Nat, x ∈ l →
        TapNatPrime x.1 ∧ 1 ≤ x.2) ∧
      List.Pairwise (fun x y : Nat × Nat => x.1 ≠ y.1) l := by
  have hmain :
      ∀ k : Nat, 1 ≤ k →
        ∃ l : List (Nat × Nat),
          tapNatPrimePowerProduct l = k ∧
          (∀ x : Nat × Nat, x ∈ l →
            TapNatPrime x.1 ∧ 1 ≤ x.2) ∧
          List.Pairwise
            (fun x y : Nat × Nat => x.1 ≠ y.1) l := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro hk
        by_cases hone : k = 1
        · subst k
          refine ⟨[], rfl, ?_, List.Pairwise.nil⟩
          intro x hx
          cases hx
        · have hktwo : 2 ≤ k := by omega
          obtain ⟨p, hp, hpk⟩ := tapExistsPrimeDvd k hktwo
          have hp2 := hp.1
          obtain ⟨e, r, he, hsplit, hfree⟩ :=
            tapPrimePowerSplit k p hktwo hp hpk
          have hrpos : 0 < r := by
            by_cases hrzero : r = 0
            · rw [hrzero, Nat.mul_zero] at hsplit
              omega
            · omega
          have hpow : 2 ≤ p ^ e := by
            have hlt : 1 < p ^ e :=
              Nat.one_lt_pow (by omega : e ≠ 0)
                (by omega : 1 < p)
            omega
          have hrlt : r < k := by
            have hmul : 2 * r ≤ k := by
              rw [hsplit]
              exact Nat.mul_le_mul_right r hpow
            omega
          obtain ⟨l, hprod, hvalid, hpair⟩ :=
            ih r hrlt (by omega : 1 ≤ r)
          refine ⟨(p, e) :: l, ?_, ?_, ?_⟩
          · change p ^ e * tapNatPrimePowerProduct l = k
            rw [hprod]
            exact hsplit.symm
          · intro x hx
            rcases (List.mem_cons).1 hx with hhead | htail
            · subst x
              exact ⟨hp, he⟩
            · exact hvalid x htail
          · apply List.Pairwise.cons
            · intro x hx hpe
              have hxvalid := hvalid x hx
              have hxpow : x.1 ^ x.2 ∣ r := by
                rw [← hprod]
                exact tapNatPrimePowerMemberDivides l x hx
              have hpdvd : p ∣ x.1 ^ x.2 := by
                have hpe' : p = x.1 := hpe
                have hsucc : x.1 ^ x.2 = x.1 ^ (x.2 - 1) * x.1 := by
                  have hone : x.2 - 1 + 1 = x.2 := Nat.sub_add_cancel hxvalid.2
                  calc
                    x.1 ^ x.2 = x.1 ^ (x.2 - 1 + 1) := by rw [hone]
                    _ = x.1 ^ (x.2 - 1) * x.1 := Nat.pow_succ _ _
                rw [hpe', hsucc]
                exact Nat.dvd_mul_left _ _
              exact hfree (Nat.dvd_trans hpdvd hxpow)
            · exact hpair
  exact hmain m hm



/-- PrimitiveFieldGenerator: powers of distinct primes are
coprime, using the core Nat.Coprime.pow lemma. -/
theorem tapCoprimeOfDistinctPrimePowers
    (p q a b : Nat)
    (hp : TapNatPrime p) (hq : TapNatPrime q)
    (hne : p ≠ q) :
    Nat.gcd (p ^ a) (q ^ b) = 1 := by
  have hgd : Nat.gcd p q ∣ p := Nat.gcd_dvd_left p q
  have hcop : Nat.Coprime p q := by
    rcases hp.2 (Nat.gcd p q) hgd with hone | heq
    · exact hone
    · have hpq : p ∣ q := by
        rw [← heq]
        exact Nat.gcd_dvd_right p q
      rcases hq.2 p hpq with hunit | hequal
      · omega
      · exact False.elim (hne hequal)
  exact (Nat.Coprime.pow a b hcop).gcd_eq_one

/-- PrimitiveFieldGenerator: Euclid's prime divisor law,
proved from the core gcd/divisor axioms rather than imported
from Mathlib. -/
theorem tapPrimeEuclid (p a b : Nat)
    (hp : TapNatPrime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · have hcop : Nat.Coprime p a := by
      have hgd : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
      rcases hp.2 (Nat.gcd p a) hgd with hone | heq
      · exact hone
      · have hpa : p ∣ a := by
          rw [← heq]
          exact Nat.gcd_dvd_right p a
        exact False.elim (ha hpa)
    exact Or.inr (hcop.dvd_of_dvd_mul_left h)


/-- PrimitiveTapSelection: every in-range passing odd witness
survives the actual finite search fuel from an earlier odd
candidate. The result may be an earlier passing candidate. -/
theorem tapSearchWitness (t i j fuel : Nat)
    (hij : i ≤ j)
    (hbound : 1 + 2 * j < 2 ^ t)
    (hpass : passesTests t (1 + 2 * j) = true)
    (hfuel : j - i + 1 ≤ fuel) :
    (tapSearchFuel t 0 (1 + 2 * i) fuel) % 2 = 1 ∧
    tapSearchFuel t 0 (1 + 2 * i) fuel < 2 ^ t ∧
    passesTests t (tapSearchFuel t 0 (1 + 2 * i) fuel) = true := by
  induction fuel generalizing i with
  | zero =>
      omega
  | succ fuel ih =>
      have hsmall : 1 + 2 * i < 2 ^ t := by omega
      have hnotBound : ¬ 2 ^ t ≤ 1 + 2 * i := by omega
      have hnonzero : 1 + 2 * i ≠ 0 := by omega
      by_cases hcurrent : passesTests t (1 + 2 * i) = true
      · have hresult :
            tapSearchFuel t 0 (1 + 2 * i) (fuel + 1) =
              1 + 2 * i := by
          simp [tapSearchFuel, hnotBound, hnonzero, hcurrent]
        rw [hresult]
        refine ⟨?_, hsmall, hcurrent⟩
        omega
      · have hfalse : passesTests t (1 + 2 * i) = false :=
          Bool.eq_false_iff.2 hcurrent
        have hlt : i < j := by
          by_cases heq : i = j
          · rw [heq] at hcurrent
            exact False.elim (hcurrent hpass)
          · omega
        have hnext : i + 1 ≤ j := by omega
        have hnextFuel : j - (i + 1) + 1 ≤ fuel := by omega
        have hrec := ih (i + 1) hnext hnextFuel
        have hstep :
            tapSearchFuel t 0 (1 + 2 * i) (fuel + 1) =
              tapSearchFuel t 0 (1 + 2 * (i + 1)) fuel := by
          simp [tapSearchFuel, hnotBound, hnonzero, hfalse,
            Nat.mul_add, Nat.add_assoc]
        rw [hstep]
        exact hrec

/-- PrimitiveTapSelection: the literal search of all odd masks
has enough fuel to reach any passing in-range odd witness. -/
theorem tapSearchReturnsPassing (t j : Nat)
    (hbound : 1 + 2 * j < 2 ^ t)
    (hpass : passesTests t (1 + 2 * j) = true) :
    (tapSearchFuel t 0 1 (2 ^ t)) % 2 = 1 ∧
    tapSearchFuel t 0 1 (2 ^ t) < 2 ^ t ∧
    passesTests t (tapSearchFuel t 0 1 (2 ^ t)) = true := by
  have hfuel : j - 0 + 1 ≤ 2 ^ t := by omega
  simpa only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] using
    (tapSearchWitness t 0 j (2 ^ t)
      (Nat.zero_le j) hbound hpass hfuel)

end L3



#print axioms L3.tapPrimeFactorsComplete
#print axioms L3.tapPrimePowerList
#print axioms L3.tapSearchReturnsPassing
