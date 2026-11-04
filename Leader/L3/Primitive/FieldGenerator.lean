import Leader.L3.Primitive.AbstractField
import Leader.L3.Primitive.NatFactors

namespace L3.TapField

set_option autoImplicit false

open Classical

variable {F : Type}

/-- A nonzero element has exact positive multiplicative order m.
Consumer: PrimitiveFeedbackMask. -/
def HasExactOrder (K : BinaryField F) (a : F) (m : Nat) : Prop :=
  a ≠ K.zero ∧ 0 < m ∧ K.pow a m = K.one ∧
    ∀ k : Nat, 0 < k → K.pow a k = K.one → m ∣ k

/-- The exact-order predicate also governs exponent zero.
Consumer: PrimitiveFeedbackMask.generatorPowersExhaust. -/
theorem orderDividesOfPow (K : BinaryField F) (a : F) (m k : Nat)
    (ha : HasExactOrder K a m) (hk : K.pow a k = K.one) :
    m ∣ k := by
  by_cases hz : k = 0
  · subst k
    exact Nat.dvd_zero m
  · exact ha.2.2.2 k (Nat.pos_of_ne_zero hz) hk

/-- The multiplicative identity has exact order one.
Consumer: PrimitiveFeedbackMask via binaryFiniteFieldGenerator. -/
private theorem exactOrderOne (K : BinaryField F) :
    HasExactOrder K K.one 1 := by
  refine ⟨K.one_ne_zero, by omega, K.one_pow 1, ?_⟩
  intro k _ _
  exact Nat.one_dvd k

/-- The prime-power divisor dichotomy: a proper divisor of p^e
divides p^(e-1). Consumer: binaryPrimePowerRootWitness. -/
private theorem primePowerProperDivisor (p e d : Nat)
    (hp : L3.TapNatPrime p) (hd : d ∣ p ^ e)
    (hproper : d ≠ p ^ e) :
    d ∣ p ^ (e - 1) := by
  induction e generalizing d with
  | zero =>
      have hone : d = 1 := Nat.dvd_one.mp (by simpa using hd)
      exact False.elim (hproper (by simp [hone]))
  | succ e ih =>
      by_cases hpd : p ∣ d
      · obtain ⟨q, hq⟩ := hpd
        have hqdiv : q ∣ p ^ e := by
          obtain ⟨w, hw⟩ := hd
          have heq : p * p ^ e = p * (q * w) := by
            calc
              p * p ^ e = p ^ (e + 1) := by
                rw [Nat.pow_succ, Nat.mul_comm]
              _ = d * w := hw
              _ = (p * q) * w := by rw [hq]
              _ = p * (q * w) := Nat.mul_assoc _ _ _
          have hp0 : 0 < p := by
            have := hp.1
            omega
          exact ⟨w, Nat.eq_of_mul_eq_mul_left hp0 heq⟩
        by_cases hmax : q = p ^ e
        · have hdpow : d = p ^ (e + 1) := by
            calc
              d = p * q := hq
              _ = p * p ^ e := by rw [hmax]
              _ = p ^ (e + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
          exact False.elim (hproper hdpow)
        · have hqsmall := ih q hqdiv hmax
          cases e with
          | zero =>
              have hqone : q = 1 := Nat.dvd_one.mp (by simpa using hqdiv)
              have hdpow : d = p ^ (0 + 1) := by
                rw [hq, hqone]
                simp
              exact False.elim (hproper hdpow)
          | succ j =>
              change d ∣ p ^ (j + 1)
              rcases hqsmall with ⟨w, hw⟩
              refine ⟨w, ?_⟩
              calc
                p ^ (j + 1) = p * p ^ j := by
                  rw [Nat.pow_succ, Nat.mul_comm]
                _ = p * (q * w) := by
                  have hw' : p ^ j = q * w := by simpa using hw
                  rw [hw']
                _ = (p * q) * w := (Nat.mul_assoc _ _ _).symm
                _ = d * w := by rw [hq]
      · have hcop : Nat.Coprime d p := by
          have hg : Nat.gcd p d ∣ p := Nat.gcd_dvd_left p d
          rcases hp.2 (Nat.gcd p d) hg with hone | heq
          · exact (Nat.gcd_comm d p).trans hone
          · have hdivp : p ∣ d := by
              have h2 := Nat.gcd_dvd_right p d
              rw [heq] at h2
              exact h2
            exact False.elim (hpd hdivp)
        have hdiv : d ∣ p * p ^ e := by
          simpa only [Nat.pow_succ, Nat.mul_comm] using hd
        exact hcop.dvd_of_dvd_mul_left hdiv

/-- Filtering keeps a nonzero head. Consumer: nonzeroFilterIdentity. -/
private theorem nonzeroConsNe (K : BinaryField F) (x : F) (xs : List F)
    (hx : x ≠ K.zero) :
    nonzeroElems K (x :: xs) = x :: nonzeroElems K xs := by
  simp [nonzeroElems, List.filter_cons, hx]

/-- Filtering drops a zero head. Consumer: nonzeroFilterLength. -/
private theorem nonzeroConsZero (K : BinaryField F) (xs : List F) :
    nonzeroElems K (K.zero :: xs) = nonzeroElems K xs := by
  simp [nonzeroElems, List.filter_cons]

/-- Removing zero from a list with no zero leaves the list unchanged.
Consumer: binaryPrimePowerRootWitness and generatorPowersExhaust. -/
private theorem nonzeroFilterIdentity (K : BinaryField F) :
    ∀ l : List F, K.zero ∉ l → nonzeroElems K l = l := by
  intro l
  induction l with
  | nil =>
      intro _
      rfl
  | cons a as ih =>
      intro h
      have ha : a ≠ K.zero := by
        intro heq
        exact h (by simp [heq])
      have ht : K.zero ∉ as := by
        intro hm
        exact h (by simp [hm])
      rw [nonzeroConsNe K a as ha, ih ht]

/-- The nonzero enumeration has one fewer entry.
Consumer: binaryPrimePowerRootWitness and generatorPowersExhaust. -/
private theorem nonzeroFilterLength (K : BinaryField F) :
    ∀ l : List F, l.Nodup → K.zero ∈ l →
      (nonzeroElems K l).length + 1 = l.length := by
  intro l
  induction l with
  | nil =>
      intro _ hm
      cases hm
  | cons a as ih =>
      intro hn hm
      have hpair := List.nodup_cons.mp hn
      by_cases ha : a = K.zero
      · subst a
        have htail := nonzeroFilterIdentity K as hpair.1
        rw [nonzeroConsZero, htail]
        rfl
      · have hmTail : K.zero ∈ as := by
          rcases List.mem_cons.mp hm with hmHead | hmRest
          · exact False.elim (ha hmHead.symm)
          · exact hmRest
        have hlen := ih hpair.2 hmTail
        rw [nonzeroConsNe K a as ha]
        simp only [List.length_cons]
        omega

/-- Exactly the nonzero elements belong to this filtered enumeration.
Consumer: binaryPrimePowerRootWitness and generatorPowersExhaust. -/
private theorem memNonzeroElems (K : BinaryField F) (E : Enumeration F)
    (a : F) : a ∈ nonzeroElems K E.elems ↔ a ≠ K.zero := by
  simp [nonzeroElems, E.complete a]

/-- A filtered enumeration remains duplicate-free.
Consumer: binaryPrimePowerRootWitness and generatorPowersExhaust. -/
private theorem nonzeroElemsNodup (K : BinaryField F)
    (E : Enumeration F) :
    (nonzeroElems K E.elems).Nodup :=
  E.nodup.filter _

/-- Field size one less than the full enumeration counts nonzero
elements exactly. Consumer: binaryPrimePowerRootWitness. -/
private theorem nonzeroElemsCard (K : BinaryField F)
    (E : Enumeration F) :
    (nonzeroElems K E.elems).length = E.elems.length - 1 := by
  have hh := nonzeroFilterLength K E.elems E.nodup (E.complete K.zero)
  omega

/-- A highest prime power of the field-unit count occurs as the exact
order of some element. Consumer: PrimitiveFeedbackMask. -/
theorem binaryPrimePowerRootWitness (K : BinaryField F)
    (E : Enumeration F) (p e r : Nat)
    (hM : 1 ≤ E.elems.length - 1)
    (hp : L3.TapNatPrime p) (he : 1 ≤ e)
    (hfactor : E.elems.length - 1 = p ^ e * r)
    (hfree : ¬ p ∣ r) :
    ∃ c : F, HasExactOrder K c (p ^ e) := by
  have hrpos : 0 < r := by
    by_cases hz : r = 0
    · rw [hz, Nat.mul_zero] at hfactor
      omega
    · omega
  have hp2 : 2 ≤ p := hp.1
  have hpPos : 0 < p := by omega
  have hPowPos : 0 < p ^ (e - 1) := Nat.pow_pos hpPos
  have hDPos : 0 < p ^ (e - 1) * r :=
    Nat.mul_pos hPowPos hrpos
  have heSucc : e - 1 + 1 = e := Nat.sub_add_cancel he
  have hMdecomp : E.elems.length - 1 =
      p * (p ^ (e - 1) * r) := by
    calc
      E.elems.length - 1 = p ^ e * r := hfactor
      _ = (p ^ (e - 1) * p) * r := by
        have hpe : p ^ e = p ^ (e - 1) * p :=
          calc
            p ^ e = p ^ (e - 1 + 1) := by rw [heSucc]
            _ = p ^ (e - 1) * p := Nat.pow_succ _ _
        rw [hpe]
      _ = p * (p ^ (e - 1) * r) := by
        rw [Nat.mul_comm (p ^ (e - 1)) p, Nat.mul_assoc]
  have hDlt : p ^ (e - 1) * r < E.elems.length - 1 := by
    have hmul : 1 * (p ^ (e - 1) * r) <
        p * (p ^ (e - 1) * r) :=
      Nat.mul_lt_mul_of_pos_right (by omega : 1 < p) hDPos
    rw [hMdecomp]
    omega
  have hWitness : ∃ a : F,
      a ∈ nonzeroElems K E.elems ∧
        K.pow a (p ^ (e - 1) * r) ≠ K.one := by
    by_cases hex : ∃ a : F,
        a ∈ nonzeroElems K E.elems ∧
          K.pow a (p ^ (e - 1) * r) ≠ K.one
    · exact hex
    · have hall : ∀ a : F, a ∈ nonzeroElems K E.elems →
          K.pow a (p ^ (e - 1) * r) = K.one := by
        intro a ha
        by_cases hpow : K.pow a (p ^ (e - 1) * r) = K.one
        · exact hpow
        · exact False.elim (hex ⟨a, ha, hpow⟩)
      have hb := rootBoundPowOne K (p ^ (e - 1) * r)
        hDPos (nonzeroElems K E.elems)
        (nonzeroElemsNodup K E) hall
      rw [nonzeroElemsCard K E] at hb
      exact False.elim (Nat.not_lt_of_ge hb hDlt)
  obtain ⟨a, haList, haD⟩ := hWitness
  have ha : a ≠ K.zero := (memNonzeroElems K E a).1 haList
  have hFull : K.pow (K.pow a r) (p ^ e) = K.one := by
    calc
      K.pow (K.pow a r) (p ^ e) =
          K.pow a (r * p ^ e) := (K.pow_mul a r (p ^ e)).symm
      _ = K.pow a (E.elems.length - 1) := by
        rw [Nat.mul_comm r (p ^ e), ← hfactor]
      _ = K.one := binaryFiniteFieldFermat K E a ha
  have hEarlier : K.pow (K.pow a r) (p ^ (e - 1)) ≠ K.one := by
    intro hz
    apply haD
    calc
      K.pow a (p ^ (e - 1) * r) =
          K.pow a (r * p ^ (e - 1)) := by
        rw [Nat.mul_comm]
      _ = K.pow (K.pow a r) (p ^ (e - 1)) :=
        K.pow_mul a r (p ^ (e - 1))
      _ = K.one := hz
  have hc : K.pow a r ≠ K.zero := K.pow_ne_zero a ha r
  refine ⟨K.pow a r, hc, Nat.pow_pos hpPos, hFull, ?_⟩
  intro k _ hk
  have hGcd : K.pow (K.pow a r) (Nat.gcd k (p ^ e)) = K.one :=
    unitPeriodGcd K (K.pow a r) hc k (p ^ e) hk hFull
  by_cases heq : Nat.gcd k (p ^ e) = p ^ e
  · rw [← heq]
    exact Nat.gcd_dvd_left k (p ^ e)
  · have hd : Nat.gcd k (p ^ e) ∣ p ^ e :=
      Nat.gcd_dvd_right k (p ^ e)
    have hsmall : Nat.gcd k (p ^ e) ∣ p ^ (e - 1) :=
      primePowerProperDivisor p e (Nat.gcd k (p ^ e)) hp hd heq
    obtain ⟨j, hj⟩ := hsmall
    have hBad : K.pow (K.pow a r) (p ^ (e - 1)) = K.one := by
      calc
        K.pow (K.pow a r) (p ^ (e - 1)) =
            K.pow (K.pow a r) (Nat.gcd k (p ^ e) * j) := by
          rw [hj]
        _ = K.pow (K.pow (K.pow a r) (Nat.gcd k (p ^ e))) j :=
          K.pow_mul (K.pow a r) (Nat.gcd k (p ^ e)) j
        _ = K.pow K.one j := by rw [hGcd]
        _ = K.one := K.one_pow j
    exact False.elim (hEarlier hBad)

/-- The product of two commuting elements of coprime exact orders
has exact order the product. Consumer: PrimitiveFeedbackMask. -/
theorem binaryCoprimePeriodProduct (K : BinaryField F)
    (a b : F) (m n' : Nat)
    (ha : HasExactOrder K a m)
    (hb : HasExactOrder K b n')
    (hcop : Nat.gcd m n' = 1) :
    HasExactOrder K (K.mul a b) (m * n') := by
  have hnz : K.mul a b ≠ K.zero := by
    intro hzero
    rcases K.mul_eq_zero a b hzero with hza | hzb
    · exact ha.1 hza
    · exact hb.1 hzb
  have hPos : 0 < m * n' := Nat.mul_pos ha.2.1 hb.2.1
  have haFull : K.pow a (m * n') = K.one := by
    rw [K.pow_mul, ha.2.2.1, K.one_pow]
  have hbFull : K.pow b (m * n') = K.one := by
    rw [Nat.mul_comm m n', K.pow_mul, hb.2.2.1, K.one_pow]
  have hFull : K.pow (K.mul a b) (m * n') = K.one := by
    rw [K.mul_pow, haFull, hbFull, K.one_mul]
  refine ⟨hnz, hPos, hFull, ?_⟩
  intro k hkPos hk
  have hProdMulM : K.pow (K.mul a b) (m * k) = K.one := by
    calc
      K.pow (K.mul a b) (m * k) =
          K.pow (K.mul a b) (k * m) := by rw [Nat.mul_comm m k]
      _ = K.pow (K.pow (K.mul a b) k) m :=
        K.pow_mul (K.mul a b) k m
      _ = K.pow K.one m := by rw [hk]
      _ = K.one := K.one_pow m
  have haMulM : K.pow a (m * k) = K.one := by
    rw [K.pow_mul, ha.2.2.1, K.one_pow]
  have hbMulM : K.pow b (m * k) = K.one := by
    have h : K.mul K.one (K.pow b (m * k)) = K.one := by
      calc
        K.mul K.one (K.pow b (m * k)) =
            K.mul (K.pow a (m * k)) (K.pow b (m * k)) := by
          rw [haMulM]
        _ = K.pow (K.mul a b) (m * k) :=
          (K.mul_pow a b (m * k)).symm
        _ = K.one := hProdMulM
    exact (K.one_mul _).symm.trans h
  have hNMul : n' ∣ m * k :=
    hb.2.2.2 (m * k) (Nat.mul_pos ha.2.1 hkPos) hbMulM
  have hCopNM : Nat.Coprime n' m := by
    change Nat.gcd n' m = 1
    rw [Nat.gcd_comm]
    exact hcop
  have hN : n' ∣ k := hCopNM.dvd_of_dvd_mul_left hNMul
  have hProdMulN : K.pow (K.mul a b) (n' * k) = K.one := by
    calc
      K.pow (K.mul a b) (n' * k) =
          K.pow (K.mul a b) (k * n') := by rw [Nat.mul_comm n' k]
      _ = K.pow (K.pow (K.mul a b) k) n' :=
        K.pow_mul (K.mul a b) k n'
      _ = K.pow K.one n' := by rw [hk]
      _ = K.one := K.one_pow n'
  have hbMulN : K.pow b (n' * k) = K.one := by
    rw [K.pow_mul, hb.2.2.1, K.one_pow]
  have haMulN : K.pow a (n' * k) = K.one := by
    have h : K.mul (K.pow a (n' * k)) K.one = K.one := by
      calc
        K.mul (K.pow a (n' * k)) K.one =
            K.mul (K.pow a (n' * k)) (K.pow b (n' * k)) := by
          rw [hbMulN]
        _ = K.pow (K.mul a b) (n' * k) :=
          (K.mul_pow a b (n' * k)).symm
        _ = K.one := hProdMulN
    exact (K.mul_one _).symm.trans h
  have hMMul : m ∣ n' * k :=
    ha.2.2.2 (n' * k) (Nat.mul_pos hb.2.1 hkPos) haMulN
  have hCopMN : Nat.Coprime m n' := hcop
  have hM : m ∣ k := hCopMN.dvd_of_dvd_mul_left hMMul
  exact hCopMN.mul_dvd_of_dvd_of_dvd hM hN

#print axioms binaryPrimePowerRootWitness
#print axioms binaryCoprimePeriodProduct

/-- A prime does not divide a power of a different prime.
Consumer: binaryFiniteFieldGenerator and PrimitiveFeedbackMask. -/
private theorem primeNotDividesDistinctPower (p q e : Nat)
    (hp : L3.TapNatPrime p) (hq : L3.TapNatPrime q)
    (hne : p ≠ q) :
    ¬ p ∣ q ^ e := by
  have hcop : Nat.Coprime p (q ^ e) := by
    have hpair := L3.tapCoprimeOfDistinctPrimePowers p q 1 e hp hq hne
    simpa only [Nat.pow_one] using hpair
  intro hd
  have hprod : p ∣ (q ^ e) * 1 := by simpa using hd
  have hone : p ∣ 1 := hcop.dvd_of_dvd_mul_left hprod
  have hpone := Nat.dvd_one.mp hone
  have hp2 := hp.1
  omega

/-- A fresh prime base cannot divide a product of other prime powers.
Consumer: binaryFiniteFieldGenerator. -/
private theorem primeNotDividesListProduct (p : Nat)
    (hp : L3.TapNatPrime p) :
    ∀ l : List (Nat × Nat),
      (∀ x : Nat × Nat, x ∈ l →
        L3.TapNatPrime x.1 ∧ 1 ≤ x.2) →
      (∀ x : Nat × Nat, x ∈ l → p ≠ x.1) →
      ¬ p ∣ L3.tapNatPrimePowerProduct l := by
  intro l
  induction l with
  | nil =>
      intro _ _ h
      have hone : p ∣ 1 := by
        simpa [L3.tapNatPrimePowerProduct] using h
      have hpone := Nat.dvd_one.mp hone
      have hp2 := hp.1
      omega
  | cons x xs ih =>
      intro hvalid hdiff h
      have hheadValid : L3.TapNatPrime x.1 ∧ 1 ≤ x.2 :=
        hvalid x (by simp)
      have hheadDiff : p ≠ x.1 := hdiff x (by simp)
      have htailValid : ∀ z : Nat × Nat, z ∈ xs →
          L3.TapNatPrime z.1 ∧ 1 ≤ z.2 := by
        intro z hz
        exact hvalid z (List.mem_cons_of_mem x hz)
      have htailDiff : ∀ z : Nat × Nat, z ∈ xs → p ≠ z.1 := by
        intro z hz
        exact hdiff z (List.mem_cons_of_mem x hz)
      have hprod : p ∣ x.1 ^ x.2 *
          L3.tapNatPrimePowerProduct xs := h
      rcases L3.tapPrimeEuclid p (x.1 ^ x.2)
          (L3.tapNatPrimePowerProduct xs) hp hprod with hfirst | hrest
      · exact primeNotDividesDistinctPower p x.1 x.2
          hp hheadValid.1 hheadDiff hfirst
      · exact ih htailValid htailDiff hrest

/-- The prime power at a list head is coprime to all later factors.
Consumer: binaryFiniteFieldGenerator. -/
private theorem primePowerCoprimeTail (p e : Nat)
    (hp : L3.TapNatPrime p) (l : List (Nat × Nat))
    (hvalid : ∀ x : Nat × Nat, x ∈ l →
      L3.TapNatPrime x.1 ∧ 1 ≤ x.2)
    (hdiff : ∀ x : Nat × Nat, x ∈ l → p ≠ x.1) :
    Nat.gcd (p ^ e) (L3.tapNatPrimePowerProduct l) = 1 := by
  have hnot : ¬ p ∣ L3.tapNatPrimePowerProduct l :=
    primeNotDividesListProduct p hp l hvalid hdiff
  have hcop : Nat.Coprime p (L3.tapNatPrimePowerProduct l) := by
    have hd : Nat.gcd p (L3.tapNatPrimePowerProduct l) ∣ p :=
      Nat.gcd_dvd_left _ _
    rcases hp.2 _ hd with hone | heq
    · exact hone
    · have hpd : p ∣ L3.tapNatPrimePowerProduct l := by
        rw [← heq]
        exact Nat.gcd_dvd_right _ _
      exact False.elim (hnot hpd)
  have hpow := Nat.Coprime.pow e 1 hcop
  simpa only [Nat.pow_one] using hpow

/-- Every prime-power member of a pairwise-distinct prime-power
list is a maximal power of its prime in the entire product.
Consumer: binaryFiniteFieldGenerator. -/
private theorem primePowerMemberExact :
    ∀ l : List (Nat × Nat),
      (∀ x : Nat × Nat, x ∈ l →
        L3.TapNatPrime x.1 ∧ 1 ≤ x.2) →
      List.Pairwise (fun x y : Nat × Nat => x.1 ≠ y.1) l →
      ∀ x : Nat × Nat, x ∈ l →
        ∃ r : Nat,
          L3.tapNatPrimePowerProduct l = x.1 ^ x.2 * r ∧
          ¬ x.1 ∣ r := by
  intro l
  induction l with
  | nil =>
      intro _ _ x hx
      cases hx
  | cons y ys ih =>
      intro hvalid hpair x hx
      have hyValid : L3.TapNatPrime y.1 ∧ 1 ≤ y.2 :=
        hvalid y (by simp)
      have htailValid : ∀ z : Nat × Nat, z ∈ ys →
          L3.TapNatPrime z.1 ∧ 1 ≤ z.2 := by
        intro z hz
        exact hvalid z (List.mem_cons_of_mem y hz)
      have htailPair :
          List.Pairwise (fun a b : Nat × Nat => a.1 ≠ b.1) ys :=
        (List.pairwise_cons.mp hpair).2
      have hdiff : ∀ z : Nat × Nat, z ∈ ys → y.1 ≠ z.1 :=
        (List.pairwise_cons.mp hpair).1
      rcases List.mem_cons.mp hx with heq | htail
      · subst x
        refine ⟨L3.tapNatPrimePowerProduct ys, rfl, ?_⟩
        exact primeNotDividesListProduct y.1 hyValid.1 ys
          htailValid hdiff
      · obtain ⟨r, hprod, hfree⟩ :=
          ih htailValid htailPair x htail
        refine ⟨y.1 ^ y.2 * r, ?_, ?_⟩
        · change y.1 ^ y.2 * L3.tapNatPrimePowerProduct ys =
            x.1 ^ x.2 * (y.1 ^ y.2 * r)
          rw [hprod, ← Nat.mul_assoc,
            Nat.mul_comm (y.1 ^ y.2) (x.1 ^ x.2), Nat.mul_assoc]
        · intro hd
          have hxValid : L3.TapNatPrime x.1 ∧ 1 ≤ x.2 :=
            htailValid x htail
          rcases L3.tapPrimeEuclid x.1 (y.1 ^ y.2) r
              hxValid.1 hd with hy | hr
          · have hne : x.1 ≠ y.1 :=
              Ne.symm (hdiff x htail)
            exact primeNotDividesDistinctPower x.1 y.1 y.2
              hxValid.1 hyValid.1 hne hy
          · exact hfree hr

/-- Build a generator for a sublist, while every selected prime
power is maximal in the fixed full unit count.
Consumer: binaryFiniteFieldGenerator. -/
private theorem generatorOfPrimePowerList (K : BinaryField F)
    (E : Enumeration F)
    (hM : 1 ≤ E.elems.length - 1) :
    ∀ l : List (Nat × Nat),
      (∀ x : Nat × Nat, x ∈ l →
        L3.TapNatPrime x.1 ∧ 1 ≤ x.2) →
      (∀ x : Nat × Nat, x ∈ l →
        ∃ r : Nat,
          E.elems.length - 1 = x.1 ^ x.2 * r ∧
          ¬ x.1 ∣ r) →
      List.Pairwise (fun x y : Nat × Nat => x.1 ≠ y.1) l →
      ∃ g : F,
        HasExactOrder K g (L3.tapNatPrimePowerProduct l) := by
  intro l
  induction l with
  | nil =>
      intro _ _ _
      exact ⟨K.one, exactOrderOne K⟩
  | cons x xs ih =>
      intro hvalid hcomponents hpair
      have hheadValid : L3.TapNatPrime x.1 ∧ 1 ≤ x.2 :=
        hvalid x (by simp)
      obtain ⟨r, hfactor, hfree⟩ := hcomponents x (by simp)
      obtain ⟨a, ha⟩ := binaryPrimePowerRootWitness K E
        x.1 x.2 r hM hheadValid.1 hheadValid.2 hfactor hfree
      have htailValid : ∀ y : Nat × Nat, y ∈ xs →
          L3.TapNatPrime y.1 ∧ 1 ≤ y.2 := by
        intro y hy
        exact hvalid y (List.mem_cons_of_mem x hy)
      have htailComponents : ∀ y : Nat × Nat, y ∈ xs →
          ∃ r : Nat,
            E.elems.length - 1 = y.1 ^ y.2 * r ∧
            ¬ y.1 ∣ r := by
        intro y hy
        exact hcomponents y (List.mem_cons_of_mem x hy)
      have htailPair :
          List.Pairwise (fun y z : Nat × Nat => y.1 ≠ z.1) xs :=
        (List.pairwise_cons.mp hpair).2
      have hdiff : ∀ y : Nat × Nat, y ∈ xs → x.1 ≠ y.1 :=
        (List.pairwise_cons.mp hpair).1
      obtain ⟨b, hb⟩ := ih htailValid htailComponents htailPair
      have hcop : Nat.gcd (x.1 ^ x.2)
          (L3.tapNatPrimePowerProduct xs) = 1 :=
        primePowerCoprimeTail x.1 x.2 hheadValid.1 xs
          htailValid hdiff
      refine ⟨K.mul a b, ?_⟩
      change HasExactOrder K (K.mul a b)
        (x.1 ^ x.2 * L3.tapNatPrimePowerProduct xs)
      exact binaryCoprimePeriodProduct K a b
        (x.1 ^ x.2) (L3.tapNatPrimePowerProduct xs) ha hb hcop

/-- Every finite field has an element of exact order the total
number of nonzero elements. Consumer: PrimitiveFeedbackMask. -/
theorem binaryFiniteFieldGenerator (K : BinaryField F)
    (E : Enumeration F)
    (hM : 1 ≤ E.elems.length - 1) :
    ∃ g : F, HasExactOrder K g (E.elems.length - 1) := by
  obtain ⟨l, hprod, hvalid, hpair⟩ :=
    L3.tapPrimePowerList (E.elems.length - 1) hM
  have hcomponents : ∀ x : Nat × Nat, x ∈ l →
      ∃ r : Nat,
        E.elems.length - 1 = x.1 ^ x.2 * r ∧
        ¬ x.1 ∣ r := by
    intro x hx
    obtain ⟨r, hr, hfree⟩ := primePowerMemberExact l
      hvalid hpair x hx
    exact ⟨r, hprod ▸ hr, hfree⟩
  obtain ⟨g, hg⟩ :=
    generatorOfPrimePowerList K E hM l hvalid hcomponents hpair
  exact ⟨g, by rw [← hprod]; exact hg⟩

#print axioms binaryFiniteFieldGenerator

/-- Two unequal bounded exponents have distinct powers of an
exact-order element. Consumer: generatorPowersExhaust. -/
private theorem powersDistinctStrict (K : BinaryField F)
    (g : F) (m i j : Nat)
    (hg : HasExactOrder K g m)
    (hij : i < j) (hj : j < m) :
    K.pow g i ≠ K.pow g j := by
  intro heq
  have hdecomp : j = i + (j - i) := by omega
  have hcancel : K.mul (K.pow g i) K.one =
      K.mul (K.pow g i) (K.pow g (j - i)) := by
    calc
      K.mul (K.pow g i) K.one = K.pow g i := K.mul_one _
      _ = K.pow g j := heq
      _ = K.pow g (i + (j - i)) := congrArg (K.pow g) hdecomp
      _ = K.mul (K.pow g i) (K.pow g (j - i)) :=
        K.pow_add g i (j - i)
  have hgap : K.pow g (j - i) = K.one :=
    K.mul_left_cancel (K.pow g i) _ _
      (K.pow_ne_zero g hg.1 i) hcancel.symm
  have hdiv : m ∣ j - i := orderDividesOfPow K g m (j - i) hg hgap
  have hle : m ≤ j - i := Nat.le_of_dvd (by omega : 0 < j - i) hdiv
  omega

/-- The power map is injective on the range below the exact order.
Consumer: generatorPowersExhaust. -/
private theorem powersInjectiveBelow (K : BinaryField F)
    (g : F) (m i j : Nat) (hg : HasExactOrder K g m)
    (hi : i < m) (hj : j < m)
    (heq : K.pow g i = K.pow g j) : i = j := by
  by_cases hij : i < j
  · exact False.elim (powersDistinctStrict K g m i j hg hij hj heq)
  · by_cases hji : j < i
    · exact False.elim
        (powersDistinctStrict K g m j i hg hji hi heq.symm)
    · omega

/-- Mapping distinct bounded exponents to powers is injective.
Consumer: generatorPowersExhaust. -/
private theorem powersMapNodup (K : BinaryField F)
    (g : F) (m : Nat) (hg : HasExactOrder K g m) :
    ∀ l : List Nat, l.Nodup →
      (∀ i, i ∈ l → i < m) →
      (l.map (fun i => K.pow g i)).Nodup := by
  intro l
  induction l with
  | nil =>
      intro _ _
      exact List.nodup_nil
  | cons i is ih =>
      intro hn hrange
      have hi : i < m := hrange i (by simp)
      have his : i ∉ is := (List.nodup_cons.mp hn).1
      have hNoTail : is.Nodup := (List.nodup_cons.mp hn).2
      have hRangeTail : ∀ j, j ∈ is → j < m := by
        intro j hj
        exact hrange j (List.mem_cons_of_mem i hj)
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨j, hj, hpow⟩ := List.mem_map.mp hmem
        have hij : i = j := powersInjectiveBelow K g m i j hg
          hi (hRangeTail j hj) hpow.symm
        exact his (hij ▸ hj)
      · exact ih hNoTail hRangeTail

/-- Find a member at a specific position for an elementary
Nodup-subset cardinality proof. Consumer: generatorPowersExhaust. -/
private theorem splitAtMember {a : F} {ys : List F}
    (ha : a ∈ ys) :
    ∃ pre post : List F, ys = pre ++ a :: post := by
  induction ys with
  | nil =>
      cases ha
  | cons y ys ih =>
      rcases List.mem_cons.mp ha with hy | htail
      · subst y
        exact ⟨[], ys, rfl⟩
      · obtain ⟨pre, post, heq⟩ := ih htail
        exact ⟨y :: pre, post, by rw [heq]; rfl⟩

/-- A duplicate-free sublist-by-membership has no more elements
than the containing list. Consumer: generatorPowersExhaust. -/
private theorem nodupSubsetLength :
    ∀ (xs ys : List F), xs.Nodup →
      (∀ a : F, a ∈ xs → a ∈ ys) →
      xs.length ≤ ys.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _
      exact Nat.zero_le _
  | cons a xs ih =>
      intro ys hn hsubset
      have ha : a ∈ ys := hsubset a (by simp)
      obtain ⟨pre, post, heq⟩ := splitAtMember ha
      have hnot : a ∉ xs := (List.nodup_cons.mp hn).1
      have htailSubset : ∀ z : F, z ∈ xs → z ∈ pre ++ post := by
        intro z hz
        have hzy : z ∈ pre ++ a :: post := by
          rw [← heq]
          exact hsubset z (List.mem_cons_of_mem a hz)
        have hzne : z ≠ a := by
          intro heqza
          exact hnot (heqza ▸ hz)
        rcases List.mem_append.mp hzy with hp | ht
        · exact List.mem_append.mpr (Or.inl hp)
        · rcases List.mem_cons.mp ht with hhead | hpost
          · exact False.elim (hzne hhead)
          · exact List.mem_append.mpr (Or.inr hpost)
      have hlen := ih (pre ++ post) (List.nodup_cons.mp hn).2 htailSubset
      rw [heq]
      simp only [List.length_cons, List.length_append] at hlen ⊢
      omega

/-- Powers of a generator exhaust every nonzero field element.
Consumer: PrimitiveFeedbackMask. -/
theorem generatorPowersExhaust (K : BinaryField F) (E : Enumeration F)
    (g : F) (hg : HasExactOrder K g (E.elems.length - 1))
    (a : F) (ha : a ≠ K.zero) :
    ∃ i : Nat, i < E.elems.length - 1 ∧ K.pow g i = a := by
  have hRange : ∀ i : Nat, i ∈ List.range (E.elems.length - 1) →
      i < E.elems.length - 1 := by
    intro i hi
    exact List.mem_range.mp hi
  have hNo : (List.range (E.elems.length - 1)).Nodup :=
    List.nodup_range
  have hPowersNo :
      ((List.range (E.elems.length - 1)).map
        (fun i => K.pow g i)).Nodup :=
    powersMapNodup K g (E.elems.length - 1) hg
      _ hNo hRange
  have hPowersSubset : ∀ z : F,
      z ∈ (List.range (E.elems.length - 1)).map
        (fun i => K.pow g i) →
      z ∈ nonzeroElems K E.elems := by
    intro z hz
    obtain ⟨i, hi, hpow⟩ := List.mem_map.mp hz
    have hzNe : z ≠ K.zero := by
      intro hzero
      have hbad : K.pow g i = K.zero := hpow.trans hzero
      exact (K.pow_ne_zero g hg.1 i) hbad
    exact (memNonzeroElems K E z).2 hzNe
  by_cases hmem : a ∈ (List.range (E.elems.length - 1)).map
      (fun i => K.pow g i)
  · obtain ⟨i, hi, heq⟩ := List.mem_map.mp hmem
    exact ⟨i, List.mem_range.mp hi, heq⟩
  · have hBigNo :
        (a :: (List.range (E.elems.length - 1)).map
          (fun i => K.pow g i)).Nodup :=
      List.nodup_cons.mpr ⟨hmem, hPowersNo⟩
    have hBigSubset : ∀ z : F,
        z ∈ a :: (List.range (E.elems.length - 1)).map
          (fun i => K.pow g i) →
        z ∈ nonzeroElems K E.elems := by
      intro z hz
      rcases List.mem_cons.mp hz with heq | ht
      · rw [heq]
        exact (memNonzeroElems K E a).2 ha
      · exact hPowersSubset z ht
    have hbound :=
      nodupSubsetLength
        (a :: (List.range (E.elems.length - 1)).map
          (fun i => K.pow g i))
        (nonzeroElems K E.elems) hBigNo hBigSubset
    have hlen := nonzeroElemsCard K E
    simp only [List.length_cons, List.length_map, List.length_range] at hbound
    omega

#print axioms generatorPowersExhaust

end L3.TapField
