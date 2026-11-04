import Leader.L3.Bank.RepairDigitFinalSites

/-!
# T18: the final rank on the projected ring

* `bankRepairDigitFinalRankStep`: no edge raises the final rank;
* `bankRepairDigitFinalRankDrop`: if some lane fails the final receipt, some edge drops it;
* `bankRepairDigitLastDelimFacts`: the closed-form last delimiter;
* `bankRepairDigitFinalBudget`: the size bound against `F + R + U + r`.
-/

namespace L3.RenewalReferenceClock

set_option autoImplicit false

section Ring

variable {c : Compiled} {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
  (S : Fin n → ProjD c) (R L : Nat) (hR : 2 ≤ R) (hRL : R + 2 ≤ L) (hLn : L < n)
  (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
  (hbS : (S (digitSite ring root (L - R))).word.beta = true)
  (hbL : (S (digitSite ring root L)).word.beta = true)
  (hbF : ∀ k, L - R < k → k < n → k ≠ L → (S (digitSite ring root k)).word.beta = false)
  (hbXY : ∀ k, k < n →
    (pairW (S (digitSite ring root k)).word (S (digitSite ring root (k + 1))).word).1.beta =
      (S (digitSite ring root k)).word.beta ∧
    (pairW (S (digitSite ring root k)).word (S (digitSite ring root (k + 1))).word).2.beta =
      (S (digitSite ring root (k + 1))).word.beta)

include hn hR hRL hLn hroot hbS hbL hbF hbXY in
theorem bankRepairDigitFinalLaneStepAll (lane : DigitLane) (k : Nat) (hk : k < n) :
    bankRepairDigitFinalLaneRankOf ring root R L lane (phiD ring S (digitSite ring root k)) ≤
      bankRepairDigitFinalLaneRankOf ring root R L lane S := by
  obtain ⟨hbX, hbY⟩ := hbXY k hk
  by_cases h1 : k + 1 < L - R
  · exact Nat.le_of_eq (bankRepairDigitFinalLaneFar ring hn root S R L hLn lane k h1 hbX hbY)
  by_cases h2 : k + 1 = L - R
  · exact Nat.le_of_eq (bankRepairDigitFinalLaneEntry ring hn root S R L hR hRL hLn hroot hbS
      lane k h2 hbX hbY)
  by_cases h3 : k + 1 < L
  · obtain ⟨i, rfl⟩ : ∃ i, k = L - R + i := ⟨k - (L - R), by omega⟩
    exact Nat.le_trans (Nat.le_add_right _ _)
      (bankRepairDigitFinalLanePipe ring hn root S R L hR hRL hLn hroot hbS hbF lane i
        (by omega) hbX hbY)
  by_cases h4 : k + 1 = L
  · exact Nat.le_trans (Nat.le_add_right _ _)
      (bankRepairDigitFinalLaneDel ring hn root S R L hR hRL hLn hroot hbL hbF lane k h4 hbX hbY)
  by_cases h5 : k + 1 < n
  · obtain ⟨j, rfl⟩ : ∃ j, k = L + j := ⟨k - L, by omega⟩
    exact Nat.le_trans (Nat.le_add_right _ _)
      (bankRepairDigitFinalLaneFin ring hn root S R L hRL hroot hbL hbF lane j h5 hbX hbY)
  · exact Nat.le_trans (Nat.le_add_right _ _)
      (bankRepairDigitFinalLaneReset ring hn root S R L hRL hLn hroot lane k (by omega)
        (by omega) hbX hbY)

include hn hR hRL hLn hroot hbS hbL hbF hbXY in
/-- No edge raises the final rank. -/
theorem bankRepairDigitFinalRankStep (k : Nat) (hk : k < n) :
    bankRepairDigitFinalRankOf ring root R L (phiD ring S (digitSite ring root k)) ≤
      bankRepairDigitFinalRankOf ring root R L S := by
  unfold bankRepairDigitFinalRankOf
  exact Nat.add_le_add
    (bankRepairDigitFinalLaneStepAll ring hn root S R L hR hRL hLn hroot hbS hbL hbF hbXY
      .writer k hk)
    (bankRepairDigitFinalLaneStepAll ring hn root S R L hR hRL hLn hroot hbS hbL hbF hbXY
      .comparison k hk)

include hn hR hRL hLn hroot hbS hbL hbF hbXY in
/-- If one lane fails the final receipt at offset `L + j0`, some edge drops the final rank. -/
theorem bankRepairDigitFinalRankDrop (lane0 : DigitLane) (j0 : Nat) (hj0 : j0 < n - L)
    (hbad : ¬ bankRepairDigitFinOKSh (n - L) j0 (bankRepairDigitInL ring root lane0 S L j0)
      (bankRepairDigitLvL ring root lane0 S L j0)) :
    ∃ k, k < n ∧
      bankRepairDigitFinalRankOf ring root R L (phiD ring S (digitSite ring root k)) + 1 ≤
        bankRepairDigitFinalRankOf ring root R L S := by
  have hlane : ∃ k, k < n ∧
      bankRepairDigitFinalLaneRankOf ring root R L lane0 (phiD ring S (digitSite ring root k)) +
        1 ≤ bankRepairDigitFinalLaneRankOf ring root R L lane0 S := by
    rcases bankRepairDigitLaneProgress (n - L) (by omega) (bankRepairDigitInL ring root lane0 S L)
        (bankRepairDigitLvL ring root lane0 S L) ⟨j0, hj0, hbad⟩ with
      ⟨j, hj, hact⟩ | hpos | ⟨hp, hi0, hl0⟩
    · refine ⟨L + j, by omega, ?_⟩
      obtain ⟨hbX, hbY⟩ := hbXY (L + j) (by omega)
      have h := bankRepairDigitFinalLaneFin ring hn root S R L hRL hroot hbL hbF lane0 j
        (by omega) hbX hbY
      rw [if_pos hact] at h
      exact h
    · refine ⟨n - 1, by omega, ?_⟩
      obtain ⟨hbX, hbY⟩ := hbXY (n - 1) (by omega)
      have h := bankRepairDigitFinalLaneReset ring hn root S R L hRL hLn hroot lane0 (n - 1)
        (by omega) (by omega) hbX hbY
      omega
    · rcases bankRepairDigitPipeProgress R hR (bankRepairDigitOutL ring root lane0 S (L - R)) with
        hD | ⟨i, hi, hlt⟩
      · refine ⟨L - 1, by omega, ?_⟩
        obtain ⟨hbX, hbY⟩ := hbXY (L - 1) (by omega)
        have h := bankRepairDigitFinalLaneDel ring hn root S R L hR hRL hLn hroot hbL hbF lane0
          (L - 1) (by omega) hbX hbY
        rcases hD with hD | hU
        · rw [if_pos (And.intro hp (Or.inl (And.intro hD (And.intro hi0 hl0))))] at h
          exact h
        · rw [if_pos (And.intro hp (Or.inr hU))] at h
          exact h
      · refine ⟨L - R + i, by omega, ?_⟩
        obtain ⟨hbX, hbY⟩ := hbXY (L - R + i) (by omega)
        have h := bankRepairDigitFinalLanePipe ring hn root S R L hR hRL hLn hroot hbS hbF lane0
          i hi hbX hbY
        rw [if_pos (And.intro hp hlt)] at h
        exact h
  obtain ⟨k, hk, hd⟩ := hlane
  refine ⟨k, hk, ?_⟩
  have hw := bankRepairDigitFinalLaneStepAll ring hn root S R L hR hRL hLn hroot hbS hbL hbF hbXY
    .writer k hk
  have hq := bankRepairDigitFinalLaneStepAll ring hn root S R L hR hRL hLn hroot hbS hbL hbF hbXY
    .comparison k hk
  unfold bankRepairDigitFinalRankOf
  cases lane0 <;> omega

end Ring

/-- The final condition on tokens fails exactly when it fails on shapes. -/
theorem bankRepairDigitFinOKShOf {A : Nat} (n L j : Nat) (hj : L + j < n) (live : Bool)
    (inp : InTok A) (h : ¬ BankRepairDigitFinalOK n (L + j) live inp) :
    ¬ bankRepairDigitFinOKSh (n - L) j (bankRepairDigitInShOf inp) live := by
  intro h'
  apply h
  rcases h' with ⟨h1, h2⟩ | h3
  · exact Or.inl ⟨by omega, h2⟩
  · right
    cases live <;> cases inp <;>
      simp_all [bankRepairDigitClsEP, bankRepairDigitInShOf, DigitFinalInput]

/-- The size of the final rank. -/
theorem bankRepairDigitFinalRankLe {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R L : Nat) (S : Fin n → ProjD c) :
    bankRepairDigitFinalRankOf ring root R L S ≤
      2 * ((2 * R + (n - L) + 3) * ((n - L) * (n - L)) + 2 * R +
        (n - L) * (2 * (n - L) + 2)) := by
  unfold bankRepairDigitFinalRankOf bankRepairDigitFinalLaneRankOf
  have h1 := bankRepairDigitLaneRankLe R (n - L) (bankRepairDigitOutL ring root .writer S (L - R))
    (bankRepairDigitInL ring root .writer S L) (bankRepairDigitLvL ring root .writer S L)
  have h2 := bankRepairDigitLaneRankLe R (n - L)
    (bankRepairDigitOutL ring root .comparison S (L - R))
    (bankRepairDigitInL ring root .comparison S L) (bankRepairDigitLvL ring root .comparison S L)
  omega

/-- `2 (lane bound) ≤ F + R + U + r` whenever the final block is no longer than `R`. -/
theorem bankRepairDigitFinalBudget (R m : Nat) (hR : 1 ≤ R) (hm : m ≤ R) :
    2 * ((2 * R + m + 3) * (m * m) + 2 * R + m * (2 * m + 2)) ≤
      bankRepairDigitForwardCount R + bankRepairDigitReturnCount R +
        bankRepairDigitSettledCount R + R := by
  unfold bankRepairDigitForwardCount bankRepairDigitReturnCount bankRepairDigitSettledCount
    bankRepairDigitBaseCount
  have e2 : R ^ 2 = R * R := Nat.pow_two R
  have e3 : R ^ 3 = R * R * R := by
    rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, e2]
  rw [e3, e2]
  have h1 : m * m ≤ R * R := Nat.mul_le_mul hm hm
  have hC : m * (2 * m + 2) ≤ R * (2 * R + 2) := Nat.mul_le_mul hm (by omega)
  have hC' : R * (2 * R + 2) = 2 * (R * R) + 2 * R := by
    rw [Nat.mul_add, Nat.mul_left_comm R 2 R, Nat.mul_comm R 2]
  generalize R * R = x at h1 hC' ⊢
  have hA : (2 * R + m + 3) * (m * m) ≤ (3 * R + 3) * x := Nat.mul_le_mul (by omega) h1
  have hB : (3 * R + 3) * x = 3 * (R * x) + 3 * x := by rw [Nat.add_mul, Nat.mul_assoc]
  have hRx : R * x = x * R := Nat.mul_comm R x
  have hD : (2 * x + 1) * (3 * x + 4 * R + 2) = 2 * (x * (3 * x + 4 * R + 2)) +
      (3 * x + 4 * R + 2) := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have hE : x * (4 * R) ≤ x * (3 * x + 4 * R + 2) := Nat.mul_le_mul_left x (by omega)
  have hE' : x * (4 * R) = 4 * (x * R) := Nat.mul_left_comm x 4 R
  have hF : x * 1 ≤ x * (2 * x + 8 * R + 1) := Nat.mul_le_mul_left x (by omega)
  have hG : x * 1 ≤ x * R := Nat.mul_le_mul_left x hR
  rw [Nat.mul_one] at hF hG
  omega

/-- The closed-form last delimiter `L = first + R ⌊(n - 1 - first) / R⌋`. -/
theorem bankRepairDigitLastDelimFacts (R first n L : Nat) (hR : 1 ≤ R) (hf0 : 0 < first)
    (hf : first < n) (b : Nat → Bool)
    (hb : ∀ k, 0 < k → k < n → (b k = true ↔ first ≤ k ∧ (k - first) % R = 0))
    (hL : L = first + R * ((n - 1 - first) / R)) :
    L < n ∧ n ≤ L + R ∧ first ≤ L ∧ b L = true ∧
      (∀ k, 0 < k → k < n → b k = true → k ≤ L) ∧
      (first < L → first ≤ L - R ∧ b (L - R) = true ∧
        ∀ k, L - R < k → k < L → b k = false) := by
  have hq1 := Nat.mul_div_le (n - 1 - first) R
  have hq2 := Nat.lt_mul_div_succ (n - 1 - first) (show 0 < R by omega)
  generalize (n - 1 - first) / R = q at hq1 hq2 hL
  rw [Nat.mul_add, Nat.mul_one] at hq2
  have hdel : ∀ k, first ≤ k → (k - first) % R = 0 → k = first + R * ((k - first) / R) := by
    intro k h1 h2
    have := Nat.div_add_mod (k - first) R
    omega
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
  · apply (hb L (by omega) (by omega)).2
    refine ⟨by omega, ?_⟩
    rw [show L - first = R * q by omega]
    exact Nat.mul_mod_right R q
  · intro k h0 hk hbk
    obtain ⟨h1, h2⟩ := (hb k h0 hk).1 hbk
    have e := hdel k h1 h2
    generalize (k - first) / R = a at e
    have ha : a < q + 1 := Nat.lt_of_mul_lt_mul_left (a := R) (by rw [Nat.mul_add, Nat.mul_one]; omega)
    have := Nat.mul_le_mul_left R (show a ≤ q by omega)
    omega
  · intro hfl
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0, Nat.mul_zero] at hL
      omega
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Nat.mul_add, Nat.mul_one] at hL hq1
    refine ⟨by omega, ?_, ?_⟩
    · apply (hb (L - R) (by omega) (by omega)).2
      refine ⟨by omega, ?_⟩
      rw [show L - R - first = R * q' by omega]
      exact Nat.mul_mod_right R q'
    · intro k h1 h2
      cases hbk : b k
      · rfl
      exfalso
      obtain ⟨h3, h4⟩ := (hb k (by omega) (by omega)).1 hbk
      have e := hdel k h3 h4
      generalize (k - first) / R = a at e
      have ha1 : q' < a := Nat.lt_of_mul_lt_mul_left (a := R) (by omega)
      have ha2 : a < q' + 1 :=
        Nat.lt_of_mul_lt_mul_left (a := R) (by rw [Nat.mul_add, Nat.mul_one]; omega)
      omega

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalLaneStepAll
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalRankStep
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalRankDrop
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinOKShOf
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalRankLe
#print axioms L3.RenewalReferenceClock.bankRepairDigitFinalBudget
#print axioms L3.RenewalReferenceClock.bankRepairDigitLastDelimFacts
