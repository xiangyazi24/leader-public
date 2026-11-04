import Leader.L3.Bank.RepairDigitFinalRows

/-!
# T18: the final-region rank on lane shapes

Positions `0 ≤ j < m` are the final block (offset `last + j`); positions `0 ≤ i < R` are the
previous block (offset `last - R + i`). A lane is read through its input shapes `inp`, its
carry-live bits `lv` and the previous block's output shapes `out`.

* A *start* is an offset `1 ≤ a < m` holding a settled input with the carry off, whose left
  neighbour has the carry off and input `E` or `P`. `last` is the largest start (`0` if none).
* `need` is `Σ_{k < last} ([start k] * k + [k is not an off-carry P])`. It counts the
  deliveries still owed to the stuck settled runs.
* `Φ` is the distance of the previous block's next delivery: the minimum over its offsets of
  `2 (R - 1 - i)` for `D`, `2 (R - 1 - i) + 1` for `U` and `2 R` for `E`.
* `Λ` gives local weights to carries, fronts, settled inputs and (while a start exists) packets.

The lane rank is `(2 R + m + 3) * need + [last > 0] * Φ + Λ`.
-/

namespace L3.RenewalReferenceClock

set_option autoImplicit false

/-! ### Site classes -/

/-- Carry off and a settled input. -/
def bankRepairDigitClsOS : BankRepairDigitInSh → Bool → Bool
  | .S _, false => true
  | _, _ => false

/-- Carry off and input `E` or `P`. -/
def bankRepairDigitClsEP : BankRepairDigitInSh → Bool → Bool
  | .E, false => true
  | .P _, false => true
  | _, _ => false

/-- Carry off and a packet. -/
def bankRepairDigitClsOP : BankRepairDigitInSh → Bool → Bool
  | .P _, false => true
  | _, _ => false

/-! ### The largest start -/

def bankRepairDigitLastOf (st : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => if st k = true then k else bankRepairDigitLastOf st k

theorem bankRepairDigitLastOfGe (st : Nat → Bool) :
    ∀ cnt k, k < cnt → st k = true → k ≤ bankRepairDigitLastOf st cnt
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | cnt + 1, k, h, hs => by
      show k ≤ (if st cnt = true then cnt else bankRepairDigitLastOf st cnt)
      by_cases hc : st cnt = true
      · rw [if_pos hc]; omega
      · rw [if_neg hc]
        have hk : k ≠ cnt := fun e => hc (e ▸ hs)
        exact bankRepairDigitLastOfGe st cnt k (by omega) hs

theorem bankRepairDigitLastOfSpec (st : Nat → Bool) :
    ∀ cnt, bankRepairDigitLastOf st cnt = 0 ∨
      (st (bankRepairDigitLastOf st cnt) = true ∧ bankRepairDigitLastOf st cnt < cnt)
  | 0 => Or.inl rfl
  | cnt + 1 => by
      show (if st cnt = true then cnt else bankRepairDigitLastOf st cnt) = 0 ∨
        (st (if st cnt = true then cnt else bankRepairDigitLastOf st cnt) = true ∧
          (if st cnt = true then cnt else bankRepairDigitLastOf st cnt) < cnt + 1)
      by_cases hc : st cnt = true
      · rw [if_pos hc]; exact Or.inr ⟨hc, by omega⟩
      · rw [if_neg hc]
        rcases bankRepairDigitLastOfSpec st cnt with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, by omega⟩

theorem bankRepairDigitLastOfLe (st : Nat → Bool) (cnt : Nat) :
    bankRepairDigitLastOf st cnt ≤ cnt := by
  rcases bankRepairDigitLastOfSpec st cnt with h | ⟨_, h⟩ <;> omega

theorem bankRepairDigitLastOfAbove (st : Nat → Bool) (cnt k : Nat)
    (h1 : bankRepairDigitLastOf st cnt < k) (h2 : k < cnt) : st k = false := by
  cases hs : st k
  · rfl
  · have := bankRepairDigitLastOfGe st cnt k h2 hs
    omega

theorem bankRepairDigitLastOfMono (st st' : Nat → Bool) (cnt : Nat)
    (h : ∀ k, k < cnt → st' k = true → st k = true) :
    bankRepairDigitLastOf st' cnt ≤ bankRepairDigitLastOf st cnt := by
  rcases bankRepairDigitLastOfSpec st' cnt with h0 | ⟨h1, h2⟩
  · rw [h0]; exact Nat.zero_le _
  · exact bankRepairDigitLastOfGe st cnt _ h2 (h _ h2 h1)

theorem bankRepairDigitLastOfCongr (st st' : Nat → Bool) :
    ∀ cnt, (∀ k, k < cnt → st' k = st k) →
      bankRepairDigitLastOf st' cnt = bankRepairDigitLastOf st cnt
  | 0, _ => rfl
  | cnt + 1, h => by
      show (if st' cnt = true then cnt else bankRepairDigitLastOf st' cnt) =
        (if st cnt = true then cnt else bankRepairDigitLastOf st cnt)
      rw [h cnt (by omega), bankRepairDigitLastOfCongr st st' cnt (fun k hk => h k (by omega))]

/-! ### Generic need inequalities -/

theorem bankRepairDigitNeedLe (st st' : Nat → Bool) (g g' : Nat → Nat) (cnt : Nat)
    (hs : ∀ k, k < cnt → st' k = true → st k = true)
    (hg : ∀ k, k < cnt → g' k ≤ g k) :
    bankRepairDigitSumCnt g' 0 (bankRepairDigitLastOf st' cnt) ≤
      bankRepairDigitSumCnt g 0 (bankRepairDigitLastOf st cnt) := by
  have hm := bankRepairDigitLastOfMono st st' cnt hs
  have hl := bankRepairDigitLastOfLe st cnt
  exact bankRepairDigitSumCntExtend g' g 0 _ _ hm (fun i _ h2 => hg i (by omega))

theorem bankRepairDigitNeedMove (st st' : Nat → Bool) (g g' : Nat → Nat) (cnt j : Nat)
    (hs : ∀ k, k < cnt → st' k = st k) (hj : st (j + 1) = false)
    (h1 : g' j = g j + 1) (h2 : g' (j + 1) + 1 = g (j + 1))
    (ho : ∀ k, k < cnt → k ≠ j → k ≠ j + 1 → g' k = g k) :
    bankRepairDigitSumCnt g' 0 (bankRepairDigitLastOf st' cnt) ≤
      bankRepairDigitSumCnt g 0 (bankRepairDigitLastOf st cnt) := by
  rw [bankRepairDigitLastOfCongr st st' cnt hs]
  have hne : bankRepairDigitLastOf st cnt ≠ j + 1 := by
    intro h
    rcases bankRepairDigitLastOfSpec st cnt with h0 | ⟨h3, _⟩
    · omega
    · rw [h, hj] at h3; exact Bool.noConfusion h3
  have hLc := bankRepairDigitLastOfLe st cnt
  generalize bankRepairDigitLastOf st cnt = L at hne hLc
  by_cases hL : L ≤ j
  · exact bankRepairDigitSumCntMono g' g 0 L (fun i _ h => Nat.le_of_eq (ho i (by omega)
      (by omega) (by omega)))
  · have := bankRepairDigitSumCntPair g' g 0 j 0 L
      (fun i _ h2 h3 h4 => Nat.le_of_eq (ho i (by omega) h3 h4)) (Nat.zero_le _) (by omega)
      (by omega)
    omega

theorem bankRepairDigitNeedSettle (st st' : Nat → Bool) (g g' : Nat → Nat) (cnt j : Nat)
    (hj1 : j + 1 < cnt) (hs1 : st (j + 1) = true) (hs1' : st' (j + 1) = false)
    (hso : ∀ k, k < cnt → k ≠ j → k ≠ j + 1 → st' k = st k)
    (hg0 : g j = 0) (hg0' : g' j ≤ j + 1) (hg1 : g (j + 1) = j + 2) (hg1' : g' (j + 1) ≤ 1)
    (hgo : ∀ k, k < cnt → k ≠ j → k ≠ j + 1 → g' k = g k) :
    bankRepairDigitSumCnt g' 0 (bankRepairDigitLastOf st' cnt) ≤
        bankRepairDigitSumCnt g 0 (bankRepairDigitLastOf st cnt) ∧
      bankRepairDigitLastOf st' cnt ≤ bankRepairDigitLastOf st cnt := by
  have hL1 : j + 1 ≤ bankRepairDigitLastOf st cnt := bankRepairDigitLastOfGe st cnt _ hj1 hs1
  have hLn := bankRepairDigitLastOfLe st cnt
  by_cases hc : bankRepairDigitLastOf st cnt = j + 1
  · have hL' : bankRepairDigitLastOf st' cnt ≤ j := by
      rcases bankRepairDigitLastOfSpec st' cnt with h0 | ⟨h1, h2⟩
      · omega
      · apply Nat.le_of_not_lt
        intro hlt
        by_cases he : bankRepairDigitLastOf st' cnt = j + 1
        · rw [he, hs1'] at h1; exact Bool.noConfusion h1
        · have e := hso _ h2 (by omega) he
          rw [e] at h1
          have := bankRepairDigitLastOfAbove st cnt _ (by omega) h2
          rw [this] at h1; exact Bool.noConfusion h1
    refine ⟨?_, by omega⟩
    rw [hc]
    exact bankRepairDigitSumCntExtend g' g 0 (bankRepairDigitLastOf st' cnt) (j + 1) (by omega)
      (fun i _ h2 => Nat.le_of_eq (hgo i (by omega) (by omega) (by omega)))
  · have hgt : j + 1 < bankRepairDigitLastOf st cnt := by omega
    have hsl : st (bankRepairDigitLastOf st cnt) = true := by
      rcases bankRepairDigitLastOfSpec st cnt with h0 | ⟨h1, _⟩
      · omega
      · exact h1
    have hlc : bankRepairDigitLastOf st cnt < cnt := by
      rcases bankRepairDigitLastOfSpec st cnt with h0 | ⟨_, h2⟩
      · omega
      · exact h2
    have heq : bankRepairDigitLastOf st' cnt = bankRepairDigitLastOf st cnt := by
      have hge : bankRepairDigitLastOf st cnt ≤ bankRepairDigitLastOf st' cnt :=
        bankRepairDigitLastOfGe st' cnt (bankRepairDigitLastOf st cnt) (by omega)
          (by rw [hso (bankRepairDigitLastOf st cnt) (by omega) (by omega) (by omega)]
              exact hsl)
      rcases bankRepairDigitLastOfSpec st' cnt with h0 | ⟨h1, h2⟩
      · omega
      · apply Nat.le_antisymm _ hge
        apply Nat.le_of_not_lt
        intro hlt
        rw [hso _ h2 (by omega) (by omega),
          bankRepairDigitLastOfAbove st cnt _ hlt h2] at h1
        exact Bool.noConfusion h1
    refine ⟨?_, Nat.le_of_eq heq⟩
    rw [heq]
    have := bankRepairDigitSumCntPair g' g 0 j 0 (bankRepairDigitLastOf st cnt)
      (fun i _ h2 h3 h4 => Nat.le_of_eq (hgo i (by omega) h3 h4)) (Nat.zero_le _) (by omega)
      (by omega)
    omega

/-- Like `bankRepairDigitNeedLe`, with `g' ≤ g` only below `cnt - 1`. -/
theorem bankRepairDigitNeedLeTop (st st' : Nat → Bool) (g g' : Nat → Nat) (cnt : Nat)
    (hs : ∀ k, k < cnt → st' k = true → st k = true)
    (hg : ∀ k, k + 1 < cnt → g' k ≤ g k) :
    bankRepairDigitSumCnt g' 0 (bankRepairDigitLastOf st' cnt) ≤
      bankRepairDigitSumCnt g 0 (bankRepairDigitLastOf st cnt) := by
  have hm := bankRepairDigitLastOfMono st st' cnt hs
  have hl : bankRepairDigitLastOf st cnt = 0 ∨ bankRepairDigitLastOf st cnt < cnt := by
    rcases bankRepairDigitLastOfSpec st cnt with h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  exact bankRepairDigitSumCntExtend g' g 0 _ _ hm (fun i _ h2 => hg i (by omega))

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairDigitLastOfGe
#print axioms L3.RenewalReferenceClock.bankRepairDigitLastOfSpec
#print axioms L3.RenewalReferenceClock.bankRepairDigitLastOfLe
#print axioms L3.RenewalReferenceClock.bankRepairDigitLastOfAbove
#print axioms L3.RenewalReferenceClock.bankRepairDigitLastOfMono
#print axioms L3.RenewalReferenceClock.bankRepairDigitLastOfCongr
#print axioms L3.RenewalReferenceClock.bankRepairDigitNeedLe
#print axioms L3.RenewalReferenceClock.bankRepairDigitNeedMove
#print axioms L3.RenewalReferenceClock.bankRepairDigitNeedSettle
#print axioms L3.RenewalReferenceClock.bankRepairDigitNeedLeTop
