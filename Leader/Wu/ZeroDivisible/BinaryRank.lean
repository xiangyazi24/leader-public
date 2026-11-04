import Leader.Core.Basic

/-! A finite binary rank with earlier physical sites more significant.
This is an arithmetic utility for the actual reset-word event proof; it makes
no assertion about protocol executions or which leader bits can change. -/
namespace PPLLAstraBinaryRank

/-- Read a Boolean vector from site zero to the last site as a binary number. -/
def weight : {n : Nat} → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n+1, f => (if f ⟨0, by omega⟩ then 2^n else 0) +
      weight (fun i : Fin n => f i.succ)

/-- All less significant sites together weigh less than the next binary place. -/
theorem weight_lt {n : Nat} (f : Fin n → Bool) : weight f < 2^n := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    have h := ih (fun i : Fin n => f i.succ)
    simp only [weight, Nat.pow_succ]
    split <;> omega

/-- Losing the first differing true bit outweighs arbitrary later gains.
The protocol proof must supply the first-difference hypotheses independently. -/
theorem first_difference_drop {n : Nat} (f g : Fin n → Bool)
    (m : Fin n) (hf : f m = true) (hg : g m = false)
    (hpre : ∀ i : Fin n, i.val < m.val → f i = g i) :
    weight g < weight f := by
  induction n with
  | zero => exact Fin.elim0 m
  | succ n ih =>
    by_cases hm : m.val = 0
    · have hm0 : m = (⟨0, by omega⟩ : Fin (n+1)) := Fin.ext hm
      rw [hm0] at hf hg
      have h := weight_lt (fun i : Fin n => g i.succ)
      simp only [weight, hf, hg, Bool.false_eq_true, ↓reduceIte]
      omega
    · let j : Fin n := ⟨m.val-1, by omega⟩
      have hj : j.succ = m := Fin.ext (by simp [j]; omega)
      have ht := ih (fun i : Fin n => f i.succ) (fun i : Fin n => g i.succ)
        j (by simpa [hj] using hf) (by simpa [hj] using hg)
        (by intro i hi; apply hpre i.succ; simp [j] at hi; simp; omega)
      have h0 := hpre ⟨0, by omega⟩ (by simp; omega)
      simp only [weight]
      rw [h0]
      omega

#print axioms weight_lt
#print axioms first_difference_drop
end PPLLAstraBinaryRank
