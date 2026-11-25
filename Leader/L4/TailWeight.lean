import Leader.L4.TaggedTailKernel
import Leader.L4.TaggedTrace
import Leader.L4.TaggedTail

namespace L4.TailWeight

open TaggedTailKernel

def expLo (T : Nat) (d : Int) : Nat := (d + 2*(T : Int)).toNat
def expHi (K : Nat) (d : Int) : Nat := ((K : Int)-d).toNat

def weight (K T : Nat) (d : Int) : Nat :=
  7^(expLo T d) * 8^(expHi K d)

theorem weight_at_zero (K T : Nat) : weight K T 0 = 7^(2*T) * 8^K := by
  have hh : (2*(T : Int)).toNat = 2*T := by omega
  simp [weight, expLo, expHi, hh]

theorem weight_floor {K T : Nat} {d : Int}
    (hlo : -2*(T : Int) ≤ d) (hhi : d ≤ (K : Int)) :
    7^(K+2*T) ≤ weight K T d := by
  have hsum : expLo T d + expHi K d = K+2*T := by
    unfold expLo expHi
    omega
  rw [← hsum, Nat.pow_add]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)

private theorem ratio_nonneg (k : Nat) (h : k ≤ 5) :
    scale * 7^k = ratioNumerator (k : Int) * 8^k := by
  have h' : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases h' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem ratio_nonpos (k : Nat) (h : k ≤ 2) :
    scale * 8^k = ratioNumerator (-(k : Int)) * 7^k := by
  have h' : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases h' with rfl | rfl | rfl <;> decide

/-- Exact integer implementation of multiplication by (7/8)^inc. -/
theorem weight_ratio {K T : Nat} {d inc : Int}
    (ha : -2*(T : Int) ≤ d) (hb : d ≤ (K : Int))
    (hc : -2*(T : Int) ≤ d+inc) (hd : d+inc ≤ (K : Int))
    (hinc : -2 ≤ inc ∧ inc ≤ 5) :
    scale * weight K T (d+inc) = ratioNumerator inc * weight K T d := by
  by_cases h : 0 ≤ inc
  · let k := inc.toNat
    have hk : inc = (k : Int) := by omega
    have h1 : expLo T (d+inc) = expLo T d + k := by
      unfold expLo; omega
    have h2 : expHi K d = expHi K (d+inc) + k := by
      unfold expHi; omega
    have hh := ratio_nonneg k (by omega)
    unfold weight
    rw [h1,h2,Nat.pow_add,Nat.pow_add,hk]
    calc
      _ = (7^(expLo T d)*8^(expHi K (d+(k : Int))))*(scale*7^k) := by
        ac_rfl
      _ = (7^(expLo T d)*8^(expHi K (d+(k : Int))))*(ratioNumerator (k : Int)*8^k) :=
        congrArg _ hh
      _ = _ := by ac_rfl
  · let k := (-inc).toNat
    have hk : inc = -(k : Int) := by omega
    have h1 : expLo T d = expLo T (d+inc) + k := by
      unfold expLo; omega
    have h2 : expHi K (d+inc) = expHi K d + k := by
      unfold expHi; omega
    have hh := ratio_nonpos k (by omega)
    unfold weight
    rw [h1,h2,Nat.pow_add,Nat.pow_add,hk]
    calc
      _ = (7^(expLo T (d+-(k : Int)))*8^(expHi K d))*(scale*8^k) := by
        ac_rfl
      _ = (7^(expLo T (d+-(k : Int)))*8^(expHi K d))*(ratioNumerator (-(k : Int))*7^k) :=
        congrArg _ hh
      _ = _ := by ac_rfl

end L4.TailWeight

#print axioms L4.TailWeight.weight_at_zero
#print axioms L4.TailWeight.weight_floor
#print axioms L4.TailWeight.weight_ratio
