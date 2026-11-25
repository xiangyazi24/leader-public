import Leader.L4.BStarH6Ordinal
import Leader.L4.RearGeometry

namespace L4.PackedOrdinalCount

open AllSizeProtocol BStarH6Ordinal BStarH6WordChart

private def previous {n : Nat} (N : 0<n) (k : Nat) (K : k≤n) : Fin n :=
  ⟨if k=0 then n-1 else k-1, by split <;> omega⟩

private theorem previous_succ {n : Nat} (N : 0<n) (i : Fin n) :
    previous N (i.val+1) (by have := i.isLt; omega) = i := by
  apply Fin.ext
  simp [previous]

private theorem right_previous {n : Nat} (N : 0<n) (i : Fin n) :
    rightNeighbor (previous N i.val (Nat.le_of_lt i.isLt)) = i := by
  apply Fin.ext
  change ((if i.val=0 then n-1 else i.val-1)+1)%n=i.val
  by_cases E : i.val=0
  · rw [if_pos E,show n-1+1=n by omega,Nat.mod_self,E]
  · rw [if_neg E,show i.val-1+1=i.val by omega,Nat.mod_eq_of_lt i.isLt]

/-- The prefix budget retains the ordinal just before its first and
last sites. At each true header the preceding word's full length pays
one width charge; a non-header increments the carried ordinal. -/
private theorem prefix_budget {n : Nat} (N : 0<n) (h : Fin n → Bool)
    (hh : ∃ i, h i=true) (r : Nat)
    (wide : ∀ e : Fin n, h (rightNeighbor e)=true → r≤ordinal h hh e+1)
    (k : Nat) (hk : k≤n) :
    r * countPrefix h k + ordinal h hh (previous N k hk)
      ≤ k + ordinal h hh (previous N 0 (Nat.zero_le _)) := by
  induction k with
  | zero => simp [countPrefix]
  | succ k ih =>
    let i : Fin n := ⟨k,by omega⟩
    have hk' : k≤n := by omega
    have P := ih hk'
    have eq : rightNeighbor (previous N k hk') = i := right_previous N i
    have O := ordinal_right h hh (previous N k hk')
    rw [eq] at O
    change r * countPrefix h (i.val+1) +
      ordinal h hh (previous N (i.val+1) hk) ≤ _
    rw [prefix_succ h i, previous_succ N i, O]
    by_cases Hi : h i=true
    · have W := wide (previous N k hk') (eq.symm ▸ Hi)
      simp [Hi,Nat.mul_add,show i.val=k from rfl]
      omega
    · have Hfalse : h i=false := Bool.eq_false_iff.mpr Hi
      simp [Hfalse,show i.val=k from rfl]
      omega

/-- Packing count directly from the incoming seam width hypothesis.
No arrangement of the headers or choice of a distinguished root is
needed, apart from the witness required to define the ordinal. -/
theorem total_mul_width_le {n : Nat} (h : Fin n → Bool)
    (hh : ∃ i, h i=true) (r : Nat)
    (wide : ∀ e : Fin n, h (rightNeighbor e)=true → r≤ordinal h hh e+1) :
    total h * r ≤ n := by
  obtain ⟨i,hi⟩ := hh
  have N : 0<n := Nat.zero_lt_of_lt i.isLt
  have P := prefix_budget N h ⟨i,hi⟩ r wide n (Nat.le_refl n)
  have same : previous N n (Nat.le_refl n) = previous N 0 (Nat.zero_le _) := by
    apply Fin.ext
    simp [previous, Nat.ne_of_gt N]
  rw [same] at P
  rw [Nat.mul_comm]
  exact Nat.le_of_add_le_add_right P

/-- Predecessor-seam version, as used by the packed-fibre producer. -/
theorem total_mul_width_le_of_predecessor {n : Nat} (h : Fin n → Bool)
    (hh : ∃ i, h i=true) (r : Nat)
    (wide : ∀ i : Fin n, h i=true → r≤ordinal h hh (RearTrace.predecessor i)+1) :
    total h * r ≤ n := by
  apply total_mul_width_le h hh r
  intro e he
  simpa only [RearTrace.predecessor_right] using wide (rightNeighbor e) he

#print axioms total_mul_width_le
#print axioms total_mul_width_le_of_predecessor
end L4.PackedOrdinalCount
