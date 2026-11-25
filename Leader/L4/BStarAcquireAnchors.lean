import Leader.L4.BStarH6WordChart

namespace L4.BStarAcquireAnchors
open AllSizeProtocol BStarH6WordChart

abbrev Header {n : Nat} (h : Fin n → Bool) := {i : Fin n // h i=true}

private theorem header_count {n : Nat} (h : Fin n → Bool) (i : Header h) :
    1 ≤ countPrefix h (i.val.val+1) ∧ countPrefix h (i.val.val+1) ≤ total h := by
  constructor
  · rw [prefix_succ h i.val,i.property]
    simp
  · exact countPrefix_mono h (Nat.succ_le_of_lt i.val.isLt)

private theorem strict_headers {n : Nat} (h : Fin n → Bool) (i j : Header h)
    (E : i.val.val < j.val.val) :
    countPrefix h (i.val.val+1) < countPrefix h (j.val.val+1) := by
  have H := countPrefix_mono h (Nat.succ_le_of_lt E)
  change countPrefix h (i.val.val+1) ≤ countPrefix h j.val.val at H
  rw [prefix_succ h j.val,j.property]
  simp
  omega

private theorem hit_count {n : Nat} (h : Fin n → Bool) (k t : Nat)
    (ht : t ≤ n) (hp : 0<k) (hk : k≤countPrefix h t) :
    ∃ i : Header h, i.val.val<t ∧ countPrefix h (i.val.val+1)=k := by
  induction t with
  | zero => simp [countPrefix] at hk; omega
  | succ t ih =>
    let j : Fin n := ⟨t, by omega⟩
    have E := prefix_succ h j
    change countPrefix h (t+1)=countPrefix h t+(h j).toNat at E
    by_cases Q : k≤countPrefix h t
    · obtain ⟨i,hi,eq⟩ := ih (by omega) Q
      exact ⟨i,by omega,eq⟩
    · cases J : h j
      · simp [J] at E
        omega
      · simp [J] at E
        exact ⟨⟨j,J⟩,Nat.lt_succ_self t,by change countPrefix h (t+1)=k; omega⟩

private theorem rem_repr (a m : Nat) (ha : 1≤a) (hm : a≤m) :
    (a : Int) % (m : Int) = if a=m then 0 else (a : Int) := by
  split
  · rename_i h
    subst a
    exact Int.emod_self
  · exact Int.emod_eq_of_lt (by omega) (by omega)

/-- An owner chart word identifies a unique H6 header, including the
wrapped header whose prefix count is total and whose chart word is 0. -/
theorem header_word_injective {n : Nat} (h : Fin n → Bool) :
    Function.Injective (fun i : Header h => word h i.val) := by
  intro i j E
  have A := header_count h i
  have B := header_count h j
  unfold word at E
  dsimp only at E
  rw [rem_repr _ _ A.1 A.2,rem_repr _ _ B.1 B.2] at E
  have C : countPrefix h (i.val.val+1)=countPrefix h (j.val.val+1) := by
    split at E <;> split at E <;> omega
  apply Subtype.ext
  apply Fin.ext
  apply Decidable.byContradiction
  intro N
  rcases Nat.lt_or_gt_of_ne N with T|T
  · have H := strict_headers h i j T
    omega
  · have H := strict_headers h j i T
    omega

/-- Every residue in the bounded owner range occurs at an H6 header. -/
theorem header_word_exists {n : Nat} (h : Fin n → Bool) (hh : ∃ i, h i=true)
    (o : Int) (ho : 0≤o) (hm : o<(total h : Int)) :
    ∃ i : Header h, word h i.val=o := by
  let k := if o=0 then total h else o.toNat
  have H : 0<total h := total_pos h hh
  have P : 0<k := by unfold k; split <;> omega
  have Q : k≤total h := by unfold k; split <;> omega
  obtain ⟨i,_,E⟩ := hit_count h k n (Nat.le_refl n) P Q
  refine ⟨i,?_⟩
  unfold word
  rw [E,rem_repr k (total h) (by omega) Q]
  by_cases z : o=0
  · simp [k,z]
  · have Hk : o.toNat ≠ total h := by omega
    simp [k,z,Hk,Int.toNat_of_nonneg ho]

/-- Enumerating all active physical headers gives each cyclic owner
exactly once. This includes the case of a single header. -/
theorem unique_header {n : Nat} (h : Fin n → Bool) (hh : ∃ i, h i=true)
    (o : Int) (ho : 0≤o) (hm : o<(total h : Int)) :
    ∃ i : Header h, word h i.val=o ∧ ∀ j : Header h, word h j.val=o → j=i := by
  obtain ⟨i,E⟩ := header_word_exists h hh o ho hm
  exact ⟨i,E,fun j J => header_word_injective h (J.trans E.symm)⟩

open BStarLongFiberOwner

/-- The intrinsic owner of a physical command occurrence. -/
def commandOwner {n : Nat} (h : Fin n → Bool) (i : Fin n) (k : Fin 11) : Int :=
  owner (total h) (word h i) (cmdDispl k)

theorem commandOwner_range {n : Nat} (h : Fin n → Bool) (hh : ∃ j, h j=true)
    (i : Fin n) (k : Fin 11) :
    0≤commandOwner h i k ∧ commandOwner h i k<(total h : Int) := by
  have H : 0<(total h : Int) := by exact_mod_cast total_pos h hh
  exact ⟨Int.emod_nonneg _ (Int.ne_of_gt H),Int.emod_lt_of_pos _ H⟩

/-- K0 is at the owner's own header. K10 is at the next chart word's
header (the same physical header when the ring has just one word). -/
theorem unique_command_header {n : Nat} (h : Fin n → Bool) (hh : ∃ j, h j=true)
    (o : Int) (ho : 0≤o) (hm : o<(total h : Int)) (k : Fin 11) :
    ∃ i : Header h, commandOwner h i.val k=o ∧
      ∀ j : Header h, commandOwner h j.val k=o → j=i := by
  have M : 0<(total h : Int) := by exact_mod_cast total_pos h hh
  let w := addressWord (total h) o (cmdDispl k)
  have N : 0 ≤ w := Int.emod_nonneg _ (Int.ne_of_gt M)
  have H : w < (total h : Int) := Int.emod_lt_of_pos _ M
  obtain ⟨i,E,uniq⟩ := unique_header h hh w N H
  refine ⟨i,?_,?_⟩
  · unfold commandOwner
    rw [E]
    exact (owner_inverse (total h) o (cmdDispl k)).trans (Int.emod_eq_of_lt ho hm)
  · intro j eq
    apply uniq
    unfold commandOwner at eq
    have q := address_inverse (total h) (word h j.val) (cmdDispl k)
    rw [eq] at q
    exact q.trans (Int.emod_eq_of_lt (word_range h j.val hh).1 (word_range h j.val hh).2) |>.symm

end L4.BStarAcquireAnchors
