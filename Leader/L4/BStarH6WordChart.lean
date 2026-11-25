import Leader.L4.BStarLongFiberOwner

/-! Cyclic word indices of an old physical H6 layout. This construction
does not assert persistence or provide within-word offsets. -/
namespace L4.BStarH6WordChart
open AllSizeProtocol BStarLongClaims BStarLongFiberOwner
open BStarLongFenceTopology

def countPrefix {n : Nat} (h : Fin n → Bool) : Nat → Nat
  | 0 => 0
  | k+1 => countPrefix h k + if hk : k<n then (h ⟨k,hk⟩).toNat else 0

def total {n : Nat} (h : Fin n → Bool) := countPrefix h n

def word {n : Nat} (h : Fin n → Bool) (i : Fin n) : Int :=
  (countPrefix h (i.val+1) : Int) % (total h : Int)

theorem prefix_succ {n : Nat} (h : Fin n → Bool) (i : Fin n) :
    countPrefix h (i.val+1)=countPrefix h i.val+(h i).toNat := by
  obtain ⟨i,hi⟩ := i
  simp [countPrefix,hi]

theorem countPrefix_mono {n : Nat} (h : Fin n → Bool) {a b : Nat} (hab : a≤b) :
    countPrefix h a≤countPrefix h b := by
  induction b with
  | zero =>
    have e : a=0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases e : a=b+1
    · subst a
      exact Nat.le_refl _
    · have H := ih (show a≤b by omega)
      rw [countPrefix]
      omega

theorem total_pos {n : Nat} (h : Fin n → Bool) (hh : ∃ i, h i=true) : 0<total h := by
  obtain ⟨i,hi⟩ := hh
  have H := countPrefix_mono h (show i.val+1≤n by have := i.isLt; omega)
  rw [prefix_succ,hi] at H
  change 0<countPrefix h n
  simp at H
  omega

theorem word_range {n : Nat} (h : Fin n → Bool) (i : Fin n) (hh : ∃ i, h i=true) :
    0≤word h i ∧ word h i<(total h : Int) := by
  have T : 0<(total h : Int) := by exact_mod_cast total_pos h hh
  exact ⟨Int.emod_nonneg _ (Int.ne_of_gt T),Int.emod_lt_of_pos _ T⟩

theorem right_word {n : Nat} (h : Fin n → Bool) (i : Fin n) :
    word h (rightNeighbor i) =
      (word h i + ((h (rightNeighbor i)).toNat : Int)) % (total h : Int) := by
  let j := rightNeighbor i
  have J : j.val=(i.val+1)%n := rfl
  unfold word
  change (countPrefix h (j.val+1) : Int) % (total h : Int) =
    ((countPrefix h (i.val+1) : Int) % (total h : Int) + ((h j).toNat : Int)) % (total h : Int)
  rw [prefix_succ h j,Int.natCast_add]
  rw [Int.add_emod,Int.add_emod ((countPrefix h (i.val+1) : Int) % (total h : Int)),
    Int.emod_emod]
  by_cases H : i.val+1<n
  · rw [J,Nat.mod_eq_of_lt H]
  · have E : i.val+1=n := by have := i.isLt; omega
    have Z : j.val=0 := by simp [J,E]
    rw [Z,E]
    simp [countPrefix,total]

def oldH6 {a : LargeParams} {n : Nat} (b : LargeRows a) (x : Fin n → LargeSite a)
    (i : Fin n) : Bool := (oldHeaders b (x i)).h6

def oldPair {a : LargeParams} {n : Nat} (b : LargeRows a) (x : Fin n → LargeSite a)
    (i : Fin n) : Pair LongGeometry := (longGeometry b (x i), longGeometry b (x (rightNeighbor i)))

def site {n : Nat} (i : Fin n) : Side → Fin n
  | .left => i
  | .right => rightNeighbor i

def physicalOwner {A : Type} {n : Nat} (h : Fin n → Bool) (i : Fin n)
    (d : A → Int) (z : At A) : Int :=
  owner (total h) (word h (site i z.side)) (d z.occurrence)

theorem physical_pair_owner {A : Type} {n : Nat} (h : Fin n → Bool) (i : Fin n)
    (d : A → Int) (z : At A) :
    physicalOwner h i d z =
      pairOwner (total h) (word h i) (h (rightNeighbor i)) d z := by
  obtain ⟨s,a⟩ := z
  cases s
  · simp [physicalOwner,pairOwner,site,shift]
  · change owner (total h) (word h (rightNeighbor i)) (d a) =
      owner (total h) (word h i + (if h (rightNeighbor i) then 1 else 0)) (d a)
    rw [right_word]
    have B : ((h (rightNeighbor i)).toNat : Int) =
        (if h (rightNeighbor i) then 1 else 0) := by cases h (rightNeighbor i) <;> rfl
    rw [B]
    unfold owner
    rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod]

theorem actual_command_owner {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (i : Fin n) (c : CommandClaim) (r : At (Fin 11))
    (hc : c∈orderedCommands (oldPair b x i)) (hr : c.destination=some r) :
    physicalOwner (oldH6 b x) i cmdDispl c.source =
      physicalOwner (oldH6 b x) i cmdDispl r := by
  rw [physical_pair_owner,physical_pair_owner]
  exact command_owner (oldPair b x i) _ _ c r hc hr

theorem actual_data_owner {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (i : Fin n) (Rsv : List (At Sheet))
    (c : DataClaim) (r : At Sheet)
    (hc : c∈orderedData (oldPair b x i) Rsv) (hr : c.destination=some r) :
    physicalOwner (oldH6 b x) i dataDispl c.source =
      physicalOwner (oldH6 b x) i dataDispl r := by
  rw [physical_pair_owner,physical_pair_owner]
  exact data_owner (oldPair b x i) _ _ Rsv c r hc hr

end L4.BStarH6WordChart
