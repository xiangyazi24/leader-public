import Init

namespace L4.BStarLiftKeyFresh

/-- A raw trace with (T) marks has old/new cut indices (0,ldots,T).
A read records its owner, not a key supplied separately from the lift. -/
def Key {Owner : Type} {T : Nat} (lift : Fin (T+1) → Owner → Nat)
    (owner : Owner) (j : Fin T) : Owner × Nat :=
  (owner, lift j.castSucc owner)

/-- A same-owner increment on an intervening mark separates the old-state
natural keys of two reads. The increment may be on the first read mark,
but must precede the second; it need not be the last mark of a tour. -/
theorem separated_keys {Owner : Type} {T : Nat}
    (lift : Fin (T+1) → Owner → Nat)
    (mono : ∀ (a b : Fin (T+1)) (i : Owner), a.val ≤ b.val → lift a i ≤ lift b i)
    (i : Owner) (a m b : Fin T)
    (am : a.val ≤ m.val) (mb : m.val < b.val)
    (inc : lift m.succ i = lift m.castSucc i + 1) :
    (Key lift i a).2 < (Key lift i b).2 := by
  have le₁ := mono a.castSucc m.castSucc i am
  have le₂ := mono m.succ b.castSucc i (show m.val+1 ≤ b.val by omega)
  change lift a.castSucc i < lift b.castSucc i
  omega

/-- On any finite trace (including one ending mid-tour), all recorded
owner/lift keys are injective, provided consecutive or nonconsecutive
same-owner reads satisfy the stated authenticated-increment premise.
The premise is external; this theorem does not assert that raw rows
supply it. -/
theorem unique_read_keys {Owner : Type} {T : Nat}
    (lift : Fin (T+1) → Owner → Nat)
    (readOwner : Fin T → Option Owner)
    (mono : ∀ (a b : Fin (T+1)) (i : Owner), a.val ≤ b.val → lift a i ≤ lift b i)
    (separate : ∀ (a b : Fin T) (i : Owner), a.val < b.val →
      readOwner a = some i → readOwner b = some i →
      ∃ m : Fin T, a.val ≤ m.val ∧ m.val < b.val ∧
        lift m.succ i = lift m.castSucc i + 1)
    {a b : Fin T} {i j : Owner}
    (ra : readOwner a = some i) (rb : readOwner b = some j)
    (same : Key lift i a = Key lift j b) : a = b := by
  have ij : i = j := congrArg Prod.fst same
  subst j
  have eq := congrArg Prod.snd same
  apply Fin.ext
  by_cases lt : a.val < b.val
  · obtain ⟨m,am,mb,inc⟩ := separate a b i lt ra rb
    have h := separated_keys lift mono i a m b am mb inc
    omega
  · by_cases gt : b.val < a.val
    · obtain ⟨m,bm,ma,inc⟩ := separate b a i gt rb ra
      have h := separated_keys lift mono i b m a bm ma inc
      omega
    · omega

#print axioms unique_read_keys
end L4.BStarLiftKeyFresh
