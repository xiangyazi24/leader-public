import Leader.L4.BStarLiftKeyFresh

namespace L4.BStarIncrementLedger
open BStarLiftKeyFresh

/-- The chosen natural coordinate starts at an explicit offset and
counts exact native INC marks for this owner. It does not infer the
natural coordinate from a wrapping raw clock. -/
def count {Owner : Type} [DecidableEq Owner] (initial : Owner→Nat)
    (mark : Nat→Option Owner) (owner : Owner) : Nat→Nat
  | 0 => initial owner
  | t+1 => count initial mark owner t + if mark t=some owner then 1 else 0

theorem count_monotone {Owner : Type} [DecidableEq Owner] (initial : Owner→Nat)
    (mark : Nat→Option Owner) (owner : Owner) {a b : Nat} (le : a≤b) :
    count initial mark owner a≤count initial mark owner b := by
  induction le with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem count_step {Owner : Type} [DecidableEq Owner] (initial : Owner→Nat)
    (mark : Nat→Option Owner) (owner : Owner) (t : Nat) (M : mark t=some owner) :
    count initial mark owner (t+1)=count initial mark owner t+1 := by
  simp [count,M]

def finite {Owner : Type} [DecidableEq Owner] {T : Nat} (initial : Owner→Nat)
    (mark : Nat→Option Owner) (t : Fin (T+1)) (owner : Owner) :=
  count initial mark owner t.val

/-- Exact INC witnesses between reads suffice for distinct old-cut
keys, even when the visible tick lies below the wrap band. -/
theorem keys_of_inc_marks {Owner : Type} [DecidableEq Owner] {T : Nat}
    (initial : Owner→Nat) (mark : Nat→Option Owner) (read : Fin T→Option Owner)
    (separate : ∀ (a b : Fin T) (i : Owner), a.val<b.val →
      read a=some i → read b=some i →
      ∃ m : Fin T, a.val≤m.val ∧ m.val<b.val ∧ mark m.val=some i)
    {a b : Fin T} {i j : Owner} (A : read a=some i) (B : read b=some j)
    (same : Key (finite initial mark) i a=Key (finite initial mark) j b) : a=b := by
  apply unique_read_keys (finite initial mark) read _ _ A B same
  · intro x y o E
    exact count_monotone initial mark o E
  · intro x y o lt X Y
    obtain ⟨m,M₁,M₂,M⟩ := separate x y o lt X Y
    exact ⟨m,M₁,M₂,count_step initial mark o m.val M⟩

/-- The offset gives disjointness from all smaller reserved keys;
the chosen offset must itself be justified by the physical cut. -/
theorem avoids_reserved {Owner : Type} [DecidableEq Owner] {T : Nat}
    (initial : Owner→Nat) (mark : Nat→Option Owner) (e : Fin T)
    (o : Owner) (k : Nat) (earlier : k<initial o) :
    (o,k)≠Key (finite initial mark) o e := by
  intro same
  have E := congrArg Prod.snd same
  change k=count initial mark o e.val at E
  have H := count_monotone initial mark o (Nat.zero_le e.val)
  change initial o≤count initial mark o e.val at H
  omega

/-- The old key uses only earlier INC marks, never the mark being read. -/
theorem count_of_prefix {Owner : Type} [DecidableEq Owner] (initial : Owner→Nat)
    (left right : Nat→Option Owner) (owner : Owner) (t : Nat)
    (equal : ∀ j,j<t→left j=right j) :
    count initial left owner t=count initial right owner t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [count,count,ih (fun j J=>equal j (Nat.lt_succ_of_lt J)),equal t (Nat.lt_succ_self t)]

end L4.BStarIncrementLedger
