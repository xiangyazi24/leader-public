import Leader.L4.Height.ProductionWidths

namespace L4.Height.ProductionCustody
open AllSizeProtocol PhysicalCustody BStarH6WordChart BStarH6Ordinal BStarTrace
open BStarAcquireAnchors BStarSteeredLikelihood
open Classical

private theorem map_nd {α β : Type} (f : α → β)
    (inj : ∀ i j, f i = f j → i = j) (l : List α) (nd : l.Nodup) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp nd
    apply List.nodup_cons.mpr
    constructor
    · intro H
      obtain ⟨z,hz,E⟩ := List.mem_map.mp H
      exact fresh ((inj z b E) ▸ hz)
    · exact ih tail

/-- Each site injects into its cyclic word-label and its offset in that word.
This uses the actual nearest-header ordinal, including at the numeric seam. -/
theorem ring_le_words_times_max {n W : Nat} (h : Fin n → Bool)
    (hh : ∃ i,h i = true)
    (bound : ∀ i,h (rightNeighbor i) = true → ordinal h hh i + 1 ≤ W) :
    n ≤ total h * W := by
  let f (i : Fin n) : Fin (total h) × Fin W :=
    (⟨(word h i).toNat, by have H := word_range h i hh; omega⟩,
     ⟨ordinal h hh i,ProductionGeometry.ordinal_lt_width h hh W bound i⟩)
  have inj (i j : Fin n) (E : f i = f j) : i = j := by
    have a : (word h i).toNat = (word h j).toNat :=
      congrArg (fun z : Fin (total h) × Fin W => z.1.val) E
    have b : ordinal h hh i = ordinal h hh j :=
      congrArg (fun z : Fin (total h) × Fin W => z.2.val) E
    have wi := (word_range h i hh).1
    have wj := (word_range h j hh).1
    have w : word h i = word h j := by omega
    let hi : Header h := ⟨back i (ordinal h hh i),(ordinal_spec h hh i).2.1⟩
    let hj : Header h := ⟨back j (ordinal h hh j),(ordinal_spec h hh j).2.1⟩
    have hij : hi = hj := by
      apply header_word_injective h
      exact (BStarCommitOperands.first_word hh i _ (ordinal_spec h hh i).2).trans
        (w.trans (BStarCommitOperands.first_word hh j _ (ordinal_spec h hh j).2).symm)
    have eq : back i (ordinal h hh i) = back j (ordinal h hh i) := by
      exact (congrArg Subtype.val hij).trans (congrArg (back j) b.symm)
    have cancel (k : Nat) : back i k = back j k → i = j := by
      induction k with
      | zero => simp only [back_zero,imp_self]
      | succ k ih =>
        intro E
        exact ih (by simpa only [BStarCommitOperands.right_back] using congrArg rightNeighbor E)
    exact cancel _ eq
  let prod := (List.finRange (total h)).flatMap (fun a => (List.finRange W).map (fun b => (a,b)))
  have sub : ((List.finRange n).map f) ⊆ prod := by
    intro p M
    change p ∈ (List.finRange (total h)).flatMap _ 
    exact List.mem_flatMap.mpr
      ⟨p.1, List.mem_finRange _, List.mem_map.mpr ⟨p.2,List.mem_finRange _,Prod.eta _⟩⟩
  have len (xs : List (Fin (total h))) :
      (xs.flatMap (fun a => (List.finRange W).map (fun b => (a,b)))).length = xs.length * W := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih,Nat.add_mul,Nat.add_comm]
  have le := (map_nd f inj _ (List.nodup_finRange n)).length_le_of_subset sub
  simpa only [List.length_map,List.length_finRange,show prod.length=total h*W by
    simpa only [List.length_finRange] using len (List.finRange (total h))] using le

/-- The paper's geometric space bound supplies the fourth owner; this is
not a separate unproved hypothesis in the block signature. -/
theorem production_of_space {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    (hs : 6 ≤ s) (hadvice : s = ell (ell n)) (hspace : 3 * 1024 * radWidth s < n) :
    Production g := by
  refine ⟨hadvice,hs,hspace,?_⟩
  have b := ring_le_words_times_max (oldH6 (rows s) g.base) g.hh (W:=1024*radWidth s) g.upperWidth
  by_cases enough : 4 ≤ total (oldH6 (rows s) g.base)
  · exact enough
  · have b' := Nat.mul_le_mul_right (1024*radWidth s) (show total (oldH6 (rows s) g.base) ≤ 3 by omega)
    have large : 3*(1024*radWidth s) < n := by simpa only [Nat.mul_assoc] using hspace
    exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans b b')) large)

/-- Exact dispatch shape, conditional on the still-open uniform production block. -/
theorem strict_publication_block_of_production_block (H : ProductionBlock)
    {s n : Nat} (_hn : 4 ≤ n)
    (hs : 6 ≤ s) (hadvice : s = ell (ell n))
    (hspace : 3 * 1024 * radWidth s < n)
    {x : Raw s n} (g : CustodyWitness x) (i : Header (oldH6 (rows s) g.base)) :
    let W := width g
    let D := 2^20 * n * W
    2^(5*longBudget+1) *
      wordSum (fun w => if RawServiceCore.publishes x i.val w then 1 else 0) (2*D) ≥ n^(2*D) := by
  classical
  exact H g (production_of_space g hs hadvice hspace) i

end L4.Height.ProductionCustody
