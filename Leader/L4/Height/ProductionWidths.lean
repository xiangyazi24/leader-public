import Leader.L4.Height.ProductionCustody
import Leader.L4.Height.ProductionGeometry

namespace L4.Height.ProductionCustody
open AllSizeProtocol PhysicalCustody BStarH6WordChart
open Classical
noncomputable section

private theorem fold_bounds (v : List Nat) (a cap : Nat) (ha : a ≤ cap)
    (h : ∀ j ∈ v, j ≤ cap) : a ≤ v.foldl max a ∧ v.foldl max a ≤ cap ∧
    ∀ j ∈ v, j ≤ v.foldl max a := by
  induction v generalizing a with
  | nil => simp [ha]
  | cons b v ih =>
    have hb := h b List.mem_cons_self
    obtain ⟨left,right,all⟩ := ih (max a b) (Nat.max_le.mpr ⟨ha,hb⟩)
      (fun j hj => h j (List.mem_cons_of_mem _ hj))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) left,right,?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl|tail
    · exact Nat.le_trans (Nat.le_max_right _ _) left
    · exact all _ tail

theorem width_bounds {s n : Nat} {x : Raw s n} (g : CustodyWitness x) :
    0 < width g ∧ width g ≤ 1024*radWidth s := by
  let f (e : Fin n) : Nat :=
    if oldH6 (rows s) g.base (rightNeighbor e) then
      BStarH6Ordinal.oldOrdinal (rows s) g.base g.hh e + 1 else 0
  have bound (j : Nat) (h : j ∈ List.ofFn f) : j ≤ 1024*radWidth s := by
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp h
    dsimp only [f]
    split
    next yes => exact g.upperWidth e yes
    next => omega
  obtain ⟨_,upper,all⟩ := fold_bounds (List.ofFn f) 0 _ (Nat.zero_le _) bound
  obtain ⟨i,hi⟩ := g.hh
  let e := RearTrace.predecessor i
  have eqn : rightNeighbor e=i := RearTrace.right_predecessor i
  have nonzero := all (f e) (List.mem_ofFn.mpr ⟨e,rfl⟩)
  change 0 < (List.ofFn f).foldl max 0 ∧ _
  refine ⟨?_,upper⟩
  have pos : 0 < f e := by simp [f,eqn,hi]
  exact Nat.lt_of_lt_of_le pos nonzero

theorem terminal_le_width {s n : Nat} {x : Raw s n} (g : CustodyWitness x) (e : Fin n)
    (endWord : oldH6 (rows s) g.base (rightNeighbor e)=true) :
    BStarH6Ordinal.oldOrdinal (rows s) g.base g.hh e+1 ≤ width g := by
  let f (u : Fin n) : Nat := if oldH6 (rows s) g.base (rightNeighbor u) then
    BStarH6Ordinal.oldOrdinal (rows s) g.base g.hh u+1 else 0
  have bound (j : Nat) (h : j∈List.ofFn f) : j≤1024*radWidth s := by
    obtain ⟨u,rfl⟩ := List.mem_ofFn.mp h
    dsimp only [f]
    split
    next y => exact g.upperWidth u y
    next => omega
  have H := (fold_bounds (List.ofFn f) 0 _ (Nat.zero_le _) bound).2.2
    (f e) (List.mem_ofFn.mpr ⟨e,rfl⟩)
  exact (show f e=BStarH6Ordinal.oldOrdinal (rows s) g.base g.hh e+1 by simp [f,endWord]) ▸ H

theorem chart_sizes {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
    {o : BStarAcquireLiteralChain.Owners (oldH6 (rows s) g.base)}
    {S : List (BStarAcquireVisitOrder.Pos n)} {len : Nat} {fall : BStarAcquireVisitOrder.Pos n}
    (C : BStarResetChartTouch.Chart (show 0<2 by decide) g.base g.hh o S len fall) :
    len+1≤11*width g ∧ 4*width g≤81*len ∧ 0<len := by
  refine ⟨ProductionGeometry.chart_length (show 0<2 by decide) C (width g) (terminal_le_width g),?_⟩
  let d := 4*width g/81+1
  have minW (v : Fin n) (term : oldH6 (rows s) g.base (rightNeighbor v)=true) :
      d≤BStarH6Ordinal.oldOrdinal (rows s) g.base g.hh v+1 := by
    let B := BStarH6Ordinal.oldOrdinal (rows s) g.base g.hh v+1
    let f (u : Fin n) : Nat := if oldH6 (rows s) g.base (rightNeighbor u) then
      BStarH6Ordinal.oldOrdinal (rows s) g.base g.hh u+1 else 0
    have bound (j : Nat) (h : j∈List.ofFn f) : j≤(81*B-1)/4 := by
      obtain ⟨u,rfl⟩ := List.mem_ofFn.mp h
      dsimp only [f]
      split
      next hu =>
        have z := g.widthRatio u v hu term
        change 4*_ < 81*B at z
        omega
      next => omega
    have large := (fold_bounds (List.ofFn f) 0 _ (Nat.zero_le _) bound).2.1
    change width g≤(81*B-1)/4 at large
    change 4*width g/81+1≤B
    have pos : 0<B := Nat.zero_lt_succ _
    omega
  have L := BStarPaceWidth.receiver_width_le_len (show 0<2 by decide) C d minW
  dsimp [d] at L
  omega

#print axioms width_bounds
#print axioms chart_sizes
end
end L4.Height.ProductionCustody

