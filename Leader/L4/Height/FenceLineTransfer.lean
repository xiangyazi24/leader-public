import Leader.L4.Height.FenceFlow

namespace L4.Height.FenceLineTransfer
open OpenFenceLine FenceGrid FenceCrossings FenceComparison

def occupiedCount (u : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k+1 => occupiedCount u k + (u (k+1)).toNat

theorem prefix_balance {n h : Nat} (bond : Nat → Fin n) (e : Fin n) (u v : Nat → Bool)
    (localStep : ∀ k,0<k → k≤h →
      (v k).toNat+flow h bond e u k=(u k).toNat+flow h bond e u (k-1))
    (k : Nat) (small : k≤h) :
    occupiedCount v k+flow h bond e u k=occupiedCount u k := by
  induction k with
  | zero => simp [occupiedCount,flow]
  | succ k ih =>
    have old := ih (by omega)
    have step := localStep (k+1) (by omega) small
    simp only [Nat.add_sub_cancel] at step
    simp only [occupiedCount]
    omega

private theorem exact_tick {n h : Nat} (bond : Nat → Fin n) (e : Fin n) (u : Nat → Bool) (k : Nat) :
    tick h bond (occupiedCount u) e k=occupiedCount u k-flow h bond e u k := by
  cases k with
  | zero => simp [tick,flow,occupiedCount]
  | succ k =>
    have left : occupiedCount u k < occupiedCount u (k+1) ↔ u (k+1)=true := by
      cases eq : u (k+1) <;> simp [occupiedCount,eq]
    have right : occupiedCount u ((k+1)+1)≤occupiedCount u (k+1) ↔ u ((k+1)+1)=false := by
      cases eq : u ((k+1)+1) <;> simp [occupiedCount,eq]
    simp only [tick,flow,Nat.add_sub_cancel,left,right]
    split <;> simp_all

/-- Actual Boolean occupancy agrees with the full-line prefix process
whenever each hop/exit obeys the local two-endpoint balance. -/
theorem transfer {n h : Nat} (bond : Nat → Fin n) (play : List (Fin n) → Fin n → Fin n)
    (stock : List (Fin n) → Nat → Bool) (full : ∀ k,0<k → k≤h → stock [] k=true)
    (balance : ∀ a e k,0<k → k≤h →
      (stock (a++[e]) k).toNat+flow h bond (play a e) (stock a) k=
        (stock a k).toNat+flow h bond (play a e) (stock a) (k-1))
    (a : List (Fin n)) (k : Nat) (hk : k≤h) :
    occupiedCount (stock a) k=count h bond play a k := by
  have frame (u v : Nat → Nat) (e : Fin n) (same : ∀ j,j≤h → u j=v j)
      (j : Nat) (small : j≤h) : tick h bond u e j=tick h bond v e j := by
    unfold tick
    rw [same j small,same (j-1) (by omega)]
    by_cases eq : j=h
    · simp [eq]
    · rw [same (j+1) (by omega)]
  have extend (a : List (Fin n)) (e : Fin n)
      (old : ∀ j,j≤h → occupiedCount (stock a) j=count h bond play a j) :
      ∀ j,j≤h → occupiedCount (stock (a++[e])) j=count h bond play (a++[e]) j := by
    intro j hj
    have B := prefix_balance bond (play a e) (stock a) (stock (a++[e])) (balance a e) j hj
    have S := frame (occupiedCount (stock a)) (count h bond play a) (play a e) old j hj
    rw [exact_tick] at S
    have trace : count h bond play (a++[e]) j=tick h bond (count h bond play a) (play a e) j := by
      simp [count,OpenFenceLine.run,OpenFenceLine.run_append]
    rw [trace,←S]
    omega
  have z (j : Nat) (small : j≤h) : occupiedCount (stock []) j=count h bond play [] j := by
    change occupiedCount (stock []) j=j
    induction j with
    | zero => rfl
    | succ j ih => simp [occupiedCount,full _ (by omega) small,ih (by omega)]
  have go (p w : List (Fin n)) (start : ∀ j,j≤h → occupiedCount (stock p) j=count h bond play p j) :
      ∀ j,j≤h → occupiedCount (stock (p++w)) j=count h bond play (p++w) j := by
    induction w generalizing p with
    | nil => simpa using start
    | cons e w ih => simpa only [List.append_assoc,List.singleton_append] using ih (p++[e]) (extend p e start)
  exact go [] a z k hk

theorem hit_mono {S : Type} {n : Nat} (step : S → Fin n → S) (P Q : S → Prop)
    (more : ∀ a,P a → Q a) (t : Nat) (a : S) : iidHitCost step Q t a≤iidHitCost step P t a := by
  classical
  induction t generalizing a with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    by_cases q : Q a
    · rw [iidHitCost_of_target step Q a q]
      exact Nat.zero_le _
    · have p : ¬P a := fun h => q (more a h)
      simp only [iidHitCost,if_neg q,if_neg p]
      apply Nat.add_le_add_left
      exact sum_ofFn_le _ _ (fun e => ih (step a e))

private theorem same_grid {n h : Nat} (F G : Line n h) (same : F.bond=G.bond)
    (fuel k j : Nat) : grid F fuel k j=grid G fuel k j := by
  induction fuel generalizing k j with
  | zero => rfl
  | succ fuel ih => simp only [grid,same,ih]

private def identityLine {n : Nat} (h : Nat) (bond : Nat → Fin n) : Line n h :=
  fullLine h bond (fun _ e => e) (fun _ e mid => ⟨[],e,mid++[e],rfl,rfl⟩)

/-- The path family depends only on the physical bonds and lengths. -/
def pairedPaths {n : Nat} (l r : Nat) (left right : Nat → Fin n) : List (List (Fin n)) :=
  paths (root (identityLine l left)) ++ paths (root (identityLine r right))

structure Clearance {n : Nat} (H : Nat) (p : List (List (Fin n))) (goal : List (Fin n) → Prop) : Prop where
  size : p.length≤2*H^2*2^(2*H+1)
  length : ∀ w∈p,w.length≤4*H+2
  done : ∀ a,load p a=0 → goal a

theorem Clearance.mono {n H : Nat} {p : List (List (Fin n))} {G K : List (Fin n) → Prop}
    (h : Clearance H p G) (incl : ∀ a,G a → K a) : Clearance H p K :=
  ⟨h.size,h.length,fun a z => incl a (h.done a z)⟩

theorem Clearance.expected {n H : Nat} {p : List (List (Fin n))} {G : List (Fin n) → Prop}
    (h : Clearance H p G) (positive : 0<H) (a : List (Fin n)) :
    IIDExpectedHittingTimeAtMost mark G a (128*n*H) := by
  intro t
  exact Nat.le_trans (hit_mono mark _ _ h.done t a)
    (candidate_clearance_cost positive p h.size h.length a t)

theorem paired_clearance {n l r H : Nat} (hl : 0<l) (hr : 0<r) (lH : l≤H) (rH : r≤H)
    (left right : Nat → Fin n) (played : List (Fin n) → Fin n → Fin n) (two : Twice played)
    : Clearance H (pairedPaths l r left right)
        (fun w => count l left played w l=0 ∧ count r right played w r=0) := by
  let L := fullLine l left played two
  let R := fullLine r right played two
  let p := paths (root L) ++ paths (root R)
  have lSize := root_size L
  have rSize := root_size R
  have hh : 0<H := Nat.lt_of_lt_of_le hl lH
  have hCount : p.length≤2*H^2*2^(2*H+1) := by
    have leftHi := Nat.pow_le_pow_right (n:=2) (by decide) (show 2*l-1≤2*H+1 by omega)
    have rightHi := Nat.pow_le_pow_right (n:=2) (by decide) (show 2*r-1≤2*H+1 by omega)
    have factor : 2≤2*H^2 := by have one := Nat.pow_pos (n:=2) hh; omega
    have sumBound : (paths (root L)).length+(paths (root R)).length≤2*2^(2*H+1) :=
      by have a := lSize.1; have b := rSize.1; omega
    exact Nat.le_trans (by simpa only [p,List.length_append] using sumBound) (Nat.mul_le_mul_right _ factor)
  have length (q : List (Fin n)) (mem : q∈p) : q.length≤4*H+2 := by
    rcases List.mem_append.mp mem with e|e
    · have := lSize.2 q e; omega
    · have := rSize.2 q e; omega
  have done (w : List (Fin n)) (z : load p w=0) :
      count l left played w l=0 ∧ count r right played w r=0 := by
    have all := matched_of_clear p w z
    exact ⟨root_clears hl L w (fun v h => all v (List.mem_append_left _ h)),
      root_clears hr R w (fun v h => all v (List.mem_append_right _ h))⟩
  have same : p=pairedPaths l r left right := by
    change paths (root L)++paths (root R)=paths (root (identityLine l left))++paths (root (identityLine r right))
    rw [show root L=root (identityLine l left) from same_grid L (identityLine l left) rfl (2*l-1) l 1,
      show root R=root (identityLine r right) from same_grid R (identityLine r right) rfl (2*r-1) r 1]
  rw [←same]
  exact ⟨hCount,length,done⟩

/-- Two lines use one candidate word, so their joint clearance bound uses
one reserve. The line lengths and physical bond maps may differ. -/
theorem two_open_lines {n l r H : Nat} (hl : 0<l) (hr : 0<r) (lH : l≤H) (rH : r≤H)
    (left right : Nat → Fin n) (played : List (Fin n) → Fin n → Fin n) (two : Twice played)
    (a : List (Fin n)) :
    IIDExpectedHittingTimeAtMost mark
      (fun w => count l left played w l=0 ∧ count r right played w r=0) a (128*n*H) := by
  exact (paired_clearance hl hr lH rH left right played two).expected (Nat.lt_of_lt_of_le hl lH) a

#print axioms two_open_lines
#print axioms transfer
end L4.Height.FenceLineTransfer
