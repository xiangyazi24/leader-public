import Leader.L4.BStarFenceShadow

namespace L4.BStarFenceCrossing
open BStarFenceShadow

def ready {k : Nat} (z : Fin k→Bool) (j : Fin k) : Bool :=
  z j && if h : j.val+1<k then !(z (succIdx j h)) else true

def bump {n k : Nat} (port : Fin k→Fin n) (e : Fin n)
    (z : Fin k→Bool) (count : Fin k→Nat) (j : Fin k) : Nat :=
  count j + (if e=port j then ready z j else false).toNat

def prev {k : Nat} (count : Fin k→Nat) (j : Fin k) : Nat :=
  if h : 0<j.val then count (predIdx j h) else 0

def Balance {k : Nat} (z : Fin k→Bool) (count : Fin k→Nat) : Prop :=
  ∀ j, count j + (z j).toNat = 1 + prev count j

private theorem local_out {x : Bool} (y : Bool) :
    (x && !y).toNat+(x && y).toNat=x.toNat := by
  cases x <;> cases y <;> decide

private theorem local_in (x y : Bool) :
    (x || y).toNat=y.toNat+(x && !y).toNat := by
  cases x <;> cases y <;> decide

theorem balance_update {n k : Nat} (port : Fin k→Fin n)
    (inj : ∀ a b,port a=port b→a=b) (e : Fin n)
    (z : Fin k→Bool) (ct : Fin k→Nat) (B : Balance z ct) :
    Balance (update port e z) (bump port e z ct) := by
  intro j
  have BJ := B j
  have ne (h : 0<j.val) : predIdx j h≠j := by
    intro E
    have := congrArg Fin.val E
    change j.val-1=j.val at this
    omega
  by_cases own : e=port j
  · have pv : prev (bump port e z ct) j=prev ct j := by
      unfold prev
      split
      · rename_i h
        have away : e≠port (predIdx j h) := fun E => ne h (inj _ _ (E.symm.trans own))
        simp [bump,away]
      · rfl
    rw [pv,←BJ]
    simp only [bump,update,if_pos own,ready]
    split
    · rw [Nat.add_assoc,local_out]
    · cases z j <;> simp
  · simp only [bump,update,if_neg own,Bool.toNat_false,Nat.add_zero]
    by_cases h : 0<j.val
    · simp only [prev,dif_pos h] at BJ ⊢
      by_cases past : e=port (predIdx j h)
      · have fit : (predIdx j h).val+1<k := by
          change j.val-1+1<k
          have := j.isLt
          omega
        have atj : succIdx (predIdx j h) fit=j := Fin.ext (by
          change j.val-1+1=j.val
          omega)
        simp only [if_pos past,bump,ready,dif_pos fit,atj]
        rw [local_in]
        omega
      · simp only [if_neg past,bump,Bool.toNat_false,Nat.add_zero]
        exact BJ
    · simpa only [prev,dif_neg h] using BJ

def trace {n k : Nat} (port : Fin k→Fin n) :
    (Fin k→Bool) → (Fin k→Nat) → List (Fin n) → ((Fin k→Bool) × (Fin k→Nat))
  | z,ct,[] => (z,ct)
  | z,ct,e::w => trace port (update port e z) (bump port e z ct) w

theorem trace_balance {n k : Nat} (port : Fin k→Fin n)
    (inj : ∀ a b,port a=port b→a=b)
    (z : Fin k→Bool) (ct : Fin k→Nat) (w : List (Fin n)) (B : Balance z ct) :
    Balance (trace port z ct w).1 (trace port z ct w).2 := by
  induction w generalizing z ct with
  | nil => exact B
  | cons e w ih => exact ih _ _ (balance_update port inj e z ct B)

theorem full_balance {n k : Nat} (port : Fin k→Fin n)
    (inj : ∀ a b,port a=port b→a=b) (w : List (Fin n)) :
    Balance (trace port (fun _ => true) (fun _ => 0) w).1
      (trace port (fun _ => true) (fun _ => 0) w).2 := by
  apply trace_balance port inj _ _ w
  intro j
  unfold prev
  split <;> rfl

theorem balance_bounds {k : Nat} {z : Fin k→Bool} {ct : Fin k→Nat}
    (B : Balance z ct) (j : Fin k) : prev ct j≤ct j ∧ ct j≤prev ct j+1 := by
  have H := B j
  cases E : z j <;> simp only [E,Bool.toNat_false,Bool.toNat_true] at H ⊢ <;> omega

theorem ready_iff {k : Nat} {z : Fin k→Bool} {ct : Fin k→Nat}
    (B : Balance z ct) (j : Fin k) :
    ready z j=true ↔ prev ct j=ct j ∧
      ∀ h : j.val+1<k, ct j < ct (succIdx j h) := by
  have A : z j=true ↔ prev ct j=ct j := by
    have H := B j
    cases E : z j <;> simp only [E,Bool.toNat_false,Bool.toNat_true,Bool.false_eq_true, false_iff, true_iff] at H ⊢ <;> omega
  unfold ready
  rw [Bool.and_eq_true_iff,A]
  apply and_congr_right
  intro _
  split
  · rename_i h
    have J := B (succIdx j h)
    have Hp : 0<(succIdx j h).val := by
      change 0<j.val+1
      omega
    have HE : predIdx (succIdx j h) Hp=j := Fin.ext (by
      change j.val+1-1=j.val
      omega)
    rw [prev,dif_pos Hp,HE] at J
    constructor
    · intro H t
      have E : z (succIdx j h)=false := by cases E : z (succIdx j h) <;> simp_all
      rw [E] at J
      simp only [Bool.toNat_false,Nat.add_zero] at J
      omega
    · intro H
      have E := H h
      cases q : z (succIdx j h)
      · rfl
      · rw [q] at J
        simp only [Bool.toNat_true] at J
        omega
  · rename_i H
    exact ⟨fun _ h => (H h).elim,fun _ => rfl⟩

/-- The kth crossing at j depends on its own (k−1)st, the upstream
(k−1)st and the downstream kth. The outlet has no downstream input. -/
theorem crossing_ready {k : Nat} {z : Fin k→Bool} {ct : Fin k→Nat}
    (B : Balance z ct) (j : Fin k) (m : Nat) (pos : 0<m) (atPrev : ct j=m-1)
    (inReady : m-1≤prev ct j)
    (outReady : ∀ h : j.val+1<k, m≤ct (succIdx j h)) :
    ready z j=true := by
  apply (ready_iff B j).mpr
  have H := (balance_bounds B j).1
  exact ⟨by omega,fun h => by have := outReady h; omega⟩

def depth {k : Nat} (j : Fin k) (m : Nat) : Nat := 2*m+(k-1-j.val)

theorem dependency_depth {k : Nat} (j : Fin k) (m : Nat) (M : 0<m) :
    depth j (m-1)<depth j m ∧
    (∀ h : 0<j.val,depth (predIdx j h) (m-1)<depth j m) ∧
    (∀ h : j.val+1<k,depth (succIdx j h) m<depth j m) := by
  have := j.isLt
  simp only [depth,predIdx,succIdx]
  exact ⟨by omega,fun h => by omega,fun h => by omega⟩

theorem depth_bound {k : Nat} (j : Fin k) (m : Nat) (M : m≤j.val+1) :
    depth j m ≤ 2*k := by
  have := j.isLt
  unfold depth
  omega

#print axioms balance_update
#print axioms full_balance
#print axioms crossing_ready
#print axioms dependency_depth
#print axioms depth_bound

theorem predecessor_bound {k : Nat} {z : Fin k→Bool} {ct : Fin k→Nat}
    (B : Balance z ct) (j : Fin k) : ct j≤j.val+1 := by
  generalize E : j.val = t
  induction t using Nat.strongRecOn generalizing j with
  | ind t ih =>
    have L := (balance_bounds B j).2
    unfold prev at L
    split at L
    · rename_i h
      have S : (predIdx j h).val<t := by
        change j.val-1<t
        omega
      have C := ih (predIdx j h).val S (predIdx j h) rfl
      change ct (predIdx j h)≤j.val-1+1 at C
      omega
    · omega

/-- Only external parents are needed. If the crossing is still
outstanding, its preceding self-crossing already follows from balance. -/
theorem crossing_ready_two {k : Nat} {z : Fin k→Bool} {ct : Fin k→Nat}
    (B : Balance z ct) (j : Fin k) (m : Nat) (pos : 0<m) (miss : ct j<m)
    (inReady : m-1≤prev ct j)
    (outReady : ∀ h : j.val+1<k, m≤ct (succIdx j h)) :
    ready z j=true := by
  have T := (balance_bounds B j).1
  exact crossing_ready B j m pos (by omega) inReady outReady

theorem outlet_saturates {k : Nat} {z : Fin k→Bool} {ct : Fin k→Nat}
    (B : Balance z ct) (out : Fin k) (last : out.val+1=k) (done : k≤ct out) :
    ∀ j, ct j=j.val+1 := by
  have stepback (j : Fin k) (h : j.val+1<k) (H : ct (succIdx j h)=(succIdx j h).val+1) :
      ct j=j.val+1 := by
    have T := (balance_bounds B (succIdx j h)).2
    have Hp : 0<(succIdx j h).val := by
      change 0<j.val+1
      omega
    have E : predIdx (succIdx j h) Hp=j := Fin.ext (by
      change j.val+1-1=j.val
      omega)
    rw [prev,dif_pos Hp,E,H] at T
    change j.val+1+1≤ct j+1 at T
    have U := predecessor_bound B j
    omega
  intro j
  generalize N : k-1-j.val = t
  induction t using Nat.strongRecOn generalizing j with
  | ind t ih =>
    by_cases H : j.val+1<k
    · have V : k-1-(succIdx j H).val<t := by
        change k-1-(j.val+1)<t
        omega
      exact stepback j H (ih _ V _ rfl)
    · have E : j=out := Fin.ext (by have := j.isLt; omega)
      subst j
      have U := predecessor_bound B out
      omega

theorem outlet_empty {k : Nat} {z : Fin k→Bool} {ct : Fin k→Nat}
    (B : Balance z ct) (out : Fin k) (last : out.val+1=k) (done : k≤ct out) :
    ∀ j,z j=false := by
  intro j
  have C := outlet_saturates B out last done j
  have V (k : Nat) (ct : Fin k→Nat) (j : Fin k) :
      (∀ a,ct a=a.val+1) → prev ct j=j.val := by
    intro S
    unfold prev
    split
    · rename_i h
      rw [S]
      change j.val-1+1=j.val
      omega
    · omega
  have BJ := B j
  rw [C,V k ct j (outlet_saturates B out last done)] at BJ
  cases E : z j
  · rfl
  · rw [E] at BJ
    simp only [Bool.toNat_true] at BJ
    omega

#print axioms predecessor_bound
#print axioms crossing_ready_two
#print axioms outlet_empty
end L4.BStarFenceCrossing
