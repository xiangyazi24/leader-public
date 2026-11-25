import Leader.L4.Height.OpenFenceLine

namespace L4.Height.FenceLineTransfer

def flow {n : Nat} (h : Nat) (bond : Nat → Fin n) (e : Fin n) (u : Nat → Bool) (k : Nat) : Nat :=
  if 0<k ∧ k≤h ∧ e=bond k ∧ u k=true ∧ (k=h ∨ u (k+1)=false) then 1 else 0

theorem hop_balance (a b : Bool) :
    (a && b).toNat+(a && !b).toNat=a.toNat ∧
      (a || b).toNat=b.toNat+(a && !b).toNat := by cases a <;> cases b <;> decide

/-- Only consecutive bonds need distinct labels for local conservation. -/
theorem balance_of_updates {n h : Nat} (bond : Nat → Fin n) (e : Fin n) (u v : Nat → Bool)
    (k : Nat) (pos : 0<k) (small : k≤h) (distinct : 1<k → bond k≠bond (k-1))
    (depart : e=bond k → v k=(if k=h then false else u k && u (k+1)))
    (arrive : 1<k → e=bond (k-1) → v k=(u (k-1) || u k))
    (hold : e≠bond k → (1<k → e≠bond (k-1)) → v k=u k) :
    (v k).toNat+flow h bond e u k=(u k).toNat+flow h bond e u (k-1) := by
  have first : 0<k-1 ↔ 1<k := by omega
  have prev : k-1+1=k := by omega
  have prevSize : k-1≤h := by omega
  have prevEnd : k-1≠h := by omega
  have no_flow (noIn : 1<k → e≠bond (k-1)) : flow h bond e u (k-1)=0 := by
    unfold flow
    split
    next live => exact False.elim (noIn (first.mp live.1) live.2.2.1)
    next => rfl
  by_cases out : e=bond k
  · rw [no_flow (fun hi eq => distinct hi (out.symm.trans eq)),depart out]
    by_cases endAt : k=h
    · subst h
      cases a : u k <;> simp [flow,pos,out,a]
    · cases a : u k <;> cases b : u (k+1) <;> simp [flow,pos,small,out,endAt,a,b]
  · have z : flow h bond e u k=0 := by simp [flow,out]
    rw [z,Nat.add_zero]
    by_cases receives : 1<k ∧ e=bond (k-1)
    · rw [arrive receives.1 receives.2]
      cases a : u (k-1) <;> cases b : u k <;>
        simp [flow,first,receives.1,receives.2,prevSize,prevEnd,prev,a,b]
    · have noIn : 1<k → e≠bond (k-1) := fun hi eq => receives ⟨hi,eq⟩
      rw [hold out noIn,no_flow noIn,Nat.add_zero]

#print axioms balance_of_updates
end L4.Height.FenceLineTransfer
