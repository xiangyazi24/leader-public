import Lean

namespace L4.ClockCycleExtrema

/-- Neighboring natural coordinates differ by at most one. -/
def Near (a b : Nat) : Prop := a ≤ b+1 ∧ b ≤ a+1

/-- Both arcs between two vertices of an ordered cycle give a bound;
the shorter has length at most half the cycle. -/
theorem span {m : Nat} (f : Fin m → Nat)
    (adj : ∀ i : Fin m, Near (f i) (f ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩))
    (i j : Fin m) : f j ≤ f i + m/2 := by
  have straight (a b : Nat) (ha : a<m) (hb : b<m) (ab : a≤b) :
      f ⟨a,ha⟩≤f ⟨b,hb⟩+(b-a) ∧ f ⟨b,hb⟩≤f ⟨a,ha⟩+(b-a) := by
    induction b with
    | zero =>
      have eq : a=0 := by omega
      subst a
      simp
    | succ b ih =>
      by_cases eq : a=b+1
      · subst a; simp
      · have hB : b<m := by omega
        have base := ih hB (by omega)
        have step : Near (f ⟨b,hB⟩) (f ⟨b+1,hb⟩) := by
          simpa only [Nat.mod_eq_of_lt hb] using adj ⟨b,hB⟩
        have A := step.1
        have B := step.2
        obtain ⟨C,D⟩ := base
        constructor <;> omega
  have hm : 0<m := Nat.zero_lt_of_lt i.isLt
  have hlast : m-1<m := by omega
  have seam : Near (f ⟨m-1,hlast⟩) (f ⟨0,hm⟩) := by
    simpa only [show m-1+1=m by omega, Nat.mod_self] using adj ⟨m-1,hlast⟩
  have arcs (a b : Fin m) (ab : a.val≤b.val) :
      f a≤f b + m/2 ∧ f b≤f a + m/2 := by
    have ⟨A,B⟩ := straight a.val b.val a.isLt b.isLt ab
    have ⟨C,D⟩ := straight 0 a.val hm a.isLt (Nat.zero_le _)
    have ⟨E,F⟩ := straight b.val (m-1) b.isLt hlast (by have := b.isLt; omega)
    change f a ≤ f b + (b.val-a.val) at A
    change f b ≤ f a + (b.val-a.val) at B
    change f ⟨0,hm⟩ ≤ f a + (a.val-0) at C
    change f a ≤ f ⟨0,hm⟩ + (a.val-0) at D
    change f b ≤ f ⟨m-1,hlast⟩ + (m-1-b.val) at E
    change f ⟨m-1,hlast⟩ ≤ f b + (m-1-b.val) at F
    have hB := b.isLt
    have S := seam.1
    have T := seam.2
    by_cases H : b.val-a.val≤m/2
    · exact ⟨by omega,by omega⟩
    · have R : m-(b.val-a.val)≤m/2 := by omega
      exact ⟨by omega,by omega⟩
  by_cases H : i.val≤j.val
  · exact (arcs i j H).2
  · exact (arcs j i (by omega)).1

/-- Realized minimum and maximum on the actual finite indexing type. -/
theorem exists_extrema {m : Nat} (hm : 0<m) (f : Fin m → Nat) :
    ∃ i j : Fin m, ∀ k : Fin m, f i≤f k ∧ f k≤f j := by
  let xs := List.ofFn f
  have nz : xs≠[] := by
    intro H
    have E := congrArg List.length H
    simp [xs] at E
    omega
  cases L : xs.min? with
  | none => exact (nz (List.min?_eq_none_iff.mp L)).elim
  | some lo =>
    cases G : xs.max? with
    | none => exact (nz (List.max?_eq_none_iff.mp G)).elim
    | some hi =>
      have ⟨low,lower⟩ := List.min?_eq_some_iff.mp L
      have ⟨high,upper⟩ := List.max?_eq_some_iff.mp G
      obtain ⟨i,ri⟩ := List.mem_ofFn.mp low
      obtain ⟨j,rj⟩ := List.mem_ofFn.mp high
      refine ⟨i,j,fun k => ?_⟩
      have h : f k∈xs := List.mem_ofFn.mpr ⟨k,rfl⟩
      exact ⟨ri.symm ▸ lower _ h,rj.symm ▸ upper _ h⟩

#print axioms span
#print axioms exists_extrema
end L4.ClockCycleExtrema
