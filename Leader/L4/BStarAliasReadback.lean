import Leader.L4.BStarAliasFold

/-! Packed scalar readback for the actual reverse-order lowering of
pending writes. Lookup honors newest-first order even with duplicates. -/
namespace L4.BStarAliasReadback
open AllSizeProtocol BStarTrace BStarLongArithmetic BStarLongRegisters
open BStarLongOutgoing BStarLongDoor

def lowerPending (xs : Pending) : Patch LW :=
  fuse (xs.reverse.map fun (a,v) => writeScalar a v)

theorem lower_cons (a v : Nat) (xs : Pending) :
    lowerPending ((a,v)::xs)=(lowerPending xs).compose (writeScalar a v) := by
  simp [lowerPending,fuse,List.foldl_append]

theorem exact_read (xs : Pending) (i : Nat) (y : BitVec LW) :
    (scalar i).read ((lowerPending xs).apply y)=
      match xs.find? (fun w => w.1==i) with
      | none => (scalar i).read y
      | some w => BitVec.ofNat _ w.2 := by
  induction xs with
  | nil =>
    simp [lowerPending,fuse,Patch.empty,Patch.apply]
  | cons w xs ih =>
    rcases w with ⟨a,v⟩
    rw [lower_cons,Patch.compose_apply]
    by_cases E : a=i
    · subst a
      simp [writeScalar,Field.read_assign]
    · rw [show (scalar i).read ((writeScalar a v).apply ((lowerPending xs).apply y)) =
          (scalar i).read ((lowerPending xs).apply y) from
          Field.read_other_assign _ _ _ _ (scalar_distinct i a (Ne.symm E))]
      simpa [E] using ih

theorem exact_nat (xs : Pending) (i : Nat) (y : BitVec LW)
    (fit : ∀ w∈xs, w.1=i → w.2<2^(widthAt scalarWidths i)) :
    source ((lowerPending xs).apply y) i=newest y xs i := by
  unfold source newest
  rw [exact_read]
  cases H : xs.find? (fun w => w.1==i) with
  | none => rfl
  | some w =>
    have A := List.mem_of_find?_eq_some H
    have B := List.find?_some H
    exact Nat.mod_eq_of_lt (fit w A (beq_iff_eq.mp B))

theorem schedule_scalar (op i : Nat) (y : BitVec LW) :
    (scalar i).read ((schedule op).apply y)=(scalar i).read y := by
  have L := scalar_before_choice i
  have R : 1764≤(scalar i).offset := by
    simp [scalar]
  unfold schedule BStarLongToken.setToken
  rw [Patch.compose_apply,Patch.compose_apply,
    Field.read_other_assign _ _ _ _ (.inr (by exact R)),
    Field.read_other_assign _ _ _ _ (.inl (Nat.le_trans L (by decide))),
    Field.read_other_assign _ _ _ _ (.inl (Nat.le_trans L (by decide)))]

/-- For the actual nonfinal ACCEPT patch, read back all the exact
pending scalar fields. If no pending write targets i, this observes
the application base y, not merely the old input captured by the row. -/
theorem accept_read {old y : BitVec LW} {op : Nat} {p : BStarLongToken.Payload}
    {j : Nat} {c : L4.Compiler.Native.Code}
    (N : nodeOf op=some j) (G : get j=some c) (H : op<407) (i : Nat) :
    let pending := (nodeResult old p.argument.toNat c).toList.map (fun v => (j,v))
    let xs := aliases old (j+1) (L4.Compiler.Native.literal.drop (j+1)) pending
    (scalar i).read ((acceptFile old op p).apply y)=
      match xs.find? (fun w => w.1==i) with
      | none => (scalar i).read y
      | some w => BitVec.ofNat _ w.2 := by
  dsimp only
  rw [BStarAliasFold.accept_nonfinal old op p j c N G H,Patch.compose_apply,schedule_scalar]
  exact exact_read _ _ _

end L4.BStarAliasReadback
