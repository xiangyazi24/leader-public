import Leader.L4.Compiler.NativeSpec

/-!
# The synchronous logical height round (shared definitions)

Every Height module imports this file. The phase semantics is the accepted
`phaseUpdate` of NativeSpec; a logical round applies phases 0..5 in order,
each synchronously on the m-cycle (every site reads the OLD snapshots of
that phase). Bits are one fair bit per site per round; only phase 1 reads
them.
-/

namespace L4.Height

open L4.Compiler.Native

/-- Cyclic predecessor on `Fin m`. -/
def left {m : Nat} (hm : 0 < m) (i : Fin m) : Fin m :=
  ⟨(i.val + m - 1) % m, Nat.mod_lt _ hm⟩

/-- Cyclic successor on `Fin m`. -/
def right {m : Nat} (hm : 0 < m) (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩

/-- One synchronous phase. -/
def phaseStep {m : Nat} (B j : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) : Fin m → Snapshot :=
  fun i => phaseUpdate B j (s (left hm i)) (s i) (s (right hm i)) (bits i)

/-- Phases 0..5 in order with one bit vector. -/
def logicalRound {m : Nat} (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (s : Fin m → Snapshot) : Fin m → Snapshot :=
  phaseStep B 5 hm bits (phaseStep B 4 hm bits (phaseStep B 3 hm bits
    (phaseStep B 2 hm bits (phaseStep B 1 hm bits (phaseStep B 0 hm bits s)))))

/-- Rounds driven by a list of bit vectors, first element first. -/
def runRounds {m : Nat} (B : Nat) (hm : 0 < m) :
    List (Fin m → Bool) → (Fin m → Snapshot) → (Fin m → Snapshot)
  | [], s => s
  | bits :: bs, s => runRounds B hm bs (logicalRound B hm bits s)

/-- The anchor predicate computed by phase 0. -/
def IsAnchor {m : Nat} (hm : 0 < m) (s : Fin m → Snapshot) (i : Fin m) : Prop :=
  (s i).x ≤ (s (left hm i)).x

instance {m : Nat} (hm : 0 < m) (s : Fin m → Snapshot) (i : Fin m) :
    Decidable (IsAnchor hm s i) := by
  unfold IsAnchor; exact inferInstance

/-- Number of anchors. -/
def anchorCount {m : Nat} (hm : 0 < m) (s : Fin m → Snapshot) : Nat :=
  (List.finRange m).countP (fun i => decide (IsAnchor hm s i))

/-- Heights are below the height modulus. -/
def Bounded {m : Nat} (B : Nat) (s : Fin m → Snapshot) : Prop :=
  ∀ i, (s i).x < B

/-- The bit vector encoded by a letter of `Fin (2^m)`; uniform letters give
independent fair bits. -/
def bitsOf {m : Nat} (e : Fin (2 ^ m)) : Fin m → Bool :=
  fun i => e.val.testBit i.val

/-- The logical chain over the alphabet `Fin (2^m)`. -/
def heightChain {m : Nat} (B : Nat) (hm : 0 < m) :
    (Fin m → Snapshot) → Fin (2 ^ m) → (Fin m → Snapshot) :=
  fun s e => logicalRound B hm (bitsOf e) s

theorem runRounds_nil {m : Nat} (B : Nat) (hm : 0 < m) (s : Fin m → Snapshot) :
    runRounds B hm [] s = s := rfl

theorem runRounds_cons {m : Nat} (B : Nat) (hm : 0 < m) (bits : Fin m → Bool)
    (bs : List (Fin m → Bool)) (s : Fin m → Snapshot) :
    runRounds B hm (bits :: bs) s = runRounds B hm bs (logicalRound B hm bits s) := rfl

end L4.Height

#print axioms L4.Height.runRounds_cons
