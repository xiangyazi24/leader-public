import Leader.PPL.Elim.RowE
import Leader.Wu.Elimination.ArbitraryInputExpectedCost
import Init.Omega

/-!
# LD(736): local geometry and non-vacuous domain

This file fixes the literal four-field Algorithm-5 process used by the LD
development.  Tags are positions from the initial configuration; they are not
recomputed after later deletions.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

abbrev Config (n : Nat) := Fin n → PPL.Elim.Cell4

def stepE {n : Nat} (ring : DirectedRing n) :
    Config n → Fin n → Config n :=
  fun C e => PopulationProtocol.step PPL.Elim.protocolE ring C e

/-- Clockwise position after t physical ring edges. -/
def advance {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (t : Nat) : Fin n :=
  ⟨(i.val + t) % n, Nat.mod_lt _ ring.hn⟩

@[simp] theorem advance_zero {n : Nat}
    (ring : DirectedRing n) (i : Fin n) :
    advance ring i 0 = i := by
  apply Fin.ext
  simp [advance, Nat.mod_eq_of_lt i.isLt]

theorem advance_add {n : Nat}
    (ring : DirectedRing n) (i : Fin n) (a b : Nat) :
    advance ring (advance ring i a) b =
      advance ring i (a + b) := by
  apply Fin.ext
  unfold advance
  dsimp only
  rw [Nat.mod_add_mod]
  congr 1
  omega

structure SectorFrame {n : Nat}
    (ring : DirectedRing n) (C : Config n) where
  left : Fin n
  right : Fin n
  gap : Nat
  gap_pos : 0 < gap
  gap_lt_n : gap < n
  left_ne_right : left ≠ right
  right_eq : advance ring left gap = right
  left_leader : (C left).leader = true
  right_leader : (C right).leader = true
  interior_follower :
    ∀ q, 0 < q → q < gap →
      (C (advance ring left q)).leader = false

structure TripleFrame {n : Nat}
    (ring : DirectedRing n) (C : Config n) where
  i : Fin n
  j : Fin n
  k : Fin n
  a : Nat
  b : Nat
  A : SectorFrame ring C
  B : SectorFrame ring C
  A_left : A.left = i
  A_right : A.right = j
  A_gap : A.gap = a
  B_left : B.left = j
  B_right : B.right = k
  B_gap : B.gap = b
  span :
    (i = k ∧ a + b = n) ∨
    (i ≠ k ∧ a + b < n)

def TaggedDeleted {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) : Prop :=
  (C F.i).leader = false ∨
  (C F.j).leader = false ∨
  (C F.k).leader = false

/-- Row E never creates a leader at a site whose leader bit was false. -/
theorem stepE_leader_false_of_false
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (e k : Fin n)
    (hk : (C k).leader = false) :
    ((stepE ring C e) k).leader = false := by
  by_cases hke : k = e
  · subst k
    simpa [stepE, PopulationProtocol.step, PPL.Elim.protocolE] using hk
  · by_cases hkr : k = ring.rightNeighbor e
    · subst k
      have hr :
          (C (ring.rightNeighbor e)).leader = false := hk
      simpa [stepE, PopulationProtocol.step, PPL.Elim.protocolE, hke] using
        (PPL.Elim.rowE_right_leader_false_of_false
          (C e) (C (ring.rightNeighbor e)) hr)
    · simpa [stepE, PopulationProtocol.step, PPL.Elim.protocolE, hke, hkr] using hk

/-- Fixed tagged deletion is absorbing under the literal row E. -/
theorem taggedDeleted_step
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0)
    (C : Config n) (e : Fin n)
    (h : TaggedDeleted F C) :
    TaggedDeleted F (stepE ring C e) := by
  rcases h with hi | hj | hk
  · exact Or.inl
      (stepE_leader_false_of_false ring C e F.i hi)
  · exact Or.inr <| Or.inl
      (stepE_leader_false_of_false ring C e F.j hj)
  · exact Or.inr <| Or.inr
      (stepE_leader_false_of_false ring C e F.k hk)

/-- Before the tagged stopping event all three tagged positions are leaders.
In the two-leader case i=k this simply repeats the same surviving bit. -/
theorem tagged_alive_of_not_deleted
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (C : Config n)
    (h : ¬ TaggedDeleted F C) :
    (C F.i).leader = true ∧
      (C F.j).leader = true ∧
      (C F.k).leader = true := by
  constructor
  · cases hi : (C F.i).leader with
    | false => exact (h (Or.inl hi)).elim
    | true => rfl
  constructor
  · cases hj : (C F.j).leader with
    | false => exact (h (Or.inr (Or.inl hj))).elim
    | true => rfl
  · cases hk : (C F.k).leader with
    | false => exact (h (Or.inr (Or.inr hk))).elim
    | true => rfl

/-- A false leader bit remains false along every row-E execution. -/
theorem leader_false_reachable
    {n : Nat} (ring : DirectedRing n)
    {C D : Config n}
    (hr : PopulationProtocol.Reachable PPL.Elim.protocolE ring C D)
    (k : Fin n) (hk : (C k).leader = false) :
    (D k).leader = false := by
  have key : ∀ X Y : PopulationProtocol.Configuration PPL.Elim.protocolE n,
      PopulationProtocol.Reachable PPL.Elim.protocolE ring X Y →
      ((show Config n from X) k).leader = false →
      ((show Config n from Y) k).leader = false := by
    intro X Y h
    induction h with
    | refl => exact id
    | step Y Z hXY hYZ ih =>
        intro hX
        rcases hYZ with ⟨e, rfl⟩
        exact stepE_leader_false_of_false ring Y e k (ih hX)
  exact key C D hr hk

/-- Until a tagged deletion, the two initially consecutive sector interiors
remain follower-only because row E has no leader creation. -/
theorem tagged_consecutive_preserved_until_delete
    {n : Nat} {ring : DirectedRing n} {C0 C : Config n}
    (F : TripleFrame ring C0)
    (hr : PopulationProtocol.Reachable PPL.Elim.protocolE ring C0 C)
    (hdel : ¬ TaggedDeleted F C) :
    (C F.i).leader = true ∧
      (C F.j).leader = true ∧
      (C F.k).leader = true ∧
      (∀ q, 0 < q → q < F.a →
        (C (advance ring F.i q)).leader = false) ∧
      (∀ q, 0 < q → q < F.b →
        (C (advance ring F.j q)).leader = false) := by
  have halive := tagged_alive_of_not_deleted F C hdel
  refine ⟨halive.1, halive.2.1, halive.2.2, ?_, ?_⟩
  · intro q hq0 hqa
    have hinit :
        (C0 (advance ring F.i q)).leader = false := by
      rw [← F.A_left]
      exact F.A.interior_follower q hq0
        (by simpa [F.A_gap] using hqa)
    exact leader_false_reachable ring hr _ hinit
  · intro q hq0 hqb
    have hinit :
        (C0 (advance ring F.j q)).leader = false := by
      rw [← F.B_left]
      exact F.B.interior_follower q hq0
        (by simpa [F.B_gap] using hqb)
    exact leader_false_reachable ring hr _ hinit

/-- Two leaders at physical sites 0 and 1, with no bullets or signals. -/
def twoLeaderFixture {n : Nat} (hn : 2 ≤ n) : Config n :=
  fun i =>
    { leader :=
        if i.val = 0 then true
        else if i.val = 1 then true
        else false
      bullet := (0 : Fin 3)
      shield := false
      signalB := false }

theorem twoLeaderFixture_pb
    {n : Nat} (hn : 2 ≤ n) (ring : DirectedRing n) :
    PPL.Elim.PB ring (twoLeaderFixture hn) := by
  constructor
  · exact ⟨⟨0, by omega⟩, by simp [twoLeaderFixture]⟩
  · intro i hlive
    simp [twoLeaderFixture] at hlive

theorem twoLeaderFixture_count
    {n : Nat} (hn : 2 ≤ n) :
    PPL.Elim.leaderCount (twoLeaderFixture hn) = 2 := by
  cases n with
  | zero =>
      omega
  | succ n =>
      cases n with
      | zero =>
          omega
      | succ m =>
          change
            (List.ofFn (fun i : Fin (Nat.succ (Nat.succ m)) =>
              if (twoLeaderFixture hn i).leader then 1 else 0)).sum = 2
          rw [List.ofFn_succ, List.sum_cons,
            List.ofFn_succ, List.sum_cons]
          have hz :
              (List.ofFn (fun i : Fin m =>
                if (twoLeaderFixture hn i.succ.succ).leader
                then 1 else 0)).sum = 0 := by
            calc
              _ = (List.ofFn (fun _ : Fin m => 0)).sum := by
                apply FiniteUniformStoppingTree.ofFn_sum_eq
                intro i
                simp [twoLeaderFixture]
              _ = 0 := by
                rw [FiniteUniformStoppingTree.ofFn_sum_const]
                simp
          rw [hz]
          simp [twoLeaderFixture]

/-- Canonical i=k two-leader frame for the non-vacuity witness. -/
def twoLeaderFrame {n : Nat} (hn : 2 ≤ n)
    (ring : DirectedRing n) :
    TripleFrame ring (twoLeaderFixture hn) := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  let A : SectorFrame ring (twoLeaderFixture hn) := {
    left := z
    right := o
    gap := 1
    gap_pos := by omega
    gap_lt_n := by omega
    left_ne_right := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [z, o] at hv
      omega
    right_eq := by
      apply Fin.ext
      simp [advance, z, o, Nat.mod_eq_of_lt (by omega : 1 < n)]
    left_leader := by
      simp [twoLeaderFixture, z]
    right_leader := by
      simp [twoLeaderFixture, o]
    interior_follower := by
      intro q hq0 hq1
      omega
  }
  let B : SectorFrame ring (twoLeaderFixture hn) := {
    left := o
    right := z
    gap := n - 1
    gap_pos := by omega
    gap_lt_n := by omega
    left_ne_right := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [z, o] at hv
      omega
    right_eq := by
      apply Fin.ext
      have hsum : 1 + (n - 1) = n := by omega
      simp [advance, z, o, hsum]
    left_leader := by
      simp [twoLeaderFixture, o]
    right_leader := by
      simp [twoLeaderFixture, z]
    interior_follower := by
      intro q hq0 hq
      have hlt : 1 + q < n := by omega
      simp [twoLeaderFixture, advance, o,
        Nat.mod_eq_of_lt hlt,
        show 1 + q ≠ 0 by omega,
        show 1 + q ≠ 1 by omega] <;> omega
  }
  exact {
    i := z
    j := o
    k := z
    a := 1
    b := n - 1
    A := A
    B := B
    A_left := rfl
    A_right := rfl
    A_gap := rfl
    B_left := rfl
    B_right := rfl
    B_gap := rfl
    span := Or.inl ⟨rfl, by omega⟩
  }

theorem ldDomain_nonempty
    {n : Nat} (hn : 2 ≤ n) (ring : DirectedRing n) :
    ∃ C : Config n,
      PPL.Elim.PB ring C ∧
      2 ≤ PPL.Elim.leaderCount C ∧
      ∃ F : TripleFrame ring C, F.i = F.k := by
  refine ⟨twoLeaderFixture hn, twoLeaderFixture_pb hn ring, ?_, ?_⟩
  · rw [twoLeaderFixture_count hn]; exact Nat.le_refl 2
  · exact ⟨twoLeaderFrame hn ring, rfl⟩

/-- Exact finite-word public LD(736) target.  This file only names the
statement; the proof is the later Wave-5 composition. -/
def LD736Statement : Prop :=
  ∀ {n : Nat} (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Config n),
    PPL.Elim.PB ring C →
    2 ≤ PPL.Elim.leaderCount C →
    ∀ F : TripleFrame ring C,
    ∀ T : Nat,
      K2ArbitraryElimination.FiniteAccounting.costNumerator
          (stepE ring) (TaggedDeleted F) C T ≤
        n ^ T * (736 * n * (F.a + F.b))

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.advance_zero
#print axioms PPL.Convergence.LDLocal.advance_add
#print axioms PPL.Convergence.LDLocal.stepE_leader_false_of_false
#print axioms PPL.Convergence.LDLocal.taggedDeleted_step
#print axioms PPL.Convergence.LDLocal.tagged_alive_of_not_deleted
#print axioms PPL.Convergence.LDLocal.leader_false_reachable
#print axioms PPL.Convergence.LDLocal.tagged_consecutive_preserved_until_delete
#print axioms PPL.Convergence.LDLocal.twoLeaderFixture_pb
#print axioms PPL.Convergence.LDLocal.twoLeaderFixture_count
#print axioms PPL.Convergence.LDLocal.ldDomain_nonempty

