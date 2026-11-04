import Leader.Wu.Elimination.SinkGapCleanup
open LDSinkGapCleanup

/-!
# Geometry for two adjacent sink gaps

Clockwise order:

  recovery.pos 0 -- recovery --> shared -- attack --> attack.pos attack.d

The only additional geometric assumptions are the shared endpoint and
`recovery.d + attack.d < n`. Ring equality, injectivity, and all separation
facts are derived; there is no opaque disjointness field.

The offset-injectivity helper below proves the full range `t < n` directly
from `GapFrame.pos`. This also covers the concatenated arc, whose offsets
can exceed the individual recovery gap's `d`.

`TargetDummyNormal` has an explicit `hψ` argument because `GapInvariant`
has that argument. It asserts no live recovery bullet and the attack
invariant, not the recovery invariant or preservation of dummy-normality.

All framing statements quantify over bounded gap offsets. An attack edge
incident to the shared node need not frame that node; the separate
away-from-shared lemma includes it when both attack endpoints avoid it.

There is no probabilistic or renewal-progress argument in this file.
-/

namespace LDTwoGapFrame

set_option autoImplicit false

/-- Two clockwise adjacent gaps whose combined arc is shorter than the ring.
The lower bounds on both lengths are already fields of `GapFrame`. -/
structure TwoGapFrame (n : Nat) where
  recovery : GapFrame n
  attack : GapFrame n
  shared : recovery.pos recovery.d = attack.pos 0
  length_lt : recovery.d + attack.d < n

variable {n ψ : Nat}

/-! ## The common ring and coordinate arithmetic -/

private theorem directedRing_eq (R R' : DirectedRing n) : R = R' := by
  cases R
  cases R'
  rfl

/-- `DirectedRing n` stores only the proof that `n` is positive, so the two
frames necessarily use the same physical ring. -/
theorem TwoGapFrame.same_ring (F : TwoGapFrame n) :
    F.recovery.ring = F.attack.ring :=
  directedRing_eq _ _

/-- The shared recovery shooter is the attack victim. -/
theorem shared_is_attack_victim (F : TwoGapFrame n) :
    F.attack.pos 0 = F.recovery.pos F.recovery.d :=
  F.shared.symm

private theorem mod_add_left (a b m : Nat) :
    (a % m + b) % m = (a + b) % m := by
  rw [Nat.add_mod (a % m) b m, Nat.mod_mod]
  exact (Nat.add_mod a b m).symm

private theorem gap_pos_zero (G : GapFrame n) : G.pos 0 = G.low := by
  apply Fin.ext
  change (G.low.val + 0) % n = G.low.val
  simp only [Nat.add_zero, Nat.mod_eq_of_lt G.low.isLt]

/-- Adding the complementary offset recovers every offset below `n`. -/
private theorem pos_offset_cancel (G : GapFrame n) (t : Nat) (ht : t < n) :
    ((G.pos t).val + (n - G.low.val)) % n = t := by
  change ((G.low.val + t) % n + (n - G.low.val)) % n = t
  rw [mod_add_left]
  have hlow : G.low.val < n := G.low.isLt
  have hsum : G.low.val + t + (n - G.low.val) = n + t := by
    omega
  rw [hsum, Nat.add_mod n t n, Nat.mod_self, Nat.zero_add,
    Nat.mod_mod, Nat.mod_eq_of_lt ht]

/-- Full-ring offset injectivity, derived from the concrete modular positions.
No hypothesis about leaders or the configuration is used. -/
theorem pos_injective_below_n (G : GapFrame n) (i j : Nat)
    (hi : i < n) (hj : j < n) (hpos : G.pos i = G.pos j) :
    i = j := by
  calc
    i = ((G.pos i).val + (n - G.low.val)) % n :=
      (pos_offset_cancel G i hi).symm
    _ = ((G.pos j).val + (n - G.low.val)) % n :=
      congrArg (fun z : Fin n => (z.val + (n - G.low.val)) % n) hpos
    _ = j := pos_offset_cancel G j hj

/-- Moving one physical edge increases the clockwise offset by one. -/
theorem gap_rightNeighbor_pos (G : GapFrame n) (t : Nat) :
    G.ring.rightNeighbor (G.pos t) = G.pos (t + 1) := by
  apply Fin.ext
  change ((G.low.val + t) % n + 1) % n =
    (G.low.val + (t + 1)) % n
  simpa only [Nat.add_assoc] using mod_add_left (G.low.val + t) 1 n

/-- Attack coordinates are recovery coordinates shifted by the recovery
length. This identity also holds for offsets outside the two gap sectors. -/
theorem TwoGapFrame.attack_pos_eq_recovery_offset (F : TwoGapFrame n)
    (t : Nat) :
    F.attack.pos t = F.recovery.pos (F.recovery.d + t) := by
  have hlow : F.attack.low = F.recovery.pos F.recovery.d :=
    (gap_pos_zero F.attack).symm.trans F.shared.symm
  have hval : F.attack.low.val =
      (F.recovery.low.val + F.recovery.d) % n :=
    congrArg Fin.val hlow
  apply Fin.ext
  change (F.attack.low.val + t) % n =
    (F.recovery.low.val + (F.recovery.d + t)) % n
  rw [hval]
  simpa only [Nat.add_assoc] using
    mod_add_left (F.recovery.low.val + F.recovery.d) t n

/-! ## Derived injectivity and the unique overlap -/

/-- Every position on the concatenated arc has a unique offset. -/
theorem TwoGapFrame.combined_pos_injective (F : TwoGapFrame n)
    (i j : Nat)
    (hi : i ≤ F.recovery.d + F.attack.d)
    (hj : j ≤ F.recovery.d + F.attack.d)
    (hpos : F.recovery.pos i = F.recovery.pos j) :
    i = j :=
  pos_injective_below_n F.recovery i j
    (Nat.lt_of_le_of_lt hi F.length_lt)
    (Nat.lt_of_le_of_lt hj F.length_lt) hpos

/-- The recovery gap's closed interval has no repeated position. -/
theorem TwoGapFrame.recovery_pos_injective (F : TwoGapFrame n)
    (i j : Nat) (hi : i ≤ F.recovery.d) (hj : j ≤ F.recovery.d)
    (hpos : F.recovery.pos i = F.recovery.pos j) :
    i = j :=
  pos_injective_below_n F.recovery i j
    (Nat.lt_of_le_of_lt hi F.recovery.hdn)
    (Nat.lt_of_le_of_lt hj F.recovery.hdn) hpos

/-- The attack gap's closed interval has no repeated position. -/
theorem TwoGapFrame.attack_pos_injective (F : TwoGapFrame n)
    (i j : Nat) (hi : i ≤ F.attack.d) (hj : j ≤ F.attack.d)
    (hpos : F.attack.pos i = F.attack.pos j) :
    i = j :=
  pos_injective_below_n F.attack i j
    (Nat.lt_of_le_of_lt hi F.attack.hdn)
    (Nat.lt_of_le_of_lt hj F.attack.hdn) hpos

/-- The exact cross-gap intersection: only recovery offset `d` and attack
 offset `0` can denote the same cell. This is a theorem, not a frame field. -/
theorem TwoGapFrame.only_shared_endpoint (F : TwoGapFrame n)
    (i j : Nat) (hi : i ≤ F.recovery.d) (hj : j ≤ F.attack.d) :
    F.recovery.pos i = F.attack.pos j ↔ i = F.recovery.d ∧ j = 0 := by
  constructor
  · intro heq
    have heq' : F.recovery.pos i =
        F.recovery.pos (F.recovery.d + j) :=
      heq.trans (F.attack_pos_eq_recovery_offset j)
    have hoff : i = F.recovery.d + j :=
      F.combined_pos_injective i (F.recovery.d + j)
        (by omega) (by omega) heq'
    omega
  · intro h
    rcases h with ⟨hi', hj'⟩
    subst i
    subst j
    exact F.shared

/-- Recovery `0..d` and attack `1..d` are disjoint. -/
theorem TwoGapFrame.recovery_ne_attack_positive (F : TwoGapFrame n)
    (i j : Nat) (hi : i ≤ F.recovery.d)
    (hj0 : 1 ≤ j) (hj : j ≤ F.attack.d) :
    F.recovery.pos i ≠ F.attack.pos j := by
  intro heq
  have h := (F.only_shared_endpoint i j hi hj).mp heq
  omega

/-- Every recovery position strictly before the shared node is disjoint
from the entire attack gap, including attack offset zero. -/
theorem TwoGapFrame.recovery_before_shared_ne_attack (F : TwoGapFrame n)
    (i j : Nat) (hi : i < F.recovery.d) (hj : j ≤ F.attack.d) :
    F.recovery.pos i ≠ F.attack.pos j := by
  intro heq
  have h := (F.only_shared_endpoint i j (by omega) hj).mp heq
  omega

/-! ## Configuration predicates -/

/-- No live bullet in the recovery sector, and the attack gap satisfies its
existing invariant. This definition alone asserts no dynamic closure. -/
def TargetDummyNormal (hψ : ψ > 0) (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) : Prop :=
  (∀ t, 1 ≤ t → t ≤ F.recovery.d →
    (C (F.recovery.pos t)).bullet ≠ ⟨2, by omega⟩) ∧
  GapInvariant hψ F.attack C

/-- This is the requested coarse stopping set. In particular, a blocked
attack is included through `GapDone`; it is not asserted to be a deletion. -/
def TwoGapDone (F : TwoGapFrame n) (C : Fin n → AgentState ψ) : Prop :=
  GapDone F.attack C ∨ EndpointDeleted F.recovery C

theorem targetDummyNormal_attack_invariant (hψ : ψ > 0)
    (F : TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hNormal : TargetDummyNormal hψ F C) :
    GapInvariant hψ F.attack C :=
  hNormal.2

/-- Dummy-normality rules out a blocked recovery gap at this configuration.
This is not a claim that later configurations remain dummy-normal. -/
theorem targetDummyNormal_not_recovery_blocked (hψ : ψ > 0)
    (F : TwoGapFrame n) (C : Fin n → AgentState ψ)
    (hNormal : TargetDummyNormal hψ F C) :
    ¬ GapBlocked F.recovery C := by
  intro hBlocked
  have hOne : 1 ≤ F.recovery.d := by
    have hd := F.recovery.hd
    omega
  exact hNormal.1 1 (Nat.le_refl 1) hOne hBlocked.1

/-! ## Physical edge framing -/

/-- The gap record selects coordinates, not a different physical kernel. -/
theorem TwoGapFrame.sinkStep_eq (hψ : ψ > 0) (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStep hψ F.recovery C e = sinkStep hψ F.attack C e := by
  unfold sinkStep
  rw [F.same_ring]

/-- Every recovery gap edge frames the positive attack sector. This is
stronger than requiring both recovery endpoints to have offsets below `d`:
the last recovery edge, which touches the shared node, is allowed too. -/
theorem recovery_edge_frames_attack_interior (hψ : ψ > 0)
    (F : TwoGapFrame n) (C : Fin n → AgentState ψ) (k t : Nat)
    (hk : k < F.recovery.d) (ht0 : 1 ≤ t) (ht : t ≤ F.attack.d) :
    sinkStep hψ F.recovery C (F.recovery.pos k) (F.attack.pos t) =
      C (F.attack.pos t) := by
  apply sinkStep_other hψ F.recovery C
    (F.recovery.pos k) (F.attack.pos t)
  · intro heq
    exact F.recovery_ne_attack_positive k t (Nat.le_of_lt hk) ht0 ht heq.symm
  · rw [gap_rightNeighbor_pos F.recovery k]
    intro heq
    exact F.recovery_ne_attack_positive (k + 1) t (by omega) ht0 ht heq.symm

/-- Every attack gap edge frames all recovery positions strictly before the
shared node. This includes the recovery interior and its left endpoint.
The shared node itself is deliberately excluded when `k = 0` is allowed. -/
theorem attack_edge_frames_recovery_interior (hψ : ψ > 0)
    (F : TwoGapFrame n) (C : Fin n → AgentState ψ) (k t : Nat)
    (hk : k < F.attack.d) (ht : t < F.recovery.d) :
    sinkStep hψ F.attack C (F.attack.pos k) (F.recovery.pos t) =
      C (F.recovery.pos t) := by
  apply sinkStep_other hψ F.attack C
    (F.attack.pos k) (F.recovery.pos t)
  · exact F.recovery_before_shared_ne_attack t k ht (Nat.le_of_lt hk)
  · rw [gap_rightNeighbor_pos F.attack k]
    exact F.recovery_before_shared_ne_attack t (k + 1) ht (by omega)

/-- If both recovery edge endpoints have offsets strictly below `d`, the
whole attack gap is framed, including the shared victim at offset zero. -/
theorem recovery_edge_away_from_shared_frames_attack_gap (hψ : ψ > 0)
    (F : TwoGapFrame n) (C : Fin n → AgentState ψ) (k t : Nat)
    (hk : k + 1 < F.recovery.d) (ht : t ≤ F.attack.d) :
    sinkStep hψ F.recovery C (F.recovery.pos k) (F.attack.pos t) =
      C (F.attack.pos t) := by
  apply sinkStep_other hψ F.recovery C
    (F.recovery.pos k) (F.attack.pos t)
  · intro heq
    exact F.recovery_before_shared_ne_attack k t (by omega) ht heq.symm
  · rw [gap_rightNeighbor_pos F.recovery k]
    intro heq
    exact F.recovery_before_shared_ne_attack (k + 1) t hk ht heq.symm

/-- The symmetric away-from-shared statement: a positive attack edge frames
the whole recovery gap, including its shared shooter. -/
theorem attack_edge_away_from_shared_frames_recovery_gap (hψ : ψ > 0)
    (F : TwoGapFrame n) (C : Fin n → AgentState ψ) (k t : Nat)
    (hk0 : 1 ≤ k) (hk : k < F.attack.d) (ht : t ≤ F.recovery.d) :
    sinkStep hψ F.attack C (F.attack.pos k) (F.recovery.pos t) =
      C (F.recovery.pos t) := by
  apply sinkStep_other hψ F.attack C
    (F.attack.pos k) (F.recovery.pos t)
  · exact F.recovery_ne_attack_positive t k ht hk0 (Nat.le_of_lt hk)
  · rw [gap_rightNeighbor_pos F.attack k]
    exact F.recovery_ne_attack_positive t (k + 1) ht (by omega) (by omega)

/-! ## The blocked attack is blocked at the shared node -/

theorem blocked_attack_victim_is_shared (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) (hBlocked : GapBlocked F.attack C) :
    (C (F.recovery.pos F.recovery.d)).shield = true ∨
      (C (F.recovery.pos F.recovery.d)).signal_B = ⟨1, by omega⟩ := by
  have hProtected :
      (C (F.attack.pos 0)).shield = true ∨
        (C (F.attack.pos 0)).signal_B = ⟨1, by omega⟩ :=
    hBlocked.2.2
  simpa only [shared_is_attack_victim F] using hProtected

/-- A blocked attack belongs to the coarse stopping set by definition. -/
theorem blocked_attack_twoGapDone (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) (hBlocked : GapBlocked F.attack C) :
    TwoGapDone F C :=
  Or.inl (Or.inr (Or.inr hBlocked))

end LDTwoGapFrame

#print axioms LDTwoGapFrame.TwoGapFrame.same_ring
#print axioms LDTwoGapFrame.shared_is_attack_victim
#print axioms LDTwoGapFrame.pos_injective_below_n
#print axioms LDTwoGapFrame.gap_rightNeighbor_pos
#print axioms LDTwoGapFrame.TwoGapFrame.attack_pos_eq_recovery_offset
#print axioms LDTwoGapFrame.TwoGapFrame.combined_pos_injective
#print axioms LDTwoGapFrame.TwoGapFrame.recovery_pos_injective
#print axioms LDTwoGapFrame.TwoGapFrame.attack_pos_injective
#print axioms LDTwoGapFrame.TwoGapFrame.only_shared_endpoint
#print axioms LDTwoGapFrame.TwoGapFrame.recovery_ne_attack_positive
#print axioms LDTwoGapFrame.TwoGapFrame.recovery_before_shared_ne_attack
#print axioms LDTwoGapFrame.targetDummyNormal_attack_invariant
#print axioms LDTwoGapFrame.targetDummyNormal_not_recovery_blocked
#print axioms LDTwoGapFrame.TwoGapFrame.sinkStep_eq
#print axioms LDTwoGapFrame.recovery_edge_frames_attack_interior
#print axioms LDTwoGapFrame.attack_edge_frames_recovery_interior
#print axioms LDTwoGapFrame.recovery_edge_away_from_shared_frames_attack_gap
#print axioms LDTwoGapFrame.attack_edge_away_from_shared_frames_recovery_gap
#print axioms LDTwoGapFrame.blocked_attack_victim_is_shared
#print axioms LDTwoGapFrame.blocked_attack_twoGapDone
