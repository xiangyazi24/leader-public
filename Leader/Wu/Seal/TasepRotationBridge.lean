import Leader.Wu.Seal.TasepSliceNormalization

/-!
# Cyclic-coordinate bridge for the seal-sweep TASEP slice

`PPartialSealSweepTasepMixingFirstBrickSol` counts the marked event in the
canonical list coordinates zero and one.  A protocol collision, however, is
attached to an arbitrary directed ring edge `e -> ring.rightNeighbor e`.

This module supplies only the missing deterministic coordinate bridge.  It
rotates a Boolean front configuration so that the chosen directed edge becomes
the first two `List.ofFn` coordinates, constructs the inverse rotation, and
proves that front mass is unchanged.  Consequently the exact canonical
marked-word predicate from the first finite-slice brick is equivalent to the
marked event on any directed cyclic edge.

No mixing estimate, AB-production statement, or carrier-to-TASEP transfer is
claimed here.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepTasepRotationBridgeSol

open PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepMixingFirstBrickSol

set_option autoImplicit false

/-! ## Concrete clockwise coordinate rotation -/

/-- Reindex a front configuration clockwise from `edge`.

Coordinate `i` in the rotated configuration reads the original site reached
after `i.val` clockwise edges from `edge`.  Thus rotated coordinates zero and
one are exactly the initiator and responder of the chosen directed edge. -/
def rotateFrontConfigFrom
    {n : Nat} (ring : DirectedRing n) (edge : Fin n)
    (C : Fin n → Bool) : Fin n → Bool :=
  fun i => C (cwPos ring edge i.val)

/-- The coordinate of an original site when the ring is viewed clockwise from
`edge`.  Its value is the canonical clockwise distance from `edge`. -/
def frontIndexFrom
    {n : Nat} (ring : DirectedRing n) (edge i : Fin n) : Fin n :=
  ⟨cwDist ring edge i, cwDist_lt ring edge i⟩

/-- Explicit inverse of `rotateFrontConfigFrom`. -/
def unrotateFrontConfigFrom
    {n : Nat} (ring : DirectedRing n) (edge : Fin n)
    (D : Fin n → Bool) : Fin n → Bool :=
  fun i => D (frontIndexFrom ring edge i)

/-- Rotated coordinate zero is the initiator of the selected edge. -/
@[simp] theorem rotateFrontConfigFrom_zero
    {n : Nat} (ring : DirectedRing n) (edge : Fin n)
    (C : Fin n → Bool) :
    rotateFrontConfigFrom ring edge C ⟨0, ring.hn⟩ = C edge := by
  simp [rotateFrontConfigFrom]

/-- On a nontrivial ring, rotated coordinate one is the responder of the
selected edge. -/
theorem rotateFrontConfigFrom_one
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n) (edge : Fin n)
    (C : Fin n → Bool) :
    rotateFrontConfigFrom ring edge C ⟨1, by omega⟩ =
      C (ring.rightNeighbor edge) := by
  change C (cwPos ring edge 1) = C (ring.rightNeighbor edge)
  simpa using congrArg C (cwPos_rightNeighbor ring edge 0).symm

/-- Clockwise distance is the left inverse of clockwise position. -/
@[simp] theorem unrotateFrontConfigFrom_rotateFrontConfigFrom
    {n : Nat} (ring : DirectedRing n) (edge : Fin n)
    (C : Fin n → Bool) :
    unrotateFrontConfigFrom ring edge
        (rotateFrontConfigFrom ring edge C) = C := by
  funext i
  simp [unrotateFrontConfigFrom, rotateFrontConfigFrom, frontIndexFrom,
    cwPos_cwDist]

/-- Bounded uniqueness of clockwise distance gives the converse inverse
identity. -/
@[simp] theorem rotateFrontConfigFrom_unrotateFrontConfigFrom
    {n : Nat} (ring : DirectedRing n) (edge : Fin n)
    (D : Fin n → Bool) :
    rotateFrontConfigFrom ring edge
        (unrotateFrontConfigFrom ring edge D) = D := by
  funext i
  change
    D (frontIndexFrom ring edge (cwPos ring edge i.val)) = D i
  congr 1
  apply Fin.ext
  exact (cwPos_bounded_unique ring edge (cwPos ring edge i.val)
    i.val i.isLt rfl).symm

/-- The concrete clockwise rotation is a bijection on Boolean front
configurations; no abstract reindexing hypothesis is carried. -/
theorem rotateFrontConfigFrom_bijective
    {n : Nat} (ring : DirectedRing n) (edge : Fin n) :
    Function.Injective (rotateFrontConfigFrom ring edge) ∧
      Function.Surjective (rotateFrontConfigFrom ring edge) := by
  constructor
  · intro C D hCD
    have h := congrArg (unrotateFrontConfigFrom ring edge) hCD
    simpa using h
  · intro D
    exact ⟨unrotateFrontConfigFrom ring edge D, by simp⟩

/-! ## Exact front-mass preservation -/

/-- Number of occupied front coordinates in a `Fin n` configuration. -/
def frontConfigMass {n : Nat} (C : Fin n → Bool) : Nat :=
  (List.ofFn (fun i => if C i then 1 else 0)).sum

/-- Encode a finite front configuration in the exact list convention used by
`allFrontWords`. -/
def frontConfigWord {n : Nat} (C : Fin n → Bool) : List Bool :=
  List.ofFn C

@[simp] theorem frontConfigWord_length
    {n : Nat} (C : Fin n → Bool) :
    (frontConfigWord C).length = n := by
  simp [frontConfigWord]

/-- Every function encoding occurs in the explicit state-space enumeration
from the first finite-slice brick. -/
theorem frontConfigWord_mem_allFrontWords
    {n : Nat} (C : Fin n → Bool) :
    frontConfigWord C ∈ allFrontWords n := by
  exact mem_allFrontWords_of_length n (frontConfigWord C)
    (frontConfigWord_length C)

/-- The function-space mass is exactly the existing list-word mass. -/
theorem frontWordMass_frontConfigWord
    {n : Nat} (C : Fin n → Bool) :
    frontWordMass (frontConfigWord C) = frontConfigMass C := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold frontConfigWord frontConfigMass
      rw [List.ofFn_succ, frontWordMass, List.ofFn_succ, List.sum_cons]
      have htail := ih (C := fun i : Fin n => C i.succ)
      have htail' :
          frontWordMass (List.ofFn (fun i : Fin n => C i.succ)) =
            (List.ofFn (fun i : Fin n =>
              if C i.succ then 1 else 0)).sum := by
        simpa [frontConfigWord, frontConfigMass] using htail
      rw [htail']

private theorem sum_ofFn_rightNeighbor
    {n : Nat} (ring : DirectedRing n) (f : Fin n → Nat) :
    (List.ofFn (fun i => f (ring.rightNeighbor i))).sum =
      (List.ofFn f).sum := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ring.hn)
  subst n
  rw [show List.ofFn
      (fun i : Fin (m + 1) => f (ring.rightNeighbor i)) =
    (List.ofFn (fun i : Fin m =>
      f (ring.rightNeighbor i.castSucc))) ++
      [f (ring.rightNeighbor (Fin.last m))] from List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.ofFn_succ, List.sum_cons]
  have hlast : ring.rightNeighbor (Fin.last m) = 0 := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor]
  have hsucc : ∀ i : Fin m,
      ring.rightNeighbor i.castSucc = i.succ := by
    intro i
    apply Fin.ext
    simp [DirectedRing.rightNeighbor,
      Nat.mod_eq_of_lt (by omega : i.val + 1 < m + 1)]
  rw [hlast]
  have hfun :
      (fun i : Fin m => f (ring.rightNeighbor i.castSucc)) =
        (fun i : Fin m => f i.succ) := by
    funext i
    rw [hsucc]
  rw [hfun]
  omega

/-- Reindexing a finite sum by any fixed clockwise translation preserves it.
This is proved by iteration of the concrete successor permutation. -/
private theorem sum_ofFn_cwPos
    {n : Nat} (ring : DirectedRing n) (f : Fin n → Nat) (steps : Nat) :
    (List.ofFn (fun i => f (cwPos ring i steps))).sum =
      (List.ofFn f).sum := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      calc
        (List.ofFn (fun i => f (cwPos ring i (steps + 1)))).sum =
            (List.ofFn (fun i =>
              (fun j => f (cwPos ring j steps))
                (ring.rightNeighbor i))).sum := by
              congr 2
              funext i
              exact congrArg f (cwPos_rightNeighbor ring i steps).symm
        _ = (List.ofFn (fun i => f (cwPos ring i steps))).sum :=
              sum_ofFn_rightNeighbor ring
                (fun j => f (cwPos ring j steps))
        _ = (List.ofFn f).sum := ih

/-- Starting at `edge` and moving by `i.val` is the same cyclic coordinate as
starting at `i` and moving by `edge.val`. -/
private theorem cwPos_start_steps_comm
    {n : Nat} (ring : DirectedRing n) (edge i : Fin n) :
    cwPos ring edge i.val = cwPos ring i edge.val := by
  apply Fin.ext
  simp [cwPos, Nat.add_comm]

/-- Clockwise coordinate rotation preserves the fixed-front slice exactly. -/
theorem frontConfigMass_rotateFrontConfigFrom
    {n : Nat} (ring : DirectedRing n) (edge : Fin n)
    (C : Fin n → Bool) :
    frontConfigMass (rotateFrontConfigFrom ring edge C) =
      frontConfigMass C := by
  unfold frontConfigMass rotateFrontConfigFrom
  have hfun :
      (fun i : Fin n =>
          if C (cwPos ring edge i.val) then 1 else 0) =
        (fun i : Fin n =>
          (fun j => if C j then 1 else 0) (cwPos ring i edge.val)) := by
    funext i
    rw [cwPos_start_steps_comm]
  rw [hfun]
  exact sum_ofFn_cwPos ring (fun j => if C j then 1 else 0) edge.val

/-! ## The arbitrary-edge event is the canonical first-two event -/

/-- Both endpoints of a directed edge carry fronts in the original
configuration. -/
def FrontConfigMarkedEdge
    {n : Nat} (ring : DirectedRing n) (C : Fin n → Bool)
    (edge : Fin n) : Prop :=
  C edge = true ∧ C (ring.rightNeighbor edge) = true

/-- The canonical first two coordinates both carry fronts. -/
def FrontConfigCanonicalMarkedPair
    {n : Nat} (hn : 2 ≤ n) (C : Fin n → Bool) : Prop :=
  C ⟨0, by omega⟩ = true ∧ C ⟨1, by omega⟩ = true

/-- Rotating from an arbitrary directed edge turns its marked event into the
canonical zero-one marked event, with no premise about the configuration. -/
theorem rotateFrontConfigFrom_canonicalMarkedPair_iff
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (edge : Fin n) (C : Fin n → Bool) :
    FrontConfigCanonicalMarkedPair hn
        (rotateFrontConfigFrom ring edge C) ↔
      FrontConfigMarkedEdge ring C edge := by
  simp only [FrontConfigCanonicalMarkedPair, FrontConfigMarkedEdge,
    rotateFrontConfigFrom_zero,
    rotateFrontConfigFrom_one ring hn edge C]

/-- Boolean form of the exact canonical predicate used inline by
`markedPairWordCount`. -/
def frontWordHasCanonicalMarkedPair : List Bool → Bool
  | true :: true :: _ => true
  | _ => false

theorem markedPairWordCount_eq_countP_canonical
    (n k : Nat) :
    markedPairWordCount n k =
      (allFrontWords n).countP (fun w =>
        decide (frontWordMass w = k) &&
          frontWordHasCanonicalMarkedPair w) := by
  rfl

/-- Under the exact `List.ofFn` encoding, the list predicate on the first two
entries is precisely the function-space canonical event. -/
theorem frontConfigWord_hasCanonicalMarkedPair_iff
    {n : Nat} (hn : 2 ≤ n) (C : Fin n → Bool) :
    frontWordHasCanonicalMarkedPair (frontConfigWord C) = true ↔
      FrontConfigCanonicalMarkedPair hn C := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  subst n
  cases hzero : C 0 <;> cases hone : C 1 <;>
    simp [frontConfigWord, FrontConfigCanonicalMarkedPair,
      List.ofFn_succ, frontWordHasCanonicalMarkedPair, hzero, hone]

/-- Exact list/`Fin` bridge for a selected directed cyclic edge.  The rotated
word lies in the same fixed-mass slice, and its first two entries are true
exactly when the original arbitrary edge is marked. -/
theorem rotatedWord_fixedSliceMarkedPair_iff
    {n k : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (edge : Fin n) (C : Fin n → Bool) :
    (decide
        (frontWordMass
          (frontConfigWord (rotateFrontConfigFrom ring edge C)) = k) &&
      frontWordHasCanonicalMarkedPair
        (frontConfigWord (rotateFrontConfigFrom ring edge C))) = true ↔
      frontConfigMass C = k ∧ FrontConfigMarkedEdge ring C edge := by
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [frontWordMass_frontConfigWord,
    frontConfigMass_rotateFrontConfigFrom,
    frontConfigWord_hasCanonicalMarkedPair_iff hn
      (rotateFrontConfigFrom ring edge C),
    rotateFrontConfigFrom_canonicalMarkedPair_iff ring hn edge C]

/-! ## Kernel dependency audit -/

#print axioms rotateFrontConfigFrom_bijective
#print axioms frontConfigMass_rotateFrontConfigFrom
#print axioms rotatedWord_fixedSliceMarkedPair_iff

end PPartialSealSweepTasepRotationBridgeSol
end PPLLCompleteMultiLeaderCleanup
