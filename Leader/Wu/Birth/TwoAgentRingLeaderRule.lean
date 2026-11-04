import Leader.Wu.Birth.TwoAgentRingNoGo

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthSmallRingN2TwoAgentRule

open PPLLExpiringComparisonRepair

abbrev Cell := BirthSmallRingN2NoGo.Cell

private theorem hOne : 0 < (1 : Nat) := by decide
private theorem hOneLe : (1 : Nat) ≤ 1 := by decide
private theorem hTwo : 0 < (2 : Nat) := by decide
private theorem hTwoLe : (2 : Nat) ≤ 2 := by decide

/-- The dedicated exception is enabled only at the legal routed n = 2 tuple. -/
def atN2Tuple (n psi width kappa tau : Nat) : Prop :=
  n = 2 ∧ psi = 1 ∧ width = 1 ∧ kappa = 2 ∧ tau = 32

instance (n psi width kappa tau : Nat) :
    Decidable (atN2Tuple n psi width kappa tau) := by
  unfold atN2Tuple; infer_instance

/-- Change only the physical leader bit; every other existing field is kept. -/
def setLeader {psi kappa tau : Nat}
    (q : ExpiringAgentState psi kappa tau) (b : Bool) :
    ExpiringAgentState psi kappa tau :=
  { q with
    core := { q.core with
      core := { q.core.core with leader := b } } }

/-- Terminal host plus the dedicated two-agent leader-count correction. -/
def row {psi width kappa tau : Nat} (n : Nat)
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let q := BirthShortDoneTerminalHost.row hpsi hwidth hle l r
  if atN2Tuple n psi width kappa tau then
    (setLeader q.1 true, setLeader q.2 false)
  else
    q

/-- Population-protocol wrapper. -/
def protocol {psi width : Nat} (n : Nat)
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa tau : Nat) : PopulationProtocol where
  Q := ExpiringAgentState psi kappa tau
  Y := Bool
  transition := row n hpsi hwidth hle
  output := fun q => q.core.core.leader

/-- One physical scheduler step of the wrapped protocol. -/
def step {n psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n) :
    Fin n → ExpiringAgentState psi kappa tau :=
  (protocol n hpsi hwidth hle kappa tau).step ring C e

/-- Routed n = 2 specialization. -/
def n2Step (C : Fin 2 → Cell) (e : Fin 2) : Fin 2 → Cell :=
  step hOne hOne hOneLe BirthSmallRingN2NoGo.ring2 C e

def leaderNat (q : Cell) : Nat :=
  if q.core.core.leader = true then 1 else 0

def leaderCount2 (C : Fin 2 → Cell) : Nat :=
  leaderNat (C 0) + leaderNat (C 1)

/-- On the active tuple every interaction output has exactly these leader bits.
This simultaneously covers 0 -> 1, 2 -> 1, and 1 -> 1. -/
theorem row_n2_leader_bits (l r : Cell) :
    (row 2 hOne hOne hOneLe l r).1.core.core.leader = true ∧
    (row 2 hOne hOne hOneLe l r).2.core.core.leader = false := by
  have h : atN2Tuple 2 1 1 2 32 := ⟨rfl, rfl, rfl, rfl, rfl⟩
  simp [row, h, setLeader]

/-- From the closed-family seed, either scheduler edge births one leader. -/
theorem seed_birth_either_edge (e : Fin 2) :
    leaderCount2 (n2Step BirthSmallRingN2NoGo.seed e) = 1 := by
  revert e
  decide

/-- After either first edge, either next scheduler edge still leaves one leader. -/
theorem seed_one_leader_stable (e0 e1 : Fin 2) :
    leaderCount2
      (n2Step (n2Step BirthSmallRingN2NoGo.seed e0) e1) = 1 := by
  revert e0 e1
  decide

/-- Representative n >= 3 check: the routed n = 3 tuple is untouched. -/
theorem row_n3_identity
    (l r : ExpiringAgentState 2 2 32) :
    row 3 hTwo hTwo hTwoLe l r =
      BirthShortDoneTerminalHost.row hTwo hTwo hTwoLe l r := by
  rfl

/-! A wrapped n = 2 version of the small-ring counting interface.  The old
`BirthSmallRingWrapper.SmallRingBirthPhaseBound` is hardwired to the unwrapped
consumer, so this specialization uses the wrapped step itself. -/

def LeaderlessAlong2 (C : Fin 2 → Cell) : List (Fin 2) → Prop
  | [] => BirthShortDoneTerminalFirstHit.Leaderless C
  | e :: es =>
      BirthShortDoneTerminalFirstHit.Leaderless C ∧
      LeaderlessAlong2 (n2Step C e) es

noncomputable def physicalNoHitBit2
    (C : Fin 2 → Cell) (es : List (Fin 2)) : Nat := by
  classical
  exact if LeaderlessAlong2 C es then 1 else 0

def run2 (C : Fin 2 → Cell) (es : List (Fin 2)) : Fin 2 → Cell :=
  es.foldl n2Step C

/-- For n = 2, a wrapped interaction is a birth exactly when its input has
leader count zero, since its output always has leader count one. -/
def birthEvent2 (C : Fin 2 → Cell) : Bool :=
  if leaderCount2 C = 0 then true else false

def NoBirthAlong2 (C : Fin 2 → Cell) : List (Fin 2) → Prop
  | [] => True
  | e :: es =>
      birthEvent2 C = false ∧ NoBirthAlong2 (n2Step C e) es

noncomputable def noBirthBit2
    (C : Fin 2 → Cell) (es : List (Fin 2)) : Nat := by
  classical
  exact if NoBirthAlong2 C es then 1 else 0

/-- Exact wrapped analogue of `SmallRingBirthPhaseBound`, specialized to n = 2. -/
def SmallRingBirthPhaseBoundN2
    (C : Fin 2 → Cell)
    (firstHorizon postHorizon postMass : Nat) : Prop :=
  2 ≤ 2 ∧ 2 ≤ 3 ∧
  BirthShortDoneTerminalFirstHit.Leaderless C ∧
  2 * FixedSpanRenewalPayload.wordSum 2 firstHorizon
      (physicalNoHitBit2 C) ≤
    2 ^ firstHorizon ∧
  ∀ (pre : List (Fin 2)) (e : Fin 2),
    pre.length < firstHorizon →
    NoBirthAlong2 C pre →
    let D := run2 C pre
    birthEvent2 D = true →
    let E := n2Step D e
    postMass ≤
      FixedSpanRenewalPayload.wordSum 2 postHorizon (noBirthBit2 E)

/-- Statement only: first hit in one step, then both one-step scheduler words
have no second birth.  This is `(firstHorizon,postHorizon,postMass) = (1,1,2)`. -/
def routed_n2_smallRingBirthPhaseBound : Prop :=
  SmallRingBirthPhaseBoundN2 BirthSmallRingN2NoGo.seed 1 1 2

end BirthSmallRingN2TwoAgentRule

#print axioms BirthSmallRingN2TwoAgentRule.row_n2_leader_bits
#print axioms BirthSmallRingN2TwoAgentRule.seed_birth_either_edge
#print axioms BirthSmallRingN2TwoAgentRule.seed_one_leader_stable
#print axioms BirthSmallRingN2TwoAgentRule.row_n3_identity
