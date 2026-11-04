import Leader.Wu.Birth.TwoAgentRingLeaderRule

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthSmallRingN2StableRule

open PPLLExpiringComparisonRepair
open FixedSpanRenewalPayload FiniteUniformStoppingTree

abbrev Cell := BirthSmallRingN2TwoAgentRule.Cell

private theorem hOne : 0 < (1 : Nat) := by decide
private theorem hOneLe : (1 : Nat) ≤ 1 := by decide
private theorem hTwo : 0 < (2 : Nat) := by decide
private theorem hTwoLe : (2 : Nat) ≤ 2 := by decide

def leaderNat {psi kappa tau : Nat}
    (q : ExpiringAgentState psi kappa tau) : Nat :=
  if q.core.core.leader = true then 1 else 0

def pairLeaderCount {psi kappa tau : Nat}
    (l r : ExpiringAgentState psi kappa tau) : Nat :=
  leaderNat l + leaderNat r

def leaderCount2 (C : Fin 2 → Cell) : Nat :=
  pairLeaderCount (C 0) (C 1)

/-- A concrete n=2 witness that the terminal host does not frame a sole leader. -/
def hostLeftOne : Cell :=
  BirthSmallRingN2TwoAgentRule.setLeader
    (BirthSmallRingN2NoGo.L false 0) true

def hostRightBullet : Cell :=
  let q := BirthSmallRingN2NoGo.R false 0
  { q with
    core := { q.core with
      core := { q.core.core with bullet := 2 } } }

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
theorem host_n2_single_leader_not_framed :
    pairLeaderCount hostLeftOne hostRightBullet = 1 ∧
    (BirthShortDoneTerminalHost.row hOne hOne hOneLe
      hostLeftOne hostRightBullet).1.core.core.leader ≠
        hostLeftOne.core.core.leader := by
  decide

/-- Run the terminal host first. At the routed n=2 tuple, correct a wrong
leader count to `(true,false)`; at count one, frame the exact input identities. -/
def row {psi width kappa tau : Nat} (n : Nat)
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  let q := BirthShortDoneTerminalHost.row hpsi hwidth hle l r
  if BirthSmallRingN2TwoAgentRule.atN2Tuple n psi width kappa tau then
    if pairLeaderCount l r = 1 then
      (BirthSmallRingN2TwoAgentRule.setLeader q.1 l.core.core.leader,
       BirthSmallRingN2TwoAgentRule.setLeader q.2 r.core.core.leader)
    else
      (BirthSmallRingN2TwoAgentRule.setLeader q.1 true,
       BirthSmallRingN2TwoAgentRule.setLeader q.2 false)
  else q

def protocol {psi width : Nat} (n : Nat)
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa tau : Nat) : PopulationProtocol where
  Q := ExpiringAgentState psi kappa tau
  Y := Bool
  transition := row n hpsi hwidth hle
  output := fun q => q.core.core.leader

def step {n psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n) :
    Fin n → ExpiringAgentState psi kappa tau :=
  (protocol n hpsi hwidth hle kappa tau).step ring C e

def n2Step (C : Fin 2 → Cell) (e : Fin 2) : Fin 2 → Cell :=
  step hOne hOne hOneLe BirthSmallRingN2NoGo.ring2 C e

private theorem n2Tuple :
    BirthSmallRingN2TwoAgentRule.atN2Tuple 2 1 1 2 32 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem row_n2_wrong_count_bits (l r : Cell)
    (h : pairLeaderCount l r ≠ 1) :
    (row 2 hOne hOne hOneLe l r).1.core.core.leader = true ∧
    (row 2 hOne hOne hOneLe l r).2.core.core.leader = false := by
  simp [row, n2Tuple, h, BirthSmallRingN2TwoAgentRule.setLeader]

theorem row_n2_one_leader_bits (l r : Cell)
    (h : pairLeaderCount l r = 1) :
    (row 2 hOne hOne hOneLe l r).1.core.core.leader = l.core.core.leader ∧
    (row 2 hOne hOne hOneLe l r).2.core.core.leader = r.core.core.leader := by
  simp [row, n2Tuple, h, BirthSmallRingN2TwoAgentRule.setLeader]

theorem row_n3_identity
    (l r : ExpiringAgentState 2 2 32) :
    row 3 hTwo hTwo hTwoLe l r =
      BirthShortDoneTerminalHost.row hTwo hTwo hTwoLe l r := by
  rfl

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

theorem n2Step_edge_zero_one_leader_identity
    (C : Fin 2 → Cell) (h : leaderCount2 C = 1) (i : Fin 2) :
    (n2Step C 0 i).core.core.leader = (C i).core.core.leader := by
  have hp : pairLeaderCount (C 0) (C 1) = 1 := by
    simpa [leaderCount2] using h
  have hr := row_n2_one_leader_bits (C 0) (C 1) hp
  obtain rfl | rfl := fin2_cases i
  · simpa [n2Step, step, protocol, PopulationProtocol.step,
      BirthSmallRingN2NoGo.ring2_right_zero] using hr.1
  · simpa [n2Step, step, protocol, PopulationProtocol.step,
      BirthSmallRingN2NoGo.ring2_right_zero] using hr.2

theorem n2Step_edge_one_one_leader_identity
    (C : Fin 2 → Cell) (h : leaderCount2 C = 1) (i : Fin 2) :
    (n2Step C 1 i).core.core.leader = (C i).core.core.leader := by
  have hp : pairLeaderCount (C 1) (C 0) = 1 := by
    simpa [leaderCount2, pairLeaderCount, Nat.add_comm] using h
  have hr := row_n2_one_leader_bits (C 1) (C 0) hp
  obtain rfl | rfl := fin2_cases i
  · simpa [n2Step, step, protocol, PopulationProtocol.step,
      BirthSmallRingN2NoGo.ring2_right_one] using hr.2
  · simpa [n2Step, step, protocol, PopulationProtocol.step,
      BirthSmallRingN2NoGo.ring2_right_one] using hr.1

theorem n2Step_one_leader_identity
    (C : Fin 2 → Cell) (h : leaderCount2 C = 1) (e i : Fin 2) :
    (n2Step C e i).core.core.leader = (C i).core.core.leader := by
  obtain rfl | rfl := fin2_cases e
  · exact n2Step_edge_zero_one_leader_identity C h i
  · exact n2Step_edge_one_one_leader_identity C h i

theorem n2Step_one_leader_count
    (C : Fin 2 → Cell) (h : leaderCount2 C = 1) (e : Fin 2) :
    leaderCount2 (n2Step C e) = 1 := by
  have h0 := n2Step_one_leader_identity C h e 0
  have h1 := n2Step_one_leader_identity C h e 1
  unfold leaderCount2 pairLeaderCount leaderNat
  rw [h0, h1]
  simpa [leaderCount2, pairLeaderCount, leaderNat] using h

theorem seed_birth_either_edge (e : Fin 2) :
    leaderCount2 (n2Step BirthSmallRingN2NoGo.seed e) = 1 := by
  revert e
  decide

theorem seed_one_leader_stable (e0 e1 : Fin 2) :
    leaderCount2
      (n2Step (n2Step BirthSmallRingN2NoGo.seed e0) e1) = 1 :=
  n2Step_one_leader_count _ (seed_birth_either_edge e0) e1

theorem seed_leader_identity_stable (e0 e1 i : Fin 2) :
    (n2Step (n2Step BirthSmallRingN2NoGo.seed e0) e1 i).core.core.leader =
      (n2Step BirthSmallRingN2NoGo.seed e0 i).core.core.leader :=
  n2Step_one_leader_identity _ (seed_birth_either_edge e0) e1 i

/-! Corrected n=2 counting interface. -/
def LeaderlessAlong2 (C : Fin 2 → Cell) : List (Fin 2) → Prop
  | [] => BirthShortDoneTerminalFirstHit.Leaderless C
  | e :: es =>
      BirthShortDoneTerminalFirstHit.Leaderless C ∧ LeaderlessAlong2 (n2Step C e) es

noncomputable def physicalNoHitBit2 (C : Fin 2 → Cell) (es : List (Fin 2)) : Nat := by
  classical
  exact if LeaderlessAlong2 C es then 1 else 0

def run2 (C : Fin 2 → Cell) (es : List (Fin 2)) : Fin 2 → Cell := es.foldl n2Step C

def birthEvent2 (C : Fin 2 → Cell) : Bool :=
  if leaderCount2 C = 0 then true else false

def NoBirthAlong2 (C : Fin 2 → Cell) : List (Fin 2) → Prop
  | [] => True
  | e :: es => birthEvent2 C = false ∧ NoBirthAlong2 (n2Step C e) es

noncomputable def noBirthBit2 (C : Fin 2 → Cell) (es : List (Fin 2)) : Nat := by
  classical
  exact if NoBirthAlong2 C es then 1 else 0

def SmallRingBirthPhaseBoundN2
    (C : Fin 2 → Cell) (firstHorizon postHorizon postMass : Nat) : Prop :=
  2 ≤ 2 ∧ 2 ≤ 3 ∧ BirthShortDoneTerminalFirstHit.Leaderless C ∧
  2 * wordSum 2 firstHorizon (physicalNoHitBit2 C) ≤ 2 ^ firstHorizon ∧
  ∀ (pre : List (Fin 2)) (e : Fin 2), pre.length < firstHorizon →
    NoBirthAlong2 C pre →
    let D := run2 C pre
    birthEvent2 D = true →
    let E := n2Step D e
    postMass ≤ wordSum 2 postHorizon (noBirthBit2 E)

private theorem wordSum_one_step_zero (f : List (Fin 2) → Nat)
    (hf : ∀ e : Fin 2, f [e] = 0) : wordSum 2 1 f = 0 := by
  rw [show (1 : Nat) = 0 + 1 by rfl, wordSum_succ]
  have h0 : ∀ e : Fin 2, (wordSum 2 0 fun u => f (e :: u)) = 0 := by
    intro e
    simpa [wordSum, allSchedules] using hf e
  rw [show (List.ofFn fun e : Fin 2 => wordSum 2 0 fun u => f (e :: u)) =
      List.ofFn (fun _ : Fin 2 => (0 : Nat)) from congrArg List.ofFn (funext h0)]
  decide

private theorem wordSum_one_step_one (f : List (Fin 2) → Nat)
    (hf : ∀ e : Fin 2, f [e] = 1) : wordSum 2 1 f = 2 := by
  rw [show (1 : Nat) = 0 + 1 by rfl, wordSum_succ]
  calc
    (List.ofFn (fun e : Fin 2 => wordSum 2 0 (fun u => f (e :: u)))).sum =
        (List.ofFn (fun _ : Fin 2 => 1)).sum := by
      apply ofFn_sum_eq
      intro e
      simpa [wordSum, allSchedules] using hf e
    _ = 2 := by decide

private theorem seed_not_leaderlessAlong_one (e : Fin 2) :
    ¬ LeaderlessAlong2 BirthSmallRingN2NoGo.seed [e] := by
  intro h
  change BirthShortDoneTerminalFirstHit.Leaderless BirthSmallRingN2NoGo.seed ∧
    BirthShortDoneTerminalFirstHit.Leaderless
      (n2Step BirthSmallRingN2NoGo.seed e) at h
  have hc := seed_birth_either_edge e
  have h0 := h.2 (0 : Fin 2)
  have h1 := h.2 (1 : Fin 2)
  simp [leaderCount2, pairLeaderCount, leaderNat, h0, h1] at hc

private theorem seed_physicalNoHitBit_singleton_zero (e : Fin 2) :
    physicalNoHitBit2 BirthSmallRingN2NoGo.seed [e] = 0 := by
  unfold physicalNoHitBit2
  rw [if_neg (seed_not_leaderlessAlong_one e)]

private theorem seed_physicalNoHit_wordSum_one :
    wordSum 2 1 (physicalNoHitBit2 BirthSmallRingN2NoGo.seed) = 0 := by
  apply wordSum_one_step_zero
  exact seed_physicalNoHitBit_singleton_zero

private theorem noBirthBit2_singleton_one
    (C : Fin 2 → Cell) (hC : leaderCount2 C = 1) (e : Fin 2) :
    noBirthBit2 C [e] = 1 := by
  unfold noBirthBit2
  rw [if_pos]
  change birthEvent2 C = false ∧ True
  simp [birthEvent2, hC]

private theorem one_leader_noBirth_wordSum_one
    (C : Fin 2 → Cell) (hC : leaderCount2 C = 1) :
    wordSum 2 1 (noBirthBit2 C) = 2 := by
  apply wordSum_one_step_one
  exact noBirthBit2_singleton_one C hC

theorem routed_n2_smallRingBirthPhaseBound :
    SmallRingBirthPhaseBoundN2 BirthSmallRingN2NoGo.seed 1 1 2 := by
  refine ⟨by decide, by decide, BirthSmallRingN2NoGo.seed_leaderless, ?_, ?_⟩
  · rw [seed_physicalNoHit_wordSum_one]
    decide
  · intro pre e hlen _hno
    cases pre with
    | nil =>
        dsimp [run2]
        intro _hb
        rw [one_leader_noBirth_wordSum_one
          (n2Step BirthSmallRingN2NoGo.seed e) (seed_birth_either_edge e)]
        exact Nat.le_refl _
    | cons a as =>
        simp at hlen

end BirthSmallRingN2StableRule

#print axioms BirthSmallRingN2StableRule.host_n2_single_leader_not_framed
#print axioms BirthSmallRingN2StableRule.row_n3_identity
#print axioms BirthSmallRingN2StableRule.seed_birth_either_edge
#print axioms BirthSmallRingN2StableRule.n2Step_one_leader_identity
#print axioms BirthSmallRingN2StableRule.seed_one_leader_stable
#print axioms BirthSmallRingN2StableRule.seed_leader_identity_stable
#print axioms BirthSmallRingN2StableRule.routed_n2_smallRingBirthPhaseBound
