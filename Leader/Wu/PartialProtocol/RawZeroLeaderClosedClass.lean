import Leader.Wu.PartialProtocol.DomainClosure

/-!
# Raw `P_partial`: a nontrivial closed zero-leader class

This module audits the compiled, unmodified `P_partial` transition, with no
overlay repair.  At `n = 2`, `psi = 1`, `kappa = 0`, and `tau = 0`, six exact
configurations form a transition-closed class.  Every state in the class emits
follower, so no finite schedule from the class can reach operational
legitimacy.  In particular, the unconditional rank-zero/rank-one producer is
false for every proposed bound.

Unlike the singleton boundary witness, this example satisfies `1 < n`.  The
homogeneous terminal-deletion configuration is not itself fixed: one
initiator/responder interaction clears the responder.  Nevertheless, the exact
word `[0, 1, 0]` takes it into the six-configuration closed class below.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair

set_option autoImplicit false

theorem rawZeroClosed_hpsi : (1 : Nat) > 0 := by
  omega

/-! ## Four exact endpoint states -/

/-- Neutral follower endpoint `N`. -/
def rawZeroClosedCoreN : BoundedAgentState 1 0 where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := false
  state := .none
  path := .bot
  reset := false
  carry := false
  count := 0
  label := 0
  h_field := false
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := 0
  bullet := 0
  shield := false
  write_state := .none
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

/-- Reset/write-depart follower endpoint `R`. -/
def rawZeroClosedCoreR : BoundedAgentState 1 0 :=
  { rawZeroClosedCoreN with
    reset := true
    write_state := .depart }

/-- `h_field` follower endpoint `H`. -/
def rawZeroClosedCoreH : BoundedAgentState 1 0 :=
  { rawZeroClosedCoreN with h_field := true }

/-- Combined reset/write-depart and `h_field` follower endpoint `RH`. -/
def rawZeroClosedCoreRH : BoundedAgentState 1 0 :=
  { rawZeroClosedCoreN with
    reset := true
    h_field := true
    write_state := .depart }

def rawZeroClosedLift (u : BoundedAgentState 1 0) :
    ExpiringAgentState 1 0 0 :=
  ⟨⟨u, false⟩, freshStall 0⟩

def rawZeroClosedN : ExpiringAgentState 1 0 0 :=
  rawZeroClosedLift rawZeroClosedCoreN

def rawZeroClosedR : ExpiringAgentState 1 0 0 :=
  rawZeroClosedLift rawZeroClosedCoreR

def rawZeroClosedH : ExpiringAgentState 1 0 0 :=
  rawZeroClosedLift rawZeroClosedCoreH

def rawZeroClosedRH : ExpiringAgentState 1 0 0 :=
  rawZeroClosedLift rawZeroClosedCoreRH

/-! ## Exact raw local transition table -/

theorem rawZeroClosed_transition_NR :
    P_partialUnconditional rawZeroClosed_hpsi 0 0
      rawZeroClosedN rawZeroClosedR =
        (rawZeroClosedH, rawZeroClosedR) := by
  rfl

theorem rawZeroClosed_transition_RN :
    P_partialUnconditional rawZeroClosed_hpsi 0 0
      rawZeroClosedR rawZeroClosedN =
        (rawZeroClosedH, rawZeroClosedR) := by
  rfl

theorem rawZeroClosed_transition_RHN :
    P_partialUnconditional rawZeroClosed_hpsi 0 0
      rawZeroClosedRH rawZeroClosedN =
        (rawZeroClosedN, rawZeroClosedR) := by
  rfl

theorem rawZeroClosed_transition_NRH :
    P_partialUnconditional rawZeroClosed_hpsi 0 0
      rawZeroClosedN rawZeroClosedRH =
        (rawZeroClosedH, rawZeroClosedR) := by
  rfl

theorem rawZeroClosed_transition_RH :
    P_partialUnconditional rawZeroClosed_hpsi 0 0
      rawZeroClosedR rawZeroClosedH =
        (rawZeroClosedH, rawZeroClosedR) := by
  rfl

theorem rawZeroClosed_transition_HR :
    P_partialUnconditional rawZeroClosed_hpsi 0 0
      rawZeroClosedH rawZeroClosedR =
        (rawZeroClosedN, rawZeroClosedRH) := by
  rfl

/-! ## Six closed configurations -/

theorem rawZeroClosedRing : DirectedRing 2 :=
  ⟨by omega⟩

theorem rawZeroClosed_nontrivial : 1 < 2 := by
  omega

/-- The witness lies in the same non-self-edge regime used by the formulation. -/
theorem rawZeroClosedRegime : OperationalRegime 2 1 where
  ring := rawZeroClosedRing
  hψ := rawZeroClosed_hpsi
  nontrivial := rawZeroClosed_nontrivial

inductive RawZeroClosedPhase where
  | p0
  | p1
  | p2
  | p3
  | p4
  | p5
  deriving DecidableEq, Repr

/-- The exact six pairs, in transition-table order:
`(N,R)`, `(R,N)`, `(RH,N)`, `(R,H)`, `(N,RH)`, `(H,R)`. -/
def rawZeroClosedConfig :
    RawZeroClosedPhase → PPartialConfig 2 1 0 0
  | .p0 => fun i => if i = 0 then rawZeroClosedN else rawZeroClosedR
  | .p1 => fun i => if i = 0 then rawZeroClosedR else rawZeroClosedN
  | .p2 => fun i => if i = 0 then rawZeroClosedRH else rawZeroClosedN
  | .p3 => fun i => if i = 0 then rawZeroClosedR else rawZeroClosedH
  | .p4 => fun i => if i = 0 then rawZeroClosedN else rawZeroClosedRH
  | .p5 => fun i => if i = 0 then rawZeroClosedH else rawZeroClosedR

/-- Exact successor phase for each of the two directed edges. -/
def rawZeroClosedNext
    (p : RawZeroClosedPhase) (e : Fin 2) : RawZeroClosedPhase :=
  match p with
  | .p0 => if e = 0 then .p5 else .p3
  | .p1 => if e = 0 then .p5 else .p3
  | .p2 => if e = 0 then .p0 else .p3
  | .p3 => if e = 0 then .p5 else .p2
  | .p4 => if e = 0 then .p5 else .p1
  | .p5 => if e = 0 then .p4 else .p3

theorem rawZeroClosed_fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  omega

/-- All twelve phase/edge cases execute the exact raw transition and remain
inside the six-phase class. -/
theorem rawZeroClosed_localStep
    (p : RawZeroClosedPhase) (e : Fin 2) :
    localStep rawZeroClosedRing
      (P_partialUnconditional rawZeroClosed_hpsi 0 0)
      (rawZeroClosedConfig p) e =
        rawZeroClosedConfig (rawZeroClosedNext p e) := by
  cases p <;> rcases rawZeroClosed_fin2_cases e with rfl | rfl <;>
    funext i <;> rcases rawZeroClosed_fin2_cases i with rfl | rfl <;> rfl

/-- Configuration-level membership in the six-state closed class. -/
def InRawZeroClosedClass (C : PPartialConfig 2 1 0 0) : Prop :=
  ∃ p : RawZeroClosedPhase, C = rawZeroClosedConfig p

theorem InRawZeroClosedClass.localStep
    (C : PPartialConfig 2 1 0 0)
    (hC : InRawZeroClosedClass C) (e : Fin 2) :
    InRawZeroClosedClass
      (localStep rawZeroClosedRing
        (P_partialUnconditional rawZeroClosed_hpsi 0 0) C e) := by
  rcases hC with ⟨p, rfl⟩
  exact ⟨rawZeroClosedNext p e, rawZeroClosed_localStep p e⟩

/-- The six configurations are closed under the packaged exact protocol. -/
theorem rawZeroClosed_closedPred :
    PopulationProtocol.ClosedPred
      (P_partialProtocolUnconditional rawZeroClosed_hpsi 0 0)
      rawZeroClosedRing InRawZeroClosedClass := by
  intro C hC C' hstep
  rcases hstep with ⟨e, rfl⟩
  rw [← localStep_eq_protocol_step]
  exact InRawZeroClosedClass.localStep C hC e

/-- Schedule-level closure, stated directly with the exact transition. -/
theorem rawZeroClosed_run
    (C : PPartialConfig 2 1 0 0)
    (hC : InRawZeroClosedClass C) (word : DetSchedule 2) :
    InRawZeroClosedClass
      (runLocalSchedule rawZeroClosedRing
        (P_partialUnconditional rawZeroClosed_hpsi 0 0) C word) := by
  induction word generalizing C with
  | nil =>
      exact hC
  | cons e rest ih =>
      simp only [runLocalSchedule]
      exact ih _ (InRawZeroClosedClass.localStep C hC e)

/-! ## Every reachable output is follower -/

theorem rawZeroClosed_phase_leader_false
    (p : RawZeroClosedPhase) (i : Fin 2) :
    ((rawZeroClosedConfig p) i).core.core.leader = false := by
  cases p <;> rcases rawZeroClosed_fin2_cases i with rfl | rfl <;> rfl

theorem InRawZeroClosedClass.leader_false
    (C : PPartialConfig 2 1 0 0)
    (hC : InRawZeroClosedClass C) (i : Fin 2) :
    (C i).core.core.leader = false := by
  rcases hC with ⟨p, rfl⟩
  exact rawZeroClosed_phase_leader_false p i

theorem rawZeroClosed_not_legit
    (C : PPartialConfig 2 1 0 0)
    (hC : InRawZeroClosedClass C) :
    ¬ PPartialLegitUnconditional rawZeroClosed_hpsi 0 0 C := by
  intro hlegit
  rcases hlegit with ⟨i, hi, _⟩
  have hfalse := hC.leader_false C i
  simp [P_partialProtocol, hfalse, isLeaderOutput] at hi

/-- No finite schedule from any member of the closed class creates a
legitimate leader output. -/
theorem rawZeroClosed_no_finite_birth
    (C : PPartialConfig 2 1 0 0)
    (hC : InRawZeroClosedClass C) :
    ¬ ∃ word : DetSchedule 2,
      PPartialLegitUnconditional rawZeroClosed_hpsi 0 0
        (runLocalSchedule rawZeroClosedRing
          (P_partialUnconditional rawZeroClosed_hpsi 0 0) C word) := by
  rintro ⟨word, hlegit⟩
  exact rawZeroClosed_not_legit _
    (rawZeroClosed_run C hC word) hlegit

/-! ## Homogeneous deletion input and producer no-go -/

def rawZeroHomogeneousDeletionCore : BoundedAgentState 1 0 :=
  { rawZeroClosedCoreN with
    state := .eliminate_signal
    path := .some 0 0 }

def rawZeroHomogeneousDeletionState : ExpiringAgentState 1 0 0 :=
  rawZeroClosedLift rawZeroHomogeneousDeletionCore

def rawZeroHomogeneousDeletionConfig : PPartialConfig 2 1 0 0 :=
  fun _ => rawZeroHomogeneousDeletionState

/-- Initiator/responder separation makes the homogeneous deletion input
non-fixed on the nontrivial ring. -/
theorem rawZeroHomogeneousDeletion_not_fixed :
    localStep rawZeroClosedRing
      (P_partialUnconditional rawZeroClosed_hpsi 0 0)
      rawZeroHomogeneousDeletionConfig 0 ≠
        rawZeroHomogeneousDeletionConfig := by
  intro heq
  have hsite := congrFun heq 1
  exact
    (by decide : rawZeroClosedN ≠ rawZeroHomogeneousDeletionState) hsite

/-- Nevertheless, three exact raw interactions take the homogeneous input
into phase `p5 = (H,R)` of the closed zero-leader class. -/
theorem rawZeroHomogeneousDeletion_enters_closed :
    runLocalSchedule rawZeroClosedRing
      (P_partialUnconditional rawZeroClosed_hpsi 0 0)
      rawZeroHomogeneousDeletionConfig [0, 1, 0] =
        rawZeroClosedConfig .p5 := by
  funext i
  rcases rawZeroClosed_fin2_cases i with rfl | rfl <;> rfl

theorem rawZeroClosed_seed_leaderCount_zero :
    P_partialLeaderCount (rawZeroClosedConfig .p5) = 0 := by
  rfl

/-- The exact unconditional base producer is false on this nontrivial ring for
every proposed bound. -/
theorem rawZeroClosed_not_baseProducer (baseBound : Nat) :
    ¬ PPartialBaseProducerUnconditional rawZeroClosed_hpsi 0 0
      rawZeroClosedRing baseBound := by
  intro hproducer
  obtain ⟨word, _hLength, hlegit⟩ :=
    hproducer (rawZeroClosedConfig .p5) (by
      rw [rawZeroClosed_seed_leaderCount_zero]
      omega)
  exact rawZeroClosed_no_finite_birth
    (rawZeroClosedConfig .p5) ⟨.p5, rfl⟩ ⟨word, hlegit⟩

#print axioms rawZeroClosed_transition_NR
#print axioms rawZeroClosed_localStep
#print axioms rawZeroClosed_closedPred
#print axioms rawZeroClosed_no_finite_birth
#print axioms rawZeroHomogeneousDeletion_enters_closed
#print axioms rawZeroClosed_not_baseProducer

end PPLLCompleteMultiLeaderCleanup
