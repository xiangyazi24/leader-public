import Leader.Wu.Elimination.SinkGapCleanupBound
import Leader.Wu.Elimination.TwoGapFrame

namespace LDSinkTwoGapEpochDefs

open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDSinkGapDoneInvariant
open LDSinkGapBlockedPreStep
  LDSinkGapCleanupBound LDTwoGapFrame PPLLRepair
open Classical
open FiniteUniformStoppingTree

set_option autoImplicit false

inductive GhostPhase where
  | seekK
  | transit
  | parked
  | resetK
  | seekJ
  | favorable
  deriving DecidableEq

structure EpochState (n ψ : Nat) (F : TwoGapFrame n) where
  conf : Fin n → AgentState ψ
  phase : GhostPhase

def Entrance {n ψ : Nat} (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : EpochState n ψ F) : Prop :=
  GapInvariant hψ F.recovery x.conf ∧
  GapInvariant hψ F.attack x.conf ∧
  ((x.conf (F.attack.pos F.attack.d)).signal_B = (1 : Fin 2) ∨
    x.phase = .transit ∨ x.phase = .parked)

/-- Success means that one endpoint of the attack gap has disappeared. -/
def Success {n ψ : Nat} (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) : Prop :=
  EndpointDeleted F.attack C

/-- Post-state shape of a shielded absorption at the attack victim. -/
def Loss {n ψ : Nat} (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) : Prop :=
  (C (F.attack.pos 1)).bullet = (0 : Fin 3) ∧
  (C (F.attack.pos 0)).shield = true ∧
  (C (F.attack.pos 0)).leader = true

/-- The pre-state had the tagged live shot parked at position 1, and the
post-state has consumed it while leaving the victim shielded and alive. -/
def AbsorbedAt {n ψ : Nat} (F : TwoGapFrame n)
    (Cpre Cpost : Fin n → AgentState ψ) : Prop :=
  (Cpre (F.attack.pos 1)).bullet = (2 : Fin 3) ∧
  (Cpre (F.attack.pos 0)).leader = true ∧
  Loss F Cpost

instance instDecidableSuccess {n ψ : Nat} (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) : Decidable (Success F C) := by
  unfold Success EndpointDeleted
  infer_instance

instance instDecidableLoss {n ψ : Nat} (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) : Decidable (Loss F C) := by
  unfold Loss
  infer_instance

instance instDecidableAbsorbedAt {n ψ : Nat} (F : TwoGapFrame n)
    (Cpre Cpost : Fin n → AgentState ψ) : Decidable (AbsorbedAt F Cpre Cpost) := by
  unfold AbsorbedAt
  infer_instance

/-- The epoch always uses the physical K2 step on the attack frame. -/
def epochStepConf {n ψ : Nat} (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : EpochState n ψ F) (e : Fin n) : Fin n → AgentState ψ :=
  sinkStepC hψ F.attack x.conf e

/-- Minimal ghost bookkeeping.  A tagged shot becomes parked once its live
bullet is observed at attack position 1; a parked tag stays parked. -/
def advancePhase {n ψ : Nat} (F : TwoGapFrame n) (p : GhostPhase)
    (C : Fin n → AgentState ψ) : GhostPhase :=
  match p with
  | .transit =>
      if (C (F.attack.pos 1)).bullet = (2 : Fin 3) then .parked else .transit
  | .parked => .parked
  | q => q

def ParkedAbsorption {n ψ : Nat} (F : TwoGapFrame n)
    (x : EpochState n ψ F) (Cpost : Fin n → AgentState ψ) : Prop :=
  x.phase = .parked ∧ AbsorbedAt F x.conf Cpost

instance instDecidableParkedAbsorption {n ψ : Nat} (F : TwoGapFrame n)
    (x : EpochState n ψ F) (Cpost : Fin n → AgentState ψ) :
    Decidable (ParkedAbsorption F x Cpost) := by
  unfold ParkedAbsorption
  infer_instance

/-- One inner attempt: shielded absorption is a failed attempt. -/
def innerStep {n ψ : Nat} (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : EpochState n ψ F) (e : Fin n) : StopNode (EpochState n ψ F) :=
  let C' := epochStepConf hψ F x e
  if Success F C' then .success
  else if ParkedAbsorption F x C' then .failure
  else .active { conf := C', phase := advancePhase F x.phase C' }

/-- One outer round: shielded absorption restarts the K-side renewal. -/
def roundStep {n ψ : Nat} (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : EpochState n ψ F) (e : Fin n) : StopNode (EpochState n ψ F) :=
  let C' := epochStepConf hψ F x e
  if Success F C' then .success
  else if ParkedAbsorption F x C' then
    .active { conf := C', phase := .resetK }
  else .active { conf := C', phase := advancePhase F x.phase C' }

theorem success_iff_endpoints {n ψ : Nat} (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) :
    Success F C ↔
      (C (F.attack.pos 0)).leader = false ∨
      (C (F.attack.pos F.attack.d)).leader = false := by
  rfl

theorem innerStep_failure_requires_parked_live {n ψ : Nat}
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : EpochState n ψ F) (e : Fin n)
    (hf : innerStep hψ F x e =
      (.failure : StopNode (EpochState n ψ F))) :
    x.phase = .parked ∧
      (x.conf (F.attack.pos 1)).bullet = (2 : Fin 3) := by
  unfold innerStep at hf
  by_cases hs : Success F (epochStepConf hψ F x e)
  · rw [if_pos hs] at hf
    cases hf
  · rw [if_neg hs] at hf
    by_cases ha : ParkedAbsorption F x (epochStepConf hψ F x e)
    · rw [if_pos ha] at hf
      exact ⟨ha.1, ha.2.1⟩
    · rw [if_neg ha] at hf
      cases hf

theorem innerStep_no_failure_of_not_parked {n ψ : Nat}
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : EpochState n ψ F) (e : Fin n)
    (hp : x.phase ≠ .parked) :
    innerStep hψ F x e ≠ (.failure : StopNode (EpochState n ψ F)) := by
  intro hf
  exact hp (innerStep_failure_requires_parked_live hψ F x e hf).1

theorem roundStep_eq_innerStep_of_not_absorbed {n ψ : Nat}
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : EpochState n ψ F) (e : Fin n)
    (ha : ¬ AbsorbedAt F x.conf (epochStepConf hψ F x e)) :
    roundStep hψ F x e = innerStep hψ F x e := by
  have hp : ¬ ParkedAbsorption F x (epochStepConf hψ F x e) := by
    intro h
    exact ha h.2
  unfold roundStep innerStep
  by_cases hs : Success F (epochStepConf hψ F x e)
  · simp [hs]
  · simp [hs, hp]

private theorem directedRing_eq {n : Nat} (R R' : DirectedRing n) : R = R' := by
  cases R with
  | mk hR =>
      cases R' with
      | mk hR' =>
          have h : hR = hR' := Subsingleton.elim _ _
          cases h
          rfl

private theorem sinkStepC_frame_independent {n ψ : Nat} (hψ : ψ > 0)
    (F G : GapFrame n) (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ F C e = sinkStepC hψ G C e := by
  unfold sinkStepC
  rw [directedRing_eq F.ring G.ring]

/-- This is intentionally only the two one-gap closure obligations.  It does
not claim that the signal/ghost disjunct of `Entrance` is already closed. -/
structure EpochClosure {n ψ : Nat} (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : EpochState n ψ F) (e : Fin n) : Prop where
  recovery :
    ¬ GapDoneC F.recovery x.conf →
      GapDoneC F.recovery (epochStepConf hψ F x e) ∨
      GapInvariant hψ F.recovery (epochStepConf hψ F x e)
  attack :
    ¬ GapDoneC F.attack x.conf →
      GapDoneC F.attack (epochStepConf hψ F x e) ∨
      GapInvariant hψ F.attack (epochStepConf hψ F x e)

theorem epochClosure_of_entrance {n ψ : Nat} (hψ : ψ > 0)
    (F : TwoGapFrame n) (x : EpochState n ψ F) (e : Fin n)
    (hE : Entrance hψ F x) : EpochClosure hψ F x e := by
  constructor
  · intro hn
    have h := sinkStepC_invariant_or_done'
      (hψ := hψ) (F := F.recovery) (C := x.conf) (e := e) hE.1 hn
    have heq : sinkStepC hψ F.recovery x.conf e = epochStepConf hψ F x e := by
      unfold epochStepConf
      exact sinkStepC_frame_independent hψ F.recovery F.attack x.conf e
    simpa only [heq] using h
  · intro hn
    simpa only [epochStepConf] using
      (sinkStepC_invariant_or_done'
        (hψ := hψ) (F := F.attack) (C := x.conf) (e := e) hE.2.1 hn)

/-- Off the one-gap stopping sets, the two invariant components of `Entrance`
survive.  No claim about the third entrance disjunct is made here. -/
theorem entrance_preserved_off_terminal {n ψ : Nat} (hψ : ψ > 0)
    (F : TwoGapFrame n) (x : EpochState n ψ F) (e : Fin n)
    (hE : Entrance hψ F x)
    (hrec0 : ¬ GapDoneC F.recovery x.conf)
    (hatt0 : ¬ GapDoneC F.attack x.conf)
    (hrec1 : ¬ GapDoneC F.recovery (epochStepConf hψ F x e))
    (hatt1 : ¬ GapDoneC F.attack (epochStepConf hψ F x e)) :
    GapInvariant hψ F.recovery (epochStepConf hψ F x e) ∧
    GapInvariant hψ F.attack (epochStepConf hψ F x e) := by
  have hc := epochClosure_of_entrance hψ F x e hE
  constructor
  · rcases hc.recovery hrec0 with hd | hi
    · exact (hrec1 hd).elim
    · exact hi
  · rcases hc.attack hatt0 with hd | hi
    · exact (hatt1 hd).elim
    · exact hi

#print axioms success_iff_endpoints
#print axioms innerStep_failure_requires_parked_live
#print axioms innerStep_no_failure_of_not_parked
#print axioms roundStep_eq_innerStep_of_not_absorbed
#print axioms epochClosure_of_entrance
#print axioms entrance_preserved_off_terminal

end LDSinkTwoGapEpochDefs
