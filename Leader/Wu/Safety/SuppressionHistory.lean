import Leader.Wu.Protocol.BoundedProtocol
import Leader.Wu.Scheduler.WhpProfiles

/-!
# Historical reset-receipt refinement

Algorithm 14's `reset_cmd` is a moving token, not a persistent receipt bit.
This finite ghost layer records whether an agent has ever held the token during
a SUPPRESS_SIG call while erasing exactly to the integrated repaired audit
transition.
-/

namespace PPLLSuppressionHistory

open PPLL PPLLRepair

structure ReceiptAgentState (ψ : Nat) where
  concrete : AgentState ψ
  receivedReset : Bool
  deriving DecidableEq, Repr

namespace ReceiptAgentState

def erase {ψ : Nat} (s : ReceiptAgentState ψ) : AgentState ψ := s.concrete

end ReceiptAgentState

private def suppressStages {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : List (AgentState ψ × AgentState ψ) :=
  let q0 := suppressSigStart l r
  let q1 := suppressSigMoveReset q0.1 q0.2
  let q2 := suppressSigTerminal hψ q1.1 q1.2
  let q3 := suppressSigEcho q2.1 q2.2
  let q4 := suppressSigFinish q3.1 q3.2
  [q0, q1, q2, q3, q4]

private def sawLeftReset {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : Bool :=
  l.reset_cmd || (suppressStages hψ l r).any (fun q => q.1.reset_cmd)

private def sawRightReset {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : Bool :=
  r.reset_cmd || (suppressStages hψ l r).any (fun q => q.2.reset_cmd)

/-- Refined local transition. Ghost observations do not influence concrete
execution. -/
def transition {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : ReceiptAgentState ψ) :
    ReceiptAgentState ψ × ReceiptAgentState ψ :=
  let pre := ppllIntegratedBeforeSuppress hψ κ l.concrete r.concrete
  let out := ppllIntegratedRepair hψ κ l.concrete r.concrete
  ({ concrete := out.1,
     receivedReset := l.receivedReset || sawLeftReset hψ pre.1 pre.2 },
   { concrete := out.2,
     receivedReset := r.receivedReset || sawRightReset hψ pre.1 pre.2 })

/-- Ghost erasure commutes exactly with the integrated repaired transition. -/
theorem erase_transition {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : ReceiptAgentState ψ) :
    let q := transition hψ κ l r
    (q.1.concrete, q.2.concrete) =
      ppllIntegratedRepair hψ κ l.concrete r.concrete := by
  simp only [transition]

theorem transition_left_received {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : ReceiptAgentState ψ) (h : l.receivedReset = true) :
    (transition hψ κ l r).1.receivedReset = true := by
  simp only [transition]
  rw [h]
  rfl

theorem transition_right_received {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : ReceiptAgentState ψ) (h : r.receivedReset = true) :
    (transition hψ κ l r).2.receivedReset = true := by
  simp only [transition]
  rw [h]
  rfl

/-- Correct historical suppression predicate. -/
def HistoricallySuppressed {ψ n : Nat} (_ring : DirectedRing n)
    (C : Fin n → ReceiptAgentState ψ) : Prop :=
  ∀ i, (C i).receivedReset = true

/-- One configuration step of the receipt-refined transition. -/
def step {ψ n : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → ReceiptAgentState ψ) (e : Fin n) :
    Fin n → ReceiptAgentState ψ :=
  let q := transition hψ κ (C e) (C (ring.rightNeighbor e))
  fun k => if k = e then q.1
    else if k = ring.rightNeighbor e then q.2 else C k

/-- Historical receipt is monotone under every refined interaction. -/
theorem historicallySuppressed_preserved
    {ψ n : Nat} (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → ReceiptAgentState ψ) (hC : HistoricallySuppressed ring C)
    (e : Fin n) : HistoricallySuppressed ring (step hψ κ ring C e) := by
  have hl := transition_left_received hψ κ (C e)
    (C (ring.rightNeighbor e)) (hC e)
  have hr := transition_right_received hψ κ (C e)
    (C (ring.rightNeighbor e)) (hC (ring.rightNeighbor e))
  intro k
  by_cases hke : k = e
  · simp only [step, if_pos hke]
    exact hl
  · by_cases hkj : k = ring.rightNeighbor e
    · simp only [step, if_neg hke, if_pos hkj]
      exact hr
    · simp only [step, if_neg hke, if_neg hkj]
      exact hC k

/-- Population protocol carrying the historical receipt ghost. -/
def protocol {ψ : Nat} (hψ : ψ > 0) (κ : Nat) : PopulationProtocol where
  Q := ReceiptAgentState ψ
  Y := LeaderOutput
  transition := transition hψ κ
  output := fun s => AgentState.outputFn s.concrete

/-! ## Finite bounded receipt refinement -/

structure BoundedReceiptAgentState (ψ κ : Nat) where
  concrete : BoundedAgentState ψ κ
  receivedReset : Bool
  deriving DecidableEq, Repr

private def attachBoundedReceipts {ψ κ : Nat}
    (out : BoundedAgentState ψ κ × BoundedAgentState ψ κ)
    (leftSeen rightSeen : Bool) :
    BoundedReceiptAgentState ψ κ × BoundedReceiptAgentState ψ κ :=
  ({ concrete := out.1, receivedReset := leftSeen },
   { concrete := out.2, receivedReset := rightSeen })

private def boundedLeftSeen {ψ κ : Nat} (hψ : ψ > 0)
    (l r : BoundedReceiptAgentState ψ κ) : Bool :=
  let pre := ppllIntegratedBeforeSuppress hψ κ
    (BoundedAgentState.erase l.concrete) (BoundedAgentState.erase r.concrete)
  l.receivedReset || sawLeftReset hψ pre.1 pre.2

private def boundedRightSeen {ψ κ : Nat} (hψ : ψ > 0)
    (l r : BoundedReceiptAgentState ψ κ) : Bool :=
  let pre := ppllIntegratedBeforeSuppress hψ κ
    (BoundedAgentState.erase l.concrete) (BoundedAgentState.erase r.concrete)
  r.receivedReset || sawRightReset hψ pre.1 pre.2

/-- Finite bounded receipt transition erasing to the integrated bounded
candidate. -/
def boundedTransition {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : BoundedReceiptAgentState ψ κ) :
    BoundedReceiptAgentState ψ κ × BoundedReceiptAgentState ψ κ :=
  let out := PPLLRepair.integratedBoundedTransition hψ κ l.concrete r.concrete
  attachBoundedReceipts out (boundedLeftSeen hψ l r)
    (boundedRightSeen hψ l r)

theorem erase_boundedTransition {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : BoundedReceiptAgentState ψ κ) :
    let q := boundedTransition hψ κ l r
    (q.1.concrete, q.2.concrete) =
      PPLLRepair.integratedBoundedTransition hψ κ l.concrete r.concrete := by
  simp only [boundedTransition, attachBoundedReceipts]

/-- Composed erasure to the integrated audit transition. -/
theorem erase_boundedTransition_to_audit {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : BoundedReceiptAgentState ψ κ) :
    let q := boundedTransition hψ κ l r
    BoundedAgentState.erase q.1.concrete = (ppllIntegratedRepair hψ κ
        (BoundedAgentState.erase l.concrete)
        (BoundedAgentState.erase r.concrete)).1 ∧
      BoundedAgentState.erase q.2.concrete = (ppllIntegratedRepair hψ κ
        (BoundedAgentState.erase l.concrete)
        (BoundedAgentState.erase r.concrete)).2 := by
  have hc := erase_boundedTransition hψ κ l r
  have ha := PPLLRepair.erase_integratedBoundedTransition
    hψ κ l.concrete r.concrete
  dsimp only at hc ha ⊢
  have hc1 : (boundedTransition hψ κ l r).1.concrete =
      (PPLLRepair.integratedBoundedTransition hψ κ l.concrete r.concrete).1 := by
    simpa only using congrArg Prod.fst hc
  have hc2 : (boundedTransition hψ κ l r).2.concrete =
      (PPLLRepair.integratedBoundedTransition hψ κ l.concrete r.concrete).2 := by
    simpa only using congrArg Prod.snd hc
  rw [hc1, hc2]
  exact ha

theorem boundedTransition_left_received {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : BoundedReceiptAgentState ψ κ) (h : l.receivedReset = true) :
    (boundedTransition hψ κ l r).1.receivedReset = true := by
  simp only [boundedTransition, attachBoundedReceipts]
  unfold boundedLeftSeen
  rw [h]
  rfl

theorem boundedTransition_right_received {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : BoundedReceiptAgentState ψ κ) (h : r.receivedReset = true) :
    (boundedTransition hψ κ l r).2.receivedReset = true := by
  simp only [boundedTransition, attachBoundedReceipts]
  unfold boundedRightSeen
  rw [h]
  rfl

private theorem sawLeftReset_of_leader {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (h : l.leader = true) :
    sawLeftReset hψ l r = true := by
  simp [sawLeftReset, suppressStages, suppressSigStart, h]

private theorem sawRightReset_of_leader {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (h : l.leader = true) :
    sawRightReset hψ l r = true := by
  simp [sawRightReset, suppressStages, suppressSigStart,
    suppressSigMoveReset, h]

/-- When the integrated prefix presents an initiator leader to SUPPRESS_SIG,
both interacting agents hold the reset token during that call and are marked
as historical recipients. -/
theorem boundedTransition_receives_of_preSuppress_leader
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : BoundedReceiptAgentState ψ κ)
    (hleader : (ppllIntegratedBeforeSuppress hψ κ
      (BoundedAgentState.erase l.concrete)
      (BoundedAgentState.erase r.concrete)).1.leader = true) :
    (boundedTransition hψ κ l r).1.receivedReset = true ∧
      (boundedTransition hψ κ l r).2.receivedReset = true := by
  have hlseen := sawLeftReset_of_leader hψ
    (ppllIntegratedBeforeSuppress hψ κ
      (BoundedAgentState.erase l.concrete)
      (BoundedAgentState.erase r.concrete)).1
    (ppllIntegratedBeforeSuppress hψ κ
      (BoundedAgentState.erase l.concrete)
      (BoundedAgentState.erase r.concrete)).2 hleader
  have hrseen := sawRightReset_of_leader hψ
    (ppllIntegratedBeforeSuppress hψ κ
      (BoundedAgentState.erase l.concrete)
      (BoundedAgentState.erase r.concrete)).1
    (ppllIntegratedBeforeSuppress hψ κ
      (BoundedAgentState.erase l.concrete)
      (BoundedAgentState.erase r.concrete)).2 hleader
  have hlall : boundedLeftSeen hψ l r = true := by
    dsimp only [boundedLeftSeen]
    rw [hlseen]
    simp
  have hrall : boundedRightSeen hψ l r = true := by
    dsimp only [boundedRightSeen]
    rw [hrseen]
    simp
  change boundedLeftSeen hψ l r = true ∧ boundedRightSeen hψ l r = true
  exact ⟨hlall, hrall⟩

def boundedReceiptCertificate (ψ κ : Nat) :
    ExhaustiveList (BoundedReceiptAgentState ψ κ) :=
  ExhaustiveList.mapSurjective
    (ExhaustiveList.prod (PPLLFinite.boundedAgentState ψ κ)
      ExhaustiveList.bool)
    (fun x => ({ concrete := x.1, receivedReset := x.2 } :
      BoundedReceiptAgentState ψ κ))
    (by
      intro s
      exact ⟨(s.concrete, s.receivedReset), by cases s; rfl⟩)

def boundedProtocol {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    PopulationProtocol where
  Q := BoundedReceiptAgentState ψ κ
  Y := LeaderOutput
  transition := boundedTransition hψ κ
  output := fun s => AgentState.outputFn (BoundedAgentState.erase s.concrete)

end PPLLSuppressionHistory
