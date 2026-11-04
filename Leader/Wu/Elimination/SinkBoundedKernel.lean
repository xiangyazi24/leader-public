import Leader.Wu.Protocol.BoundedState
import Leader.Wu.Elimination.SinkAbsorbStepShape

/-!
# Exact finite implementation of the elimination kernel

The elimination analysis uses `AgentState`, whose audit payloads include raw
natural numbers.  The physical K2 row changes only already finite fields.  We
prove preservation of the entire declared value domain, then reify that exact
row on `BoundedAgentState`.  No saturation, normalization, additional protocol
bit, or population-size parameter is introduced.

This certifies the elimination row and its same-edge configuration execution.
It does not identify an assembled controller dispatcher with that row.
-/

namespace LDSinkBoundedKernel

open PPLLRepair LDSinkKernelC LDSinkGapCleanup LDSinkProtectedAbsorption

set_option autoImplicit false

private theorem fire_domain {ψ : Nat} (hψ : 0 < ψ) (κ : Nat)
    (l r : AgentState ψ) :
    ((eliminateLeadersNoCollisionFire hψ l r).1.inProtocolDomain κ ↔
      l.inProtocolDomain κ) ∧
    ((eliminateLeadersNoCollisionFire hψ l r).2.inProtocolDomain κ ↔
      r.inProtocolDomain κ) := by
  unfold eliminateLeadersNoCollisionFire
  repeat (first | exact ⟨Iff.rfl, Iff.rfl⟩ | split)

private theorem move_domain {ψ : Nat} (hψ : 0 < ψ) (κ : Nat)
    (nl : Fin ψ) (l r : AgentState ψ) :
    ((absorbProtectedMove hψ nl l r).1.inProtocolDomain κ ↔
      l.inProtocolDomain κ) ∧
    ((absorbProtectedMove hψ nl l r).2.inProtocolDomain κ ↔
      r.inProtocolDomain κ) := by
  unfold absorbProtectedMove eliminateLeadersNoCollisionZeroLeaderEgressMove
  repeat (first | exact ⟨Iff.rfl, Iff.rfl⟩ | split)

private theorem signal_domain {ψ : Nat} (κ : Nat)
    (nl : Fin ψ) (l r : AgentState ψ) :
    ((eliminateLeadersNoCollisionSignalLeaderSink nl l r).1.inProtocolDomain κ ↔
      l.inProtocolDomain κ) ∧
    ((eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.inProtocolDomain κ ↔
      r.inProtocolDomain κ) := by
  unfold eliminateLeadersNoCollisionSignalLeaderSink
  repeat (first | exact ⟨Iff.rfl, Iff.rfl⟩ | split)

private theorem dummy_domain {ψ : Nat} (κ : Nat)
    (q : AgentState ψ × AgentState ψ) :
    ((dummyBulletSink q).1.inProtocolDomain κ ↔ q.1.inProtocolDomain κ) ∧
    ((dummyBulletSink q).2.inProtocolDomain κ ↔ q.2.inProtocolDomain κ) := by
  unfold dummyBulletSink
  repeat (first | exact ⟨Iff.rfl, Iff.rfl⟩ | split)

/-- All six unbounded payload restrictions are preserved in both directions.
The proof follows FIRE, protected MOVE, SIGNAL, and dummy cleanup separately;
in particular it covers every count value, including the bound itself. -/
theorem kernel_domain_iff {ψ : Nat} (hψ : 0 < ψ) (κ : Nat)
    (l r : AgentState ψ) :
    ((sinkKernelC hψ l r).1.inProtocolDomain κ ↔ l.inProtocolDomain κ) ∧
    ((sinkKernelC hψ l r).2.inProtocolDomain κ ↔ r.inProtocolDomain κ) := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := absorbProtectedMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  have h0 := fire_domain hψ κ l r
  have h1 := move_domain hψ κ nl q0.1 q0.2
  have h2 := signal_domain κ nl q1.1 q1.2
  have h3 := dummy_domain κ q2
  exact ⟨h3.1.trans (h2.1.trans (h1.1.trans h0.1)),
    h3.2.trans (h2.2.trans (h1.2.trans h0.2))⟩

/-- The counted row is the exact K2 output, reified using its proved domain
closure.  Its type depends only on the two approved local parameters. -/
def boundedKernel {ψ κ : Nat} (hψ : 0 < ψ)
    (l r : BoundedAgentState ψ κ) :
    BoundedAgentState ψ κ × BoundedAgentState ψ κ :=
  let q := sinkKernelC hψ l.erase r.erase
  let hd := kernel_domain_iff hψ κ l.erase r.erase
  (BoundedAgentState.ofDomain q.1 (hd.1.mpr l.erase_inProtocolDomain),
   BoundedAgentState.ofDomain q.2 (hd.2.mpr r.erase_inProtocolDomain))

/-- Erasure commutes with the complete physical row on every bounded input,
without any coherence, cleanup, reachability, or strict count-bound premise. -/
theorem erase_boundedKernel {ψ κ : Nat} (hψ : 0 < ψ)
    (l r : BoundedAgentState ψ κ) :
    ((boundedKernel hψ l r).1.erase, (boundedKernel hψ l r).2.erase) =
      sinkKernelC hψ l.erase r.erase := by
  simp only [boundedKernel, BoundedAgentState.erase_ofDomain]

/-- Pointwise erasure retains the entire audit configuration. -/
def eraseConfig {ψ κ n : Nat} (C : Fin n → BoundedAgentState ψ κ) :
    Fin n → AgentState ψ := fun i => (C i).erase

/-- The same directed edge and endpoint priority as `sinkStepC`. -/
def boundedStep {ψ κ n : Nat} (hψ : 0 < ψ) (F : GapFrame n)
    (C : Fin n → BoundedAgentState ψ κ) (e : Fin n) :
    Fin n → BoundedAgentState ψ κ :=
  let q := boundedKernel hψ (C e) (C (F.ring.rightNeighbor e))
  fun i => if i = e then q.1
    else if i = F.ring.rightNeighbor e then q.2 else C i

/-- One physical scheduler interaction corresponds to exactly one audit
interaction.  In particular the reduction inserts no uncharged stutters. -/
theorem erase_boundedStep {ψ κ n : Nat} (hψ : 0 < ψ) (F : GapFrame n)
    (C : Fin n → BoundedAgentState ψ κ) (e : Fin n) :
    eraseConfig (boundedStep hψ F C e) = sinkStepC hψ F (eraseConfig C) e := by
  have hk := erase_boundedKernel hψ (C e) (C (F.ring.rightNeighbor e))
  funext i
  simp only [eraseConfig, boundedStep, sinkStepC, updatePair]
  split
  · exact congrArg Prod.fst hk
  · split
    · exact congrArg Prod.snd hk
    · rfl

/-- Execute a finite word of actual directed-edge choices. -/
def run {S E : Type} (step : S → E → S) : S → List E → S
  | s, [] => s
  | s, e :: es => run step (step s e) es

/-- The exact finite-carrier execution realizes the audit execution for every
schedule word.  The scheduler alphabet and word length are unchanged. -/
theorem erase_run {ψ κ n : Nat} (hψ : 0 < ψ) (F : GapFrame n)
    (C : Fin n → BoundedAgentState ψ κ) (es : List (Fin n)) :
    eraseConfig (run (boundedStep hψ F) C es) =
      run (sinkStepC hψ F) (eraseConfig C) es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    simp only [run, ih, erase_boundedStep]

/-- The finite implementation reads the same leader output at every site. -/
theorem leader_output {ψ κ n : Nat} (C : Fin n → BoundedAgentState ψ κ)
    (i : Fin n) : (eraseConfig C i).leader = (C i).leader := rfl

end LDSinkBoundedKernel

#print axioms LDSinkBoundedKernel.kernel_domain_iff
#print axioms LDSinkBoundedKernel.erase_boundedKernel
#print axioms LDSinkBoundedKernel.erase_boundedStep
#print axioms LDSinkBoundedKernel.erase_run
