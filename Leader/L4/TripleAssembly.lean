import Leader.L4.TripleResidual
import Leader.L4.TripleRenewal

namespace L4.TripleAssembly
open TripleResidual TripleRenewal

/-- The remaining physical inputs, on the actual stopped pair-step
observer. The numerical replay and restart estimates do not assume these
inputs hold by definition. Distances in this interface are physical. -/
structure PhysicalStageB {p c n : Nat} (x : Config p c n) (a b : Nat) where
  prep : Stage (advance (p:=p) (c:=c) (n:=n)) (init x)
  sealed : Obs p c n → Prop
  prepMean : IIDExpectedHittingTimeAtMost prep.next prep.ready prep.start (6*n*(a+b))
  prepared : ∀ y, prep.reachable y → prep.ready y → (prep.project y).stopped ≠ true →
    sealed (prep.project y)
  oneEdge : b=1 → ∀ y, sealed y →
    IIDExpectedHittingTimeAtMost advance (fun u => u.stopped = true) y (6*n*(a+1))
  moderate : 2≤b → a≤2*b → ∀ y, sealed y → y.stopped ≠ true →
    Nonempty (UniformAttempt advance (fun u => u.stopped = true) sealed (n*(5*a+4*b)) 64 y)
  long : 2≤b → 2*b<a → ∀ y, sealed y → y.stopped ≠ true →
    Nonempty (UniformAttempt advance (fun u => u.stopped = true) sealed (10*n*(a+b)) 256 y)

def ConcretePhysicalStageB : Prop :=
  ∀ {p c n : Nat} (x : Config p c n) (v : Fin n) (a b : Nat),
    2 ≤ p → 12 ≤ c → 4 ≤ n → QuietEntrance x →
    Start x v a b → Nonempty (PhysicalStageB x (a+1) (b+1))

theorem sharp_clock_of_physical_stageB (h : ConcretePhysicalStageB) :
    ConcreteTripleSharpClock := by
  intro p c n x v a b hp hc hn hx hv
  obtain ⟨s⟩ := h x v a b hp hc hn hx hv
  have ht := consecutiveRootClock_of_interfaces s.prep (fun u => u.stopped = true)
    s.sealed (a+1) (b+1) (by omega) s.prepMean s.prepared s.oneEdge s.moderate s.long
  simpa only [show a + 1 + (b+1) = a+b+2 by omega] using ht

end L4.TripleAssembly

#print axioms L4.TripleAssembly.sharp_clock_of_physical_stageB
