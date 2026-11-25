import Leader.L4.TripleAssembly
import Leader.L4.TripleDirtyPrep
import Leader.L4.TripleModerate
import Leader.L4.RestartClosure

namespace L4.TripleBoundary
open TripleResidual TripleRenewal TripleAssembly TriplePhase TripleDirtyPrep

def Certified {p c n : Nat} (v : Fin n) (a b : Nat) (z : Obs p c n) : Prop :=
  MCOV z.config ∧ COV z.config ∧ ∃ l r, Paired z.config v a b l r

/-- The two remaining disjoint post-preparation cases. These are on the
actual raw original scheduler and already carry a paired seal. -/
structure MissingBoundary : Prop where
  oneEdge : ∀ {p c n a : Nat} (_hn : 4≤n) (v : Fin n) (z : Obs p c n),
    Certified v a 0 z → IIDExpectedHittingTimeAtMost advance (fun u => u.stopped=true)
      z (6*n*(a+1+1))
  long : ∀ {p c n a b : Nat} (_hn : 4≤n) (v : Fin n) (z : Obs p c n),
    1≤b → 2*(b+1)<a+1 → Certified v a b z → z.stopped≠true →
    Nonempty (UniformAttempt advance (fun u => u.stopped=true) (Certified v a b)
      (10*n*((a+1)+(b+1))) 256 z)

theorem physicalStageB_of_boundary (h : MissingBoundary) : ConcretePhysicalStageB := by
  intro p c n x v a b _ _ hn hq hs
  let prep := pairPrepStage hn v a b (init x) (.inr ⟨hq.1,hq.2.1,hs⟩)
  have hb : b+1<n := by
    rcases hs.arity with hh | ⟨hh,_⟩ <;> omega
  refine ⟨⟨prep, Certified v a b, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have hM := expected_pair_cut hn v a b (init x) (.inr ⟨hq.1,hq.2.1,hs⟩) hs.at_least_two hb
    refine expected_mono hM ?_
    rw [show a+b+2=(a+1)+(b+1) by omega]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
  · intro y hy hd hS
    change PairGeom v a b y at hy
    change PairCut v a b y at hd
    change y.stopped≠true at hS
    exact ⟨(hy.resolve_left hS).1,(hy.resolve_left hS).2.1,hd.resolve_left hS⟩
  · intro h1 y hy
    have he : b=0 := by omega
    subst b
    exact h.oneEdge hn v y hy
  · intro hm ha y hy hY
    exact ⟨TripleModerate.moderateAttempt hn v a b (by omega) ha y hy hY⟩
  · intro hm hl y hy hY
    exact h.long hn v y (by omega) hl hy hY

theorem restartTrial_of_boundary (h : MissingBoundary) : RestartSerial.RootIndependentRestartTrial :=
  RestartClosure.concreteRestartTrial_of_physical_stageB (physicalStageB_of_boundary h)

end L4.TripleBoundary
