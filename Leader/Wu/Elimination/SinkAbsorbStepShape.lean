import Leader.Wu.Elimination.SinkAbsorbKernel
import Leader.Wu.Elimination.SinkGapCleanup


open LDSinkGapCleanup LDSinkKernelC PPLLRepair


namespace LDSinkProtectedAbsorption


set_option autoImplicit false


variable {n ψ : Nat}


/-!
# CStages: protected absorption and the raw ring-step dichotomy


The guard is evaluated AFTER FIRE. We do not assume that FIRE is inert.
The exact protected output retains the entire post-FIRE initiator and
replaces the responder's bullet and signal by zero and one, respectively.
Relative to the original initiator, FIRE may change bullet, shield, and
signal; claiming that only its signal can change would be incorrect.


No GapInvariant, closure, rank, or probabilistic hypothesis is used here.
This file targets the supplied local C/gap interfaces. The newer gap module
was not available on connected main; this file was not compiler-tested here.
-/


/-- The original whole-ring update with only its local kernel replaced. -/
def sinkStepC (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) : Fin n → AgentState ψ :=
  updatePair C e (F.ring.rightNeighbor e)
    (sinkKernelC hψ (C e) (C (F.ring.rightNeighbor e)))


/-- Exactly absorbProtectedMove's guard, on FIRE's two outputs. -/
def ProtectedGuard (hψ : ψ > 0) (l r : AgentState ψ) : Prop :=
  (eliminateLeadersNoCollisionFire hψ l r).1.leader = true ∧
  (eliminateLeadersNoCollisionFire hψ l r).1.shield = true ∧
  (eliminateLeadersNoCollisionFire hψ l r).2.leader = false ∧
  (eliminateLeadersNoCollisionFire hψ l r).2.bullet = (2 : Fin 3)


/-- The six requested field facts, reusable for a pair of updated cells. -/
def ProtectedAbsorbShape (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) : Prop :=
  q.2.bullet = (0 : Fin 3) ∧
  q.2.signal_B = (1 : Fin 2) ∧
  q.1.leader = l.leader ∧ q.2.leader = r.leader ∧
  q.1.label = l.label ∧ q.2.label = r.label


/-- Off the post-FIRE guard, the two raw steps are exactly equal. -/
theorem sinkStepC_eq_of_not_guard (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hnot : ¬ ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e))) :
    sinkStepC hψ F C e = sinkStep hψ F C e := by
  have hk := kernelC_eq_of_not_protected hψ
    (C e) (C (F.ring.rightNeighbor e)) hnot
  unfold sinkStepC sinkStep
  rw [hk]


/-- Neither FIRE branch changes a leader bit. -/
private theorem fire_leaders (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.leader = l.leader ∧
    (eliminateLeadersNoCollisionFire hψ l r).2.leader = r.leader := by
  by_cases hl : l.leader = true ∧ l.signal_B = (1 : Fin 2) <;>
    by_cases hr : r.leader = true ∧ r.signal_B = (1 : Fin 2) <;>
      simp [eliminateLeadersNoCollisionFire, hl, hr]


/-- A protected input has a leader initiator and a follower responder. -/
theorem protectedGuard_input_leaders (hψ : ψ > 0)
    (l r : AgentState ψ) (hg : ProtectedGuard hψ l r) :
    l.leader = true ∧ r.leader = false := by
  have hf := fire_leaders hψ l r
  exact ⟨hf.1.symm.trans hg.1, hf.2.symm.trans hg.2.2.1⟩


/-- After clearing the incoming bullet, SIGNAL seeds one at the responder.
Finite signal cases avoid referring to the stage's private finMax helper. -/
private theorem signal_after_clear (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = true) :
    eliminateLeadersNoCollisionSignalLeaderSink nl l
        { r with bullet := (0 : Fin 3) } =
      (l, { r with bullet := (0 : Fin 3), signal_B := (1 : Fin 2) }) := by
  have htwo : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  rcases htwo l.signal_B with hs | hs <;>
    rcases htwo r.signal_B with ht | ht <;>
      simp [eliminateLeadersNoCollisionSignalLeaderSink, hl, hs, ht] <;>
        rfl


/-- Exact protected suffix on an arbitrary POST-FIRE pair.
FIRE is not called again. The final dummy sink is inert on the cleared
responder, so the post-FIRE initiator is retained as an entire record. -/
theorem protectedAbsorb_postFire (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ)
    (hp : l.leader = true ∧ l.shield = true ∧
      r.leader = false ∧ r.bullet = (2 : Fin 3)) :
    dummyBulletSink
        (eliminateLeadersNoCollisionSignalLeaderSink nl
          (absorbProtectedMove hψ nl l r).1
          (absorbProtectedMove hψ nl l r).2) =
      (l, { r with bullet := (0 : Fin 3), signal_B := (1 : Fin 2) }) := by
  have hm : absorbProtectedMove hψ nl l r =
      (l, { r with bullet := (0 : Fin 3) }) := by
    simp only [absorbProtectedMove, if_pos hp]
  rw [hm]
  change dummyBulletSink
    (eliminateLeadersNoCollisionSignalLeaderSink nl l
      { r with bullet := (0 : Fin 3) }) = _
  rw [signal_after_clear nl l r hp.1]
  simp [dummyBulletSink, hp.1, hp.2.2.1]


/-- Compose FIRE with the exact protected suffix; FIRE need not be inert. -/
theorem sinkKernelC_protected_eq (hψ : ψ > 0) (l r : AgentState ψ)
    (hg : ProtectedGuard hψ l r) :
    sinkKernelC hψ l r =
      ((eliminateLeadersNoCollisionFire hψ l r).1,
        { (eliminateLeadersNoCollisionFire hψ l r).2 with
          bullet := (0 : Fin 3), signal_B := (1 : Fin 2) }) := by
  exact protectedAbsorb_postFire hψ
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
    (eliminateLeadersNoCollisionFire hψ l r).1
    (eliminateLeadersNoCollisionFire hψ l r).2 hg


/-- Every initiator field agrees with FIRE's output, not necessarily its input. -/
theorem sinkKernelC_protected_initiator (hψ : ψ > 0)
    (l r : AgentState ψ) (hg : ProtectedGuard hψ l r) :
    (sinkKernelC hψ l r).1 =
      (eliminateLeadersNoCollisionFire hψ l r).1 := by
  rw [sinkKernelC_protected_eq hψ l r hg]


/-- The responder is a follower, hence its FIRE was inert. -/
theorem sinkKernelC_protected_responder (hψ : ψ > 0)
    (l r : AgentState ψ) (hg : ProtectedGuard hψ l r) :
    (sinkKernelC hψ l r).2 =
      { r with bullet := (0 : Fin 3), signal_B := (1 : Fin 2) } := by
  have hr := (protectedGuard_input_leaders hψ l r hg).2
  have hf : (eliminateLeadersNoCollisionFire hψ l r).2 = r := by
    simp [eliminateLeadersNoCollisionFire, hr]
  rw [sinkKernelC_protected_eq hψ l r hg, hf]


/-- Protected absorption removes the live bullet, seeds the absence signal,
and preserves both original leader bits and labels. -/
theorem sinkKernelC_protected (hψ : ψ > 0) (l r : AgentState ψ)
    (hg : ProtectedGuard hψ l r) :
    (sinkKernelC hψ l r).2.bullet = (0 : Fin 3) ∧
    (sinkKernelC hψ l r).2.signal_B = (1 : Fin 2) ∧
    (sinkKernelC hψ l r).1.leader = l.leader ∧
    (sinkKernelC hψ l r).2.leader = r.leader ∧
    (sinkKernelC hψ l r).1.label = l.label ∧
    (sinkKernelC hψ l r).2.label = r.label := by
  have heq := sinkKernelC_protected_eq hψ l r hg
  have hf := fire_leaders hψ l r
  have hlabels := kernelC_labels hψ l r
  refine ⟨?_, ?_, ?_, ?_, hlabels.1, hlabels.2⟩
  · rw [heq]
  · rw [heq]
  · exact (congrArg
      (fun q : AgentState ψ × AgentState ψ => q.1.leader) heq).trans hf.1
  · exact (congrArg
      (fun q : AgentState ψ × AgentState ψ => q.2.leader) heq).trans hf.2


/-- Cells not incident to the scheduled edge are framed. -/
theorem sinkStepC_other (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e k : Fin n) (h1 : k ≠ e)
    (h2 : k ≠ F.ring.rightNeighbor e) :
    sinkStepC hψ F C e k = C k :=
  updatePair_other C e (F.ring.rightNeighbor e) k _ h1 h2


/-- Lift the pair facts to the actual updated cells and frame all others.
The guard itself proves the endpoints distinct via their opposite leader
bits; no additional ring-size or gap-invariant assumption is needed. -/
theorem sinkStepC_protected_shape (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hg : ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e))) :
    ProtectedAbsorbShape (C e) (C (F.ring.rightNeighbor e))
      (sinkStepC hψ F C e e,
        sinkStepC hψ F C e (F.ring.rightNeighbor e)) ∧
    (∀ k : Fin n, k ≠ e → k ≠ F.ring.rightNeighbor e →
      sinkStepC hψ F C e k = C k) := by
  have hlr := protectedGuard_input_leaders hψ
    (C e) (C (F.ring.rightNeighbor e)) hg
  have hne : F.ring.rightNeighbor e ≠ e := by
    intro h
    have hr := hlr.2
    rw [h] at hr
    have hbad : (true : Bool) = false := hlr.1.symm.trans hr
    cases hbad
  have hi : sinkStepC hψ F C e e =
      (sinkKernelC hψ (C e) (C (F.ring.rightNeighbor e))).1 := by
    simp only [sinkStepC, updatePair_initiator]
  have hj : sinkStepC hψ F C e (F.ring.rightNeighbor e) =
      (sinkKernelC hψ (C e) (C (F.ring.rightNeighbor e))).2 := by
    simp [sinkStepC, updatePair, hne]
  constructor
  · rw [hi, hj]
    exact sinkKernelC_protected hψ (C e) (C (F.ring.rightNeighbor e)) hg
  · intro k h1 h2
    exact sinkStepC_other hψ F C e k h1 h2


/-- Every raw K2 step is either the old step or a certified protected
absorption. The second disjunct includes all six field facts and complete
off-edge framing, without treating either outcome as a stopping event. -/
theorem sinkStepC_eq_or_absorb (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ F C e = sinkStep hψ F C e ∨
      (ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e)) ∧
        ProtectedAbsorbShape (C e) (C (F.ring.rightNeighbor e))
          (sinkStepC hψ F C e e,
            sinkStepC hψ F C e (F.ring.rightNeighbor e)) ∧
        (∀ k : Fin n, k ≠ e → k ≠ F.ring.rightNeighbor e →
          sinkStepC hψ F C e k = C k)) := by
  classical
  by_cases hg : ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e))
  · exact Or.inr ⟨hg, sinkStepC_protected_shape hψ F C e hg⟩
  · exact Or.inl (sinkStepC_eq_of_not_guard hψ F C e hg)


end LDSinkProtectedAbsorption


#print axioms LDSinkProtectedAbsorption.sinkStepC_eq_of_not_guard
#print axioms LDSinkProtectedAbsorption.protectedGuard_input_leaders
#print axioms LDSinkProtectedAbsorption.protectedAbsorb_postFire
#print axioms LDSinkProtectedAbsorption.sinkKernelC_protected_eq
#print axioms LDSinkProtectedAbsorption.sinkKernelC_protected_initiator
#print axioms LDSinkProtectedAbsorption.sinkKernelC_protected_responder
#print axioms LDSinkProtectedAbsorption.sinkKernelC_protected
#print axioms LDSinkProtectedAbsorption.sinkStepC_other
#print axioms LDSinkProtectedAbsorption.sinkStepC_protected_shape
#print axioms LDSinkProtectedAbsorption.sinkStepC_eq_or_absorb
