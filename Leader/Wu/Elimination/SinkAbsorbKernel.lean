import Leader.Wu.Elimination.SinkStallWitness

open LDSinkGapCleanup LDSinkStallWitness
open PPLLRepair

namespace LDSinkKernelC

set_option autoImplicit false

/-!
Variant C changes only MOVE, absorbing an incoming live follower bullet at
an already shielded leader. FIRE precedes that test; SIGNAL and the existing
dummy sink follow it unchanged.

The conservation comparison is for the same input pair. It does not assert
trajectory equivalence, last-leader safety, or general convergence.
-/

/-- The guard is evaluated on the arguments supplied to MOVE, hence on the
post-FIRE pair when called by sinkKernelC. The fallback is the exact egress
MOVE used by the original sinkKernel, not a reimplementation. -/
def absorbProtectedMove {ψ : Nat} (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.leader = true ∧ l.shield = true ∧
      r.leader = false ∧ r.bullet = (2 : Fin 3) then
    (l, { r with bullet := (0 : Fin 3) })
  else
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r

/-- Identical staging and next-label calculation to sinkKernel; only its
MOVE call is replaced. In particular, absorption occurs before SIGNAL. -/
def sinkKernelC {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := absorbProtectedMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  dummyBulletSink q2

/-- The exception guard is explicitly on FIRE's output, not its input. -/
theorem kernelC_eq_of_not_protected {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hnot : ¬ (
      (eliminateLeadersNoCollisionFire hψ l r).1.leader = true ∧
      (eliminateLeadersNoCollisionFire hψ l r).1.shield = true ∧
      (eliminateLeadersNoCollisionFire hψ l r).2.leader = false ∧
      (eliminateLeadersNoCollisionFire hψ l r).2.bullet = (2 : Fin 3))) :
    sinkKernelC hψ l r = sinkKernel hψ l r := by
  simp only [sinkKernelC, sinkKernel, absorbProtectedMove, if_neg hnot]

/-! Each stage is framed separately. The repeat loop closes a branch before
continuing to the next one, rather than stopping at its first reflexive leaf. -/

private theorem fire_labels {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.label = l.label ∧
    (eliminateLeadersNoCollisionFire hψ l r).2.label = r.label := by
  constructor <;>
    (simp only [eliminateLeadersNoCollisionFire] <;>
      (repeat split <;> rfl))

private theorem egressMove_labels {ψ : Nat} (hψ : ψ > 0)
    (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r).1.label =
      l.label ∧
    (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r).2.label =
      r.label := by
  unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  repeat (first | rfl | exact True.intro | apply And.intro | split)

private theorem absorbProtectedMove_labels {ψ : Nat} (hψ : ψ > 0)
    (nl : Fin ψ) (l r : AgentState ψ) :
    (absorbProtectedMove hψ nl l r).1.label = l.label ∧
    (absorbProtectedMove hψ nl l r).2.label = r.label := by
  by_cases hp : l.leader = true ∧ l.shield = true ∧
      r.leader = false ∧ r.bullet = (2 : Fin 3)
  · simp [absorbProtectedMove, hp]
  · simpa only [absorbProtectedMove, if_neg hp] using
      egressMove_labels hψ nl l r

/-- The unchanged suffix, named only for the proofs below. -/
private def finish {ψ : Nat} (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ) : AgentState ψ × AgentState ψ :=
  dummyBulletSink (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2)

/-- Frame SIGNAL before putting its output inside the dummy-sink guard. -/
private theorem signal_frame {ψ : Nat} (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2).1.label =
      q.1.label ∧
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2).2.label =
      q.2.label ∧
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2).1.leader =
      q.1.leader ∧
    (eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2).2.leader =
      q.2.leader := by
  unfold eliminateLeadersNoCollisionSignalLeaderSink
  dsimp only
  repeat (first | rfl | exact True.intro | apply And.intro | split)

/-- The sink's own guards are handled on an arbitrary, already-produced pair. -/
private theorem dummySink_frame {ψ : Nat}
    (q : AgentState ψ × AgentState ψ) :
    (dummyBulletSink q).1.label = q.1.label ∧
    (dummyBulletSink q).2.label = q.2.label ∧
    (dummyBulletSink q).1.leader = q.1.leader ∧
    (dummyBulletSink q).2.leader = q.2.leader := by
  unfold dummyBulletSink
  dsimp only
  repeat (first | rfl | exact True.intro | apply And.intro | split)

private theorem finish_labels {ψ : Nat} (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ) :
    (finish nl q).1.label = q.1.label ∧
    (finish nl q).2.label = q.2.label := by
  let s := eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2
  have hs := signal_frame nl q
  have hd := dummySink_frame s
  change (dummyBulletSink s).1.label = q.1.label ∧
    (dummyBulletSink s).2.label = q.2.label
  exact ⟨hd.1.trans hs.1, hd.2.1.trans hs.2.1⟩

private theorem finish_leaders {ψ : Nat} (nl : Fin ψ)
    (q : AgentState ψ × AgentState ψ) :
    (finish nl q).1.leader = q.1.leader ∧
    (finish nl q).2.leader = q.2.leader := by
  let s := eliminateLeadersNoCollisionSignalLeaderSink nl q.1 q.2
  have hs := signal_frame nl q
  have hd := dummySink_frame s
  change (dummyBulletSink s).1.leader = q.1.leader ∧
    (dummyBulletSink s).2.leader = q.2.leader
  exact ⟨hd.2.2.1.trans hs.2.2.1, hd.2.2.2.trans hs.2.2.2⟩

/-- In the new branch the original MOVE was a shield-blocked identity.
Clearing only the incoming bullet therefore changes neither leader bit.
Outside that branch the two MOVE functions agree entirely. -/
private theorem absorbProtectedMove_leaders {ψ : Nat} (hψ : ψ > 0)
    (nl : Fin ψ) (l r : AgentState ψ) :
    (absorbProtectedMove hψ nl l r).1.leader =
      (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r).1.leader ∧
    (absorbProtectedMove hψ nl l r).2.leader =
      (eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r).2.leader := by
  by_cases hp : l.leader = true ∧ l.shield = true ∧
      r.leader = false ∧ r.bullet = (2 : Fin 3)
  · have hold :
        eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r =
          (l, r) := by
      simp [eliminateLeadersNoCollisionZeroLeaderEgressMove,
        hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
    simp [absorbProtectedMove, hp, hold]
  · simp [absorbProtectedMove, hp]

/-- Both input labels are preserved by the complete variant-C kernel. -/
theorem kernelC_labels {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (sinkKernelC hψ l r).1.label = l.label ∧
    (sinkKernelC hψ l r).2.label = r.label := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := absorbProtectedMove hψ nl q0.1 q0.2
  have h0 := fire_labels hψ l r
  have h1 := absorbProtectedMove_labels hψ nl q0.1 q0.2
  have h2 := finish_labels nl q1
  change (finish nl q1).1.label = l.label ∧
    (finish nl q1).2.label = r.label
  exact ⟨h2.1.trans (h1.1.trans h0.1),
    h2.2.trans (h1.2.trans h0.2)⟩

/-- For the same input pair, variant C has exactly the original kernel's
output leader bits. This is stronger than a one-way no-new-deletion claim,
but is not a comparison between executions with different intermediate states. -/
theorem kernelC_no_new_deletion {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (sinkKernelC hψ l r).1.leader = (sinkKernel hψ l r).1.leader ∧
    (sinkKernelC hψ l r).2.leader = (sinkKernel hψ l r).2.leader := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let qC := absorbProtectedMove hψ nl q0.1 q0.2
  let qB := eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl q0.1 q0.2
  have hm := absorbProtectedMove_leaders hψ nl q0.1 q0.2
  have hc := finish_leaders nl qC
  have hb := finish_leaders nl qB
  change (finish nl qC).1.leader = (finish nl qB).1.leader ∧
    (finish nl qC).2.leader = (finish nl qB).2.leader
  exact ⟨hc.1.trans (hm.1.trans hb.1.symm),
    hc.2.trans (hm.2.trans hb.2.symm)⟩

/-! ## Escape from the checked six-agent stall witness -/

/-- One raw variant-C step on the witness ring, without a stopping rule. -/
def stepC (C : Fin 6 → AgentState 1) (e : Fin 6) :
    Fin 6 → AgentState 1 :=
  updatePair C e (rightNeighbor e)
    (sinkKernelC (by decide : 1 > 0) (C e) (C (rightNeighbor e)))

/-- The exact pair on edge (0,1): absorption clears the live bullet before
SIGNAL, which then writes the leader's positive absence signal. -/
theorem stallC_pair :
    sinkKernelC (by decide : 1 > 0) (stall 0) (stall 1) =
      (stall 0,
        { (stall 1) with bullet := (0 : Fin 3), signal_B := (1 : Fin 2) }) := by
  rfl

/-- At agent 1 after edge 0, the bullet is zero and the signal is one. -/
theorem stallC_step_signal :
    (stepC stall 0 1).bullet = (0 : Fin 3) ∧
    (stepC stall 0 1).signal_B = (1 : Fin 2) := by
  exact ⟨rfl, rfl⟩

/-- Inequality is witnessed by one concrete field, not function decidability. -/
theorem stallC_step0_ne : stepC stall 0 ≠ stall := by
  intro heq
  have hb := congrArg
    (fun C : Fin 6 → AgentState 1 => (C 1).bullet) heq
  exact (by decide : (0 : Fin 3) ≠ 2) hb

/-- The requested raw updatePair escape, witnessed by edge (0,1). -/
theorem stallC_moves : ∃ e : Fin 6,
    updatePair stall e (rightNeighbor e)
      (sinkKernelC (by decide : 1 > 0)
        (stall e) (stall (rightNeighbor e))) ≠ stall := by
  exact ⟨0, stallC_step0_ne⟩

/-- The original witness runner with its step replaced by variant C. -/
def run_C : List (Fin 6) → (Fin 6 → AgentState 1) →
    (Fin 6 → AgentState 1)
  | [], C => C
  | e :: es, C => run_C es (stepC C e)

/-- A single scheduled edge already escapes the old fixed point. -/
theorem stallC_run_changes :
    ∃ es : List (Fin 6), run_C es stall ≠ stall := by
  exact ⟨[0], stallC_step0_ne⟩

end LDSinkKernelC

#print axioms LDSinkKernelC.kernelC_eq_of_not_protected
#print axioms LDSinkKernelC.kernelC_labels
#print axioms LDSinkKernelC.kernelC_no_new_deletion
#print axioms LDSinkKernelC.stallC_pair
#print axioms LDSinkKernelC.stallC_step_signal
#print axioms LDSinkKernelC.stallC_step0_ne
#print axioms LDSinkKernelC.stallC_moves
#print axioms LDSinkKernelC.stallC_run_changes
