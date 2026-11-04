import Leader.Wu.Elimination.SinkAbsorbKernel
import Leader.Wu.Safety.Counterexamples


open LDSinkGapCleanup LDSinkKernelC
open PPLLRepair PPLLCounterexample


namespace LDSinkKernelCRegression


set_option autoImplicit false


/-!
# K2 regression on the original T7 witness


Source locations read on the connected leader/main:
* Leader/Wu/Safety/Counterexamples.lean:760-769: bulletCounterConfig and its agents.
* Leader/Wu/Safety/Counterexamples.lean:875-877: bullet_counter_collision_fields.
* Leader/Wu/Safety/Counterexamples.lean:901-912: paperSafe_not_closed_by_bullet.
* Leader/Wu/Safety/Counterexamples.lean:964-992: bulletRepairedPair,
  bulletRepairedSuccessor, bullet_repair_removes_collision, and
  bullet_repair_witness_remains_peaceful.
* Leader/Wu/Safety/SafeConfig.lean:32-54: isPeacefulBullet and noNonPeacefulBullet.
* Leader/Wu/Protocol/Repairs.lean:194-323: the staged R7 Algorithm-15 kernel.


The original R7 regression runs ppllNoBulletSignalCollision, a full
protocol wrapper. Here we apply the actual imported sinkKernelC directly
to the same input pair and perform the same two-cell ring update.
We do not identify those different full transition functions.


T7 is a shielded contact both before and after FIRE. K2 therefore absorbs
its bullet: the responder has bullet = 0 and signal_B = 1 afterwards.
isPeacefulBullet itself requires bullet = 2. Thus the requested literal
pointwise peacefulness statement is false; the appropriate condition-2
certificate is noNonPeacefulBullet. All four successor bullets are zero.


The off-contact equality is a genuine general theorem against sinkKernel.
For T7, a computed bridge also identifies that old sink output with R7's
Algorithm-15 output. Its off-contact antecedent is false on the actual
witness; it must not be cited as equality on the executed absorption branch.


This is a single-witness certificate, not a global closure, last-leader,
or convergence theorem. This file has not been compiler-tested here.
-/


/-- Reuse the exact four-agent input of the checked R7 regression. -/
abbrev t7Config : Fin 4 → AgentState 2 := bulletCounterConfig


/-- Explicit restatement using the repository's public agent constructors. -/
theorem t7_agents :
    t7Config 0 = a0 ∧
    t7Config 1 = { a1 with bullet := (2 : Fin 3) } ∧
    t7Config 2 = state2 0 ∧
    t7Config 3 = state2 1 :=
  ⟨rfl, rfl, rfl, rfl⟩


/-- The scheduled pair really is edge (0,1) of the original ring4. -/
theorem t7_edge : ring4.rightNeighbor (0 : Fin 4) = 1 := by
  rfl


/-- Exactly the guard used by absorbProtectedMove, on its supplied pair. -/
def ProtectedContact {ψ : Nat} (l r : AgentState ψ) : Prop :=
  l.leader = true ∧ l.shield = true ∧
    r.leader = false ∧ r.bullet = (2 : Fin 3)


/-- Keep the post-FIRE boundary explicit. -/
def t7FirePair : AgentState 2 × AgentState 2 :=
  eliminateLeadersNoCollisionFire (by decide : 2 > 0)
    (t7Config 0) (t7Config 1)


/-- Both input signals are zero, so neither endpoint fires. -/
theorem t7_fire_inert :
    t7FirePair = (t7Config 0, t7Config 1) := by
  rfl


theorem t7_input_is_protected :
    ProtectedContact (t7Config 0) (t7Config 1) :=
  ⟨rfl, rfl, rfl, rfl⟩


/-- The actual K2 execution takes the new absorption branch. -/
theorem t7_takes_absorption_branch :
    ProtectedContact t7FirePair.1 t7FirePair.2 :=
  ⟨rfl, rfl, rfl, rfl⟩


/-- K2 itself, with no alteration of its SIGNAL or dummy-sink stages. -/
def t7AbsorbPair : AgentState 2 × AgentState 2 :=
  sinkKernelC (by decide : 2 > 0) (t7Config 0) (t7Config 1)


/-- Exact output: absorption precedes the leader's signal seeding. -/
theorem t7_absorb_pair_eq :
    t7AbsorbPair =
      (t7Config 0,
        { (t7Config 1) with
          bullet := (0 : Fin 3), signal_B := (1 : Fin 2) }) := by
  rfl


/-- Unlike R7, K2 removes this bullet rather than clamping its signal. -/
theorem t7_absorb_pair_fields :
    t7AbsorbPair.2.bullet = (0 : Fin 3) ∧
    t7AbsorbPair.2.signal_B = (1 : Fin 2) :=
  ⟨rfl, rfl⟩


/-- Same input ring and scheduled cells as bulletRepairedSuccessor. -/
def t7AbsorbSuccessor : Fin 4 → AgentState 2 :=
  updatePair t7Config 0 (ring4.rightNeighbor 0) t7AbsorbPair


/-- Field-only finite computation; no equality decision on configurations. -/
theorem t7_absorb_no_live :
    ∀ i : Fin 4, (t7AbsorbSuccessor i).bullet = (0 : Fin 3) := by
  decide


/-- The local absorption does not change any leader bit or label. -/
theorem t7_absorb_leaders_labels :
    ∀ i : Fin 4,
      (t7AbsorbSuccessor i).leader = (t7Config i).leader ∧
      (t7AbsorbSuccessor i).label = (t7Config i).label := by
  decide


/-- K2's condition-2 certificate: every remaining live bullet is peaceful.
There are no live bullets in this particular successor. -/
theorem t7_absorb_witness_peaceful :
    noNonPeacefulBullet (by decide : 2 > 0) ring4
      t7AbsorbSuccessor := by
  intro i hi
  have hbad : (0 : Fin 3) = 2 := (t7_absorb_no_live i).symm.trans hi
  exact False.elim ((by decide : (0 : Fin 3) ≠ 2) hbad)


/-- No cell in the complete successor has a live-bullet/signal collision. -/
theorem t7_absorb_removes_collision :
    ¬ ∃ i : Fin 4,
      (t7AbsorbSuccessor i).bullet = (2 : Fin 3) ∧
      (t7AbsorbSuccessor i).signal_B = (1 : Fin 2) := by
  intro h
  obtain ⟨i, hi, _⟩ := h
  have hbad : (0 : Fin 3) = 2 := (t7_absorb_no_live i).symm.trans hi
  exact (by decide : (0 : Fin 3) ≠ 2) hbad


/-- Why the requested unguarded isPeacefulBullet-at-1 version is false. -/
theorem t7_absorb_not_a_live_peaceful_bullet :
    ¬ isPeacefulBullet (by decide : 2 > 0) ring4
      t7AbsorbSuccessor 1 := by
  intro h
  have hbad : (0 : Fin 3) = 2 := (t7_absorb_no_live 1).symm.trans h.1
  exact (by decide : (0 : Fin 3) ≠ 2) hbad


/-- Preserve the original full-wrapper R7 regression as an explicit contrast. -/
theorem t7_r7_reference :
    (bulletRepairedPair.2.bullet = (2 : Fin 3) ∧
      bulletRepairedPair.2.signal_B = (0 : Fin 2)) ∧
    isPeacefulBullet (by decide : 2 > 0) ring4
      bulletRepairedSuccessor 1 :=
  ⟨bullet_repair_removes_collision,
    bullet_repair_witness_remains_peaceful⟩


/-- R7's Algorithm-15 subkernel, not its full protocol wrapper. -/
def t7R7BasePair : AgentState 2 × AgentState 2 :=
  eliminateLeadersNoCollision (by decide : 2 > 0)
    (t7Config 0) (t7Config 1)


/-- On this input only, both old local kernels leave the whole pair unchanged. -/
theorem t7_sink_eq_r7_base :
    sinkKernel (by decide : 2 > 0) (t7Config 0) (t7Config 1) =
      t7R7BasePair := by
  rfl


/-- General off-contact equality uses the POST-FIRE guard, as required by
kernelC_eq_of_not_protected. It does not compare the full R7 wrapper. -/
theorem k2_agrees_with_sink_off_shielded_contact {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hnot : ¬ ProtectedContact
      (eliminateLeadersNoCollisionFire hψ l r).1
      (eliminateLeadersNoCollisionFire hψ l r).2) :
    sinkKernelC hψ l r = sinkKernel hψ l r :=
  kernelC_eq_of_not_protected hψ l r hnot


/-- Requested T7-local R7 comparison. The concrete bridge is not a global
sink/base equivalence. Its premise is false on T7's actual post-FIRE pair. -/
theorem k2_agrees_with_r7_off_shielded_contact
    (hnot : ¬ ProtectedContact t7FirePair.1 t7FirePair.2) :
    t7AbsorbPair = t7R7BasePair := by
  have hsame := k2_agrees_with_sink_off_shielded_contact
    (by decide : 2 > 0) (t7Config 0) (t7Config 1) hnot
  exact hsame.trans t7_sink_eq_r7_base


/-- The input-guard wording is valid here because T7's FIRE is inert. -/
theorem k2_agrees_with_r7_off_shielded_contact_input
    (hnot : ¬ ProtectedContact (t7Config 0) (t7Config 1)) :
    t7AbsorbPair = t7R7BasePair := by
  apply k2_agrees_with_r7_off_shielded_contact
  rw [t7_fire_inert]
  exact hnot


/-- The actual executed branch is not equal to the full R7 regression pair. -/
theorem t7_absorb_ne_r7 : t7AbsorbPair ≠ bulletRepairedPair := by
  intro h
  have hbullet := congrArg
    (fun q : AgentState 2 × AgentState 2 => q.2.bullet) h
  have hbad : (0 : Fin 3) = 2 :=
    t7_absorb_pair_fields.1.symm.trans
      (hbullet.trans bullet_repair_removes_collision.1)
  exact (by decide : (0 : Fin 3) ≠ 2) hbad


end LDSinkKernelCRegression


#print axioms LDSinkKernelCRegression.t7_agents
#print axioms LDSinkKernelCRegression.t7_edge
#print axioms LDSinkKernelCRegression.t7_fire_inert
#print axioms LDSinkKernelCRegression.t7_input_is_protected
#print axioms LDSinkKernelCRegression.t7_takes_absorption_branch
#print axioms LDSinkKernelCRegression.t7_absorb_pair_eq
#print axioms LDSinkKernelCRegression.t7_absorb_pair_fields
#print axioms LDSinkKernelCRegression.t7_absorb_no_live
#print axioms LDSinkKernelCRegression.t7_absorb_leaders_labels
#print axioms LDSinkKernelCRegression.t7_absorb_witness_peaceful
#print axioms LDSinkKernelCRegression.t7_absorb_removes_collision
#print axioms LDSinkKernelCRegression.t7_absorb_not_a_live_peaceful_bullet
#print axioms LDSinkKernelCRegression.t7_r7_reference
#print axioms LDSinkKernelCRegression.t7_sink_eq_r7_base
#print axioms LDSinkKernelCRegression.k2_agrees_with_sink_off_shielded_contact
#print axioms LDSinkKernelCRegression.k2_agrees_with_r7_off_shielded_contact
#print axioms LDSinkKernelCRegression.k2_agrees_with_r7_off_shielded_contact_input
#print axioms LDSinkKernelCRegression.t7_absorb_ne_r7
