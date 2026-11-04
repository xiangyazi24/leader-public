import Leader.Wu.Protocol.RepairRegression

/-!
# First operational legitimacy candidate and its obstruction

A semantic Definition-1 target is correct but not directly checkable from local
signal fields.  The first natural operational candidate below combines Wu's
five fields with value bounds, the exact integrated CHECK boundary, and local
support for every `increment_group` command.  It rejects T1 and T8 at their
immediate bad boundaries.

The candidate is nevertheless not inductive.  A bounded latent comparison
carrier can be harmless at the current CHECK boundary, become re-armed later in
the same integrated interaction, and create a leader on the next same edge.
This isolates why a preserved lifecycle/provenance refinement is necessary;
conjoining one-step boundary predicates is insufficient.
-/

namespace PPLLOperationalLegitimacy

open PPLL PPLLRepair PPLLCounterexample PPLLWriteProvenance

/-- Exact no-terminal-equality obligation at the integrated candidate's CHECK
boundary. -/
def IntegratedCheckBoundarySafe {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) : Prop :=
  ∀ e : Fin n,
    let q0 := ppllSaturatedBeforeCheck hψ κ
      (C e) (C (ring.rightNeighbor e))
    let q1 := checkSig hψ q0.1 q0.2
    ¬(q1.2.label = ⟨ψ - 1, by omega⟩ ∧ q1.2.state = .equal)

/-- Every active terminal increment command has the local path3 support proved
necessary by WRITE_SEQ provenance. -/
def IncrementCommandsSupported {ψ n : Nat}
    (C : Fin n → AgentState ψ) : Prop :=
  ∀ i, IncrementCommandSupported (C i)

/-- First operational legitimacy proposal.  The four conjuncts are concrete
and falsifiable; no field assumes semantic output stability or future
closedness. -/
def FirstOperationalLegitimate {ψ n : Nat} (hψ : ψ > 0) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) : Prop :=
  PaperSafeConfig hψ ring C ∧
  (∀ i, (C i).inProtocolDomain κ) ∧
  IntegratedCheckBoundarySafe hψ κ ring C ∧
  IncrementCommandsSupported C

/-! ## Immediate known-witness rejection -/

/-- The exact integrated CHECK boundary rejects T1's already-terminal forged
carrier. -/
theorem firstOperationalLegitimate_rejects_t1 :
    ¬FirstOperationalLegitimate (by omega : 2 > 0) 10 ring4
      counterConfig := by
  intro h
  exact h.2.2.1 2 (by decide)

/-- Local increment support rejects T8's orphan terminal write command. -/
theorem firstOperationalLegitimate_rejects_t8 :
    ¬FirstOperationalLegitimate (by omega : 2 > 0) 10 ring4
      writeCounterConfig := by
  intro h
  exact writeCounter_orphan_increment_not_supported (h.2.2.2 3)

/-! ## Latent source-aligned carrier -/

private def latentL : AgentState 2 :=
  { counterConfig 2 with state := .none }

private def latentR : AgentState 2 :=
  { counterConfig 3 with state := .depart }

/-- T11 predecessor: the same complete `00` source-aligned fields as T1, but
with state tags that do not finish equality at the current CHECK boundary. -/
def latentConfig : Fin 4 → AgentState 2
  | ⟨0, _⟩ => counterConfig 0
  | ⟨1, _⟩ => counterConfig 1
  | ⟨2, _⟩ => latentL
  | ⟨3, _⟩ => latentR

private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi := i.isLt
  omega

private theorem latent_unique : hasUniqueLeader 4 latentConfig := by
  refine ⟨0, by decide, ?_⟩
  intro j hj
  rcases fin4_cases j with h | h | h | h <;> subst j
  · rfl
  · have hf : (latentConfig 1).isLeader = false := by decide
    rw [hf] at hj
    contradiction
  · have hf : (latentConfig 2).isLeader = false := by decide
    rw [hf] at hj
    contradiction
  · have hf : (latentConfig 3).isLeader = false := by decide
    rw [hf] at hj
    contradiction

private theorem latent_no_bad_bullet :
    noNonPeacefulBullet (by omega : 2 > 0) ring4 latentConfig := by
  intro i hi
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [latentConfig, latentL, latentR, counterConfig,
      a0, a1, a2, a3, state2] at hi

private theorem latent_no_free_barrier :
    noFreeBarrier (by omega : 2 > 0) ring4 latentConfig := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [DirectedRing.rightNeighbor, isBarrier, latentConfig, latentL,
      latentR, counterConfig, a0, a1, a2, a3, state2]

private theorem latent_no_free_overwriting :
    noFreeOverwritingSignal (by omega : 2 > 0) ring4 latentConfig := by
  refine ⟨0, by decide, by decide, ?_⟩
  intro i hi hbound hfree
  obtain ⟨_, haligned⟩ := hfree.1
  obtain ⟨p, hpath, _⟩ := haligned 0 (by omega)
  have hnone : ∀ k : Fin 4, (latentConfig k).path3 = none := by
    intro k
    rcases fin4_cases k with h | h | h | h <;> subst k <;> decide
  rw [hnone] at hpath
  contradiction

private theorem latent_stable_id :
    isStableIDSequence (by omega : 2 > 0) ring4 latentConfig := by
  refine ⟨0, by decide, by decide, ?_, ?_⟩
  · intro k hk
    have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases h with h | h | h | h <;> subst k <;> decide
  · intro i hi hlt
    have hieq : i = 1 := by omega
    subst i
    unfold groupID
    simp [List.range_succ, latentConfig, latentL, latentR, counterConfig,
      a0, a1, a2, a3, state2, trailingZeros]

/-- The latent carrier still satisfies all five literal paper fields. -/
theorem latentConfig_paper_safe :
    PaperSafeConfig (by omega : 2 > 0) ring4 latentConfig where
  unique_leader := latent_unique
  no_nonpeaceful_bullet := latent_no_bad_bullet
  no_free_barrier := latent_no_free_barrier
  no_free_overwriting_signal := latent_no_free_overwriting
  stable_id_sequence := latent_stable_id

/-- Every latent-carrier field lies in the finite Algorithm-1 domain. -/
theorem latentConfig_inProtocolDomain :
    ∀ i, (latentConfig i).inProtocolDomain 10 := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [latentConfig, latentL, latentR, AgentState.inProtocolDomain,
      counterConfig, a0, a1, a2, a3, state2]

/-- No edge produces terminal CHECK equality in the current interaction. -/
theorem latentConfig_integratedCheckBoundarySafe :
    IntegratedCheckBoundarySafe (by omega : 2 > 0) 10 ring4 latentConfig := by
  intro e
  rcases fin4_cases e with h | h | h | h <;> subst e <;> decide

/-- The latent configuration carries no increment command, so T8's local leaf
obligation holds vacuously but honestly. -/
theorem latentConfig_incrementCommandsSupported :
    IncrementCommandsSupported latentConfig := by
  intro i hinc
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [latentConfig, latentL, latentR, counterConfig,
      a0, a1, a2, a3, state2] at hinc

/-- The first operational legitimacy proposal is inhabited. -/
theorem latentConfig_firstOperationalLegitimate :
    FirstOperationalLegitimate (by omega : 2 > 0) 10 ring4 latentConfig :=
  ⟨latentConfig_paper_safe, latentConfig_inProtocolDomain,
    latentConfig_integratedCheckBoundarySafe,
    latentConfig_incrementCommandsSupported⟩

/-- Finite-carrier form of the first operational legitimacy proposal, defined
by exact concrete erasure rather than a second field transcription. -/
def FirstFiniteOperationalLegitimate {ψ κ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (C : Fin n → BoundedAgentState ψ κ) : Prop :=
  FirstOperationalLegitimate hψ κ ring (PPLLRepair.eraseConfig C)

/-! ## Failure of one-step preservation -/

/-- First integrated interaction on the latent carrier. -/
def latentSuccessor : Fin 4 → AgentState 2 :=
  PopulationProtocol.step (PPLLRepair.integratedProtocol (by omega) 10)
    ring4 latentConfig 2

set_option maxRecDepth 4096 in
/-- The first successor is unsafe at the next CHECK boundary on the same edge. -/
theorem latentSuccessor_not_integratedCheckBoundarySafe :
    ¬IntegratedCheckBoundarySafe (by omega : 2 > 0) 10 ring4
      latentSuccessor := by
  intro hsafe
  exact hsafe 2 (by decide)

/-- The concrete first operational legitimacy proposal is not closed under the
integrated audit candidate. -/
theorem firstOperationalLegitimate_not_closed :
    ¬PopulationProtocol.ClosedPred
      (PPLLRepair.integratedProtocol (by decide : 2 > 0) 10) ring4
      (FirstOperationalLegitimate (by decide : 2 > 0) 10 ring4) := by
  intro hclosed
  have hnext := hclosed latentConfig latentConfig_firstOperationalLegitimate
    latentSuccessor ⟨2, rfl⟩
  exact latentSuccessor_not_integratedCheckBoundarySafe hnext.2.2.1

/-! ### Exact finite-carrier lift -/

/-- Reification of the latent predecessor into the actual finite carrier. -/
def latentFiniteConfig : Fin 4 → BoundedAgentState 2 10 := fun i =>
  BoundedAgentState.ofDomain (latentConfig i)
    (latentConfig_inProtocolDomain i)

theorem erase_latentFiniteConfig :
    PPLLRepair.eraseConfig latentFiniteConfig = latentConfig := by
  funext i
  simp [latentFiniteConfig, PPLLRepair.eraseConfig,
    BoundedAgentState.erase_ofDomain]

/-- The finite first-candidate predicate is inhabited by the latent carrier. -/
theorem latentFiniteConfig_firstOperationalLegitimate :
    FirstFiniteOperationalLegitimate (by omega : 2 > 0) ring4
      latentFiniteConfig := by
  unfold FirstFiniteOperationalLegitimate
  rw [erase_latentFiniteConfig]
  exact latentConfig_firstOperationalLegitimate

/-- First latent interaction in the finite integrated protocol. -/
def latentFiniteSuccessor : Fin 4 → BoundedAgentState 2 10 :=
  PopulationProtocol.step
    (PPLLRepair.integratedBoundedProtocol (by omega) 10)
    ring4 latentFiniteConfig 2

/-- Exact erasure identifies the finite and audit latent successors. -/
theorem erase_latentFiniteSuccessor :
    PPLLRepair.eraseConfig latentFiniteSuccessor = latentSuccessor := by
  unfold latentFiniteSuccessor
  rw [PPLLRepair.erase_integrated_step]
  rw [erase_latentFiniteConfig]
  rfl

/-- The finite successor leaves the first-candidate predicate. -/
theorem latentFiniteSuccessor_not_firstOperationalLegitimate :
    ¬FirstFiniteOperationalLegitimate (by omega : 2 > 0) ring4
      latentFiniteSuccessor := by
  intro h
  unfold FirstFiniteOperationalLegitimate at h
  rw [erase_latentFiniteSuccessor] at h
  exact latentSuccessor_not_integratedCheckBoundarySafe h.2.2.1

/-- The failure is present on the actual finite protocol, not an artifact of
the unbounded audit carrier. -/
theorem firstFiniteOperationalLegitimate_not_closed :
    ¬PopulationProtocol.ClosedPred
      (PPLLRepair.integratedBoundedProtocol (by decide : 2 > 0) 10) ring4
      (FirstFiniteOperationalLegitimate (by decide : 2 > 0) ring4) := by
  intro hclosed
  have hnext := hclosed latentFiniteConfig
    latentFiniteConfig_firstOperationalLegitimate latentFiniteSuccessor
      ⟨2, rfl⟩
  exact latentFiniteSuccessor_not_firstOperationalLegitimate hnext

/-- Second same-edge interaction after the latent handoff. -/
def latentAfterTwo : Fin 4 → AgentState 2 :=
  PopulationProtocol.step (PPLLRepair.integratedProtocol (by omega) 10)
    ring4 latentSuccessor 2

set_option maxRecDepth 4096 in
/-- The second interaction creates and migrates a new leader. -/
theorem latentAfterTwo_creates_leader :
    (latentAfterTwo 2).leader = true := by
  decide

set_option maxRecDepth 4096 in
/-- Therefore even the predecessor satisfying all first-candidate operational
fields is not already Definition-1 safe. -/
theorem latentConfig_not_semantically_safe :
    ¬PopulationProtocol.IsSafe
      (PPLLRepair.integratedProtocol (by omega) 10) ring4
      latentConfig isLeaderOutput := by
  intro hsafe
  have hreach1 : PopulationProtocol.Reachable
      (PPLLRepair.integratedProtocol (by omega) 10) ring4
      latentConfig latentSuccessor :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  have hreach2 : PopulationProtocol.Reachable
      (PPLLRepair.integratedProtocol (by omega) 10) ring4
      latentSuccessor latentAfterTwo :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  have hout := hsafe.2 latentAfterTwo (hreach1.trans hreach2) 2
  change AgentState.outputFn (latentAfterTwo 2) =
    AgentState.outputFn (latentConfig 2) at hout
  have hne : AgentState.outputFn (latentAfterTwo 2) ≠
      AgentState.outputFn (latentConfig 2) := by decide
  exact hne hout

private def latentLeaderTest (C : Fin 4 → AgentState 2) : Bool :=
  (C 2).leader

set_option maxRecDepth 4096 in
/-- Exactly one of the sixteen two-edge schedules exposes the latent carrier's
output change. -/
theorem latent_bad_schedule_count :
    hitCount ring4 (PPLLRepair.ppllIntegratedRepair (by omega) 10)
      latentLeaderTest latentConfig 2 = 1 := by
  decide

/-- The latent two-step bad event has exact probability `1/16`. -/
theorem latent_bad_event_probability :
    hitProbability ring4 (PPLLRepair.ppllIntegratedRepair (by omega) 10)
      latentLeaderTest latentConfig 2 = (1 : Rat) / 16 := by
  unfold hitProbability
  rw [latent_bad_schedule_count, allSchedules_length]
  rfl

end PPLLOperationalLegitimacy
