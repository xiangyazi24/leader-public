import Leader.Wu.Scheduler.TraceConvergence

/-!
# Erasing proof refinements versus executable protocol repairs

A proof ghost may summarize past events, but exact simulation forbids it from
changing the physical transition.  In particular, an “unknown” provenance tag
cannot deny a physical CHECK that creates a leader.  The honest use of such a
ghost is instead:

1. total-lift every arbitrary physical state as untrusted;
2. prove physical/refined step and output erasure;
3. prove a trusted subset closed and output-preserving;
4. prove random-scheduler cleanup from total lifts into that trusted subset.

If authorization must actually block CHECK, it is executable state and belongs
in a separately named physical protocol whose extra states are counted.
-/

namespace PPLLErasingRefinement

open PPLL PPLLRepair PPLLCounterexample PPLLResearchFormulation
  PPLLRepairRegression

/-- A total local proof refinement of one fixed physical transition and output
function.  Ghost state may evolve but cannot influence the erased physical
step or output. -/
structure ErasingLocalRefinement
    (Physical Refined Output : Type)
    (physicalTransition : Physical → Physical → Physical × Physical)
    (physicalOutput : Physical → Output) where
  refinedTransition : Refined → Refined → Refined × Refined
  refinedOutput : Refined → Output
  erase : Refined → Physical
  lift : Physical → Refined
  erase_lift : ∀ s, erase (lift s) = s
  transition_erases : ∀ l r,
    let refined := refinedTransition l r
    let physical := physicalTransition (erase l) (erase r)
    erase refined.1 = physical.1 ∧ erase refined.2 = physical.2
  output_erases : ∀ s, refinedOutput s = physicalOutput (erase s)

namespace ErasingLocalRefinement

variable {Physical Refined Output : Type}
variable {T : Physical → Physical → Physical × Physical}
  {out : Physical → Output}

/-- Packaged physical protocol associated with the refinement. -/
def physicalProtocol
    (_R : ErasingLocalRefinement Physical Refined Output T out) :
    PopulationProtocol where
  Q := Physical
  Y := Output
  transition := T
  output := out

/-- Packaged refined protocol. -/
def refinedProtocol
    (R : ErasingLocalRefinement Physical Refined Output T out) :
    PopulationProtocol where
  Q := Refined
  Y := Output
  transition := R.refinedTransition
  output := R.refinedOutput

/-- Pointwise erasure of refined configurations. -/
def eraseConfig
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (C : Fin n → Refined) : Fin n → Physical :=
  fun i => R.erase (C i)

/-- Pointwise total lift of arbitrary physical configurations. -/
def liftConfig
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (C : Fin n → Physical) : Fin n → Refined :=
  fun i => R.lift (C i)

/-- Every physical configuration has an exact refined representative. -/
theorem erase_liftConfig
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (C : Fin n → Physical) :
    R.eraseConfig (R.liftConfig C) = C := by
  funext i
  exact R.erase_lift (C i)

/-- Exact local simulation extends to one ring interaction. -/
theorem erase_localStep
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (ring : DirectedRing n) (C : Fin n → Refined) (e : Fin n) :
    R.eraseConfig (localStep ring R.refinedTransition C e) =
      localStep ring T (R.eraseConfig C) e := by
  funext i
  let j := ring.rightNeighbor e
  let refined := R.refinedTransition (C e) (C j)
  let physical := T (R.erase (C e)) (R.erase (C j))
  have ht : R.erase refined.1 = physical.1 ∧
      R.erase refined.2 = physical.2 :=
    R.transition_erases (C e) (C j)
  change R.erase (if i = e then refined.1 else if i = j then refined.2 else C i) =
    (if i = e then physical.1 else if i = j then physical.2 else R.erase (C i))
  by_cases hie : i = e
  · simp [hie, ht.1]
  · by_cases hij : i = j
    · have hje : j ≠ e := by
        intro h
        exact hie (hij.trans h)
      simp [hij, hje, ht.2]
    · simp [hie, hij]

/-- Packaged refined and physical protocol steps commute with erasure. -/
theorem erase_protocolStep
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (ring : DirectedRing n) (C : Fin n → Refined) (e : Fin n) :
    R.eraseConfig (R.refinedProtocol.step ring C e) =
      R.physicalProtocol.step ring (R.eraseConfig C) e := by
  change R.eraseConfig (localStep ring R.refinedTransition C e) =
    localStep ring T (R.eraseConfig C) e
  exact R.erase_localStep ring C e

/-- Every physical execution from an erased refined state has a synchronized
refined execution on the same edge choices. Determinism and total refined
transition—not trust of the initial ghost—supply the lift. -/
theorem lift_physical_reachable
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (ring : DirectedRing n)
    {C : R.refinedProtocol.Configuration n}
    {D : R.physicalProtocol.Configuration n}
    (h : PopulationProtocol.Reachable R.physicalProtocol ring
      (R.eraseConfig C) D) :
    ∃ Dref : Fin n → Refined,
      PopulationProtocol.Reachable R.refinedProtocol ring C Dref ∧
      R.eraseConfig Dref = D := by
  induction h
  · exact ⟨C, .refl C, rfl⟩
  · rename_i D₁ D₂ _ hone ih
    obtain ⟨C₁, hC₁, herase⟩ := ih
    obtain ⟨e, hD₂⟩ := hone
    let C₂ := R.refinedProtocol.step ring C₁ e
    refine ⟨C₂, PopulationProtocol.Reachable.step C C₁ C₂ hC₁
      ⟨e, rfl⟩, ?_⟩
    dsimp only [C₂]
    rw [R.erase_protocolStep, herase]
    exact hD₂.symm

/-- Definition-1 safety of a refined state projects to Definition-1 safety of
its physical erasure. Exact step/output simulation ensures that every physical
future has a synchronized refined future. -/
theorem isSafe_erases {outL : Physical → LeaderOutput}
    (R : ErasingLocalRefinement Physical Refined LeaderOutput T outL)
    (ring : DirectedRing n) (C : Fin n → Refined)
    (hsafe : PopulationProtocol.IsSafe R.refinedProtocol ring C
      isLeaderOutput) :
    PopulationProtocol.IsSafe R.physicalProtocol ring
      (R.eraseConfig C) isLeaderOutput := by
  constructor
  · obtain ⟨leader, hleader, hunique⟩ := hsafe.1
    refine ⟨leader, ?_, ?_⟩
    · change isLeaderOutput (outL (R.erase (C leader))) = true
      rw [← R.output_erases]
      exact hleader
    · intro j hj
      apply hunique j
      change isLeaderOutput (outL (R.erase (C j))) = true at hj
      rw [← R.output_erases] at hj
      exact hj
  · intro D hreach i
    obtain ⟨Dref, href, herase⟩ := R.lift_physical_reachable ring hreach
    have hout := hsafe.2 Dref href i
    have hd := congrFun herase i
    change R.erase (Dref i) = D i at hd
    change outL (D i) = outL (R.erase (C i))
    calc
      outL (D i) = outL (R.erase (Dref i)) := congrArg outL hd.symm
      _ = R.refinedOutput (Dref i) := (R.output_erases _).symm
      _ = R.refinedOutput (C i) := hout
      _ = outL (R.erase (C i)) := R.output_erases _

/-- Exact erasure commutes with every finite edge schedule. -/
theorem erase_runLocalSchedule
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (ring : DirectedRing n) (C : Fin n → Refined) (s : DetSchedule n) :
    R.eraseConfig (runLocalSchedule ring R.refinedTransition C s) =
      runLocalSchedule ring T (R.eraseConfig C) s := by
  induction s generalizing C with
  | nil => rfl
  | cons e rest ih =>
    simp only [runLocalSchedule]
    rw [ih, R.erase_localStep]

/-- Any output change visible after erasure is necessarily visible in the
refined execution.  A proof ghost cannot turn that physical transition into an
output-preserving one. -/
theorem refined_output_changes_of_erased_change
    (R : ErasingLocalRefinement Physical Refined Output T out)
    {before after : Refined}
    (hchange : out (R.erase after) ≠ out (R.erase before)) :
    R.refinedOutput after ≠ R.refinedOutput before := by
  intro heq
  apply hchange
  exact (R.output_erases after).symm.trans
    (heq.trans (R.output_erases before))

/-- Specialized to a total lift and one edge: if the physical step changes an
agent output, the same-edge refined step changes that output as well. -/
theorem lifted_step_output_change
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (ring : DirectedRing n) (C : Fin n → Physical) (e i : Fin n)
    (hchange : out (localStep ring T C e i) ≠ out (C i)) :
    let refinedC := R.liftConfig C
    let refinedNext := localStep ring R.refinedTransition refinedC e
    R.refinedOutput (refinedNext i) ≠ R.refinedOutput (refinedC i) := by
  dsimp only
  apply R.refined_output_changes_of_erased_change
  have hs := congrFun (R.erase_localStep ring (R.liftConfig C) e) i
  have hc := congrFun (R.erase_liftConfig C) i
  change R.erase
      (localStep ring R.refinedTransition (R.liftConfig C) e i) =
    localStep ring T (R.eraseConfig (R.liftConfig C)) e i at hs
  change R.erase (R.liftConfig C i) = C i at hc
  rw [hs, hc, R.erase_liftConfig]
  exact hchange

/-! ## Honest trusted-set and cleanup interfaces -/

/-- Trusted refined configurations are inductive under every edge. -/
def TrustedClosed
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (ring : DirectedRing n) (Trusted : (Fin n → Refined) → Prop) : Prop :=
  ∀ C, Trusted C → ∀ e, Trusted (localStep ring R.refinedTransition C e)

/-- Every trusted refined configuration currently has one leader output. -/
def TrustedUniqueLeader {outL : Physical → LeaderOutput}
    (R : ErasingLocalRefinement Physical Refined LeaderOutput T outL)
    (Trusted : (Fin n → Refined) → Prop) : Prop :=
  ∀ C, Trusted C → UniqueLeaderOutput R.refinedProtocol n C isLeaderOutput

/-- Every edge from a trusted configuration preserves the full output vector. -/
def TrustedStepOutput
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (ring : DirectedRing n) (Trusted : (Fin n → Refined) → Prop) : Prop :=
  ∀ C, Trusted C → ∀ e i,
    R.refinedOutput (localStep ring R.refinedTransition C e i) =
      R.refinedOutput (C i)

/-- A particular schedule cleans an arbitrary physical input into the trusted
refined subset.  Random-scheduler convergence must count schedules satisfying
this predicate; total lifting alone supplies no trust. -/
def CleanupWithinSchedule
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (ring : DirectedRing n) (Trusted : (Fin n → Refined) → Prop)
    (C : Fin n → Physical) (s : DetSchedule n) : Prop :=
  Trusted (runLocalSchedule ring R.refinedTransition (R.liftConfig C) s)

private theorem trustedClosed_as_ClosedPred
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (ring : DirectedRing n) (Trusted : (Fin n → Refined) → Prop)
    (hclosed : R.TrustedClosed ring Trusted) :
    PopulationProtocol.ClosedPred R.refinedProtocol ring Trusted := by
  intro C hC C' hone
  obtain ⟨e, rfl⟩ := hone
  rw [← localStep_eq_protocol_step]
  exact hclosed C hC e

private theorem trustedStep_as_outputPreserving
    (R : ErasingLocalRefinement Physical Refined Output T out)
    (ring : DirectedRing n) (Trusted : (Fin n → Refined) → Prop)
    (hstep : R.TrustedStepOutput ring Trusted) :
    StepOutputPreservingOn R.refinedProtocol ring Trusted := by
  intro C hC C' hone i
  obtain ⟨e, rfl⟩ := hone
  rw [← localStep_eq_protocol_step]
  exact hstep C hC e i

/-- The three local trusted-set obligations imply Definition-1 safety of the
refined protocol.  This is a proof interface, not an instantiation for P_PLL. -/
theorem trusted_isSafe {outL : Physical → LeaderOutput}
    (R : ErasingLocalRefinement Physical Refined LeaderOutput T outL)
    (ring : DirectedRing n) (Trusted : (Fin n → Refined) → Prop)
    (hclosed : R.TrustedClosed ring Trusted)
    (hunique : R.TrustedUniqueLeader Trusted)
    (hstep : R.TrustedStepOutput ring Trusted)
    {C : Fin n → Refined} (hC : Trusted C) :
    PopulationProtocol.IsSafe R.refinedProtocol ring C isLeaderOutput := by
  apply isSafe_of_operational_legitimacy R.refinedProtocol ring
    isLeaderOutput Trusted (R.trustedClosed_as_ClosedPred ring Trusted hclosed)
    hunique (R.trustedStep_as_outputPreserving ring Trusted hstep) hC

end ErasingLocalRefinement

/-! ## Concrete receipt refinement instance -/

/-- The historical reset-receipt layer is an erasing proof refinement of the
finite integrated physical candidate: its ghost never changes physical state
or output. -/
def receiptRefinement {n ψ : Nat} (regime : OperationalRegime n ψ)
    (κ : Nat) :
    ErasingLocalRefinement
      (BoundedAgentState ψ κ)
      (PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ)
      LeaderOutput
      (PPLLRepair.integratedBoundedTransition regime.hψ κ)
      (fun s => AgentState.outputFn (BoundedAgentState.erase s)) where
  refinedTransition := PPLLSuppressionHistory.boundedTransition regime.hψ κ
  refinedOutput := fun s => AgentState.outputFn
    (BoundedAgentState.erase s.concrete)
  erase := fun s => s.concrete
  lift := freshReceiptState
  erase_lift := by intro s; rfl
  transition_erases := by
    intro l r
    have h := PPLLSuppressionHistory.erase_boundedTransition
      regime.hψ κ l r
    dsimp only at h ⊢
    have hleft :
        (PPLLSuppressionHistory.boundedTransition regime.hψ κ l r).1.concrete =
          (PPLLRepair.integratedBoundedTransition regime.hψ κ
            l.concrete r.concrete).1 := by
      simpa only using congrArg Prod.fst h
    have hright :
        (PPLLSuppressionHistory.boundedTransition regime.hψ κ l r).2.concrete =
          (PPLLRepair.integratedBoundedTransition regime.hψ κ
            l.concrete r.concrete).2 := by
      simpa only using congrArg Prod.snd h
    exact ⟨hleft, hright⟩
  output_erases := by intro s; rfl

/-! ## No-ghost-guard theorem for the finite T1 trace -/

/-- Every exact erasing refinement of the integrated finite transition inherits
T1's output-changing edge from its canonical total lift.  Therefore an
untrusted ghost tag can classify T1 outside a trusted set, but cannot “deny”
its physical CHECK. -/
theorem t1_survives_every_erasing_refinement
    {Refined : Type}
    (R : ErasingLocalRefinement
      (BoundedAgentState 2 10) Refined LeaderOutput
      (PPLLRepair.integratedBoundedTransition (by omega) 10)
      (fun s => AgentState.outputFn (BoundedAgentState.erase s))) :
    let refinedC := R.liftConfig t1FiniteConfig
    let refinedNext := localStep ring4 R.refinedTransition refinedC 2
    R.refinedOutput (refinedNext 2) ≠ R.refinedOutput (refinedC 2) := by
  apply R.lifted_step_output_change
  have hstep : localStep ring4
      (PPLLRepair.integratedBoundedTransition (by omega) 10)
      t1FiniteConfig 2 = t1FiniteSuccessor := by
    rfl
  rw [congrFun hstep 2]
  exact t1_finite_output_changes

end PPLLErasingRefinement
