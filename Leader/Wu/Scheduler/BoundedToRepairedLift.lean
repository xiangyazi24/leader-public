import Leader.Wu.Scheduler.BoundedRouteFromPointwise


set_option autoImplicit false
set_option Elab.async false


/-!
# Exact bounded-to-repaired lift on the erasure image


This module concerns exactly `PPLLRepair.boundedProtocol` and
`PPLLRepair.protocol`, not `PPLL.protocol` or either integrated candidate.


The image restriction cannot be removed by this erasure argument because
raw states outside `inProtocolDomain` have no bounded preimage and no
uniform entrance into the image is supplied.


The restriction is on initial configurations only: every occurrence of
`PopulationProtocol.IsSafe` below quantifies over all reachable futures of
the named protocol. Reverse lifting of repaired executions is proved, not
assumed. The same scheduler word and every one of its prefixes are retained,
so the two protocols have equal stabilizing-schedule counts at every horizon.


The existing global `UniformOneOverNFailureAtHorizon` cannot express an
initial-domain restriction. The final theorem therefore writes its
image-restricted expansion explicitly, with c = 1 and the unchanged horizon.
-/


namespace ZZLiftToRepaired


open PPLLResearchFormulation


/-! ## The section and its exact image -/


/-- Pointwise section of erasure on the explicitly certified numeric domain. -/
def reifyConfig {ψ κ n : Nat}
    (C : Fin n → AgentState ψ)
    (hC : ∀ i : Fin n, (C i).inProtocolDomain κ) :
    Fin n → BoundedAgentState ψ κ :=
  fun i => BoundedAgentState.ofDomain (C i) (hC i)


/-- Every erased bounded configuration satisfies the numeric domain. -/
theorem eraseConfig_domain {ψ κ n : Nat}
    (B : Fin n → BoundedAgentState ψ κ) :
    ∀ i : Fin n, (PPLLRepair.eraseConfig B i).inProtocolDomain κ := by
  intro i
  exact BoundedAgentState.erase_inProtocolDomain (B i)


/-- Erasing the section returns the original raw configuration exactly. -/
theorem erase_reifyConfig {ψ κ n : Nat}
    (C : Fin n → AgentState ψ)
    (hC : ∀ i : Fin n, (C i).inProtocolDomain κ) :
    PPLLRepair.eraseConfig (reifyConfig C hC) = C := by
  funext i
  exact BoundedAgentState.erase_ofDomain (C i) (hC i)


/-- Reifying an erased bounded configuration returns it exactly. -/
theorem reify_eraseConfig {ψ κ n : Nat}
    (B : Fin n → BoundedAgentState ψ κ) :
    reifyConfig (PPLLRepair.eraseConfig B) (eraseConfig_domain B) = B := by
  funext i
  exact BoundedAgentState.ofDomain_erase (B i)


/-- The domain restriction is exactly the erasure image, not a smaller set. -/
theorem mem_erase_image_iff {ψ κ n : Nat}
    (C : Fin n → AgentState ψ) :
    (∃ B : Fin n → BoundedAgentState ψ κ,
      PPLLRepair.eraseConfig B = C) ↔
      (∀ i : Fin n, (C i).inProtocolDomain κ) := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := h
    rw [← hB]
    exact eraseConfig_domain B
  · intro hC
    exact ⟨reifyConfig C hC, erase_reifyConfig C hC⟩


/-- A concrete obstruction to a section on all raw configurations.
This is a statement about erasure, not a nonconvergence theorem. -/
theorem no_preimage_of_count_gt {ψ κ n : Nat}
    (C : Fin n → AgentState ψ) (i : Fin n)
    (hcount : κ < (C i).count) :
    ¬ (∃ B : Fin n → BoundedAgentState ψ κ,
      PPLLRepair.eraseConfig B = C) := by
  intro h
  have hdom := (mem_erase_image_iff (κ := κ) C).1 h
  have hle : (C i).count ≤ κ := (hdom i).1
  omega


/-! ## Reverse reachable-execution lifting and domain closedness -/


/-- Lift every repaired execution from any supplied bounded preimage.
Each repaired edge is replayed as that same edge on the bounded carrier. -/
theorem lift_reachable {ψ κ n : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n)
    {C D : (PPLLRepair.protocol hψ κ).Configuration n}
    (h : PopulationProtocol.Reachable
      (PPLLRepair.protocol hψ κ) ring C D) :
    ∀ B : Fin n → BoundedAgentState ψ κ,
      PPLLRepair.eraseConfig B = C →
      ∃ B' : Fin n → BoundedAgentState ψ κ,
        PopulationProtocol.Reachable
          (PPLLRepair.boundedProtocol hψ κ) ring B B' ∧
        PPLLRepair.eraseConfig B' = D := by
  induction h with
  | refl =>
      intro B hB
      refine ⟨B, ?_, hB⟩
      exact @PopulationProtocol.Reachable.refl n
        (PPLLRepair.boundedProtocol hψ κ) ring B
  | step D E _hCD hDE ih =>
      intro B hB
      obtain ⟨B', hBB', hB'D⟩ := ih B hB
      obtain ⟨e, hE⟩ := hDE
      refine ⟨(PPLLRepair.boundedProtocol hψ κ).step ring B' e, ?_, ?_⟩
      · exact @PopulationProtocol.Reachable.step n
          (PPLLRepair.boundedProtocol hψ κ) ring
          B B' ((PPLLRepair.boundedProtocol hψ κ).step ring B' e)
          hBB' ⟨e, rfl⟩
      · exact
          (PPLLRepair.erase_step hψ ring B' e).trans
            ((congrArg
              (fun X : (PPLLRepair.protocol hψ κ).Configuration n =>
                (PPLLRepair.protocol hψ κ).step ring X e) hB'D).trans
              hE.symm)


/-- Every repaired future of a domain-legal start is again domain-legal. -/
theorem domain_reachable {ψ κ n : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n)
    {C D : (PPLLRepair.protocol hψ κ).Configuration n}
    (hC : ∀ i : Fin n, (C i).inProtocolDomain κ)
    (h : PopulationProtocol.Reachable
      (PPLLRepair.protocol hψ κ) ring C D) :
    ∀ i : Fin n, (D i).inProtocolDomain κ := by
  obtain ⟨B', _hreach, hB'⟩ :=
    lift_reachable hψ ring h (reifyConfig C hC)
      (erase_reifyConfig C hC)
  rw [← hB']
  exact eraseConfig_domain B'


/-- Closedness of the explicit initial domain under the repaired protocol. -/
theorem domain_closed {ψ κ n : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (PPLLRepair.protocol hψ κ) ring
      (fun C => ∀ i : Fin n, (C i).inProtocolDomain κ) := by
  intro C hC D hstep
  exact domain_reachable hψ ring hC
    (PopulationProtocol.OneStep.to_reachable hstep)


/-! ## Full semantic safety, in both directions -/


/-- Full IsSafe equivalence on an erased configuration.
The forward implication uses reverse execution lifting; the reverse
implication uses the repository's bounded-to-repaired erase_reachable. -/
theorem isSafe_erase_iff {ψ κ n : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n)
    (B : Fin n → BoundedAgentState ψ κ) :
    PopulationProtocol.IsSafe (PPLLRepair.boundedProtocol hψ κ)
        ring B isLeaderOutput ↔
      PopulationProtocol.IsSafe (PPLLRepair.protocol hψ κ)
        ring (PPLLRepair.eraseConfig B) isLeaderOutput := by
  constructor
  · intro hsafe
    refine ⟨?_, ?_⟩
    · change ∃ i : Fin n,
        isLeaderOutput (AgentState.outputFn (BoundedAgentState.erase (B i))) = true ∧
        ∀ j : Fin n,
          isLeaderOutput (AgentState.outputFn (BoundedAgentState.erase (B j))) = true →
          j = i
      exact hsafe.1
    · intro D hreach i
      obtain ⟨B', hB', hD⟩ := lift_reachable hψ ring hreach B rfl
      have hout := hsafe.2 B' hB' i
      change AgentState.outputFn (BoundedAgentState.erase (B' i)) =
        AgentState.outputFn (BoundedAgentState.erase (B i)) at hout
      change AgentState.outputFn (D i) =
        AgentState.outputFn (BoundedAgentState.erase (B i))
      have hi : BoundedAgentState.erase (B' i) = D i := congrFun hD i
      exact
        (congrArg (fun s : AgentState ψ => AgentState.outputFn s) hi).symm.trans hout
  · intro hsafe
    refine ⟨?_, ?_⟩
    · change ∃ i : Fin n,
        isLeaderOutput (AgentState.outputFn (BoundedAgentState.erase (B i))) = true ∧
        ∀ j : Fin n,
          isLeaderOutput (AgentState.outputFn (BoundedAgentState.erase (B j))) = true →
          j = i
      exact hsafe.1
    · intro B' hreach i
      have hraw := PPLLRepair.erase_reachable hψ ring hreach
      have hout := hsafe.2 (PPLLRepair.eraseConfig B') hraw i
      change AgentState.outputFn (BoundedAgentState.erase (B' i)) =
        AgentState.outputFn (BoundedAgentState.erase (B i)) at hout
      change AgentState.outputFn (BoundedAgentState.erase (B' i)) =
        AgentState.outputFn (BoundedAgentState.erase (B i))
      exact hout


/-- The section preserves and reflects full semantic safety. -/
theorem isSafe_reify_iff {ψ κ n : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C : (PPLLRepair.protocol hψ κ).Configuration n)
    (hC : ∀ i : Fin n, (C i).inProtocolDomain κ) :
    PopulationProtocol.IsSafe (PPLLRepair.boundedProtocol hψ κ)
        ring (reifyConfig C hC) isLeaderOutput ↔
      PopulationProtocol.IsSafe (PPLLRepair.protocol hψ κ)
        ring C isLeaderOutput := by
  have h := isSafe_erase_iff hψ ring (reifyConfig C hC)
  rw [erase_reifyConfig C hC] at h
  exact h


/-! ## Same-word and same-prefix execution -/


/-- Erasure commutes with the original protocol schedule interpreter. -/
theorem erase_runSchedule {ψ κ n : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n)
    (B : Fin n → BoundedAgentState ψ κ) (w : DetSchedule n) :
    PPLLRepair.eraseConfig
        (runSchedule (PPLLRepair.boundedProtocol hψ κ) ring B w) =
      runSchedule (PPLLRepair.protocol hψ κ) ring
        (PPLLRepair.eraseConfig B) w := by
  induction w generalizing B with
  | nil => rfl
  | cons e es ih =>
      change
        PPLLRepair.eraseConfig
            (runSchedule (PPLLRepair.boundedProtocol hψ κ) ring
              ((PPLLRepair.boundedProtocol hψ κ).step ring B e) es) =
          runSchedule (PPLLRepair.protocol hψ κ) ring
            ((PPLLRepair.protocol hψ κ).step ring
              (PPLLRepair.eraseConfig B) e) es
      exact
        (ih ((PPLLRepair.boundedProtocol hψ κ).step ring B e)).trans
          (congrArg
            (fun X : (PPLLRepair.protocol hψ κ).Configuration n =>
              runSchedule (PPLLRepair.protocol hψ κ) ring X es)
            (PPLLRepair.erase_step hψ ring B e))


/-- The same exact commutation for the interpreter appearing in hpoint. -/
theorem erase_runLocalSchedule {ψ κ n : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n)
    (B : Fin n → BoundedAgentState ψ κ) (w : DetSchedule n) :
    PPLLRepair.eraseConfig
        (runLocalSchedule ring
          (PPLLRepair.boundedProtocol hψ κ).transition B w) =
      runLocalSchedule ring (PPLLRepair.protocol hψ κ).transition
        (PPLLRepair.eraseConfig B) w := by
  exact
    (congrArg
      (fun X : (PPLLRepair.boundedProtocol hψ κ).Configuration n =>
        PPLLRepair.eraseConfig X)
      (runLocalSchedule_eq_runSchedule
        (PPLLRepair.boundedProtocol hψ κ) ring B w)).trans
      ((erase_runSchedule hψ ring B w).trans
        (runLocalSchedule_eq_runSchedule
          (PPLLRepair.protocol hψ κ) ring (PPLLRepair.eraseConfig B) w).symm)


/-- A scheduler word succeeds on one side exactly when it succeeds on the
other; the witnessing prefix length is unchanged. -/
theorem reachesSafeWithinSchedule_erase_iff {ψ κ n : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n)
    (B : Fin n → BoundedAgentState ψ κ) (w : DetSchedule n) :
    ReachesSafeWithinSchedule (PPLLRepair.boundedProtocol hψ κ)
        ring isLeaderOutput B w ↔
      ReachesSafeWithinSchedule (PPLLRepair.protocol hψ κ)
        ring isLeaderOutput (PPLLRepair.eraseConfig B) w := by
  unfold ReachesSafeWithinSchedule
  constructor
  · intro h
    obtain ⟨k, hk, hs⟩ := h
    refine ⟨k, hk, ?_⟩
    have hs' :=
      (isSafe_erase_iff hψ ring
        (runSchedule (PPLLRepair.boundedProtocol hψ κ)
          ring B (w.take k))).1 hs
    rw [erase_runSchedule hψ ring B (w.take k)] at hs'
    exact hs'
  · intro h
    obtain ⟨k, hk, hs⟩ := h
    refine ⟨k, hk, ?_⟩
    apply
      (isSafe_erase_iff hψ ring
        (runSchedule (PPLLRepair.boundedProtocol hψ κ)
          ring B (w.take k))).2
    rw [erase_runSchedule hψ ring B (w.take k)]
    exact hs


/-! ## Exact equality of the named protocols' scheduler counts -/


/-- Count equality at every horizon, not merely an inequality.
Both sides count the same edge-word list with equivalent success predicates. -/
theorem stabilizingScheduleCount_erase {ψ κ n : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n)
    (B : Fin n → BoundedAgentState ψ κ) (t : Nat) :
    stabilizingScheduleCount (PPLLRepair.boundedProtocol hψ κ)
        ring isLeaderOutput B t =
      stabilizingScheduleCount (PPLLRepair.protocol hψ κ)
        ring isLeaderOutput (PPLLRepair.eraseConfig B) t := by
  classical
  have hp :
      (fun w : DetSchedule n =>
        if ReachesSafeWithinSchedule (PPLLRepair.boundedProtocol hψ κ)
          ring isLeaderOutput B w then true else false) =
      (fun w : DetSchedule n =>
        if ReachesSafeWithinSchedule (PPLLRepair.protocol hψ κ)
          ring isLeaderOutput (PPLLRepair.eraseConfig B) w
        then true else false) := by
    funext w
    by_cases hb : ReachesSafeWithinSchedule
        (PPLLRepair.boundedProtocol hψ κ) ring isLeaderOutput B w
    · have hr := (reachesSafeWithinSchedule_erase_iff hψ ring B w).1 hb
      simp only [if_pos hb, if_pos hr]
    · have hr : ¬ ReachesSafeWithinSchedule
          (PPLLRepair.protocol hψ κ) ring isLeaderOutput
          (PPLLRepair.eraseConfig B) w := by
        intro hraw
        exact hb ((reachesSafeWithinSchedule_erase_iff hψ ring B w).2 hraw)
      simp only [if_neg hb, if_neg hr]
  unfold stabilizingScheduleCount
  exact congrArg
    (fun p : DetSchedule n → Bool => (allSchedules n t).countP p) hp


/-- Count equality for every raw start satisfying the explicit domain. -/
theorem stabilizingScheduleCount_reify {ψ κ n : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C : (PPLLRepair.protocol hψ κ).Configuration n)
    (hC : ∀ i : Fin n, (C i).inProtocolDomain κ) (t : Nat) :
    stabilizingScheduleCount (PPLLRepair.boundedProtocol hψ κ)
        ring isLeaderOutput (reifyConfig C hC) t =
      stabilizingScheduleCount (PPLLRepair.protocol hψ κ)
        ring isLeaderOutput C t := by
  have h := stabilizingScheduleCount_erase hψ ring (reifyConfig C hC) t
  rw [erase_reifyConfig C hC] at h
  exact h


/-- For each supplied c and t, the bounded global statement is equivalent
to the repaired statement with exactly the initial-image restriction.
The repaired side counts its own IsSafe prefix events. -/
theorem uniformOneOverNFailure_iff_on_image {ψ κ n : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n) (c t : Nat) :
    UniformOneOverNFailureAtHorizon (PPLLRepair.boundedProtocol hψ κ)
        ring isLeaderOutput c t ↔
      (c < n ∧ 0 < t ∧
        ∀ C : (PPLLRepair.protocol hψ κ).Configuration n,
          (∀ i : Fin n, (C i).inProtocolDomain κ) →
          (allSchedules n t).length ≤
            stabilizingScheduleCount (PPLLRepair.protocol hψ κ)
              ring isLeaderOutput C t + c * n ^ (t - 1)) := by
  constructor
  · intro h
    obtain ⟨hc, ht, hall⟩ := h
    refine ⟨hc, ht, ?_⟩
    intro C hC
    have hb := hall (reifyConfig C hC)
    rw [stabilizingScheduleCount_reify hψ ring C hC t] at hb
    exact hb
  · intro h
    obtain ⟨hc, ht, hall⟩ := h
    refine ⟨hc, ht, ?_⟩
    intro B
    have hr := hall (PPLLRepair.eraseConfig B) (eraseConfig_domain B)
    rw [← stabilizingScheduleCount_erase hψ ring B t] at hr
    exact hr


/-! ## The requested lifted bounded route -/


/-- Same L, horizon, and 1/n failure allowance as the bounded route.
Only the initial configurations are restricted; repaired IsSafe remains full. -/
theorem repaired_explicitOneOverNSSLE_on_domain_of_pointwise
    {ψ κ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (hn2 : 1 < n)
    (hpoint :
      ∀ C : (PPLLRepair.boundedProtocol hψ κ).Configuration n,
        ¬ PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ κ) ring C isLeaderOutput →
        ∃ w : DetSchedule n,
          PopulationProtocol.IsSafe
            (PPLLRepair.boundedProtocol hψ κ) ring
            (runLocalSchedule ring
              (PPLLRepair.boundedProtocol hψ κ).transition C w)
            isLeaderOutput) :
    ∃ L : Nat, 0 < L ∧
      let t := ((n - 1) * (n ^ L - 1) + 1) * L
      1 < n ∧ 0 < t ∧
        ∀ C : (PPLLRepair.protocol hψ κ).Configuration n,
          (∀ i : Fin n, (C i).inProtocolDomain κ) →
          (allSchedules n t).length ≤
            stabilizingScheduleCount (PPLLRepair.protocol hψ κ)
              ring isLeaderOutput C t + 1 * n ^ (t - 1) := by
  obtain ⟨L, hL, hbounded⟩ :=
    ZZBoundedRoute.bounded_explicitOneOverNSSLE_of_pointwise
      (κ := κ) hψ ring hn2 hpoint
  refine ⟨L, hL, ?_⟩
  exact
    (uniformOneOverNFailure_iff_on_image (κ := κ) hψ ring 1
      (((n - 1) * (n ^ L - 1) + 1) * L)).1 hbounded


end ZZLiftToRepaired


#print axioms ZZLiftToRepaired.reifyConfig
#print axioms ZZLiftToRepaired.eraseConfig_domain
#print axioms ZZLiftToRepaired.erase_reifyConfig
#print axioms ZZLiftToRepaired.reify_eraseConfig
#print axioms ZZLiftToRepaired.mem_erase_image_iff
#print axioms ZZLiftToRepaired.no_preimage_of_count_gt
#print axioms ZZLiftToRepaired.lift_reachable
#print axioms ZZLiftToRepaired.domain_reachable
#print axioms ZZLiftToRepaired.domain_closed
#print axioms ZZLiftToRepaired.isSafe_erase_iff
#print axioms ZZLiftToRepaired.isSafe_reify_iff
#print axioms ZZLiftToRepaired.erase_runSchedule
#print axioms ZZLiftToRepaired.erase_runLocalSchedule
#print axioms ZZLiftToRepaired.reachesSafeWithinSchedule_erase_iff
#print axioms ZZLiftToRepaired.stabilizingScheduleCount_erase
#print axioms ZZLiftToRepaired.stabilizingScheduleCount_reify
#print axioms ZZLiftToRepaired.uniformOneOverNFailure_iff_on_image
#print axioms ZZLiftToRepaired.repaired_explicitOneOverNSSLE_on_domain_of_pointwise
