import Leader.Wu.Safety.PermitRepairQuietLap


namespace R1QuietWaitNotClosed


open PPLLExpiringComparisonRepair R1CandidateKernel


set_option autoImplicit false
set_option Elab.async false


/-- The old `witness`, with exactly site 5's WAIT token released. -/
def waitSeed (i : Fin 9) : ExpiringAgentState 3 3 48 :=
  let u := R1CandidateKernel.witness i
  if i = 5 then
    let b := { u.core.core with wait := false }
    ⟨⟨b, u.core.path0Crossed⟩, u.stall⟩
  else u


/- Closed finite certificate for membership in the unchanged candidate. -/
theorem waitSeed_bool :
    candR1B (by decide : 0 < 3) (by decide : 2 ≤ 3)
      witnessRing waitSeed = true := by
  decide +kernel


theorem waitSeed_mem :
    CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3)
      witnessRing waitSeed :=
  (candR1B_iff (by decide) (by decide)
    witnessRing waitSeed).1 waitSeed_bool


/-- Serve the physical edge 4 -> 5 once. -/
def waitAfter : FC 9 3 3 48 :=
  BirthCheckPermitRepairLeaf.step1 (by decide : 0 < 3)
    (by decide : 2 ≤ 3) witnessRing waitSeed (4 : Fin 9)


/-- Named equality recorded before the fixture/row opacity barrier. -/
private theorem waitAfter_eq :
    waitAfter =
      BirthCheckPermitRepairLeaf.step1 (by decide : 0 < 3)
        (by decide : 2 ≤ 3) witnessRing waitSeed (4 : Fin 9) := rfl


/- The width-two WAIT finish moves the false token from site 5 to site 4. -/
theorem waitAfter_token :
    (waitAfter (4 : Fin 9)).core.core.wait = false ∧
      (waitAfter (5 : Fin 9)).core.core.wait = true := by
  decide +kernel


/- Re-running the actual next CHECK prefix on predecessor edge 3 -> 4 starts
GEN on both endpoints before CHECK: both states are `.produce`. -/
theorem waitAfter_pred_check_produce :
    (checkInput (by decide : 0 < 3) (by decide : 2 ≤ 3)
      (waitAfter (3 : Fin 9))
      (waitAfter (witnessRing.rightNeighbor (3 : Fin 9)))).1.core.state =
        .produce ∧
    (checkInput (by decide : 0 < 3) (by decide : 2 ≤ 3)
      (waitAfter (3 : Fin 9))
      (waitAfter (witnessRing.rightNeighbor (3 : Fin 9)))).2.core.state =
        .produce := by
  decide +kernel


/- From here on, do not execute the fixture or either physical row by whnf. -/
attribute [local irreducible]
  waitSeed waitAfter
  BirthCheckPermitRepairLeaf.step1 BirthCheckPermitRepair.row


/-- Abstract projection of the exact `EdgeSafe` field used below. -/
private theorem candidate_checkInput_left_quiet
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hC : CandR1 hpsi h2 ring C)
    (f : Fin n) :
    AuthQuiet
      (checkInput hpsi h2 (C f) (C (ring.rightNeighbor f))).1 := by
  obtain ⟨_, hA⟩ := hC
  exact (hA.2.2.2.2 f).2.1


/-- The concrete predecessor CHECK contradicts the abstract `AuthQuiet` cut. -/
theorem waitAfter_not_candR1 :
    ¬ CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3)
      witnessRing waitAfter := by
  intro hC
  have hq := candidate_checkInput_left_quiet
    (by decide : 0 < 3) (by decide : 2 ≤ 3)
    witnessRing waitAfter hC (3 : Fin 9)
  have hnone :
      (checkInput (by decide : 0 < 3) (by decide : 2 ≤ 3)
        (waitAfter (3 : Fin 9))
        (waitAfter (witnessRing.rightNeighbor (3 : Fin 9)))).1.core.state =
          .none :=
    hq.1.1
  have hbad : MainState.none = MainState.produce :=
    hnone.symm.trans waitAfter_pred_check_produce.1
  cases hbad


/-- One-step non-closure of the unchanged `CandR1`. -/
theorem candR1_not_closed_wait :
    ∃ (C : FC 9 3 3 48) (e : Fin 9),
      CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3) witnessRing C ∧
      ¬ CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3) witnessRing
        (BirthCheckPermitRepairLeaf.step1 (by decide : 0 < 3)
          (by decide : 2 ≤ 3) witnessRing C e) := by
  refine ⟨waitSeed, (4 : Fin 9), waitSeed_mem, ?_⟩
  rw [← waitAfter_eq]
  exact waitAfter_not_candR1


/-- Candidate-independent failure of the all-edge quiet CHECK-input clause.
Any proposed successor predicate retaining this conjunct is falsified by the
same member and the same one-step service. -/
theorem quietCheckInput_not_closed :
    ∃ (C : FC 9 3 3 48) (e : Fin 9),
      CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3) witnessRing C ∧
      ¬ (∀ f : Fin 9,
        AuthQuiet
          (checkInput (by decide : 0 < 3) (by decide : 2 ≤ 3)
            (BirthCheckPermitRepairLeaf.step1 (by decide : 0 < 3)
              (by decide : 2 ≤ 3) witnessRing C e f)
            (BirthCheckPermitRepairLeaf.step1 (by decide : 0 < 3)
              (by decide : 2 ≤ 3) witnessRing C e
              (witnessRing.rightNeighbor f))).1) := by
  refine ⟨waitSeed, (4 : Fin 9), waitSeed_mem, ?_⟩
  intro hquiet
  have hnone :
      (checkInput (by decide : 0 < 3) (by decide : 2 ≤ 3)
        (waitAfter (3 : Fin 9))
        (waitAfter (witnessRing.rightNeighbor (3 : Fin 9)))).1.core.state =
          .none := by
    rw [waitAfter_eq]
    exact (hquiet (3 : Fin 9)).1.1
  have hbad : MainState.none = MainState.produce :=
    hnone.symm.trans waitAfter_pred_check_produce.1
  cases hbad


end R1QuietWaitNotClosed
