import Leader.Wu.Birth.ZeroLeaderClosedRingFour

/-!
# A coupled ψ = 1, κ = 1, n = 2 zero-leader closed class

This file tests the added finite-parameter gate `n ≤ 2 ^ ψ` at its smallest
nontrivial instance.  It reuses the accepted four-state bounded local closure
and proves that the gate does not exclude the zero-leader closed family when
`ψ = 1`, `κ = 1`, and `n = 2`.
-/

namespace ZZZeroLeaderCoupled

open PopulationProtocol
open PPLLResearchFormulation
open ZZZeroLeaderFinite
open ZZZeroLeaderClosed

set_option autoImplicit false
set_option Elab.async false

abbrev P : PopulationProtocol := ZZZeroLeaderClosed.P

def ring2 : DirectedRing 2 := ⟨by decide⟩

/-- The proposed parameter coupling holds at this instance. -/
theorem ring2_coupling : 2 ≤ 2 ^ (1 : Nat) := by decide

abbrev BConfig := Fin 2 → BoundedAgentState 1 1

def ZeroLeaderFamily (C : BConfig) : Prop :=
  ∀ i : Fin 2, ∃ c : Code4, C i = bcell c

def zeroConfig : BConfig := fun _ => bcell .A

theorem zeroConfig_mem : ZeroLeaderFamily zeroConfig := by
  intro i
  exact ⟨.A, rfl⟩

private theorem ring2_right_ne (e : Fin 2) :
    ring2.rightNeighbor e ≠ e := by
  have he : e = 0 ∨ e = 1 := by
    have hi := e.isLt
    omega
  rcases he with rfl | rfl <;> decide

private theorem zeroFamily_localStep
    (C : BConfig) (hC : ZeroLeaderFamily C) (e : Fin 2) :
    ZeroLeaderFamily
      (localStep ring2 (PPLLRepair.boundedTransition hψ1 1) C e) := by
  let j := ring2.rightNeighbor e
  have hne : j ≠ e := ring2_right_ne e
  obtain ⟨lc, hl⟩ := hC e
  obtain ⟨rc, hr⟩ := hC j
  have hpair := bounded_pair_transition lc rc
  intro i
  by_cases hie : i = e
  · subst i
    refine ⟨leftNext lc, ?_⟩
    have hleft :
        (localStep ring2 (PPLLRepair.boundedTransition hψ1 1) C e) e =
          (PPLLRepair.boundedTransition hψ1 1 (C e) (C j)).1 := by
      simp [localStep, j]
    rw [hleft, hl, hr]
    exact congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      refine ⟨rightNext lc, ?_⟩
      have hright :
          (localStep ring2 (PPLLRepair.boundedTransition hψ1 1) C e) j =
            (PPLLRepair.boundedTransition hψ1 1 (C e) (C j)).2 := by
        simp [localStep, j, hne]
      rw [hright, hl, hr]
      exact congrArg Prod.snd hpair
    · have hCi := hC i
      have hother :
          (localStep ring2 (PPLLRepair.boundedTransition hψ1 1) C e) i = C i := by
        simp [localStep, j, hie, hij]
      simpa only [hother] using hCi

theorem zeroFamily_closed :
    PopulationProtocol.ClosedPred P ring2 ZeroLeaderFamily := by
  intro C hC C' hstep
  rcases hstep with ⟨e, rfl⟩
  have heq :
      localStep ring2 (PPLLRepair.boundedTransition hψ1 1) C e =
        P.step ring2 C e := by
    rfl
  rw [← heq]
  exact zeroFamily_localStep C hC e

theorem zeroFamily_not_isSafe
    (C : P.Configuration 2) (hC : ZeroLeaderFamily C) :
    ¬ PopulationProtocol.IsSafe P ring2 C isLeaderOutput := by
  intro hsafe
  obtain ⟨i, hi, _⟩ := hsafe.1
  obtain ⟨c, hc⟩ := hC i
  have hi0 : isLeaderOutput (P.output (C i)) = false := by
    rw [hc]
    change isLeaderOutput
      (AgentState.outputFn (BoundedAgentState.erase (bcell c))) = false
    rw [erase_bcell]
    simp [AgentState.outputFn, isLeaderOutput,
      ZZZeroLeaderFinite.cell_zero_leader c]
  rw [hi0] at hi
  cases hi

theorem zeroFamily_run
    (C : BConfig) (hC : ZeroLeaderFamily C)
    (word : DetSchedule 2) :
    ZeroLeaderFamily
      (runLocalSchedule ring2
        (PPLLRepair.boundedTransition hψ1 1) C word) := by
  induction word generalizing C with
  | nil => exact hC
  | cons e rest ih =>
      simp only [runLocalSchedule]
      exact ih _ (zeroFamily_localStep C hC e)

theorem zeroConfig_no_schedule_to_isSafe
    (word : DetSchedule 2) :
    ¬ PopulationProtocol.IsSafe P ring2
      (runLocalSchedule ring2 P.transition zeroConfig word)
      isLeaderOutput := by
  have hfamily := zeroFamily_run zeroConfig zeroConfig_mem word
  have hfamily' :
      ZeroLeaderFamily
        (runLocalSchedule ring2 P.transition zeroConfig word) := by
    simpa only [P, ZZZeroLeaderClosed.P, PPLLRepair.boundedProtocol] using hfamily
  exact zeroFamily_not_isSafe _ hfamily'

theorem bounded_hproducer_false (L : Nat) :
    ¬ (∀ C : (PPLLRepair.boundedProtocol hψ1 1).Configuration 2,
      ¬ PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ1 1) ring2 C isLeaderOutput →
      ∃ w : DetSchedule 2,
        w.length ≤ L ∧
        PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ1 1) ring2
            (runLocalSchedule ring2
              (PPLLRepair.boundedProtocol hψ1 1).transition C w)
            isLeaderOutput) := by
  intro hproducer
  have hbad : ¬ PopulationProtocol.IsSafe P ring2 zeroConfig isLeaderOutput :=
    zeroFamily_not_isSafe zeroConfig zeroConfig_mem
  obtain ⟨w, _hL, hsafe⟩ := hproducer zeroConfig hbad
  exact zeroConfig_no_schedule_to_isSafe w hsafe

/-- Main coupled headline: the `n ≤ 2^ψ` gate holds, yet the bounded producer
premise still fails at `ψ = 1`, `κ = 1`, `n = 2`. -/
theorem coupling_and_bounded_hproducer_false (L : Nat) :
    2 ≤ 2 ^ (1 : Nat) ∧
      ¬ (∀ C : (PPLLRepair.boundedProtocol hψ1 1).Configuration 2,
        ¬ PopulationProtocol.IsSafe
            (PPLLRepair.boundedProtocol hψ1 1) ring2 C isLeaderOutput →
        ∃ w : DetSchedule 2,
          w.length ≤ L ∧
          PopulationProtocol.IsSafe
            (PPLLRepair.boundedProtocol hψ1 1) ring2
              (runLocalSchedule ring2
                (PPLLRepair.boundedProtocol hψ1 1).transition C w)
              isLeaderOutput) :=
  ⟨ring2_coupling, bounded_hproducer_false L⟩

#print axioms ring2_coupling
#print axioms zeroFamily_closed
#print axioms zeroFamily_run
#print axioms zeroConfig_no_schedule_to_isSafe
#print axioms bounded_hproducer_false
#print axioms coupling_and_bounded_hproducer_false

end ZZZeroLeaderCoupled
