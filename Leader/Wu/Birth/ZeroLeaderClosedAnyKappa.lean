import Leader.Wu.Protocol.BoundedProtocol
import Leader.Wu.Birth.ZeroLeaderTableAnyKappa
import Leader.Wu.Safety.CorrectedFormulation
import Init.Data.Fin.Lemmas
import Lean

set_option autoImplicit false
set_option Elab.async false

/-!
# Positive-κ bounded zero-leader obstruction

The raw four-state family certified at `ψ = 1, κ = 1` is unchanged for every
positive counter bound.  This file lifts that parameterized raw table through
the actual bounded protocol and carries it to arbitrary finite schedules on a
four-agent directed ring.
-/

namespace ZZZeroLeaderKappa

open PopulationProtocol
open ZZZeroLeaderFinite
open ZZZeroLeaderKappaPrefix
open PPLLResearchFormulation

def hψ1 : (0 : Nat) < 1 := by decide

def ring4 : DirectedRing 4 := ⟨by decide⟩

abbrev P (κ : Nat) : PopulationProtocol :=
  PPLLRepair.boundedProtocol hψ1 κ

/-! ## Parameterized bounded lift -/

private theorem cell_domain (κ : Nat) (c : Code4) :
    (cell c).inProtocolDomain κ := by
  cases c <;>
    change (0 : Nat) ≤ κ ∧ True ∧ True ∧ True ∧ True ∧ True <;>
    exact ⟨Nat.zero_le _, trivial, trivial, trivial, trivial, trivial⟩

def bcell (κ : Nat) (c : Code4) : BoundedAgentState 1 κ :=
  BoundedAgentState.ofDomain (cell c) (cell_domain κ c)

theorem erase_bcell (κ : Nat) (c : Code4) :
    BoundedAgentState.erase (bcell κ c) = cell c := by
  exact BoundedAgentState.erase_ofDomain (cell c) (cell_domain κ c)

private theorem bounded_erase_injective (κ : Nat) :
    Function.Injective (@BoundedAgentState.erase 1 κ) := by
  intro a b hab
  apply BoundedAgentState.eraseToDomain_bijective.1
  apply Subtype.ext
  exact hab

theorem bounded_pair_transition (κ : Nat) (hκ : 0 < κ)
    (l r : Code4) :
    PPLLRepair.boundedTransition hψ1 κ (bcell κ l) (bcell κ r) =
      (bcell κ (leftNext l), bcell κ (rightNext l)) := by
  apply Prod.ext
  · apply bounded_erase_injective κ
    have hb :=
      (PPLLRepair.erase_boundedTransition hψ1 κ
        (bcell κ l) (bcell κ r)).1
    rw [erase_bcell, erase_bcell,
      ZZZeroLeaderKappaPrefix.pair_transition_of_pos κ hκ] at hb
    exact hb.trans (erase_bcell κ _).symm
  · apply bounded_erase_injective κ
    have hb :=
      (PPLLRepair.erase_boundedTransition hψ1 κ
        (bcell κ l) (bcell κ r)).2
    rw [erase_bcell, erase_bcell,
      ZZZeroLeaderKappaPrefix.pair_transition_of_pos κ hκ] at hb
    exact hb.trans (erase_bcell κ _).symm

/-! ## Configuration-level closure -/

abbrev BConfig (κ : Nat) := Fin 4 → BoundedAgentState 1 κ

def ZeroLeaderFamily (κ : Nat) (C : BConfig κ) : Prop :=
  ∀ i : Fin 4, ∃ c : Code4, C i = bcell κ c

def zeroConfig (κ : Nat) : BConfig κ :=
  fun _ => bcell κ .A

theorem zeroConfig_mem (κ : Nat) :
    ZeroLeaderFamily κ (zeroConfig κ) := by
  intro i
  exact ⟨.A, rfl⟩

private theorem ring4_right_ne (e : Fin 4) :
    ring4.rightNeighbor e ≠ e := by
  have he : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by
    have hi := e.isLt
    omega
  rcases he with rfl | rfl | rfl | rfl <;> decide

private theorem zeroFamily_localStep
    (κ : Nat) (hκ : 0 < κ) (C : BConfig κ)
    (hC : ZeroLeaderFamily κ C) (e : Fin 4) :
    ZeroLeaderFamily κ
      (localStep ring4 (PPLLRepair.boundedTransition hψ1 κ) C e) := by
  let j := ring4.rightNeighbor e
  have hne : j ≠ e := ring4_right_ne e
  obtain ⟨lc, hl⟩ := hC e
  obtain ⟨rc, hr⟩ := hC j
  have hpair := bounded_pair_transition κ hκ lc rc
  intro i
  by_cases hie : i = e
  · subst i
    refine ⟨leftNext lc, ?_⟩
    have hleft :
        (localStep ring4 (PPLLRepair.boundedTransition hψ1 κ) C e) e =
          (PPLLRepair.boundedTransition hψ1 κ (C e) (C j)).1 := by
      simp [localStep, j]
    rw [hleft, hl, hr]
    exact congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      refine ⟨rightNext lc, ?_⟩
      have hright :
          (localStep ring4 (PPLLRepair.boundedTransition hψ1 κ) C e) j =
            (PPLLRepair.boundedTransition hψ1 κ (C e) (C j)).2 := by
        simp [localStep, j, hne]
      rw [hright, hl, hr]
      exact congrArg Prod.snd hpair
    · have hCi := hC i
      have hother :
          (localStep ring4 (PPLLRepair.boundedTransition hψ1 κ) C e) i = C i := by
        simp [localStep, j, hie, hij]
      rw [hother]
      exact hCi

theorem zeroFamily_closed (κ : Nat) (hκ : 0 < κ) :
    PopulationProtocol.ClosedPred (P κ) ring4 (ZeroLeaderFamily κ) := by
  intro C hC C' hstep
  rcases hstep with ⟨e, rfl⟩
  have heq :
      localStep ring4 (PPLLRepair.boundedTransition hψ1 κ) C e =
        (P κ).step ring4 C e := by
    rfl
  rw [← heq]
  exact zeroFamily_localStep κ hκ C hC e

theorem zeroFamily_reachable {κ : Nat} (hκ : 0 < κ)
    {C : (P κ).Configuration 4}
    (hC : ZeroLeaderFamily κ C)
    {D : (P κ).Configuration 4}
    (hr : PopulationProtocol.Reachable (P κ) ring4 C D) :
    ZeroLeaderFamily κ D :=
  PopulationProtocol.ClosedPred.reachable (zeroFamily_closed κ hκ) hC hr

/-! ## No leader and no safe schedule -/

theorem bcell_zero_leader (κ : Nat) (c : Code4) :
    (bcell κ c).leader = false := by
  change (BoundedAgentState.erase (bcell κ c)).leader = false
  rw [erase_bcell]
  exact ZZZeroLeaderFinite.cell_zero_leader c

theorem zeroFamily_leader_false (κ : Nat)
    (C : (P κ).Configuration 4) (hC : ZeroLeaderFamily κ C)
    (i : Fin 4) :
    (C i).leader = false := by
  obtain ⟨c, hc⟩ := hC i
  rw [hc]
  exact bcell_zero_leader κ c

theorem zeroFamily_not_isSafe (κ : Nat)
    (C : (P κ).Configuration 4) (hC : ZeroLeaderFamily κ C) :
    ¬ PopulationProtocol.IsSafe (P κ) ring4 C isLeaderOutput := by
  intro hsafe
  obtain ⟨i, hi, _⟩ := hsafe.1
  obtain ⟨c, hc⟩ := hC i
  have hi0 : isLeaderOutput ((P κ).output (C i)) = false := by
    rw [hc]
    change isLeaderOutput
      (AgentState.outputFn (BoundedAgentState.erase (bcell κ c))) = false
    rw [erase_bcell]
    simp [AgentState.outputFn, isLeaderOutput,
      ZZZeroLeaderFinite.cell_zero_leader c]
  rw [hi0] at hi
  cases hi

theorem zeroFamily_run (κ : Nat) (hκ : 0 < κ)
    (C : BConfig κ) (hC : ZeroLeaderFamily κ C)
    (word : DetSchedule 4) :
    ZeroLeaderFamily κ
      (runLocalSchedule ring4
        (PPLLRepair.boundedTransition hψ1 κ) C word) := by
  induction word generalizing C with
  | nil => exact hC
  | cons e rest ih =>
      simp only [runLocalSchedule]
      exact ih _ (zeroFamily_localStep κ hκ C hC e)

theorem zeroConfig_no_schedule_to_isSafe (κ : Nat) (hκ : 0 < κ)
    (word : DetSchedule 4) :
    ¬ PopulationProtocol.IsSafe (P κ) ring4
      (runLocalSchedule ring4 (P κ).transition (zeroConfig κ) word)
      isLeaderOutput := by
  have hfamily := zeroFamily_run κ hκ (zeroConfig κ)
    (zeroConfig_mem κ) word
  have hfamily' :
      ZeroLeaderFamily κ
        (runLocalSchedule ring4 (P κ).transition (zeroConfig κ) word) := by
    simpa only [P, PPLLRepair.boundedProtocol] using hfamily
  exact zeroFamily_not_isSafe κ _ hfamily'

/-! ## Explicit universal-κ producer refutation -/

theorem bounded_hproducer_false (κ : Nat) (hκ : 0 < κ) (L : Nat) :
    ¬ (∀ C : (PPLLRepair.boundedProtocol hψ1 κ).Configuration 4,
      ¬ PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ1 κ) ring4 C isLeaderOutput →
      ∃ w : DetSchedule 4,
        w.length ≤ L ∧
        PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ1 κ) ring4
            (runLocalSchedule ring4
              (PPLLRepair.boundedProtocol hψ1 κ).transition C w)
            isLeaderOutput) := by
  intro hproducer
  have hbad : ¬ PopulationProtocol.IsSafe
      (PPLLRepair.boundedProtocol hψ1 κ) ring4
      (zeroConfig κ) isLeaderOutput :=
    zeroFamily_not_isSafe κ (zeroConfig κ) (zeroConfig_mem κ)
  obtain ⟨w, _hL, hsafe⟩ := hproducer (zeroConfig κ) hbad
  exact zeroConfig_no_schedule_to_isSafe κ hκ w hsafe

theorem all_positive_kappa_bounded_hproducer_false :
    ∀ κ : Nat, 0 < κ → ∀ L : Nat, ¬ (∀ C :
      (PPLLRepair.boundedProtocol hψ1 κ).Configuration 4,
      ¬ PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ1 κ) ring4 C isLeaderOutput →
      ∃ w : DetSchedule 4,
        w.length ≤ L ∧
        PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ1 κ) ring4
            (runLocalSchedule ring4
              (PPLLRepair.boundedProtocol hψ1 κ).transition C w)
            isLeaderOutput) := by
  intro κ hκ L
  exact bounded_hproducer_false κ hκ L

#print axioms pPsi_cell
#print axioms waitSaturated_cell_eq_one
#print axioms beforeCheck_cell_eq_one
#print axioms full_cell_eq_one
#print axioms ZZZeroLeaderKappaPrefix.pair_transition_of_pos
#print axioms bounded_pair_transition
#print axioms zeroFamily_closed
#print axioms zeroFamily_reachable
#print axioms zeroFamily_run
#print axioms zeroFamily_not_isSafe
#print axioms zeroConfig_no_schedule_to_isSafe
#print axioms bounded_hproducer_false
#print axioms all_positive_kappa_bounded_hproducer_false

end ZZZeroLeaderKappa
