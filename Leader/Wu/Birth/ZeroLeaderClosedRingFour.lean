import Leader.Wu.Protocol.BoundedProtocol
import Leader.Wu.Birth.ZeroLeaderTablePsiOne
import Leader.Wu.Safety.CorrectedFormulation
import Init.Data.Fin.Lemmas
import Lean

set_option autoImplicit false
set_option Elab.async false

/-!
# ψ=1, κ=1: a bounded zero-leader closed class

`ZZZeroLeaderFinite` supplies the independently checked four-state raw local
table.  This file lifts that table through the actual bounded transition,
then proves configuration-level `ClosedPred`, schedule exclusion, and the
failure of the bounded-protocol producer premise.
-/

namespace ZZZeroLeaderClosed

open PopulationProtocol
open ZZZeroLeaderFinite
open PPLLResearchFormulation

def hψ1 : (0 : Nat) < 1 := by decide

def ring4 : DirectedRing 4 := ⟨by decide⟩

def P : PopulationProtocol := PPLLRepair.boundedProtocol hψ1 1

/-! ## The bounded lift -/

private theorem cell_domain (c : Code4) :
    (cell c).inProtocolDomain 1 := by
  cases c <;>
    change (0 : Nat) ≤ 1 ∧ True ∧ True ∧ True ∧ True ∧ True <;>
    exact ⟨Nat.zero_le _, trivial, trivial, trivial, trivial, trivial⟩

def bcell (c : Code4) : BoundedAgentState 1 1 :=
  BoundedAgentState.ofDomain (cell c) (cell_domain c)

theorem erase_bcell (c : Code4) :
    BoundedAgentState.erase (bcell c) = cell c := by
  exact BoundedAgentState.erase_ofDomain (cell c) (cell_domain c)

private theorem bounded_erase_injective :
    Function.Injective (@BoundedAgentState.erase 1 1) := by
  intro a b hab
  apply BoundedAgentState.eraseToDomain_bijective.1
  apply Subtype.ext
  exact hab

theorem bounded_pair_transition (l r : Code4) :
    PPLLRepair.boundedTransition hψ1 1 (bcell l) (bcell r) =
      (bcell (leftNext l), bcell (rightNext l)) := by
  apply Prod.ext
  · apply bounded_erase_injective
    have hb :=
      (PPLLRepair.erase_boundedTransition hψ1 1
        (bcell l) (bcell r)).1
    rw [erase_bcell, erase_bcell,
      ZZZeroLeaderFinite.pair_transition] at hb
    exact hb.trans (erase_bcell _).symm
  · apply bounded_erase_injective
    have hb :=
      (PPLLRepair.erase_boundedTransition hψ1 1
        (bcell l) (bcell r)).2
    rw [erase_bcell, erase_bcell,
      ZZZeroLeaderFinite.pair_transition] at hb
    exact hb.trans (erase_bcell _).symm

/-! ## Configuration family and exact closedness -/

abbrev BConfig := Fin 4 → BoundedAgentState 1 1

def ZeroLeaderFamily (C : BConfig) : Prop :=
  ∀ i : Fin 4, ∃ c : Code4, C i = bcell c

def zeroConfig : BConfig :=
  fun _ => bcell .A

theorem zeroConfig_mem : ZeroLeaderFamily zeroConfig := by
  intro i
  exact ⟨.A, rfl⟩

private theorem ring4_right_ne (e : Fin 4) :
    ring4.rightNeighbor e ≠ e := by
  have he : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by
    have hi := e.isLt
    omega
  rcases he with rfl | rfl | rfl | rfl <;> decide

private theorem zeroFamily_localStep
    (C : BConfig) (hC : ZeroLeaderFamily C) (e : Fin 4) :
    ZeroLeaderFamily
      (localStep ring4 (PPLLRepair.boundedTransition hψ1 1) C e) := by
  let j := ring4.rightNeighbor e
  have hne : j ≠ e := ring4_right_ne e
  obtain ⟨lc, hl⟩ := hC e
  obtain ⟨rc, hr⟩ := hC j
  have hpair := bounded_pair_transition lc rc
  intro i
  by_cases hie : i = e
  · subst i
    refine ⟨leftNext lc, ?_⟩
    have hleft :
        (localStep ring4 (PPLLRepair.boundedTransition hψ1 1) C e) e =
          (PPLLRepair.boundedTransition hψ1 1 (C e) (C j)).1 := by
      simp [localStep, j]
    rw [hleft, hl, hr]
    exact congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      refine ⟨rightNext lc, ?_⟩
      have hright :
          (localStep ring4 (PPLLRepair.boundedTransition hψ1 1) C e) j =
            (PPLLRepair.boundedTransition hψ1 1 (C e) (C j)).2 := by
        simp [localStep, j, hne]
      rw [hright, hl, hr]
      exact congrArg Prod.snd hpair
    · have hCi := hC i
      have hother :
          (localStep ring4 (PPLLRepair.boundedTransition hψ1 1) C e) i = C i := by
        simp [localStep, j, hie, hij]
      simpa only [hother] using hCi

theorem zeroFamily_closed :
    PopulationProtocol.ClosedPred P ring4 ZeroLeaderFamily := by
  intro C hC C' hstep
  rcases hstep with ⟨e, rfl⟩
  have heq :
      localStep ring4 (PPLLRepair.boundedTransition hψ1 1) C e =
        P.step ring4 C e := by
    rfl
  rw [← heq]
  exact zeroFamily_localStep C hC e

theorem zeroFamily_reachable {C : P.Configuration 4}
    (hC : ZeroLeaderFamily C)
    {D : P.Configuration 4}
    (hr : PopulationProtocol.Reachable P ring4 C D) :
    ZeroLeaderFamily D :=
  PopulationProtocol.ClosedPred.reachable zeroFamily_closed hC hr

/-! ## Zero output and schedule exclusion -/

theorem bcell_zero_leader (c : Code4) :
    (bcell c).leader = false := by
  change (BoundedAgentState.erase (bcell c)).leader = false
  rw [erase_bcell]
  exact ZZZeroLeaderFinite.cell_zero_leader c

theorem zeroFamily_leader_false
    (C : P.Configuration 4) (hC : ZeroLeaderFamily C) (i : Fin 4) :
    (C i).leader = false := by
  obtain ⟨c, hc⟩ := hC i
  rw [hc]
  exact bcell_zero_leader c

theorem zeroFamily_not_isSafe
    (C : P.Configuration 4) (hC : ZeroLeaderFamily C) :
    ¬ PopulationProtocol.IsSafe P ring4 C isLeaderOutput := by
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
    (word : DetSchedule 4) :
    ZeroLeaderFamily
      (runLocalSchedule ring4
        (PPLLRepair.boundedTransition hψ1 1) C word) := by
  induction word generalizing C with
  | nil => exact hC
  | cons e rest ih =>
      simp only [runLocalSchedule]
      exact ih _ (zeroFamily_localStep C hC e)

theorem zeroFamily_no_schedule_to_isSafe
    (C : P.Configuration 4) (hC : ZeroLeaderFamily C)
    (word : DetSchedule 4) :
    ¬ PopulationProtocol.IsSafe P ring4
      (runLocalSchedule ring4 P.transition C word)
      isLeaderOutput := by
  have hfamily := zeroFamily_run C hC word
  have hfamily' :
      ZeroLeaderFamily
        (runLocalSchedule ring4 P.transition C word) := by
    simpa only [P, PPLLRepair.boundedProtocol] using hfamily
  exact zeroFamily_not_isSafe _ hfamily'

theorem zeroConfig_no_schedule_to_isSafe
    (word : DetSchedule 4) :
    ¬ PopulationProtocol.IsSafe P ring4
      (runLocalSchedule ring4 P.transition zeroConfig word)
      isLeaderOutput := by
  exact zeroFamily_no_schedule_to_isSafe zeroConfig zeroConfig_mem word

/-! ## Explicit failure of the bounded-protocol producer premise -/

theorem bounded_hproducer_false (L : Nat) :
    ¬ (∀ C : (PPLLRepair.boundedProtocol hψ1 1).Configuration 4,
      ¬ PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ1 1) ring4 C isLeaderOutput →
      ∃ w : DetSchedule 4,
        w.length ≤ L ∧
        PopulationProtocol.IsSafe
          (PPLLRepair.boundedProtocol hψ1 1) ring4
            (runLocalSchedule ring4
              (PPLLRepair.boundedProtocol hψ1 1).transition C w)
            isLeaderOutput) := by
  intro hproducer
  have hbad : ¬ PopulationProtocol.IsSafe P ring4 zeroConfig isLeaderOutput :=
    zeroFamily_not_isSafe zeroConfig zeroConfig_mem
  obtain ⟨w, _hL, hsafe⟩ := hproducer zeroConfig hbad
  exact zeroConfig_no_schedule_to_isSafe w hsafe

#print axioms bounded_pair_transition
#print axioms zeroFamily_closed
#print axioms zeroFamily_reachable
#print axioms zeroFamily_run
#print axioms zeroFamily_no_schedule_to_isSafe
#print axioms zeroConfig_no_schedule_to_isSafe
#print axioms bounded_hproducer_false

end ZZZeroLeaderClosed
