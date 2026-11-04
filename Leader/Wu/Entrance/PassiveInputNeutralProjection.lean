import Leader.Wu.Entrance.PassiveOuterNeutralFrame
import Leader.Wu.Splice.RiskLeafIdentification
import Leader.Wu.Splice.HostRightLabelLaw
import Leader.Core.Basic

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost B9FullCarrierRows B9SpliceTableHost
open B9RiskRefinementPhys3 B9HostRightLabelLaw

variable {n ψ κ τ : Nat}

section OpaqueConcretePort

attribute [local irreducible]
  B9FullCarrierRows.fullRowPort hostR2C

/-- The already-proved bare-R1 physical projection package. -/
private theorem q13892_r1_projection_package
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) :
    B9RiskRefinementPhys3.SpliceProjectionFacts
        (B9Host.r1Host (kappa := κ) (tau := τ) hψ h2) ∧
      B9HostRightLabelLaw.RightLabelLaw hψ
        (B9Host.r1Host (kappa := κ) (tau := τ) hψ h2) := by
  exact ⟨B9RiskRefinementPhys3.r1Host_spliceProjectionFacts hψ h2,
    B9HostRightLabelLaw.r1Host_right_label_law hψ h2⟩

/-- Phys4 is a physical projection route only; it does not recover the
operational action tag. -/
private theorem q13892_phys4_projection_route
    (h : B9RiskRefinementPhys4.R1Row10gLeafRiskViewCompletionClause) :
    B9RiskRefinementPhys3.R1ConcreteRowB9PhysicalProjectionObligation := by
  exact B9RiskRefinementPhys4.r1Host_concreteRowB9PhysicalProjection h

private theorem q13892_rightNeighbor_leftNeighbor
    (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  show ((i.val + n - 1) % n + 1) % n = i.val
  have hn := ring.hn
  have hi := i.isLt
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · have h1 : (i.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, show n - 1 + 1 = n by omega, Nat.mod_self, h0]
  · have h1 : (i.val + n - 1) % n = i.val - 1 := by
      rw [show i.val + n - 1 = (i.val - 1) + n by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, show i.val - 1 + 1 = i.val by omega]
    exact Nat.mod_eq_of_lt hi

/-- Leaderlessness kills the only top-level B9 delete HOST arm, independently
of the prepared-deletion bits inside the selected host. -/
private theorem q13892_no_ldc
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hLead : outputFinal l = false) :
    ¬ B9SpliceTableHost.ldc
      (B9FullCarrierHost.shadowHostAt
        (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
        (hostR2C (κ := κ) (τ := τ) hψ h2) l.phys r.phys)
      (B9FullCarrierHost.toOld carrierLaws l).carrier
      (B9FullCarrierHost.toOld carrierLaws r).carrier := by
  intro h
  have hl := h.1
  change outputFinal l = true at hl
  rw [hLead] at hl
  cases hl

/-- Sole residual: the finite controller selector after the physical delete
route has been excluded.  This is strictly smaller than input-neutrality:
it is pair-local and contains no ring, trace, or post-state assertion. -/
def ConcretePortHostSelectorResidual
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) : Prop :=
  ∀ (l r : Cell ψ κ τ),
    (¬ B9SpliceTableHost.ldc
      (B9FullCarrierHost.shadowHostAt
        (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
        (hostR2C (κ := κ) (τ := τ) hψ h2) l.phys r.phys)
      (B9FullCarrierHost.toOld carrierLaws l).carrier
      (B9FullCarrierHost.toOld carrierLaws r).carrier) →
    (concretePortLocal (κ := κ) (τ := τ) hψ h2).action l r = .host →
      l.spliceRole ≠ .predecessorArmed ∧
      l.spliceRole ≠ .victimArmed ∧
      r.spliceRole ≠ .front ∧
      (l.spliceRole = .none →
        l.repairPending = false ∧ l.acquireTicket = false)

private theorem q13892_selector_facts
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (hS : ConcretePortHostSelectorResidual
      (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ) (hLead : outputFinal l = false)
    (ha : (concretePortLocal (κ := κ) (τ := τ) hψ h2).action l r = .host) :
    l.spliceRole ≠ .predecessorArmed ∧
    l.spliceRole ≠ .victimArmed ∧
    r.spliceRole ≠ .front ∧
    (l.spliceRole = .none →
      l.repairPending = false ∧ l.acquireTicket = false) := by
  exact hS l r (q13892_no_ldc hψ h2 l r hLead) ha


/-- The global input-neutral theorem now uses only the pair-local selector
residual.  There is no unfolding of the concrete port. -/
theorem concreteB7PassiveInputOuterNeutral_of_selector
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := κ) (τ := τ) hψ h2) :
    ConcreteB7PassiveInputOuterNeutralObligation
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C hA hL i
  have hHost : ∀ e : Fin n,
      (concretePortLocal (κ := κ) (τ := τ) hψ h2).action
        (C e) (C (ring.rightNeighbor e)) = .host := by
    intro e
    exact (hA.2.2.2 e).2.1
  have hOut := q13892_selector_facts hψ h2 hS
    (C i) (C (ring.rightNeighbor i)) (hL i) (hHost i)
  have hNP : (C i).spliceRole ≠ .predecessorArmed := hOut.1
  have hNV : (C i).spliceRole ≠ .victimArmed := hOut.2.1
  let p := ring.leftNeighbor i
  have hp : ring.rightNeighbor p = i :=
    q13892_rightNeighbor_leftNeighbor ring i
  have hIn :
      (concretePortLocal (κ := κ) (τ := τ) hψ h2).action
        (C p) (C i) = .host := by
    have h := hHost p
    rw [hp] at h
    exact h
  have hInFacts := q13892_selector_facts hψ h2 hS
    (C p) (C i) (hL p) hIn
  have hNF : (C i).spliceRole ≠ .front := hInFacts.2.2.1
  have hRole : (C i).spliceRole = .none := by
    cases hr : (C i).spliceRole with
    | none => rfl
    | predecessorArmed => exact (hNP hr).elim
    | front => exact (hNF hr).elim
    | victimArmed => exact (hNV hr).elim
  have hRest := hOut.2.2.2 hRole
  exact ⟨hRole, hRest.1, hRest.2⟩

end OpaqueConcretePort

end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
