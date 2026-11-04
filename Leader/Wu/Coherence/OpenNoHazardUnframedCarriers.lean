import Leader.Wu.Coherence.ReachableOpenNoHazardServed
import Leader.Wu.Coherence.ReachableAdjacentRootEndpoint

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31OpenNoHazardMainClear

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31OpenNoHazard
open R2CoherenceV31ReachableOpenNoHazard5
open R2CoherenceV31ReachableAdjacentRoot2

variable {n ψ κ τ : Nat}

/-- Exactly the six `MainClear` fields which `pairHazardV3` does not frame. -/
def MainClearUnframedR2V31 (u : R2.Cell ψ κ τ) : Prop :=
  u.base.core.core.state = .none ∧
    u.base.core.core.path2 = none ∧
    u.base.core.core.path4 = none ∧
    u.base.core.core.path5 = none ∧
    u.base.core.core.p = false ∧
    u.base.core.core.p_carry = false

/-- Residual left by the row census.  `pairHazardV3 = false` supplies the
main-path frame; this asks only that the six unframed MainClear carriers stay
empty at an endpoint which was MainClear before the proposal. -/
def OpenNoHazardMainClearUnframedCarrierGuardV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) : Prop :=
  ∀ (l r : Cell ψ κ τ),
    pairHazardV3 l.phys r.phys
        (proposalV3 hψ (by decide : 0 < 2) h2 l r).1
        (proposalV3 hψ (by decide : 0 < 2) h2 l r).2 = false →
      (MainClearV3 l →
          MainClearUnframedR2V31
            (proposalV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
      (MainClearV3 r →
          MainClearUnframedR2V31
            (proposalV3 hψ (by decide : 0 < 2) h2 l r).2)

private theorem branch_openNoHazard_conditions_mc
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open ∧
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = false) := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem pairHazardV3_false_paths_mc
    (l r ql qr : R2.Cell ψ κ τ)
    (h : pairHazardV3 l r ql qr = false) :
    l.base.core.core.path = ql.base.core.core.path ∧
      r.base.core.core.path = qr.base.core.core.path := by
  have hp : pairPathChangesV3 l r ql qr = false := by
    cases hh : pairPathChangesV3 l r ql qr with
    | false => exact rfl
    | true => simp [pairHazardV3, hh] at h
  simpa [pairPathChangesV3, pathChangedV3] using hp

private theorem mainClear_path_mc
    (u : Cell ψ κ τ) (h : MainClearV3 u) :
    u.phys.base.core.core.path = .bot := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at h
  simpa [eraseCellV3, R2Coherence.raw] using h.2.1

private theorem mainClear_install_mc
    (u : Cell ψ κ τ) (q : R2.Cell ψ κ τ)
    (hp : q.base.core.core.path = .bot)
    (hu : MainClearUnframedR2V31 q) : MainClearV3 (install u q) := by
  unfold MainClearUnframedR2V31 at hu
  rcases hu with ⟨hs, h2c, h4, h5, hpc, hpcc⟩
  unfold MainClearV3 R2CoherenceBranches.MainClear
  have h :
      q.base.core.core.state = .none ∧
      q.base.core.core.path = .bot ∧
      q.base.core.core.path2 = none ∧
      q.base.core.core.path4 = none ∧
      q.base.core.core.path5 = none ∧
      q.base.core.core.p = false ∧
      q.base.core.core.p_carry = false :=
    ⟨hs, hp, h2c, h4, h5, hpc, hpcc⟩
  simpa [eraseCellV3, install, R2Coherence.raw] using h


theorem proposalV3_mainClear_of_unframedCarrierGuard
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (hG : OpenNoHazardMainClearUnframedCarrierGuardV31
      (κ := κ) (τ := τ) hψ h2)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    (MainClearV3 l → MainClearV3
      (install l (proposalV3 hψ (by decide : 0 < 2) h2 l r).1)) ∧
    (MainClearV3 r → MainClearV3
      (install r (proposalV3 hψ (by decide : 0 < 2) h2 l r).2)) := by
  let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
  rcases branch_openNoHazard_conditions_mc hψ h2 l r hb with
    ⟨_, _, _, _, hHaz0⟩
  have hHaz : pairHazardV3 l.phys r.phys q.1 q.2 = false := by
    simpa [q] using hHaz0
  have hPaths := pairHazardV3_false_paths_mc l.phys r.phys q.1 q.2 hHaz
  have hGuard := hG l r (by simpa [q] using hHaz)
  constructor
  · intro hm
    change MainClearV3 (install l q.1)
    have hu := hGuard.1 hm
    change MainClearUnframedR2V31 q.1 at hu
    exact mainClear_install_mc l q.1
      (hPaths.1.symm.trans (mainClear_path_mc l hm)) hu
  · intro hm
    change MainClearV3 (install r q.2)
    have hu := hGuard.2 hm
    change MainClearUnframedR2V31 q.2 at hu
    exact mainClear_install_mc r q.2
      (hPaths.2.symm.trans (mainClear_path_mc r hm)) hu

private theorem row_openNoHazard_eq_install_mc
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
    rowV3 hψ (by decide : 0 < 2) h2 l r =
      (install l q.1, install r q.2) := by
  rcases branch_openNoHazard_conditions_mc hψ h2 l r hb with
    ⟨hln, hrn, hlo, hro, hHaz⟩
  let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
  change rowV3 hψ (by decide : 0 < 2) h2 l r =
    (install l q.1, install r q.2)
  simp [rowV3, ordinaryStageV3, openStageV3,
    hln, hrn, hlo, hro, q, hHaz]

private theorem step_left_eq_install_mc
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard) :
    let q := proposalV3 hψ (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))
    stepV3 hψ h2 ring C e e = install (C e) q.1 := by
  let q := proposalV3 hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  have hrow : rowV3 hψ (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e)) =
      (install (C e) q.1, install (C (ring.rightNeighbor e)) q.2) := by
    simpa [q] using row_openNoHazard_eq_install_mc hψ h2
      (C e) (C (ring.rightNeighbor e)) hb
  simpa [stepV3, protocolV3, PopulationProtocol.step] using
    congrArg Prod.fst hrow

private theorem step_right_eq_install_mc
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard) :
    let q := proposalV3 hψ (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      install (C (ring.rightNeighbor e)) q.2 := by
  let q := proposalV3 hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  have hrow : rowV3 hψ (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e)) =
      (install (C e) q.1, install (C (ring.rightNeighbor e)) q.2) := by
    simpa [q] using row_openNoHazard_eq_install_mc hψ h2
      (C e) (C (ring.rightNeighbor e)) hb
  simpa [stepV3, protocolV3, PopulationProtocol.step, hne] using
    congrArg Prod.snd hrow


theorem servedMainClear_openNoHazard_of_unframedCarrierGuard
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hG : OpenNoHazardMainClearUnframedCarrierGuardV31
      (κ := κ) (τ := τ) hψ h2)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
      .openNoHazard)
    (hServed : p = e ∨ p = ring.rightNeighbor e)
    (hm : MainClearV3 (C p)) :
    MainClearV3 (stepV3 hψ h2 ring C e p) := by
  let q := proposalV3 hψ (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
  have hPair :
      (MainClearV3 (C e) → MainClearV3 (install (C e) q.1)) ∧
      (MainClearV3 (C (ring.rightNeighbor e)) →
        MainClearV3 (install (C (ring.rightNeighbor e)) q.2)) := by
    simpa [q] using proposalV3_mainClear_of_unframedCarrierGuard
      hψ h2 hG (C e) (C (ring.rightNeighbor e)) hb
  rcases hServed with hpe | hpr
  · subst p
    have heq : stepV3 hψ h2 ring C e e = install (C e) q.1 := by
      simpa [q] using step_left_eq_install_mc hψ h2 ring C e hb
    rw [heq]
    exact hPair.1 hm
  · subst p
    by_cases hsame : ring.rightNeighbor e = e
    · rw [hsame] at hm ⊢
      have heq : stepV3 hψ h2 ring C e e = install (C e) q.1 := by
        simpa [q] using step_left_eq_install_mc hψ h2 ring C e hb
      rw [heq]
      exact hPair.1 hm
    · have heq : stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
          install (C (ring.rightNeighbor e)) q.2 := by
        simpa [q] using step_right_eq_install_mc hψ h2 ring C e hsame hb
      rw [heq]
      exact hPair.2 hm

theorem openNoHazardServedMainClearPreservation_of_unframedCarrierGuard
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hG : OpenNoHazardMainClearUnframedCarrierGuardV31
      (κ := κ) (τ := τ) hψ h2) :
    OpenNoHazardServedMainClearPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e p _hGeom _hTrace _hPlus hb hServed hm
  exact servedMainClear_openNoHazard_of_unframedCarrierGuard
    hψ h2 ring hG C e p hb hServed hm

theorem openNoHazardAdjacentRootEndpointMainClearPsi2_of_unframedCarrierGuard
    (ring : DirectedRing n)
    (hG : OpenNoHazardMainClearUnframedCarrierGuardV31
      (κ := κ) (τ := τ)
      (by decide : 0 < 2) (by decide : 2 ≤ 2)) :
    OpenNoHazardAdjacentRootEndpointMainClearPsi2V31
      (kappa := κ) (tau := τ) ring := by
  intro C e p hm _hRoot _hNextRoot hb hServed
  exact servedMainClear_openNoHazard_of_unframedCarrierGuard
    (by decide : 0 < 2) (by decide : 2 ≤ 2) ring hG
    C e p hb hServed hm

end R2CoherenceV31OpenNoHazardMainClear
