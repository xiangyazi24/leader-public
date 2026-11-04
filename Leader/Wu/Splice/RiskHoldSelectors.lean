import Leader.Wu.Splice.RecoveryGateResiduals
import Leader.Wu.Splice.RiskHostResidual

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace B9RiskRefinementPhys7

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open Q11593SpliceControllerDesign
open B9Host B9SpliceTableHost
open B9SpliceControllerR1Table B9SpliceControllerR1TableV6
open B9OrphanToFence B9SpliceTableV10e

variable {n psi kappa tau : Nat}

/-- The common prefix of the two physical-hold selectors in the stuttering
arm of `row10gH`. -/
def Row10gHoldPrefix
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) : Prop :=
  row10dgH host hpsi l r = (l, r) ∧
  ¬ (role l.carrier = .predecessorArmed ∧
      l.carrier.repairPending = true) ∧
  ¬ VictimRightScrubGuardV6 r ∧
  ¬ FrontRightScrubGuardV6 r ∧
  ¬ MalformedRightPendingGuardV6 r

/-- Exact unfenced `physicalHoldH` selector. -/
def Row10gPlainHoldSelected
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) : Prop :=
  Row10gHoldPrefix host hpsi l r ∧
    role r.carrier ≠ .predecessorArmed

/-- Exact fenced `physicalHoldH` selector. -/
def Row10gFencedHoldSelected
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) : Prop :=
  Row10gHoldPrefix host hpsi l r ∧
    role r.carrier = .predecessorArmed ∧
    r.carrier.repairPending = false

theorem row10gH_eq_plainHold
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau)
    (h : Row10gPlainHoldSelected host hpsi l r) :
    row10gH host hpsi l r = physicalHoldH host l r := by
  rcases h with ⟨⟨hq, hL, hV, hF, hM⟩, hR⟩
  unfold row10gH
  dsimp only
  rw [if_pos hq, if_neg hL, if_neg hV, if_neg hF, if_neg hM,
    if_neg hR]

theorem row10gH_eq_fencedHold
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau)
    (h : Row10gFencedHoldSelected host hpsi l r) :
    row10gH host hpsi l r =
      ((physicalHoldH host l r).1, fenceV6 (physicalHoldH host l r).2) := by
  rcases h with ⟨⟨hq, hL, hV, hF, hM⟩, hR, hP⟩
  unfold row10gH
  dsimp only
  rw [if_pos hq, if_neg hL, if_neg hV, if_neg hF, if_neg hM,
    if_pos hR]
  simp [hP]

/-- Physical meaning: a plain hold is exactly the selected host physical row. -/
theorem row10g_plainHold_physRow
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau)
    (h : Row10gPlainHoldSelected host hpsi l r) :
    PhysRow host l r (row10gH host hpsi l r) := by
  rw [row10gH_eq_plainHold host hpsi l r h]
  exact phys_hold host l r

/-- Fencing changes only controller/ticket data; the physical pair is still
exactly the selected host row. -/
theorem row10g_fencedHold_physRow
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau)
    (h : Row10gFencedHoldSelected host hpsi l r) :
    PhysRow host l r (row10gH host hpsi l r) := by
  rw [row10gH_eq_fencedHold host hpsi l r h]
  exact phys_fence host l r

abbrev C2Config (n psi : Nat) :=
  FinalCandidateR2C.Config n psi psi (16 * psi)

abbrev c2OldAt (C : C2Config n psi) (i : Fin n) :
    B9SpliceTableHost.Cell psi psi (16 * psi) :=
  FinalCandidateR2C.FinalCandidateR2C.oldCell (C i)

/-- C2 leaderlessness already supplies both follower hypotheses needed by the
old HOST-domain implication. -/
theorem c2Passive_old_followers
    (C : C2Config n psi)
    (hC : B9RecoveryGate.C2PassiveLeaderless C)
    (i j : Fin n) :
    leader (base (c2OldAt C i)) = false ∧
    leader (base (c2OldAt C j)) = false := by
  have hi := hC.2.2 i
  have hj := hC.2.2 j
  constructor
  · change FinalCandidateR2C.FinalCandidateR2C.outputFinal (C i) = false
    exact hi
  · change FinalCandidateR2C.FinalCandidateR2C.outputFinal (C j) = false
    exact hj

theorem c2Passive_not_ldc
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : C2Config n psi)
    (hC : B9RecoveryGate.C2PassiveLeaderless C) (e : Fin n) :
    let host := B9RecoveryGateResiduals.C2R1Host hpsi h2
    let l := c2OldAt C e
    let r := c2OldAt C (ring.rightNeighbor e)
    ¬ ldc host l.carrier r.carrier := by
  dsimp only
  intro hd
  have hf := c2Passive_old_followers C hC e (ring.rightNeighbor e)
  have hleft :
      leader (c2OldAt C e).carrier.splice.base = false := by
    simpa only [B9SpliceTableHost.base] using hf.1
  have ht := hd.1
  rw [hleft] at ht
  cases ht

theorem c2Passive_rowB9_eq_row10g
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : C2Config n psi)
    (hC : B9RecoveryGate.C2PassiveLeaderless C) (e : Fin n) :
    let host := B9RecoveryGateResiduals.C2R1Host hpsi h2
    let l := c2OldAt C e
    let r := c2OldAt C (ring.rightNeighbor e)
    rowB9 host hpsi l r = row10gH host hpsi l r := by
  dsimp only
  have hn := c2Passive_not_ldc hpsi h2 ring C hC e
  dsimp only at hn
  simp [rowB9, hn]

def C2HoldSelected
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : C2Config n psi) (e : Fin n) : Prop :=
  let host := B9RecoveryGateResiduals.C2R1Host hpsi h2
  let l := c2OldAt C e
  let r := c2OldAt C (ring.rightNeighbor e)
  Row10gPlainHoldSelected host hpsi l r ∨
    Row10gFencedHoldSelected host hpsi l r

/-- Minimal *C2-local* missing datum.  Followers are omitted because
`C2PassiveLeaderless` proves them; only the prepared-deletion domain remains. -/
def PhysHoldDomainClause
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : C2Config n psi,
    B9RecoveryGate.C2PassiveLeaderless C →
    ∀ e : Fin n, C2HoldSelected hpsi h2 ring C e →
      BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen hpsi
        (base (c2OldAt C e))
        (base (c2OldAt C (ring.rightNeighbor e)))

def C2HoldDomainResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : C2Config n psi,
    B9RecoveryGate.C2PassiveLeaderless C →
    ∀ e : Fin n, C2HoldSelected hpsi h2 ring C e →
      leader (base (c2OldAt C e)) = false ∧
      leader (base (c2OldAt C (ring.rightNeighbor e))) = false ∧
      BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen hpsi
        (base (c2OldAt C e))
        (base (c2OldAt C (ring.rightNeighbor e)))

theorem c2HoldDomainResidual_of_physHoldDomainClause
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hHold : PhysHoldDomainClause hpsi h2 ring) :
    C2HoldDomainResidual hpsi h2 ring := by
  intro C hC e hs
  have hf := c2Passive_old_followers C hC e (ring.rightNeighbor e)
  exact ⟨hf.1, hf.2, hHold C hC e hs⟩

/-- Source-level interface check: the current gate still stores the old global
completion before its C2-passive mass binder.  Therefore the local clause above
cannot inhabit the current second field without first localizing/retiring it. -/
theorem currentC2Gate_requires_global_completion
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hGate : B9RecoveryGate.C2RecoveryGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring) :
    B9RiskRefinementPhys4.R1Row10gLeafRiskViewCompletionClause :=
  hGate.2.1

end B9RiskRefinementPhys7
