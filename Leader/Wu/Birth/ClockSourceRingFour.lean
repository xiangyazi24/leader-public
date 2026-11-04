import Leader.Wu.Birth.ShortDoneTerminalOrdinaryLabel
import Leader.Wu.Birth.ClockSourceFromPassiveCyclic
import Leader.Wu.Birth.LabelGeometryStabilization
import Leader.Wu.Scheduler.FixedSpanRenewalPayload

set_option autoImplicit false

namespace BirthPhaseClockSourceR1

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open LDSinkBoundedKernel
open BirthWaitPassive
open BirthShortDoneTerminalPassiveR1
  BirthShortDoneTerminalPassiveR4
  BirthShortDoneTerminalPassiveLocal3Rotation
open BirthShortDoneTerminalOrdinaryLabelR1
open PPLLWallSweepRepair PPLLWallSweepFinite

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthShortDoneTerminalPassiveR4.FullConfig n psi kappa tau

/-- The B1 local source predicate, copied from the statement-only target
without importing that unfinished file. -/
def LocalClockSource
    (hpsi : 0 < psi) (hn : 4 <= n)
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Prop :=
  exists a : Fin n,
    BirthShortDoneTerminalPassiveLocal3Rotation.LocalLine3At
      hpsi hn ring a C

/-- Literal width-two execution of the exact current terminal consumer. -/
def currentRun
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (w : List (Fin n)) : FC n psi kappa tau :=
  LDSinkBoundedKernel.run
    (BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring) C w

/-- The exact unconditional physical-core frame at the current P-prime cut. -/
theorem current_pprime_core_frame
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    let q := authorizedPPsiLeaderResetProbeWall hpsi l r
    (q.1.core, q.2.core) =
      pPsiLeaderResetProbeWall hpsi l.core r.core :=
  PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall_core hpsi l r

/-- On a leaderless pair with no left reset command, the current reset-aware
P-prime cut really is literal Algorithm-2 `pPsi` on its raw cores. -/
theorem current_pprime_eq_literal_pPsi_of_leaderless_no_reset
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hreset : l.core.reset_cmd = false) :
    let q := authorizedPPsiLeaderResetProbeWall hpsi l r
    (q.1.core, q.2.core) = pPsi hpsi l.core r.core := by
  change
    ((authorizedPPsiLeaderResetProbeWall hpsi l r).1.core,
      (authorizedPPsiLeaderResetProbeWall hpsi l r).2.core) =
        pPsi hpsi l.core r.core
  calc
    _ = pPsiLeaderResetProbeWall hpsi l.core r.core :=
      PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall_core hpsi l r
    _ = pPsiLeaderProbeWall hpsi l.core r.core :=
      PPLLWallSweepRepair.pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_no_reset
        hpsi l.core r.core hreset
    _ = pPsi hpsi l.core r.core :=
      PPLLWallSweepRepair.pPsiLeaderProbeWall_eq_pPsi_of_no_leaders
        hpsi l.core r.core hl hr

variable {width : Nat}

/-- Existing exact-current-host one-edge ruler producer, restated at the B1
interface.  The only extra gate is the real prepared ordinary-branch premise. -/
theorem current_edge_label_or_physical_birth
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (hn : 1 < n) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n)
    (hzero : BirthShortDoneTerminalFirstHit.Leaderless C)
    (hopen : PreparedOrdinaryOpen hpsi (C e) (C (ring.rightNeighbor e))) :
    let D := BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring C e
    (exists i, (D i).core.core.leader = true) \/
      (BirthShortDoneTerminalFirstHit.Leaderless D ∧
        (D e).core.core.label = (C e).core.core.label ∧
        (D (ring.rightNeighbor e)).core.core.label =
          ⟨((C e).core.core.label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩) := by
  exact
    BirthShortDoneTerminalOrdinaryLabelR1.ordinary_edge_label_or_physical_birth
      hpsi hwidth hle hn ring C e hzero hopen

private theorem hpsi2 : 0 < (2 : Nat) := by decide
private theorem htwo2 : 2 <= (2 : Nat) := by decide
private theorem hn4 : 4 <= (4 : Nat) := by decide

private theorem fin2_val_zero_or_one (x : Fin 2) :
    x.val = 0 \/ x.val = 1 := by
  omega

/-- Smallest nontrivial post-sanitation closure: on four sites at psi=2,
global passivity and cyclic labels automatically contain a zero-label anchor,
so the existing Local3 adapter produces a clock source immediately. -/
theorem n4_psi2_passive_cyclic_has_localClockSource
    (kappa tau : Nat) (ring : DirectedRing 4)
    (C : FC 4 2 kappa tau)
    (hpass : HostPassive C)
    (hcyc : HostCyclic hpsi2 ring C) :
    LocalClockSource hpsi2 hn4 ring C := by
  let root : Fin 4 := 0
  rcases fin2_val_zero_or_one (raw (C root)).label with hz | ho
  · exact
      ⟨root,
        BirthPhaseClockSourceAudit.localLine3At_of_hostPassive_hostCyclic_zero
          hpsi2 htwo2 hn4 ring C hpass hcyc root hz⟩
  · let anchor : Fin 4 := ring.rightNeighbor root
    have hnext := congrArg Fin.val (hcyc root)
    change
      (raw (C (ring.rightNeighbor root))).label.val =
        ((raw (C root)).label.val + 1) % 2 at hnext
    have hzAnchor : (raw (C anchor)).label.val = 0 := by
      change (raw (C (ring.rightNeighbor root))).label.val = 0
      calc
        (raw (C (ring.rightNeighbor root))).label.val =
            ((raw (C root)).label.val + 1) % 2 := hnext
        _ = (1 + 1) % 2 := by rw [ho]
        _ = 0 := by decide
    exact
      ⟨anchor,
        BirthPhaseClockSourceAudit.localLine3At_of_hostPassive_hostCyclic_zero
          hpsi2 htwo2 hn4 ring C hpass hcyc anchor hzAnchor⟩

/-- The target existential is therefore immediate, with the empty current-host
word, once the n=4, psi=2 sanitation/ruler entrance has already been reached. -/
theorem n4_psi2_passive_cyclic_reaches_localClockSource_or_leader
    (kappa tau : Nat) (ring : DirectedRing 4)
    (C : FC 4 2 kappa tau)
    (_hzero : BirthShortDoneTerminalFirstHit.Leaderless C)
    (hpass : HostPassive C)
    (hcyc : HostCyclic hpsi2 ring C) :
    exists w : List (Fin 4),
      let D := currentRun hpsi2 htwo2 ring C w
      (exists i : Fin 4, (D i).core.core.leader = true) \/
        LocalClockSource hpsi2 hn4 ring D := by
  refine ⟨[], ?_⟩
  have hs := n4_psi2_passive_cyclic_has_localClockSource
    kappa tau ring C hpass hcyc
  simpa only [currentRun, LDSinkBoundedKernel.run] using
    (show (exists i : Fin 4, (C i).core.core.leader = true) \/
        LocalClockSource hpsi2 hn4 ring C from Or.inr hs)

/-- Copy of the target numerator, kept here only to expose the quantifier bug
in the proposed mass statement without importing the unfinished target file. -/
noncomputable def sourceNumerator
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (T : Nat) : Nat := by
  classical
  exact FixedSpanRenewalPayload.wordSum n T (fun w =>
    let D := currentRun hpsi h2 ring C w
    if ((exists i : Fin n, (D i).core.core.leader = true) \/
        LocalClockSource hpsi hn ring D)
    then 1 else 0)

theorem quantitative_target_shape_impossible
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (C : FC n psi kappa tau) :
    ¬ (forall T Q : Nat,
      n ^ T <= Q * sourceNumerator hpsi h2 hn ring C T) := by
  intro h
  have h00 := h 0 0
  simp at h00

end BirthPhaseClockSourceR1

#print axioms BirthPhaseClockSourceR1.current_pprime_core_frame
#print axioms BirthPhaseClockSourceR1.current_pprime_eq_literal_pPsi_of_leaderless_no_reset
#print axioms BirthPhaseClockSourceR1.current_edge_label_or_physical_birth
#print axioms BirthPhaseClockSourceR1.n4_psi2_passive_cyclic_has_localClockSource
#print axioms BirthPhaseClockSourceR1.n4_psi2_passive_cyclic_reaches_localClockSource_or_leader
#print axioms BirthPhaseClockSourceR1.quantitative_target_shape_impossible
