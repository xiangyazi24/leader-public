import Leader.Wu.Birth.RowCountFrame
import Leader.Wu.Birth.ResetFreeCountMono

set_option autoImplicit false

namespace BirthB1CountStepReduction

open BirthShortDoneTerminalHost BirthSigMoveDisposalRepair PPLLAuthorizedComparisonRepair
open BirthB1RowCountFrame

variable {n psi kappa tau : Nat}

/-- The remaining one-letter obligation, stated on the authorized metadata chain
(width 2, the B7 host): counts do not decrease when both endpoints are
leaderless and reset-free before AND no leader is born in this letter. -/
structure InnerCountMono (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat) : Prop where
  mono : forall (l r : AuthorizedAgentState psi),
    l.core.count <= kappa -> r.core.count <= kappa ->
    l.core.reset_cmd = false -> r.core.reset_cmd = false ->
    (doneMetadataAuthorizedEntryWidth hpsi (by decide : 0 < 2) h2 kappa l r).1.core.leader = false ->
    (doneMetadataAuthorizedEntryWidth hpsi (by decide : 0 < 2) h2 kappa l r).2.core.leader = false ->
    l.core.count <= (doneMetadataAuthorizedEntryWidth hpsi (by decide : 0 < 2) h2 kappa l r).1.core.count /\
      r.core.count <= (doneMetadataAuthorizedEntryWidth hpsi (by decide : 0 < 2) h2 kappa l r).2.core.count

/-- No birth in this letter, read on the inner metadata of the scheduled pair. -/
def NoInnerBirth (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (e : Fin n) : Prop :=
  let l0 := prepareExpiringDisposal hpsi (C e)
  let r0 := prepareExpiringDisposal hpsi (C (ring.rightNeighbor e))
  let m := doneMetadataAuthorizedEntryWidth hpsi (by decide : 0 < 2) h2 kappa l0.core.erase r0.core.erase
  m.1.core.leader = false /\ m.2.core.leader = false

theorem step_apply (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e k : Fin n) :
    P.step ring C e k =
      (if k = e then (P.transition (C e) (C (ring.rightNeighbor e))).1
       else if k = ring.rightNeighbor e then
         (P.transition (C e) (C (ring.rightNeighbor e))).2
       else C k) := by
  unfold PopulationProtocol.step
  rcases hq : P.transition (C e) (C (ring.rightNeighbor e)) with ⟨a, b⟩
  simp [hq]

theorem currentStep2_apply (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (e k : Fin n) :
    BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e k =
      (if k = e then (row hpsi (by decide : 0 < 2) h2 (C e) (C (ring.rightNeighbor e))).1
       else if k = ring.rightNeighbor e then
         (row hpsi (by decide : 0 < 2) h2 (C e) (C (ring.rightNeighbor e))).2
       else C k) :=
  step_apply (BirthShortDoneTerminalConsumer.protocol hpsi (by decide : 0 < 2) h2 kappa tau) ring C e k

theorem count_step_of_inner
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (hI : InnerCountMono hpsi h2 kappa)
    (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (e : Fin n)
    (hL : BirthB1LeaderlessResetFree.Leaderless C)
    (hR : BirthB1LeaderlessResetFree.ResetFree C)
    (hNB : NoInnerBirth hpsi h2 ring C e) :
    BirthB1ResetFreeCountMono.CountMonoStep C
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) := by
  intro i
  have hmono := hI.mono
    (prepareExpiringDisposal hpsi (C e)).core.erase
    (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e))).core.erase
    (Fin.is_le _)
    (Fin.is_le _)
    (by rw [prepare_reset_eq]; exact hR e)
    (by rw [prepare_reset_eq]; exact hR _)
    hNB.1 hNB.2
  have hrow := row_count_eq hpsi (by decide : 0 < 2) h2 (C e) (C (ring.rightNeighbor e))
  show (BirthB1ResetFreeControlled.rawAt C i).count <=
    (BirthB1ResetFreeControlled.rawAt
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) i).count
  unfold BirthB1ResetFreeControlled.rawAt
  rw [currentStep2_apply]
  by_cases hie : i = e
  · rw [if_pos hie, hie]
    have h1 := hrow.1
    change countE (row hpsi _ h2 (C e) (C (ring.rightNeighbor e))).1 = _ at h1
    show countE (C e) <= countE (row hpsi _ h2 (C e) (C (ring.rightNeighbor e))).1
    rw [h1, <- prepare_count_eq hpsi (C e)]
    exact hmono.1
  · rw [if_neg hie]
    by_cases hij : i = ring.rightNeighbor e
    · rw [if_pos hij, hij]
      have h2' := hrow.2
      change countE (row hpsi _ h2 (C e) (C (ring.rightNeighbor e))).2 = _ at h2'
      show countE (C (ring.rightNeighbor e)) <=
        countE (row hpsi _ h2 (C e) (C (ring.rightNeighbor e))).2
      rw [h2', <- prepare_count_eq hpsi (C (ring.rightNeighbor e))]
      exact hmono.2
    · rw [if_neg hij]
      exact Nat.le_refl _

end BirthB1CountStepReduction
