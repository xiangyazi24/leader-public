import Leader.Wu.Birth.FirstBirthCohort


set_option autoImplicit false


namespace Q11583PPrimePeakSafe


open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
  BirthPhaseCohortDesign


variable {n psi kappa tau : Nat}


/-- Prepared label geometry: every edge whose prepared responder is a follower
has the cyclic successor label.  No timer/reset/probe hypothesis is used. -/
def PreparedFollowerRulerAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (e : Fin n) : Prop :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase
  r0.core.leader = false ->
    r0.core.label =
      ⟨(l0.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩


/-- A prepared follower ruler excludes the actual P-prime birth guard. -/
theorem preparedFollowerRulerAt_pprimeBlocked
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (e : Fin n)
    (hruler : PreparedFollowerRulerAt hpsi ring C e) :
    PPrimeBlockedAt hpsi ring C e := by
  unfold PreparedFollowerRulerAt at hruler
  unfold PPrimeBlockedAt
  dsimp only at hruler ⊢
  intro hbirth
  unfold PPrimeBarrierBirthGuard at hbirth
  rcases hbirth with ⟨_, hrFollower, _, _, hbarrier⟩
  unfold isBarrier at hbarrier
  exact hbarrier (hruler hrFollower)


/-- Global timer-free static blocker. -/
theorem preparedFollowerRuler_pprimeBlocked
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (hruler : ∀ e, PreparedFollowerRulerAt hpsi ring C e) :
    ∀ e, PPrimeBlockedAt hpsi ring C e := by
  intro e
  exact preparedFollowerRulerAt_pprimeBlocked hpsi ring C e (hruler e)


end Q11583PPrimePeakSafe

#print axioms Q11583PPrimePeakSafe.preparedFollowerRulerAt_pprimeBlocked
#print axioms Q11583PPrimePeakSafe.preparedFollowerRuler_pprimeBlocked
