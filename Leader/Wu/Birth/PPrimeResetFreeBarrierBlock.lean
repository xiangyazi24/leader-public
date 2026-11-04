import Leader.Wu.Birth.FirstBirthCohort


namespace Q11540PPrimeLatchDesign


open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open BirthPhaseCohortDesign


set_option autoImplicit false


/-- The prepared edge is not even eligible to re-arm a fresh P-prime probe.
This is strictly stronger than `PPrimeBlockedAt`: it drops only the responder
`probe = true` conjunct from the current birth guard. -/
def NoResetFreeFollowerBarrierAt
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase
  ¬ (l0.core.leader = false ∧
      r0.core.leader = false ∧
      l0.core.reset_cmd = false ∧
      isBarrier hpsi l0.core r0.core)


/-- Immediate source-level implication: a P-prime birth guard would supply
exactly the four forbidden reset-free follower/barrier facts. -/
theorem noResetFreeFollowerBarrierAt_implies_pprimeBlocked
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n)
    (h : NoResetFreeFollowerBarrierAt hpsi ring C e) :
    PPrimeBlockedAt hpsi ring C e := by
  unfold NoResetFreeFollowerBarrierAt at h
  unfold PPrimeBlockedAt
  dsimp only at h ⊢
  intro hguard
  apply h
  rcases hguard with ⟨hl, hr, hreset, hprobe, hbarrier⟩
  exact ⟨hl, hr, hreset, hbarrier⟩


#print axioms Q11540PPrimeLatchDesign.noResetFreeFollowerBarrierAt_implies_pprimeBlocked


end Q11540PPrimeLatchDesign
