import Leader.L3.Grant.ShortLedger

/-!
# G17: `StageGrantLeaderlessClock` on the finite advice branch, and for all `n ≥ 5`

The finite counter bound (`GrantShortBound.lean`) and the ledger comparison
(`GrantShortLedger.lean`) give the clause of `StageGrantLeaderlessClock` for
`useSmall = true` at the rate `headlinePermitRate n * n^2`.  With the spatial
branch (`GrantLeaderlessSpatial.lean`) this closes the stage for every ring
of `n ≥ 5` agents.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- **The finite-branch clause (`hshort`).**  For `n ≥ 5` with
`useSmall = true` and every purified, leaderless, grant-free configuration,
the expected time to `headlineGrantReady ∨ headlineGeneratedTarget` is at most
`headlinePermitRate n * n^2`.

Consumer: `stageGrantLeaderlessClockOfSmallBand` (GrantLeaderlessSpatial.lean). -/
theorem grantLeaderlessShortClause {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ∀ C : HeadlineConfiguration n,
      headlinePurified ring C →
      (∀ i : Fin n, (C i).l = false) →
      (∀ i : Fin n, (C i).grant = false) →
      UniformFirstHit.ExpectedHittingTimeAtMost
        (headlinePhysicalNext ring)
        (fun D => headlineGrantReady ring D ∨
          headlineGeneratedTarget ring D)
        C ((headlinePermitRate n * n ^ 2 : Nat) : Rat) := by
  intro C hp _ _
  have hnpos : 0 < n := by omega
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) _ hnpos C _).2
  intro T
  have hcost := grantShortCostBound ring hn hsmall C hp T
  have hle := shortLedgerBound n hn hsmall
  exact Nat.le_trans hcost (Nat.mul_le_mul_left _ hle)

/-- **`StageGrantLeaderlessClock` for every ring of `n ≥ 5` agents.**  The
spatial branch is `grantLeaderlessSpatialClause`, the finite branch is
`grantLeaderlessShortClause`.

Consumer: `stageFirstGrantAll`. -/
theorem stageGrantLeaderlessClockAll {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) : StageGrantLeaderlessClock ring :=
  stageGrantLeaderlessClockOfSmallBand ring
    (fun hs => grantLeaderlessShortClause ring hn hs)

/-- `StageFirstGrant` for every ring of `n ≥ 5` agents.

Consumer: the headline assembly (`HeadlineAssembly.lean`). -/
theorem stageFirstGrantAll {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) : StageFirstGrant ring :=
  stageFirstGrant_of_leaderless_clock ring hn
    (stageGrantLeaderlessClockAll ring hn)

end L3

#print axioms L3.grantLeaderlessShortClause
#print axioms L3.stageGrantLeaderlessClockAll
#print axioms L3.stageFirstGrantAll
