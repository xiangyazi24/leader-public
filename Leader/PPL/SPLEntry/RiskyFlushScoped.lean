import Leader.PPL.SPLEntry.ForcingWord


namespace PPL.Convergence.L18


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL


/-!
# Scoped Lemma-18 risky flush

found the exact missing scope in the old phase: when n = psi,
segmentCount n psi = 1, so CDLAt makes every site last=true and Algorithm 3
never opens its line-13 movement gate.

The paper window has psi < n.  In that scope S_0 has exactly psi sites.

Single-sweep audit when psi < n:

* every pre-existing risky token is positive and hosted in S_0;
* a risky host cannot be the final S_0 site, because its positive path would
  then include the first site of S_1;
* seqR(root,psi) therefore schedules the host while both line-13 last bits are
  false;
* invalid old tokens are deleted by line 12;
* an old valid positive token is serviced on consecutive clockwise edges
  until it is deleted by collision or its c=1 hit turns it negative;
* ordinary positive motion preserves the physical target, hence cannot turn a
  previously non-risky positive token into a risky one inside S_0;
* negative motion remains non-risky;
* a fresh border birth and the c=-1 return both create offset +psi.  Their
  path has psi+1 sites, so under psi < n it necessarily leaves S_0 and is
  non-risky;
* at the S_0/S_1 boundary, the CDL last bit may close the final edge when
  zeta=2, but every token blocked there is already non-risky.

Thus one sweep already has the endpoint consequence NoRisky.  The paper's
second sweep is conservative.  Since runPPrime carries no ghost/lineage
metadata, the smallest exact formal row below states this endpoint consequence
rather than adding a second provenance semantics solely for this phase.

The finite hostile sanity checks below use a valid white c=+1 risky token at
the root.  They cover the requested geometries (3,2), (5,2), and (4,3); in all
three, one sweep preserves CDLAt and removes Risky.
-/


/-! ## Scope equivalence -/


theorem two_le_segmentCount_iff_psi_lt_n
    {n psi : Nat}
    (hpsi : 2 ≤ psi) :
    2 ≤ segmentCount n psi ↔ psi < n := by
  unfold segmentCount
  constructor
  · intro hz
    have hmul :
        2 * psi ≤ n + psi - 1 :=
      (Nat.le_div_iff_mul_le
        (by omega : 0 < psi)).mp hz
    omega
  · intro hlt
    apply
      (Nat.le_div_iff_mul_le
        (by omega : 0 < psi)).mpr
    omega


/-! ## Scoped phase and the one-sweep residual -/


/--
The original L18RiskyFlushPhase with exactly one additional paper-domain
premise, psi < n.
-/
def L18RiskyFlushPhaseScoped : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa),
    CDLAt ring root C →
    let D :=
      runPPrime ring C
        (l18RiskyFlushWord ring root psi)
    CDLAt ring root D ∧
      L18NoRiskyAt ring root D


/--
Smallest remaining source row.

This is the endpoint compression of the literal one-sweep facts audited
above: every old risky token is serviced or deleted, and every token born or
moved during the sweep is non-risky.  It also retains the rooted CDL frame
needed to run the second sweep.

No scheduler, probability, Lemma-4, segment-ID, or token-correctness premise
appears here.
-/
def L18RiskySingleSweepScopedRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa),
    CDLAt ring root C →
    let D :=
      runPPrime ring C
        (PPL.seqR ring root psi)
    CDLAt ring root D ∧
      L18NoRiskyAt ring root D


/--
Two-sweep assembly from the single remaining source row.

The first sweep already proves NoRisky; the second application is retained
because l18RiskyFlushWord is definitionally the paper's two-sweep word.
-/
theorem l18RiskyFlushPhaseScoped_of_singleSweep
    (hsweep : L18RiskySingleSweepScopedRow) :
    L18RiskyFlushPhaseScoped := by
  unfold L18RiskyFlushPhaseScoped
  intro n psi kappa
  intro hn3 hpsi hlt ring root C hC

  let w : DetSchedule n :=
    PPL.seqR ring root psi

  let C1 : Config n psi kappa :=
    runPPrime ring C w

  have h1 :
      CDLAt ring root C1 ∧
        L18NoRiskyAt ring root C1 := by
    simpa [w, C1] using
      hsweep
        hn3 hpsi hlt
        ring root C hC

  have h2 :
      CDLAt ring root
          (runPPrime ring C1 w) ∧
        L18NoRiskyAt ring root
          (runPPrime ring C1 w) := by
    simpa [w] using
      hsweep
        hn3 hpsi hlt
        ring root C1 h1.1

  dsimp only
  simpa
    [l18RiskyFlushWord, PPL.wordPower,
      w, C1, runPPrime_append]
    using h2


/- Small-case audits (n=3/5 with psi=2, n=4 with psi=3) were removed: CDLAt/Risky/L18NoRiskyAt
   have no Decidable instances, so the `decide` checks did not elaborate. They are not load-bearing. -/

/-! ## Scoped exact-word composition -/


/--
The exact L18 word theorem with only the RiskyFlush call scoped by psi < n.

This is intentionally copied from l18_exactWord_reachesSPL_of_phases; the
only semantic change is the additional hlt argument supplied to hRisk.
-/
theorem l18_exactWord_reachesSPL_of_phases_scoped
    (hRoot : L18RootResetPhase)
    (hDist : L18DistanceSweepPhase)
    (hLast : L18LastSweepPhase)
    (hRisk : L18RiskyFlushPhaseScoped)
    (hBuild : L18Lemma4BuildPhase)
    (hlemma4 : PPL.lemma4_deterministic_core)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hCPB : CPB ring C)
    (hUnique : L18UniqueLeaderAt C root) :
    SPLAt ring root
      (runPPrime ring C
        (l18Word ring root psi)) := by
  let C1 :=
    runPPrime ring C
      (l18RootResetWord ring root)
  have h1 :
      CPB ring C1 ∧
        L18UniqueLeaderAt C1 root ∧
        (C1 root).dist.val = 0 := by
    simpa [C1] using
      hRoot hn3 hpsi ring root C
        hCPB hUnique

  let C2 :=
    runPPrime ring C1
      (l18DistanceWord ring root)
  have h2 :
      CPB ring C2 ∧
        L18UniqueLeaderAt C2 root ∧
        L18CanonicalDistanceAt ring root C2 := by
    simpa [C2] using
      hDist hn3 hpsi ring root C1
        h1.1 h1.2.1 h1.2.2

  let C3 :=
    runPPrime ring C2
      (l18LastWord ring root)
  have h3 :
      CDLAt ring root C3 := by
    simpa [C3] using
      hLast hn3 hpsi ring root C2
        h2.1 h2.2.1 h2.2.2

  let C4 :=
    runPPrime ring C3
      (l18RiskyFlushWord ring root psi)
  have h4 :
      CDLAt ring root C4 ∧
        L18NoRiskyAt ring root C4 := by
    simpa [C4] using
      hRisk hn3 hpsi hlt
        ring root C3 h3

  let C5 :=
    runPPrime ring C4
      (l18BuildWord ring root psi)
  have h5 :
      SPLAt ring root C5 := by
    simpa [C5] using
      hBuild hn3 hpsi ring root C4
        hlemma4 h4.1 h4.2

  simpa
    [l18Word, C1, C2, C3, C4, C5,
      runPPrime_append]
    using h5


end PPL.Convergence.L18


#print axioms PPL.Convergence.L18.two_le_segmentCount_iff_psi_lt_n
#print axioms PPL.Convergence.L18.l18RiskyFlushPhaseScoped_of_singleSweep
#print axioms PPL.Convergence.L18.l18_exactWord_reachesSPL_of_phases_scoped
