import Leader.Wu.Splice.CheckStickyGate


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9CheckCleanupReleasedSafe


open PPLL PPLLRepair PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair
open PPLLWallSweepRepair
open PPLLComparisonHistory
open B9CheckStructuralCensus B9CheckXSupplierDesign
open B9CheckRouteLifecycle


variable {n psi kappa tau : Nat}


/-- Local spelling of the exact source-side GENSIG root. -/
def Q5790Root (hpsi : 0 < psi) (u : AgentState psi) : Prop :=
  u.leader = false ∧
    u.label = (⟨0, hpsi⟩ : Fin psi) ∧
    u.wait = false ∧
    u.path = .bot


/-- Local spelling of the existing two-field cleanup history. -/
def Q5790History (beforeWait afterWait : AgentState psi) : Prop :=
  afterWait.signal_B = (1 : Fin 2) ∨ beforeWait.reset = true


/-- Exactly the guard on which the one-field rearm fires. -/
def Q5790RearmGuard (hpsi : 0 < psi)
    (beforeWait afterWait : AgentState psi) : Prop :=
  Q5790Root hpsi afterWait ∧ Q5790History beforeWait afterWait


/-- Actual left state immediately before the repaired entry-WAIT used by the
current CHECK reconstruction. -/
def cleanupBeforeWaitAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n) :
    AgentState psi :=
  let p := preparedPairAt hpsi ring C e
  let q := PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall
    hpsi p.1 p.2
  q.1.core


/-- Actual left post-WAIT state at the current width-two entry cut. -/
def cleanupAfterWaitAt
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n) :
    AgentState psi :=
  let p := preparedPairAt hpsi ring C e
  let q := PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall
    hpsi p.1 p.2
  let w := BirthShortWaitTerminalEntryRepair.waitWidthEntry
    hpsi (by decide : 0 < 2) h2 kappa q.1.core q.2.core
  w.1


/-- Endpoint form of the rearm fence. If the current recomputation exposes the
bad root, the two-field cleanup history needed by the rearm is present. -/
def CleanupEndpointRearmFence
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  ∀ e,
    Q5790Root hpsi (cleanupAfterWaitAt hpsi h2 ring C e) ->
      Q5790History
        (cleanupBeforeWaitAt hpsi ring C e)
        (cleanupAfterWaitAt hpsi h2 ring C e)


/-- Exact canonicality conjunct missing from the present cleanup capstone. -/
def CleanupEndpointAuthorizationCanonical
    (D : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  ∀ i, AuthorizationCanonical (D i).core.erase


/-- Proof-interface spelling that every endpoint really came out of a final
`authorizedReconcile`. The current capstone does not expose this provenance. -/
def CleanupEndpointFinalReconciled
    (D : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  ∀ i, ∃
      (f : AgentState psi -> AgentState psi ->
        AgentState psi × AgentState psi)
      (l r : AuthorizedAgentState psi),
    (D i).core.erase = (authorizedReconcile f l r).1 ∨
      (D i).core.erase = (authorizedReconcile f l r).2


/-- The easy half: final generic reconciliation gives endpoint canonicality. -/
theorem cleanupEndpointCanonical_of_finalReconciled
    (D : BirthPhaseCohortDesign.FC n psi kappa tau)
    (h : CleanupEndpointFinalReconciled D) :
    CleanupEndpointAuthorizationCanonical D := by
  intro i
  rcases h i with ⟨f, l, r, hi | hi⟩
  · rw [hi]
    exact (authorizedReconcile_canonical f l r).1
  · rw [hi]
    exact (authorizedReconcile_canonical f l r).2


/-- Exact remaining cleanup-to-route statement. Current main does not prove it:
the current entry-WAIT host does not yet consume the one-field rearm. -/
def CleanupEndpointReleasedSafe
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  ∀ (S : XSupplierConfig n psi kappa tau),
    CleanupEndpointRearmFence hpsi h2 ring
        (B9CheckRouteLifecycle.xPhysical S) ->
    (∀ i, AuthorizationCanonical
      (S i).splice.carrier.splice.base.core.erase) ->
    (∀ i, ComparisonNeutral
      (S i).splice.carrier.splice.base.core.erase.core) ->
    ∀ i, ReleasedSiteSafeV9
      (kappa := kappa) (tau := tau) hpsi h2 ring S i


/-- The exact proof-side conclusion still missing after the census. -/
def NoCurrentRouteWitnesses
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  ∀ (e pos : Fin n) (referenceC : Fin n -> AgentState psi)
      (leader sourceSite : Fin n) (history : LocalComparisonHistory n)
      (carrier : EqualPrefixCarrier ring
        (currentCheckOutputRawConfig hpsi h2 ring C e)
        referenceC leader),
    ¬ CurrentRouteWitnessAt hpsi h2 ring C e pos
      referenceC leader sourceSite history carrier


/-- Once current CHECK reconstruction has no route witness, release safety is
immediate at every physical site. -/
theorem releasedSiteSafe_of_noCurrentRouteWitnesses
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (S : XSupplierConfig n psi kappa tau) (i : Fin n)
    (h : NoCurrentRouteWitnesses hpsi h2 ring
      (B9CheckRouteLifecycle.xPhysical S)) :
    ReleasedSiteSafeV9
      (kappa := kappa) (tau := tau) hpsi h2 ring S i := by
  unfold ReleasedSiteSafeV9
  intro e pos referenceC leader sourceSite history carrier hw
  exact (h e pos referenceC leader sourceSite history carrier hw).elim


end B9CheckCleanupReleasedSafe


#print axioms B9CheckCleanupReleasedSafe.cleanupEndpointCanonical_of_finalReconciled
#print axioms B9CheckCleanupReleasedSafe.releasedSiteSafe_of_noCurrentRouteWitnesses
