import Leader.Wu.Birth.DoneLineageQuarantine


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace BirthDoneLineageLeaseTransitions


open PPLL PPLLRepair PPLLWallSweepRepair
open PPLLComparisonHistory
open BirthDoneLineageQuarantineDesign


variable {n psi : Nat}


/-! ## Module-local decidability -/


private instance instDecidableDoneHandoffGuardLocal
    (hpsi : 0 < psi) (l r : AgentState psi) :
    Decidable (DoneHandoffGuard hpsi l r) := by
  unfold DoneHandoffGuard
  infer_instance


private instance instDecidableCertifiedDoneRolesLocal
    (l r : LineageCell psi) :
    Decidable (CertifiedDoneRoles l r) := by
  unfold CertifiedDoneRoles
  infer_instance


private instance instDecidableComparisonNeutralLocal
    (u : AgentState psi) : Decidable (ComparisonNeutral u) := by
  unfold ComparisonNeutral
  infer_instance


/-! ## Edge-local lease transitions -/


/-- A fresh source can be armed only across a completely neutral incoming
boundary.  This is the prospective reservation point: arbitrary initialized
roles cannot manufacture an arm on top of a live comparison carrier. -/
def SourceArmReady (l r : LineageCell psi) : Prop :=
  l.role = .none /\
    r.role = .none /\
    ComparisonNeutral l.concrete /\
    ComparisonNeutral r.concrete


private instance instDecidableSourceArmReady
    (l r : LineageCell psi) : Decidable (SourceArmReady l r) := by
  unfold SourceArmReady
  infer_instance


/-- The predecessor permit may be granted either to an armed fresh source or
in front of an already committed frontier.  In the armed case this is also the
constant-state source commit: `sourceArmed` is consumed into `frontier`. -/
def GrantPredecessorPermitReady (l r : LineageCell psi) : Prop :=
  l.role = .none /\
    (r.role = .sourceArmed \/ r.role = .frontier)


private instance instDecidableGrantPredecessorPermitReady
    (l r : LineageCell psi) :
    Decidable (GrantPredecessorPermitReady l r) := by
  unfold GrantPredecessorPermitReady
  infer_instance


/-- First half of source creation.  The base protocol state is framed; only
the prospective source endpoint is armed. -/
def armSource (l r : LineageCell psi) :
    LineageCell psi × LineageCell psi :=
  if SourceArmReady l r then
    (l, { r with role := .sourceArmed })
  else
    (l, r)


/-- Grant the incoming predecessor permit and commit the right endpoint as the
frontier.  For a fresh source the marked source writer must already have
established the common trusted source used in the preservation theorem below.
For an existing frontier this is the permit re-grant before its next handoff. -/
def grantPredecessorPermit (l r : LineageCell psi) :
    LineageCell psi × LineageCell psi :=
  if GrantPredecessorPermitReady l r then
    ({ l with role := .predecessorPermit },
     { r with role := .frontier })
  else
    (l, r)


/-- Final DONE commit.  This is exactly the already-adopted quarantine: a
certified permit/frontier pair moves the frontier one site left; a live
uncertified handoff is refused and scrubbed. -/
def commitFrontier (hpsi : 0 < psi)
    (l r : LineageCell psi) : LineageCell psi × LineageCell psi :=
  quarantineDepart hpsi l r


/-- Local self-stabilizing scrub.  The caller uses this action for a forged or
stale lease pattern.  A physically neutral cell is framed and its role is
cleared; an active cell is cleared with the repository comparison eraser and
its role is also cleared. -/
def scrubCell (u : LineageCell psi) : LineageCell psi :=
  if ComparisonNeutral u.concrete then
    { u with role := .none }
  else
    clearIncoming u


/-- Edge-local form of the scrub. -/
def localScrub (l r : LineageCell psi) :
    LineageCell psi × LineageCell psi :=
  (scrubCell l, scrubCell r)


/-! ## First transition facts -/


theorem armSource_of_ready
    (l r : LineageCell psi) (h : SourceArmReady l r) :
    armSource l r = (l, { r with role := .sourceArmed }) := by
  simp [armSource, h]


theorem grantPredecessorPermit_of_ready
    (l r : LineageCell psi)
    (h : GrantPredecessorPermitReady l r) :
    grantPredecessorPermit l r =
      ({ l with role := .predecessorPermit },
       { r with role := .frontier }) := by
  simp [grantPredecessorPermit, h]


theorem commitFrontier_of_certified
    (hpsi : 0 < psi) (l r : LineageCell psi)
    (hg : DoneHandoffGuard hpsi l.concrete r.concrete)
    (hc : CertifiedDoneRoles l r) :
    commitFrontier hpsi l r =
      ({ concrete := { l.concrete with state := .depart }
         role := .frontier },
       { concrete := r.concrete
         role := .none }) := by
  exact quarantineDepart_of_certified hpsi l r hg hc


theorem scrubCell_of_neutral
    (u : LineageCell psi) (h : ComparisonNeutral u.concrete) :
    scrubCell u = { u with role := .none } := by
  simp [scrubCell, h]


theorem scrubCell_of_not_neutral
    (u : LineageCell psi) (h : ¬ ComparisonNeutral u.concrete) :
    scrubCell u = clearIncoming u := by
  simp [scrubCell, h]


theorem scrubCell_role_none (u : LineageCell psi) :
    (scrubCell u).role = .none := by
  by_cases h : ComparisonNeutral u.concrete
  · rw [scrubCell_of_neutral u h]
  · rw [scrubCell_of_not_neutral u h]
    rfl


theorem scrubCell_neutral (u : LineageCell psi) :
    ComparisonNeutral (scrubCell u).concrete := by
  by_cases h : ComparisonNeutral u.concrete
  · rw [scrubCell_of_neutral u h]
    exact h
  · rw [scrubCell_of_not_neutral u h]
    simpa [clearIncoming] using clearComparisonSignal_neutral u.concrete


theorem localScrub_roles_none (l r : LineageCell psi) :
    (localScrub l r).1.role = .none /\
      (localScrub l r).2.role = .none := by
  change (scrubCell l).role = .none /\ (scrubCell r).role = .none
  exact ⟨scrubCell_role_none l, scrubCell_role_none r⟩


/-! ## Lease invariant -/


/-- Reattach an unchanged proof history to the physical state carried by a
lineage cell.  The source ID remains proof-side; no `Fin n` value is added to
the executable lease. -/
def attachHistory (m : MarkedAgentState n psi)
    (c : LineageCell psi) : MarkedAgentState n psi :=
  { concrete := c.concrete
    history := m.history }


/-- The exact local lease invariant at a post-control DONE cut.  The first half
forces every live physical DONE guard to have the certified role pair.  The
second half says that pair represents one common trusted source. -/
def LeaseCutInvariant (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) : Prop :=
  DoneRoleReady hpsi l r lrole rrole /\
    RoleLineageSound l r lrole rrole


/-- Convenience form used to state preservation of the executable pair
transitions while keeping source authentication in proof history. -/
def LeasePairInvariant (hpsi : 0 < psi)
    (ml mr : MarkedAgentState n psi)
    (l r : LineageCell psi) : Prop :=
  LeaseCutInvariant hpsi
    (attachHistory ml l) (attachHistory mr r) l.role r.role


/-- Arming a neutral source boundary cannot expose a live DONE cut. -/
theorem armSource_preserves_leasePairInvariant
    (hpsi : 0 < psi)
    (ml mr : MarkedAgentState n psi)
    (l r : LineageCell psi)
    (_hinv : LeasePairInvariant hpsi ml mr l r)
    (hready : SourceArmReady l r) :
    LeasePairInvariant hpsi ml mr
      (armSource l r).1 (armSource l r).2 := by
  rw [armSource_of_ready l r hready]
  have hrneutral : ComparisonNeutral r.concrete := hready.2.2.2
  unfold LeasePairInvariant LeaseCutInvariant
  constructor
  · unfold DoneRoleReady
    intro hg
    have hg' : DoneHandoffGuard hpsi l.concrete r.concrete := by
      simpa [attachHistory] using hg
    unfold DoneHandoffGuard at hg'
    have hd := hg'.1
    rw [hrneutral.1] at hd
    cases hd
  · unfold RoleLineageSound
    intro hpred
    have hnone : l.role = .none := hready.1
    rw [hnone] at hpred
    cases hpred


/-- Granting a permit/frontier pair is safe exactly when the proof-side state
marks already authenticate one source.  This is the causal premise supplied by
the marked source writer or by the surviving frontier. -/
theorem grantPredecessorPermit_preserves_leasePairInvariant
    (hpsi : 0 < psi)
    (ml mr : MarkedAgentState n psi)
    (l r : LineageCell psi)
    (_hinv : LeasePairInvariant hpsi ml mr l r)
    (hready : GrantPredecessorPermitReady l r)
    (hsource : SameTrustedSource ml.history.state mr.history.state) :
    LeasePairInvariant hpsi ml mr
      (grantPredecessorPermit l r).1
      (grantPredecessorPermit l r).2 := by
  rw [grantPredecessorPermit_of_ready l r hready]
  unfold LeasePairInvariant LeaseCutInvariant
  constructor
  · unfold DoneRoleReady
    intro _
    exact ⟨rfl, rfl⟩
  · unfold RoleLineageSound
    intro _ _
    simpa [attachHistory, SameTrustedSource] using hsource


/-- The adopted DONE commit preserves the local cut invariant.  If the guard is
false it frames the pair.  If it is true, the old invariant forces the
certified pair, and the commit leaves `frontier/none`; the just-executed left
endpoint is `.depart`, so the same edge is no longer a live DONE cut. -/
theorem commitFrontier_preserves_leasePairInvariant
    (hpsi : 0 < psi)
    (ml mr : MarkedAgentState n psi)
    (l r : LineageCell psi)
    (hinv : LeasePairInvariant hpsi ml mr l r) :
    LeasePairInvariant hpsi ml mr
      (commitFrontier hpsi l r).1
      (commitFrontier hpsi l r).2 := by
  by_cases hg : DoneHandoffGuard hpsi l.concrete r.concrete
  · have hroles : CertifiedDoneRoles l r := by
      have hi := hinv
      unfold LeasePairInvariant LeaseCutInvariant at hi
      have hready := hi.1
      unfold DoneRoleReady at hready
      unfold CertifiedDoneRoles
      apply hready
      simpa [attachHistory] using hg
    rw [commitFrontier_of_certified hpsi l r hg hroles]
    simp [LeasePairInvariant, LeaseCutInvariant, DoneRoleReady,
      RoleLineageSound, DoneHandoffGuard, attachHistory]
  · simpa [commitFrontier, quarantineDepart, hg] using hinv


/-- Scrub is stronger than preservation: irrespective of the incoming role
pattern it establishes a safe local cut by clearing both roles, and it makes
the right physical endpoint comparison-neutral. -/
theorem localScrub_preserves_leasePairInvariant
    (hpsi : 0 < psi)
    (ml mr : MarkedAgentState n psi)
    (l r : LineageCell psi) :
    LeasePairInvariant hpsi ml mr
      (localScrub l r).1 (localScrub l r).2 := by
  change LeasePairInvariant hpsi ml mr (scrubCell l) (scrubCell r)
  have hlrole := scrubCell_role_none l
  have hrneutral := scrubCell_neutral r
  unfold LeasePairInvariant LeaseCutInvariant
  constructor
  · unfold DoneRoleReady
    intro hg
    have hg' : DoneHandoffGuard hpsi
        (scrubCell l).concrete (scrubCell r).concrete := by
      simpa [attachHistory] using hg
    unfold DoneHandoffGuard at hg'
    have hd := hg'.1
    rw [hrneutral.1] at hd
    cases hd
  · unfold RoleLineageSound
    intro hpred
    rw [hlrole] at hpred
    cases hpred


/-! ## Ring invariant and existing DONE certificate -/


/-- All oriented current DONE cuts satisfy the local lease invariant after the
exact repository preclear/transfers/leader-wall/local-control prefix. -/
def LeaseSafe (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (M : Fin n -> MarkedAgentState n psi)
    (role : Fin n -> LineageRole) : Prop :=
  forall e : Fin n,
    let q := currentDoneCut hpsi (M e) (M (ring.rightNeighbor e))
    LeaseCutInvariant hpsi q.1 q.2
      (role e) (role (ring.rightNeighbor e))


/-- `LeaseSafe` is exactly strong enough to manufacture the already-adopted
`DoneCutCertified` on every physical edge. -/
theorem leaseSafe_doneCutCertified
    (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (M : Fin n -> MarkedAgentState n psi)
    (role : Fin n -> LineageRole)
    (h : LeaseSafe hpsi ring M role)
    (e : Fin n) :
    DoneCutCertified hpsi (M e) (M (ring.rightNeighbor e))
      (role e) (role (ring.rightNeighbor e)) := by
  unfold LeaseSafe at h
  have he := h e
  unfold DoneCutCertified
  dsimp only
  unfold LeaseCutInvariant at he
  exact he


/-- Therefore the new invariant feeds the existing prospective interface
without changing `BirthDoneLineageQuarantineDesign`. -/
theorem leaseSafe_prospectiveDoneSafe
    (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (M : Fin n -> MarkedAgentState n psi)
    (role : Fin n -> LineageRole)
    (h : LeaseSafe hpsi ring M role) :
    ProspectiveDoneSafe hpsi ring M role := by
  intro e
  exact leaseSafe_doneCutCertified hpsi ring M role h e


/-- Immediate CHECK-side consumer: every edge receives the existing current
DONE compatibility premise. -/
theorem leaseSafe_currentDoneMoveCompatible
    (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (M : Fin n -> MarkedAgentState n psi)
    (role : Fin n -> LineageRole)
    (h : LeaseSafe hpsi ring M role)
    (e : Fin n) :
    CurrentDoneMoveCompatible hpsi
      (M e) (M (ring.rightNeighbor e)) := by
  exact
    prospectiveDoneSafe_currentDoneMoveCompatible
      hpsi ring M role (leaseSafe_prospectiveDoneSafe hpsi ring M role h) e


/-! ## Sourceless scrub: no permanent trap -/


/-- There is no physical comparison source/carrier anywhere in the
configuration.  Roles may still be arbitrary garbage from initialization. -/
def NoComparisonSource
    (C : Fin n -> LineageCell psi) : Prop :=
  forall i : Fin n, ComparisonNeutral (C i).concrete


/-- Pointwise scrub used after the local scrub action has been scheduled over
the configuration. -/
def scrubConfiguration
    (C : Fin n -> LineageCell psi) : Fin n -> LineageCell psi :=
  fun i => scrubCell (C i)


/-- In a sourceless configuration the scrub does not need to alter physical
state at all: it clears every arbitrary lease role to `none`. -/
theorem sourceless_scrub_clears_every_role
    (C : Fin n -> LineageCell psi)
    (h : NoComparisonSource C) :
    forall i : Fin n,
      (scrubConfiguration C i).concrete = (C i).concrete /\
        (scrubConfiguration C i).role = .none := by
  intro i
  have hi := h i
  simp [scrubConfiguration, scrubCell, hi]


/-- Functional form: after a sourceless scrub the lease layer is globally
neutral.  This theorem is independent of every leader bit, so it also covers a
leaderless+sourceless configuration and rules out a lease-only permanent trap. -/
theorem sourceless_scrub_role_function_none
    (C : Fin n -> LineageCell psi)
    (h : NoComparisonSource C) :
    (fun i => (scrubConfiguration C i).role) =
      (fun _ : Fin n => LineageRole.none) := by
  funext i
  exact (sourceless_scrub_clears_every_role C h i).2


#print axioms BirthDoneLineageLeaseTransitions.armSource_preserves_leasePairInvariant
#print axioms BirthDoneLineageLeaseTransitions.grantPredecessorPermit_preserves_leasePairInvariant
#print axioms BirthDoneLineageLeaseTransitions.commitFrontier_preserves_leasePairInvariant
#print axioms BirthDoneLineageLeaseTransitions.localScrub_preserves_leasePairInvariant
#print axioms BirthDoneLineageLeaseTransitions.leaseSafe_doneCutCertified
#print axioms BirthDoneLineageLeaseTransitions.leaseSafe_currentDoneMoveCompatible
#print axioms BirthDoneLineageLeaseTransitions.sourceless_scrub_clears_every_role
#print axioms BirthDoneLineageLeaseTransitions.sourceless_scrub_role_function_none


end BirthDoneLineageLeaseTransitions
