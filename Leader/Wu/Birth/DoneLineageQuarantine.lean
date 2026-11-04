import Leader.Wu.Comparison.HistoryDoneMove
import Leader.Wu.WallSweep.Repair


set_option autoImplicit false


namespace BirthDoneLineageQuarantineDesign


open PPLL PPLLRepair PPLLWallSweepRepair
open PPLLComparisonHistory


variable {n psi : Nat}


/-- Constant physical lineage lease.  Four values = two extra bits. -/
inductive LineageRole
  | none
  | sourceArmed
  | predecessorPermit
  | frontier
  deriving DecidableEq, Repr


/-- Proof-side view of one physical endpoint plus the proposed controller. -/
structure LineageCell (psi : Nat) where
  concrete : AgentState psi
  role : LineageRole


/-- The literal backward-depart guard in the current single-use control tail,
evaluated after both local control applications. -/
def DoneHandoffGuard (hpsi : 0 < psi)
    (l r : AgentState psi) : Prop :=
  r.state = .depart /\
    l.label.val < psi - 1 /\
    l.state = .CHECK_ready


/-- The only physical role pair allowed to execute the old DONE handoff. -/
def CertifiedDoneRoles (l r : LineageCell psi) : Prop :=
  l.role = .predecessorPermit /\ r.role = .frontier


private instance instDecidableDoneHandoffGuard
    (hpsi : 0 < psi) (l r : AgentState psi) :
    Decidable (DoneHandoffGuard hpsi l r) := by
  unfold DoneHandoffGuard
  infer_instance


private instance instDecidableCertifiedDoneRoles
    (l r : LineageCell psi) :
    Decidable (CertifiedDoneRoles l r) := by
  unfold CertifiedDoneRoles
  infer_instance


/-- Reuse the repository's existing comparison eraser and drop the lease. -/
def clearIncoming (u : LineageCell psi) : LineageCell psi :=
  { concrete := clearComparisonSignal u.concrete
    role := .none }


/-- Proposed replacement for the final backward-depart assignment only.
All earlier current DONE stages remain in their existing order.


On a certified role pair this performs exactly the old physical write
`left.state := depart`.  On an uncertified live guard it refuses that write
and scrubs the incoming right comparison carrier. -/
def quarantineDepart (hpsi : 0 < psi)
    (l r : LineageCell psi) : LineageCell psi × LineageCell psi :=
  if hg : DoneHandoffGuard hpsi l.concrete r.concrete then
    if hc : CertifiedDoneRoles l r then
      ({ concrete := { l.concrete with state := .depart }
         role := .frontier },
       { concrete := r.concrete
         role := .none })
    else
      ({ concrete := l.concrete
         role := .none },
       clearIncoming r)
  else
    (l, r)


/-- Certified handoff = the old physical state write plus lease transfer. -/
theorem quarantineDepart_of_certified
    (hpsi : 0 < psi) (l r : LineageCell psi)
    (hg : DoneHandoffGuard hpsi l.concrete r.concrete)
    (hc : CertifiedDoneRoles l r) :
    quarantineDepart hpsi l r =
      ({ concrete := { l.concrete with state := .depart }
         role := .frontier },
       { concrete := r.concrete
         role := .none }) := by
  simp [quarantineDepart, hg, hc]


/-- An uncertified live handoff is refused and the incoming component is
physically neutralized. -/
theorem quarantineDepart_of_mismatch
    (hpsi : 0 < psi) (l r : LineageCell psi)
    (hg : DoneHandoffGuard hpsi l.concrete r.concrete)
    (hc : ¬ CertifiedDoneRoles l r) :
    quarantineDepart hpsi l r =
      ({ concrete := l.concrete
         role := .none },
       clearIncoming r) := by
  simp [quarantineDepart, hg, hc]


/-- The mismatch branch really removes the complete comparison carrier. -/
theorem quarantineDepart_mismatch_right_neutral
    (hpsi : 0 < psi) (l r : LineageCell psi)
    (hg : DoneHandoffGuard hpsi l.concrete r.concrete)
    (hc : ¬ CertifiedDoneRoles l r) :
    ComparisonNeutral (quarantineDepart hpsi l r).2.concrete := by
  rw [quarantineDepart_of_mismatch hpsi l r hg hc]
  exact clearComparisonSignal_neutral r.concrete


/-- The exact marked pair immediately before the repository's final
`markedSigMoveDepart`: preclear, transfers, leader wall, then both current
single-use local controls. -/
def currentDoneCut (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi) :
    MarkedAgentState n psi × MarkedAgentState n psi :=
  let p := markedSigMoveLeaderPreclear hpsi l r
  let moved := markedDoneTransfers p.1 p.2
  let wall := PPLLWallSweepHistory.markedComparisonLeaderWall
    moved.1 moved.2
  (markedSingleUseApplyControl hpsi wall.1,
    markedSingleUseApplyControl hpsi wall.2)


/-- Physical readiness half of the prospective invariant. -/
def DoneRoleReady (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) : Prop :=
  DoneHandoffGuard hpsi l.concrete r.concrete ->
    lrole = .predecessorPermit /\ rrole = .frontier


/-- Ghost soundness half: a certified physical lease pair represents one
trusted comparison source.  No source ID is stored in the physical role. -/
def RoleLineageSound
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) : Prop :=
  lrole = .predecessorPermit ->
    rrole = .frontier ->
      exists source : Fin n,
        l.history.state = .trusted source /\
        r.history.state = .trusted source


/-- Exact certificate required at the literal current DONE cut. -/
def DoneCutCertified (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole) : Prop :=
  let q := currentDoneCut hpsi l r
  DoneRoleReady hpsi q.1 q.2 lrole rrole /\
    RoleLineageSound q.1 q.2 lrole rrole


/-- The proposed physical/ghost lease certificate discharges the existing
repository premise `CurrentDoneMoveCompatible` without changing that premise. -/
theorem currentDoneMoveCompatible_of_cut_certificate
    (hpsi : 0 < psi)
    (l r : MarkedAgentState n psi)
    (lrole rrole : LineageRole)
    (hcert : DoneCutCertified hpsi l r lrole rrole) :
    CurrentDoneMoveCompatible hpsi l r := by
  have hc := hcert
  unfold DoneCutCertified at hc
  dsimp only at hc
  unfold CurrentDoneMoveCompatible
  change SigMoveDepartCompatible hpsi
    (currentDoneCut hpsi l r).1 (currentDoneCut hpsi l r).2
  intro hg
  have hguard : DoneHandoffGuard hpsi
      (currentDoneCut hpsi l r).1.concrete
      (currentDoneCut hpsi l r).2.concrete := hg
  have hroles := hc.1 hguard
  exact hc.2 hroles.1 hroles.2


/-- Ring form of the prospective obligation.  A whole-step preservation proof
must re-establish this on all incident oriented edges after every current row. -/
def ProspectiveDoneSafe (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (M : Fin n -> MarkedAgentState n psi)
    (role : Fin n -> LineageRole) : Prop :=
  forall e : Fin n,
    DoneCutCertified hpsi (M e) (M (ring.rightNeighbor e))
      (role e) (role (ring.rightNeighbor e))


/-- Immediate consumer of the global prospective invariant. -/
theorem prospectiveDoneSafe_currentDoneMoveCompatible
    (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (M : Fin n -> MarkedAgentState n psi)
    (role : Fin n -> LineageRole)
    (h : ProspectiveDoneSafe hpsi ring M role)
    (e : Fin n) :
    CurrentDoneMoveCompatible hpsi
      (M e) (M (ring.rightNeighbor e)) :=
  currentDoneMoveCompatible_of_cut_certificate
    hpsi (M e) (M (ring.rightNeighbor e))
      (role e) (role (ring.rightNeighbor e)) (h e)


#print axioms BirthDoneLineageQuarantineDesign.quarantineDepart_of_certified
#print axioms BirthDoneLineageQuarantineDesign.quarantineDepart_of_mismatch
#print axioms BirthDoneLineageQuarantineDesign.quarantineDepart_mismatch_right_neutral
#print axioms BirthDoneLineageQuarantineDesign.currentDoneMoveCompatible_of_cut_certificate
#print axioms BirthDoneLineageQuarantineDesign.prospectiveDoneSafe_currentDoneMoveCompatible


end BirthDoneLineageQuarantineDesign
