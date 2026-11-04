import Leader.Wu.Splice.RiskRowCensus


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9RiskRefinementPhys4


open B9Host B9SpliceTableHost B9RiskAbstraction
open B9HostRightLabelLaw
open B9RiskRefinementPhys.B9RiskRefinementPhys
open B9RiskRefinementPhys3


/-!
Source quotations.


`R1Row10gLeafIdentificationObligation`,
Leader/Wu/Splice/RiskRowCensus.lean:326-345:


def R1Row10gLeafIdentificationObligation : Prop :=
  ∀ {psi kappa tau : Nat}
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Cell psi kappa tau),
    let host := r1Host (kappa := kappa) (tau := tau) hpsi h2
    let v := riskViewOf host hpsi l r
    let w := row10gH host hpsi l r
    SpliceProjectionFacts host ->
    ¬ ldc host l.carrier r.carrier ->
      (base w.1 = base l ∧ base w.2 = base r ∧
        inputPhysPublic v = (absRowB9 v).phys) ∨
      (leader (base l) = false ∧ leader (base r) = false ∧
        BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
          hpsi (base l) (base r) ∧
        base w.1 = (host.row (base l) (base r)).1 ∧
        base w.2 = (host.row (base l) (base r)).2 ∧
        absHostPhys v = (absRowB9 v).phys) ∨
      (base w.1 = base l ∧
        base w.2 = relabelCell hpsi (base l) (base r) ∧
        relabelPhysPublic v = (absRowB9 v).phys)


`absRowB9`, Leader/Wu/Splice/RiskAbstraction.lean:579-583:


def absRowB9 (v : RiskView) : AbsOut :=
  if gLdc v then
    if reservedFront v.left then wHoldRepair v else wDelete v
  else
    absRow10g v


`riskViewOf`, Leader/Wu/Splice/RiskAbstraction.lean:751-768:


noncomputable def riskViewOf
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : RiskView := by
  classical
  let hp := host.row (base l) (base r)
  exact
    { left := controllerOf l,
      right := controllerOf r,
      inLeaderL := B9Host.leader (base l),
      inLeaderR := B9Host.leader (base r),
      hostLeaderL := B9Host.leader hp.1,
      hostLeaderR := B9Host.leader hp.2,
      alignedBefore := decide (B9Host.Aligned (base l) (base r)),
      alignedHost := decide (B9Host.Aligned hp.1 hp.2),
      hostLabelEqL := decide (B9Host.label hp.1 = B9Host.label (base l)),
      hostLabelEqR := decide (B9Host.label hp.2 = B9Host.label (base r)),
      row10dgStutters := decide
        (B9SpliceTableHost.row10dgH host hpsi l r = (l, r)) }


`row10gH_trichotomy`, Leader/Wu/Splice/HostTable.lean:551-565:


theorem row10gH_trichotomy (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) : TriRow host hpsi l r (row10gH host hpsi l r) := by
  classical
  unfold row10gH
  dsimp only
  by_cases hq : row10dgH host hpsi l r = (l, r)
  · rw [if_pos hq]
    repeat' apply tri_ite
    all_goals first
      | exact tri_keep host hpsi l r _ rfl rfl
      | exact Or.inr (Or.inl (phys_hold host l r))
      | exact Or.inr (Or.inl (phys_fence host l r))
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rw [if_neg hq]
    exact row10dgH_trichotomy host hpsi l r
-/


/-!
Source decision.


The priority selector itself is finite: `RiskView.row10dgStutters` is already
present (Leader/Wu/Splice/RiskAbstraction.lean:64-76), and it is populated by the exact
`row10dgH = (l,r)` test above.  What is *not* present is enough full physical
state to choose an exact `TriRow` disjunct and certify the HOST domain:


* `TriRow` compares complete `base` states, while `RiskView` has no `stall`.
  `ZeroRefreshOnlyGuardH` explicitly reads both stall values and
  `SameExceptStall` (Leader/Wu/Splice/HostTable.lean:191-197).
* the HOST clause required by Phys3 contains `PreparedOrdinaryOpen`; that is
  the pair of prepared/normalized `deletionActive` bits at
  Leader/Wu/Birth/ShortDoneTerminalOrdinaryLabel.lean:36-43, and neither bit is
  a `RiskView` field.


Accordingly this is the minimal conservative completion seam: it adds no new
abstract writer or guard.  It says only how each coarse `TriRow` alternative
maps to the already-existing abstract physical summary; the HOST implication
also carries exactly the three domain facts required by Phys3's five-field
HOST theorem.
-/
def R1Row10gLeafRiskViewCompletionClause : Prop :=
  ∀ {psi kappa tau : Nat}
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Cell psi kappa tau),
    let host := r1Host (kappa := kappa) (tau := tau) hpsi h2
    let v := riskViewOf host hpsi l r
    let w := row10gH host hpsi l r
    SpliceProjectionFacts host ->
    ¬ ldc host l.carrier r.carrier ->
      (((base w.1 = base l ∧ base w.2 = base r) ->
          inputPhysPublic v = (absRowB9 v).phys) ∧
       (PhysRow host l r w ->
          leader (base l) = false ∧
          leader (base r) = false ∧
          BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
            hpsi (base l) (base r) ∧
          absHostPhys v = (absRowB9 v).phys) ∧
       ((base w.1 = base l ∧
           base w.2 = relabelCell hpsi (base l) (base r)) ->
          relabelPhysPublic v = (absRowB9 v).phys))



theorem r1Row10gLeafIdentification_of_riskViewCompletion
    (hCompletion : R1Row10gLeafRiskViewCompletionClause) :
    R1Row10gLeafIdentificationObligation := by
  intro psi kappa tau hpsi h2 l r
  dsimp only
  intro hFacts hNotLdc
  have hC := hCompletion
    (psi := psi) (kappa := kappa) (tau := tau) hpsi h2 l r
  dsimp only at hC
  have hC' := hC hFacts hNotLdc
  have hTri := row10gH_trichotomy
    (r1Host (kappa := kappa) (tau := tau) hpsi h2) hpsi l r
  rcases hTri with hKeep | hHost | hRelabel
  · exact Or.inl ⟨hKeep.1, hKeep.2, hC'.1 hKeep⟩
  · have hDomain := hC'.2.1 hHost
    exact Or.inr (Or.inl
      ⟨hDomain.1, hDomain.2.1, hDomain.2.2.1,
        hHost.1, hHost.2, hDomain.2.2.2⟩)
  · exact Or.inr (Or.inr
      ⟨hRelabel.1, hRelabel.2, hC'.2.2 hRelabel⟩)


/-- The requested R1 corollary.  It is conditional because current `RiskView`
does not contain the exact physical leaf/domain information isolated above. -/
theorem r1Host_concreteRowB9PhysicalProjection
    (hCompletion : R1Row10gLeafRiskViewCompletionClause) :
    R1ConcreteRowB9PhysicalProjectionObligation :=
  r1Host_concreteRowB9PhysicalProjection_of_leafIdentification
    (r1Row10gLeafIdentification_of_riskViewCompletion hCompletion)


end B9RiskRefinementPhys4
