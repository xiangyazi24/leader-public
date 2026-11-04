import Leader.Wu.Splice.RiskPhysicalObligation
import Leader.Wu.Splice.HostRightLabelLaw

set_option autoImplicit false
set_option Elab.async false

namespace B9RiskRefinementPhys2

open B9Host B9SpliceTableHost B9RiskAbstraction
open B9HostRightLabelLaw

variable {psi kappa tau : Nat}

/-!
Source citations, current main @ 86055a7e or later:
* ConcreteRowB9PhysicalProjectionObligation:
  Leader/Wu/Splice/RiskPhysicalObligation.lean:25-34.
* AbsPairPhys (the five physical coordinates):
  Leader/Wu/Splice/RiskAbstraction.lean:40-49.
* The original abstract HOST summary `hostPhys` copies `v.hostLabelEqR`:
  Leader/Wu/Splice/RiskAbstraction.lean:224-227.
* `riskViewOf` records `hostLabelEqR` by the literal host-output equality test;
  `concreteOutPhys` records the same concrete equality test:
  Leader/Wu/Splice/RiskAbstraction.lean:751-779.
* Cell/base projection:
  Leader/Wu/Splice/HostTable.lean:47-52.
* RightLabelLaw and its R1 instance:
  Leader/Wu/Splice/HostRightLabelLaw.lean:33-45,50-72.
* Law-determined HOST summary `absHostPhys`:
  Leader/Wu/Splice/HostRightLabelLaw.lean:75-89.
* Boolean right-label consequence:
  Leader/Wu/Splice/HostRightLabelLaw.lean:137-161.
* Full five-field HOST-leaf projection:
  Leader/Wu/Splice/HostRightLabelLaw.lean:164-198.
* Width-two concrete host `r1Host`:
  Leader/Wu/Splice/HostRow.lean:315-322.
* PreparedOrdinaryOpen:
  Leader/Wu/Birth/ShortDoneTerminalOrdinaryLabel.lean:36-43.
-/

theorem host_leaf_phys_projection_five_fields
    (hpsi : 0 < psi)
    (host : HostRow (Phys psi kappa tau))
    (hLaw : RightLabelLaw hpsi host)
    (l r wL wR : B9SpliceTableHost.Cell psi kappa tau)
    (hl : leader (base l) = false)
    (hr : leader (base r) = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi (base l) (base r))
    (hwL : base wL = (host.row (base l) (base r)).1)
    (hwR : base wR = (host.row (base l) (base r)).2) :
    let got := B9RiskAbstraction.concreteOutPhys l r wL wR
    let want := absHostPhys (B9RiskAbstraction.riskViewOf host hpsi l r)
    got.leaderL = want.leaderL ∧
    got.leaderR = want.leaderR ∧
    got.aligned = want.aligned ∧
    got.labelEqL = want.labelEqL ∧
    got.labelEqR = want.labelEqR := by
  dsimp only
  have h := host_leaf_phys_projection
    hpsi host hLaw l r wL wR hl hr hopen hwL hwR
  rw [h]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Part (1), concrete width-two R1 instance.
Source: `r1Host`, Leader/Wu/Splice/HostRow.lean:320-322;
`r1Host_right_label_law`, Leader/Wu/Splice/HostRightLabelLaw.lean:50-72. -/
theorem r1Host_host_leaf_phys_projection_five_fields
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r wL wR : B9SpliceTableHost.Cell psi kappa tau)
    (hl : leader (base l) = false)
    (hr : leader (base r) = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi (base l) (base r))
    (hwL : base wL =
      ((B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2).row
        (base l) (base r)).1)
    (hwR : base wR =
      ((B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2).row
        (base l) (base r)).2) :
    let got := B9RiskAbstraction.concreteOutPhys l r wL wR
    let want := absHostPhys
      (B9RiskAbstraction.riskViewOf
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        hpsi l r)
    got.leaderL = want.leaderL ∧
    got.leaderR = want.leaderR ∧
    got.aligned = want.aligned ∧
    got.labelEqL = want.labelEqL ∧
    got.labelEqR = want.labelEqR := by
  exact host_leaf_phys_projection_five_fields
    hpsi
    (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
    (r1Host_right_label_law
      (kappa := kappa) (tau := tau) hpsi h2)
    l r wL wR hl hr hopen hwL hwR

/-- Public spelling of the original private abstract HOST physical summary.
It is deliberately the *observed* host bit, not unconditional preservation.
Source: private `hostPhys`, Leader/Wu/Splice/RiskAbstraction.lean:224-227. -/
noncomputable def observedHostPhys
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) : AbsPairPhys :=
  let v := B9RiskAbstraction.riskViewOf host hpsi l r
  { leaderL := v.hostLeaderL
    leaderR := v.hostLeaderR
    aligned := v.alignedHost
    labelEqL := v.hostLabelEqL
    labelEqR := v.hostLabelEqR }

/-- The exact reason part (2)'s premise is false: `riskViewOf.hostLabelEqR`
is the concrete equality test against the old right endpoint.
Source: Leader/Wu/Splice/RiskAbstraction.lean:751-769. -/
theorem riskView_hostLabelEqR_is_actual
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau) :
    (B9RiskAbstraction.riskViewOf host hpsi l r).hostLabelEqR =
      decide
        (label (host.row (base l) (base r)).2 = label (base r)) := by
  rfl

/-- Part (3), the honest relation replacing the requested “two obligations”
relation.  On exactly the domain where RightLabelLaw determines the no-birth
HOST result, its law summary equals the original exact-observation HOST
summary.  In output-leader cases `absHostPhys` intentionally keeps the
observed bit; in the two-follower case the final field is exactly
`host_right_labelEqR_decide_eq_alignedBefore`.

Sources: `absHostPhys`, Leader/Wu/Splice/HostRightLabelLaw.lean:75-89;
`host_right_labelEqR_decide_eq_alignedBefore`,
Leader/Wu/Splice/HostRightLabelLaw.lean:137-161;
original `hostPhys`, Leader/Wu/Splice/RiskAbstraction.lean:224-227. -/
theorem law_host_summary_eq_observed_host_summary
    (hpsi : 0 < psi)
    (host : HostRow (Phys psi kappa tau))
    (hLaw : RightLabelLaw hpsi host)
    (l r : B9SpliceTableHost.Cell psi kappa tau)
    (hl : leader (base l) = false)
    (hr : leader (base r) = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi (base l) (base r)) :
    absHostPhys (B9RiskAbstraction.riskViewOf host hpsi l r) =
      observedHostPhys host hpsi l r := by
  classical
  unfold B9HostRightLabelLaw.absHostPhys observedHostPhys
  unfold B9RiskAbstraction.riskViewOf
  dsimp only
  apply B9RiskAbstraction.AbsPairPhys.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · by_cases hOL : leader (host.row (base l) (base r)).1 = true
    · simp [hOL]
    · have hOL0 : leader (host.row (base l) (base r)).1 = false :=
        Bool.eq_false_iff.mpr hOL
      by_cases hOR : leader (host.row (base l) (base r)).2 = true
      · simp [hOL0, hOR]
      · have hOR0 : leader (host.row (base l) (base r)).2 = false :=
          Bool.eq_false_iff.mpr hOR
        have hEq := host_right_labelEqR_decide_eq_alignedBefore
          hpsi host hLaw (base l) (base r)
          hl hr hopen hOL0 hOR0
        simpa [hOL0, hOR0] using hEq.symm

/-- HOST-leaf projection rewritten into the original abstract HOST summary.
This is the usable seam for the eventual rowB9 branch assembly.
Sources: `host_leaf_phys_projection`, Leader/Wu/Splice/HostRightLabelLaw.lean:164-198;
`law_host_summary_eq_observed_host_summary` above. -/
theorem host_leaf_phys_projection_observed
    (hpsi : 0 < psi)
    (host : HostRow (Phys psi kappa tau))
    (hLaw : RightLabelLaw hpsi host)
    (l r wL wR : B9SpliceTableHost.Cell psi kappa tau)
    (hl : leader (base l) = false)
    (hr : leader (base r) = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi (base l) (base r))
    (hwL : base wL = (host.row (base l) (base r)).1)
    (hwR : base wR = (host.row (base l) (base r)).2) :
    B9RiskAbstraction.concreteOutPhys l r wL wR =
      observedHostPhys host hpsi l r := by
  exact
    (host_leaf_phys_projection
      hpsi host hLaw l r wL wR hl hr hopen hwL hwR).trans
    (law_host_summary_eq_observed_host_summary
      hpsi host hLaw l r hl hr hopen)

/-!
Part (2) audit conclusion.

`ConcreteRowB9PhysicalProjectionObligation` (Leader/Wu/Splice/RiskPhysicalObligation.lean:
25-34) has no clause asserting `labelEqR = true`.  Its RHS is
`(absRowB9 v).phys`; every abstract HOST leaf is built by private `hostOut`,
which uses private `hostPhys`, and private `hostPhys.labelEqR` is exactly
`v.hostLabelEqR` (Leader/Wu/Splice/RiskAbstraction.lean:243-246,224-227).
`riskViewOf` makes that bit the actual host-output equality test
(Leader/Wu/Splice/RiskAbstraction.lean:751-769).

Therefore the conditional request to define
`ConcreteRowB9PhysicalProjectionObligationLaw` is NOT triggered.  Introducing
such a global replacement would silently change non-HOST leaves and would
also incorrectly replace output-leader HOST cases, where RightLabelLaw makes
no alignment claim.  The theorem above proves the precise local agreement
that a sound branch assembly may use.
-/

end B9RiskRefinementPhys2
