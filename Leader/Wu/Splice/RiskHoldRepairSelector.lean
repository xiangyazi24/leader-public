import Leader.Wu.Splice.RiskControllerProjection

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9RiskRefinement2D

open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV6
open B9OrphanToFence B9SpliceTableV10j
open B9Host B9SpliceTableHost B9RiskAbstraction B9RiskRefinement
open B9RiskRefinement2 B9RiskRefinement2C

variable {psi kappa tau : Nat}

inductive HoldRepairSelector where
  | reservedFront
  | pendingPred
  | victimPending
  | scrub
  | idle
  deriving DecidableEq

def holdRepairScrub (c : AbsController) : Prop :=
  absVictimClear c ∨ absFrontClear c ∨ absMalformedPending c

noncomputable def holdRepairSelector
    (c : AbsController) : HoldRepairSelector := by
  classical
  exact if absReservedFront c then .reservedFront
    else if absPendingPred c then .pendingPred
    else if absVictimPending c then .victimPending
    else if holdRepairScrub c then .scrub
    else .idle

def evalHoldRepairSelector
    (s : HoldRepairSelector) (l r : AbsController) : ControllerPair :=
  match s with
  | .reservedFront => (l, absCtlFence r)
  | .pendingPred => (l, absCtlSettle r)
  | .victimPending => (l, absCtlClearControl r)
  | .scrub => (l, absCtlClearControl r)
  | .idle => (l, r)

private theorem reservedFront_ctl_iff
    (r : Cell psi kappa tau) :
    ReservedFrontHoldGuard r.carrier ↔ absReservedFront (ctlOf r) := by
  rfl

private theorem pendingPred_ctl_iff
    (r : Cell psi kappa tau) :
    (role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true) ↔
      absPendingPred (ctlOf r) := by
  rfl

private theorem victimPending_ctl_iff
    (r : Cell psi kappa tau) :
    (role r.carrier = .victimArmed ∧ r.carrier.repairPending = true) ↔
      absVictimPending (ctlOf r) := by
  rfl

private theorem scrub_ctl_iff
    (r : Cell psi kappa tau) :
    (VictimRightScrubGuardV6 r ∨ FrontRightScrubGuardV6 r ∨
        MalformedRightPendingGuardV6 r) ↔
      holdRepairScrub (ctlOf r) := by
  rfl

private theorem selector_reserved (c : AbsController)
    (h : absReservedFront c) :
    holdRepairSelector c = .reservedFront := by
  unfold holdRepairSelector
  rw [if_pos h]

private theorem selector_pending (c : AbsController)
    (h0 : ¬ absReservedFront c) (h1 : absPendingPred c) :
    holdRepairSelector c = .pendingPred := by
  unfold holdRepairSelector
  rw [if_neg h0, if_pos h1]

private theorem selector_victim (c : AbsController)
    (h0 : ¬ absReservedFront c) (h1 : ¬ absPendingPred c)
    (h2 : absVictimPending c) :
    holdRepairSelector c = .victimPending := by
  unfold holdRepairSelector
  rw [if_neg h0, if_neg h1, if_pos h2]

private theorem selector_scrub (c : AbsController)
    (h0 : ¬ absReservedFront c) (h1 : ¬ absPendingPred c)
    (h2 : ¬ absVictimPending c) (h3 : holdRepairScrub c) :
    holdRepairSelector c = .scrub := by
  unfold holdRepairSelector
  rw [if_neg h0, if_neg h1, if_neg h2, if_pos h3]

private theorem selector_idle (c : AbsController)
    (h0 : ¬ absReservedFront c) (h1 : ¬ absPendingPred c)
    (h2 : ¬ absVictimPending c) (h3 : ¬ holdRepairScrub c) :
    holdRepairSelector c = .idle := by
  unfold holdRepairSelector
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]

section OpaqueHoldRepair

attribute [local irreducible]
  B9SpliceTableV10j.holdRepairV10j
  B9RiskAbstraction.riskViewOf

-- Public output frames used below are exactly:
-- B9RiskRefinement2C.lean:80-82  ctlOf_clearControlV6_q13708
-- B9RiskRefinement2C.lean:84-86  ctlOf_fenceV6_q13708
-- B9RiskRefinement2C.lean:88-90  ctlOf_settleV6_q13708

theorem concrete_holdRepair_selector
    (l r : Cell psi kappa tau) :
    ctlPair (B9SpliceTableV10j.holdRepairV10j l r) =
      evalHoldRepairSelector (holdRepairSelector (ctlOf r))
        (ctlOf l) (ctlOf r) := by
  classical
  have hw := B9SpliceTableV10j.holdRepairV10j.eq_1 l r
  rw [hw]
  split
  · rename_i hRF
    have hs := selector_reserved (ctlOf r) ((reservedFront_ctl_iff r).1 hRF)
    rw [hs]
    simp only [ctlPair_mk, evalHoldRepairSelector,
      ctlOf_fenceV6_q13708]
  · rename_i hnRF
    have hnRF' : ¬ absReservedFront (ctlOf r) := by
      intro h
      exact hnRF ((reservedFront_ctl_iff r).2 h)
    split
    · rename_i hP
      have hs := selector_pending (ctlOf r) hnRF'
        ((pendingPred_ctl_iff r).1 hP)
      rw [hs]
      simp only [ctlPair_mk, evalHoldRepairSelector,
        ctlOf_settleV6_q13708]
    · rename_i hnP
      have hnP' : ¬ absPendingPred (ctlOf r) := by
        intro h
        exact hnP ((pendingPred_ctl_iff r).2 h)
      split
      · rename_i hV
        have hs := selector_victim (ctlOf r) hnRF' hnP'
          ((victimPending_ctl_iff r).1 hV)
        rw [hs]
        simp only [ctlPair_mk, evalHoldRepairSelector,
          ctlOf_clearControlV6_q13708]
      · rename_i hnV
        have hnV' : ¬ absVictimPending (ctlOf r) := by
          intro h
          exact hnV ((victimPending_ctl_iff r).2 h)
        split
        · rename_i hS
          have hs := selector_scrub (ctlOf r) hnRF' hnP' hnV'
            ((scrub_ctl_iff r).1 hS)
          rw [hs]
          simp only [ctlPair_mk, evalHoldRepairSelector,
            ctlOf_clearControlV6_q13708]
        · rename_i hnS
          have hnS' : ¬ holdRepairScrub (ctlOf r) := by
            intro h
            exact hnS ((scrub_ctl_iff r).2 h)
          have hs := selector_idle (ctlOf r) hnRF' hnP' hnV' hnS'
          rw [hs]
          simp only [ctlPair_mk, evalHoldRepairSelector]

theorem riskView_right_holdRepairSelector
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau) :
    holdRepairSelector (riskViewOf host hpsi l r).right =
      holdRepairSelector (ctlOf r) := by
  rw [B9RiskRefinement2.riskView_right_ctl]


theorem abstract_holdRepair_selector (v : RiskView) :
    absCtlHoldRepair v =
      evalHoldRepairSelector (holdRepairSelector v.right) v.left v.right := by
  classical
  unfold B9RiskRefinement2.absCtlHoldRepair
  unfold B9RiskRefinement2.absCtlHoldRepairPair
  split
  · rename_i hRFb
    have hRF : absReservedFront v.right :=
      (B9RiskRefinement2.bReservedFront_true_iff v.right).1 hRFb
    rw [selector_reserved v.right hRF]
    rfl
  · rename_i hnRFb
    have hnRF : ¬ absReservedFront v.right := by
      intro h
      exact hnRFb ((B9RiskRefinement2.bReservedFront_true_iff v.right).2 h)
    split
    · rename_i hPb
      have hP : absPendingPred v.right :=
        (B9RiskRefinement2.bPendingPred_true_iff v.right).1 hPb
      rw [selector_pending v.right hnRF hP]
      rfl
    · rename_i hnPb
      have hnP : ¬ absPendingPred v.right := by
        intro h
        exact hnPb ((B9RiskRefinement2.bPendingPred_true_iff v.right).2 h)
      split
      · rename_i hVb
        have hV : absVictimPending v.right := by
          change
            (decide (v.right.spliceRole = SpliceRole.victimArmed) &&
              v.right.repairPending) = true at hVb
          unfold absVictimPending
          simpa using hVb
        rw [selector_victim v.right hnRF hnP hV]
        rfl
      · rename_i hnVb
        have hnV : ¬ absVictimPending v.right := by
          intro hV
          apply hnVb
          change
            (decide (v.right.spliceRole = SpliceRole.victimArmed) &&
              v.right.repairPending) = true
          unfold absVictimPending at hV
          simpa using hV
        split
        · rename_i hSb
          have hS : holdRepairScrub v.right := by
            change
              ((decide (v.right.spliceRole = SpliceRole.victimArmed) &&
                  !v.right.repairPending) ||
                (decide (v.right.spliceRole = SpliceRole.front) &&
                  !v.right.repairPending) ||
                (v.right.repairPending &&
                  !(decide (v.right.spliceRole = SpliceRole.predecessorArmed)) &&
                  !(decide (v.right.spliceRole = SpliceRole.front)) &&
                  !(decide (v.right.spliceRole = SpliceRole.victimArmed)))) = true
              at hSb
            unfold holdRepairScrub absVictimClear absFrontClear
              absMalformedPending
            simpa [and_assoc, or_assoc] using hSb
          rw [selector_scrub v.right hnRF hnP hnV hS]
          rfl
        · rename_i hnSb
          have hnS : ¬ holdRepairScrub v.right := by
            intro hS
            apply hnSb
            change
              ((decide (v.right.spliceRole = SpliceRole.victimArmed) &&
                  !v.right.repairPending) ||
                (decide (v.right.spliceRole = SpliceRole.front) &&
                  !v.right.repairPending) ||
                (v.right.repairPending &&
                  !(decide (v.right.spliceRole = SpliceRole.predecessorArmed)) &&
                  !(decide (v.right.spliceRole = SpliceRole.front)) &&
                  !(decide (v.right.spliceRole = SpliceRole.victimArmed)))) = true
            unfold holdRepairScrub absVictimClear absFrontClear
              absMalformedPending at hS
            simpa [and_assoc, or_assoc] using hS
          rw [selector_idle v.right hnRF hnP hnV hnS]
          rfl

theorem holdRepairControllerProjection
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi) :
    HoldRepairControllerProjectionObligation host hpsi := by
  intro l r
  calc
    ctlPair (B9SpliceTableV10j.holdRepairV10j l r) =
        evalHoldRepairSelector (holdRepairSelector (ctlOf r))
          (ctlOf l) (ctlOf r) := concrete_holdRepair_selector l r
    _ = evalHoldRepairSelector
          (holdRepairSelector (riskViewOf host hpsi l r).right)
          (riskViewOf host hpsi l r).left
          (riskViewOf host hpsi l r).right := by
        rw [B9RiskRefinement2.riskView_left_ctl,
          B9RiskRefinement2.riskView_right_ctl]
    _ = absCtlHoldRepair (riskViewOf host hpsi l r) :=
      (abstract_holdRepair_selector (riskViewOf host hpsi l r)).symm

theorem r1Host_holdRepairControllerProjectionObligation
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) :
    HoldRepairControllerProjectionObligation
      (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2) hpsi := by
  exact holdRepairControllerProjection
    (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2) hpsi

end OpaqueHoldRepair
end B9RiskRefinement2D
