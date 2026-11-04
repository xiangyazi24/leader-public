import Leader.Wu.Splice.RiskHostLeaf

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9RiskRefinementPhys3

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceV10cLiveness
open B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j
open B9Host B9SpliceTableHost B9RiskAbstraction B9RiskRefinement
open B9HostRightLabelLaw B9RiskRefinementPhys2
open B9RiskRefinementPhys.B9RiskRefinementPhys

variable {psi kappa tau : Nat}

/-!
## rowB9 physical census

Source tree:
* `row7H`: Leader/Wu/Splice/HostTable.lean:131-169.
* `row8H`, `row9H`, `row10bH`: Leader/Wu/Splice/HostTable.lean:172-192.
* `row10cH`, `row10dgH`: Leader/Wu/Splice/HostTable.lean:200-215.
* `row10gH`: Leader/Wu/Splice/HostTable.lean:218-237.
* top `rowB9`: Leader/Wu/Splice/HostTable.lean:240-248.
* public HOST endpoint frames `phys_ordinary`, `phys_delete`, `phys_hold`,
  `phys_fence`: Leader/Wu/Splice/HostTable.lean:488-504.
* public coarse row classifiers `row7H_trichotomy`, `row10dgH_trichotomy`,
  `row10gH_trichotomy`, `holdRepair_trichotomy`, `rowB9_trichotomy`:
  Leader/Wu/Splice/HostTable.lean:527-583.
* abstract KEEP/HOST/RELABEL summaries:
  Leader/Wu/Splice/RiskAbstraction.lean:218-247.
* abstract priority tree: Leader/Wu/Splice/RiskAbstraction.lean:470-559.

TOP rowB9 (240-248):
1. `ldc` + reserved-left -> `holdRepairV10j`: KEEP.
2. `ldc` + not reserved-left -> `deleteWriteH`: HOST (`phys_delete`).
3. not `ldc` -> `row10gH`: first missing exact public leaf selector.

Inside `row10gH` (218-237), the stuttering branch selects KEEP except for
`physicalHoldH` / physical fence, which are HOST (`phys_hold`, `phys_fence`).
The non-stuttering branch delegates to `row10dgH`.

Inside `row10dgH` (207-215), the four repair branches are KEEP; fallback is
`row10cH`.  `row10cH` true is KEEP and false delegates to `row10bH`.
`row10bH` fence advance is KEEP; `row9H` fence busy is RELABEL; `row8H`
right-stale is KEEP; remaining fallbacks descend to `row7H`.

Inside `row7H` (131-169), target-clear host-fence advance and move-commit are
RELABEL; DELETE and ordinary fallback are HOST; every other listed writer is
KEEP.  `row7H_trichotomy` exposes only the coarse class, not the matching
private abstract leaf.
-/

/-- Public copy of private abstract KEEP physical summary.
Source: Leader/Wu/Splice/RiskAbstraction.lean:218-221. -/
def inputPhysPublic (v : RiskView) : AbsPairPhys :=
  { leaderL := v.inLeaderL
    leaderR := v.inLeaderR
    aligned := v.alignedBefore
    labelEqL := true
    labelEqR := true }

/-- Public copy of private abstract RELABEL physical summary.
Source: Leader/Wu/Splice/RiskAbstraction.lean:229-232. -/
def relabelPhysPublic (v : RiskView) : AbsPairPhys :=
  { leaderL := v.inLeaderL
    leaderR := v.inLeaderR
    aligned := true
    labelEqL := true
    labelEqR := v.alignedBefore }

/-- Package exactly the three public SpliceLaws projections.
Sources: Leader/Wu/Splice/RiskPhysicalObligation.lean:50-87. -/
structure SpliceProjectionFacts
    (host : HostRow (Phys psi kappa tau)) : Prop where
  leftFollowerLabel :
    ∀ l r : Phys psi kappa tau,
      leader l = false -> label (host.row l r).1 = label l
  rightLeader :
    ∀ l r : Phys psi kappa tau,
      leader r = true -> leader (host.row l r).2 = true
  alignedFollowers :
    ∀ l r : Phys psi kappa tau,
      leader l = false -> leader r = false ->
      leader (host.row l r).1 = false ->
      leader (host.row l r).2 = false ->
      Aligned l r -> Aligned (host.row l r).1 (host.row l r).2

theorem spliceProjectionFacts_of_laws
    (host : HostRow (Phys psi kappa tau)) (h : SpliceLaws host) :
    SpliceProjectionFacts host := by
  refine ⟨?_, ?_, ?_⟩
  · intro l r hl
    exact spliceLaws_leftFollowerLabel host h l r hl
  · intro l r hr
    exact spliceLaws_rightLeader host h l r hr
  · intro l r hl hr hOL hOR hA
    exact spliceLaws_alignedFollowers host h l r hl hr hOL hOR hA

theorem r1Host_spliceProjectionFacts
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) :
    SpliceProjectionFacts
      (r1Host (kappa := kappa) (tau := tau) hpsi h2) :=
  spliceProjectionFacts_of_laws _
    (r1Host_spliceLaws (kappa := kappa) (tau := tau) hpsi h2)

/-- Exact concrete KEEP projection. -/
theorem concreteOutPhys_keep
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r wL wR : Cell psi kappa tau)
    (hL : base wL = base l) (hR : base wR = base r) :
    concreteOutPhys l r wL wR =
      inputPhysPublic (riskViewOf host hpsi l r) := by
  classical
  unfold concreteOutPhys inputPhysPublic B9RiskAbstraction.riskViewOf
  dsimp only
  rw [hL, hR]
  simp

/-- Exact concrete HOST projection from public endpoint frame. -/
theorem concreteOutPhys_of_physRow
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r wL wR : Cell psi kappa tau)
    (h : PhysRow host l r (wL, wR)) :
    concreteOutPhys l r wL wR = observedHostPhys host hpsi l r := by
  classical
  rcases h with ⟨hL, hR⟩
  unfold concreteOutPhys observedHostPhys B9RiskAbstraction.riskViewOf
  dsimp only
  rw [hL, hR]


/-- Exact concrete RELABEL projection.
Sources: `relabelCell`, Leader/Wu/Splice/HostTable.lean:456-459;
`rightLabel_eq_old_iff_aligned`, Leader/Wu/Splice/HostRightLabelLaw.lean:109-134. -/
theorem concreteOutPhys_relabel
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r wL wR : Cell psi kappa tau)
    (hL : base wL = base l)
    (hR : base wR = relabelCell hpsi (base l) (base r)) :
    concreteOutPhys l r wL wR =
      relabelPhysPublic (riskViewOf host hpsi l r) := by
  classical
  unfold concreteOutPhys relabelPhysPublic B9RiskAbstraction.riskViewOf
  dsimp only
  rw [hL, hR]
  apply AbsPairPhys.ext
  · rfl
  · exact relabelCell_leader hpsi (base l) (base r)
  · have hA : Aligned (base l) (relabelCell hpsi (base l) (base r)) := by
      unfold Aligned relabelCell B9Host.label
      rfl
    simp [hA]
  · simp
  · have hnext :
        label (relabelCell hpsi (base l) (base r)) =
          B6LocalRuler.nextLabel hpsi (label (base l)) := by
      rfl
    have hiff := rightLabel_eq_old_iff_aligned
      hpsi (base l) (base r) (relabelCell hpsi (base l) (base r)) hnext
    by_cases hA : Aligned (base l) (base r)
    · have hEq := hiff.mpr hA
      simp [hA, hEq]
    · have hNe :
          label (relabelCell hpsi (base l) (base r)) ≠ label (base r) := by
        intro hEq
        exact hA (hiff.mp hEq)
      simp [hA, hNe]

/-- Reassemble structure equality from compiled five-field R1 HOST theorem.
Source: Leader/Wu/Splice/RiskHostLeaf.lean:41-102. -/
theorem r1Host_host_leaf_phys_projection_from_five_fields
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r wL wR : Cell psi kappa tau)
    (hl : leader (base l) = false)
    (hr : leader (base r) = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi (base l) (base r))
    (hwL : base wL =
      ((r1Host (kappa := kappa) (tau := tau) hpsi h2).row
        (base l) (base r)).1)
    (hwR : base wR =
      ((r1Host (kappa := kappa) (tau := tau) hpsi h2).row
        (base l) (base r)).2) :
    concreteOutPhys l r wL wR =
      absHostPhys
        (riskViewOf (r1Host (kappa := kappa) (tau := tau) hpsi h2)
          hpsi l r) := by
  have h := r1Host_host_leaf_phys_projection_five_fields
    (kappa := kappa) (tau := tau)
    hpsi h2 l r wL wR hl hr hopen hwL hwR
  dsimp only at h
  apply AbsPairPhys.ext
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

/-- `holdRepairV10j` is controller-only; physical bases stay unchanged. -/
theorem holdRepair_bases
    (l r : Cell psi kappa tau) :
    base (holdRepairV10j l r).1 = base l ∧
      base (holdRepairV10j l r).2 = base r := by
  classical
  unfold holdRepairV10j
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

private def q13868_roleEq
    (c : AbsController) (r : SpliceRole) : Bool :=
  decide (c.spliceRole = r)

private def q13868_setControl
    (_c : AbsController) (r : SpliceRole) (p : Bool) : AbsController :=
  { spliceRole := r, repairPending := p, acquireTicket := false }

private def q13868_clearControl (c : AbsController) : AbsController :=
  q13868_setControl c .none false

private def q13868_fenceCtl (_c : AbsController) : AbsController :=
  { spliceRole := .none, repairPending := false, acquireTicket := true }

private def q13868_settleCtl (_c : AbsController) : AbsController :=
  { spliceRole := .predecessorArmed,
    repairPending := false, acquireTicket := false }

private def q13868_reservedFront (c : AbsController) : Bool :=
  q13868_roleEq c .front && c.repairPending

private def q13868_pendingPred (c : AbsController) : Bool :=
  q13868_roleEq c .predecessorArmed && c.repairPending

private def q13868_victimPending (c : AbsController) : Bool :=
  q13868_roleEq c .victimArmed && c.repairPending

private def q13868_victimClear (c : AbsController) : Bool :=
  q13868_roleEq c .victimArmed && !c.repairPending

private def q13868_frontClear (c : AbsController) : Bool :=
  q13868_roleEq c .front && !c.repairPending

private def q13868_malformedPending (c : AbsController) : Bool :=
  c.repairPending &&
    !q13868_roleEq c .predecessorArmed &&
    !q13868_roleEq c .front &&
    !q13868_roleEq c .victimArmed

private def q13868_keepOut
    (v : RiskView) (l r : AbsController) : AbsOut :=
  { left := l, right := r, phys := inputPhysPublic v }

private def q13868_clearRight (v : RiskView) : AbsOut :=
  q13868_keepOut v v.left (q13868_clearControl v.right)

private def q13868_wHoldRepair (v : RiskView) : AbsOut :=
  if q13868_reservedFront v.right then
    q13868_keepOut v v.left (q13868_fenceCtl v.right)
  else if q13868_pendingPred v.right then
    q13868_keepOut v v.left (q13868_settleCtl v.right)
  else if q13868_victimPending v.right then
    q13868_clearRight v
  else if q13868_victimClear v.right ||
      q13868_frontClear v.right || q13868_malformedPending v.right then
    q13868_clearRight v
  else
    q13868_keepOut v v.left v.right

private theorem q13868_wHoldRepair_phys (v : RiskView) :
    (q13868_wHoldRepair v).phys = inputPhysPublic v := by
  unfold q13868_wHoldRepair
  repeat' split
  all_goals rfl


theorem inputPhys_eq_absRowB9_of_ldc_reserved
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau)
    (hdel : ldc host l.carrier r.carrier)
    (hRF : ReservedFrontHoldGuard l.carrier) :
    inputPhysPublic (riskViewOf host hpsi l r) =
      (absRowB9 (riskViewOf host hpsi l r)).phys := by
  classical
  have hd := hdel
  rw [guard_ldc_eq_abs host hpsi l r] at hd
  unfold absGuardLdc at hd
  have hf := hRF
  rw [guard_reservedFront_left_eq_abs host hpsi l r] at hf
  unfold absReservedFront at hf
  rcases hd with ⟨hIL, hHL⟩
  rcases hf with ⟨hRole, hPend⟩
  symm
  unfold B9RiskAbstraction.absRowB9
  split
  · split
    · exact q13868_wHoldRepair_phys (riskViewOf host hpsi l r)
    · rename_i hnot
      change ¬ ((decide
        ((riskViewOf host hpsi l r).left.spliceRole = SpliceRole.front) &&
        (riskViewOf host hpsi l r).left.repairPending) = true) at hnot
      have htrue :
          (decide
            ((riskViewOf host hpsi l r).left.spliceRole = SpliceRole.front) &&
            (riskViewOf host hpsi l r).left.repairPending) = true := by
        rw [hRole, hPend]
        rfl
      exact (hnot htrue).elim
  · rename_i hnot
    change ¬ (((riskViewOf host hpsi l r).inLeaderL &&
      !(riskViewOf host hpsi l r).hostLeaderL) = true) at hnot
    have htrue :
        ((riskViewOf host hpsi l r).inLeaderL &&
          !(riskViewOf host hpsi l r).hostLeaderL) = true := by
      rw [hIL, hHL]
      rfl
    exact (hnot htrue).elim


/-- Second top abstract branch: LDC + non-reserved-left is abstract HOST.
Again split the private selectors explicitly.  The selected `wDelete.phys`
is definitionally the observed HOST record, so that branch is `rfl`.
Sources: Leader/Wu/Splice/RiskAbstraction.lean:243-247,357-360,550-555;
`observedHostPhys`: Leader/Wu/Splice/RiskHostLeaf.lean:104-116. -/
theorem observedHostPhys_eq_absRowB9_of_ldc_not_reserved
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : Cell psi kappa tau)
    (hdel : ldc host l.carrier r.carrier)
    (hRF : ¬ ReservedFrontHoldGuard l.carrier) :
    observedHostPhys host hpsi l r =
      (absRowB9 (riskViewOf host hpsi l r)).phys := by
  classical
  have hd := hdel
  rw [guard_ldc_eq_abs host hpsi l r] at hd
  unfold absGuardLdc at hd
  have hf := hRF
  rw [guard_reservedFront_left_eq_abs host hpsi l r] at hf
  unfold absReservedFront at hf
  rcases hd with ⟨hIL, hHL⟩
  symm
  unfold B9RiskAbstraction.absRowB9
  split
  · split
    · rename_i hsel
      change ((decide
        ((riskViewOf host hpsi l r).left.spliceRole = SpliceRole.front) &&
        (riskViewOf host hpsi l r).left.repairPending) = true) at hsel
      have hbad :
          (riskViewOf host hpsi l r).left.spliceRole = SpliceRole.front ∧
            (riskViewOf host hpsi l r).left.repairPending = true := by
        simpa using hsel
      exact (hf hbad).elim
    · rfl
  · rename_i hnot
    change ¬ (((riskViewOf host hpsi l r).inLeaderL &&
      !(riskViewOf host hpsi l r).hostLeaderL) = true) at hnot
    have htrue :
        ((riskViewOf host hpsi l r).inLeaderL &&
          !(riskViewOf host hpsi l r).hostLeaderL) = true := by
      simp [hIL, hHL]
    exact (hnot htrue).elim

/-- First genuinely missing public seam after the two top LDC branches.
`row10gH_trichotomy` (Leader/Wu/Splice/HostTable.lean:550-565) gives only
KEEP/HOST/RELABEL; it does not identify the selected private abstract leaf.
The HOST alternative also carries exactly the follower/open domain required
by the compiled five-field theorem. -/
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


/-- R1 specialization of the original physical projection statement. -/
def R1ConcreteRowB9PhysicalProjectionObligation : Prop :=
  ∀ {psi kappa tau : Nat}
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Cell psi kappa tau),
    let host := r1Host (kappa := kappa) (tau := tau) hpsi h2
    let v := riskViewOf host hpsi l r
    let w := rowB9 host hpsi l r
    concreteOutPhys l r w.1 w.2 = (absRowB9 v).phys

/-- Branch-by-branch closure up to the unchanged `row10gH` residual.
The HOST residual alternative is closed by the compiled five-field theorem;
SpliceProjectionFacts comes from the three public projections in
Leader/Wu/Splice/RiskPhysicalObligation.lean:50-87. -/
theorem r1Host_concreteRowB9PhysicalProjection_of_leafIdentification
    (hLeaf : R1Row10gLeafIdentificationObligation) :
    R1ConcreteRowB9PhysicalProjectionObligation := by
  intro psi kappa tau hpsi h2 l r
  dsimp only
  let host : HostRow (Phys psi kappa tau) :=
    r1Host (kappa := kappa) (tau := tau) hpsi h2
  change
    concreteOutPhys l r (rowB9 host hpsi l r).1
        (rowB9 host hpsi l r).2 =
      (absRowB9 (riskViewOf host hpsi l r)).phys
  have hFacts : SpliceProjectionFacts host := by
    simpa [host] using
      (r1Host_spliceProjectionFacts (kappa := kappa) (tau := tau) hpsi h2)
  by_cases hdel : ldc host l.carrier r.carrier
  · by_cases hRF : ReservedFrontHoldGuard l.carrier
    · have hw : rowB9 host hpsi l r = holdRepairV10j l r := by
        simp [B9SpliceTableHost.rowB9, hdel, hRF]
      rw [hw]
      have hb := holdRepair_bases l r
      have hc := concreteOutPhys_keep host hpsi l r
        (holdRepairV10j l r).1 (holdRepairV10j l r).2 hb.1 hb.2
      exact hc.trans
        (inputPhys_eq_absRowB9_of_ldc_reserved
          host hpsi l r hdel hRF)
    · have hw : rowB9 host hpsi l r = deleteWriteH host l r := by
        simp [B9SpliceTableHost.rowB9, hdel, hRF]
      rw [hw]
      have hp :
          PhysRow host l r
            ((deleteWriteH host l r).1, (deleteWriteH host l r).2) := by
        simpa using (phys_delete host l r)
      have hc := concreteOutPhys_of_physRow host hpsi l r
        (deleteWriteH host l r).1 (deleteWriteH host l r).2 hp
      exact hc.trans
        (observedHostPhys_eq_absRowB9_of_ldc_not_reserved
          host hpsi l r hdel hRF)
  · have hw : rowB9 host hpsi l r = row10gH host hpsi l r := by
      simp [B9SpliceTableHost.rowB9, hdel]
    rw [hw]
    have hs := hLeaf (kappa := kappa) (tau := tau)
      hpsi h2 l r hFacts hdel
    rcases hs with hk | hh | hr
    · rcases hk with ⟨hL, hR, hAbs⟩
      exact (concreteOutPhys_keep host hpsi l r
        (row10gH host hpsi l r).1 (row10gH host hpsi l r).2
        hL hR).trans hAbs
    · rcases hh with ⟨hl, hr, hopen, hL, hR, hAbs⟩
      have hc := r1Host_host_leaf_phys_projection_from_five_fields
        (kappa := kappa) (tau := tau) hpsi h2 l r
        (row10gH host hpsi l r).1 (row10gH host hpsi l r).2
        hl hr hopen (by simpa [host] using hL) (by simpa [host] using hR)
      exact hc.trans hAbs
    · rcases hr with ⟨hL, hR, hAbs⟩
      exact (concreteOutPhys_relabel host hpsi l r
        (row10gH host hpsi l r).1 (row10gH host hpsi l r).2
        hL hR).trans hAbs

/-- Original-obligation shape, specialized to certified R1 host. -/
theorem r1Host_original_physical_projection_instance
    (hLeaf : R1Row10gLeafIdentificationObligation)
    {psi kappa tau : Nat}
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Cell psi kappa tau)
    (_hgeo : SpliceLaws
      (r1Host (kappa := kappa) (tau := tau) hpsi h2)) :
    let host := r1Host (kappa := kappa) (tau := tau) hpsi h2
    let v := riskViewOf host hpsi l r
    let w := rowB9 host hpsi l r
    concreteOutPhys l r w.1 w.2 = (absRowB9 v).phys := by
  exact r1Host_concreteRowB9PhysicalProjection_of_leafIdentification hLeaf
    hpsi h2 l r

end B9RiskRefinementPhys3
