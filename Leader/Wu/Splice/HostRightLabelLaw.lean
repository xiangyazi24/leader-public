import Leader.Wu.Splice.HostRightFollowerLabel


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9HostRightLabelLaw


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open B9Host B9SpliceTableHost B9RiskAbstraction


variable {psi kappa tau : Nat}

attribute [ext] B9RiskAbstraction.AbsPairPhys



/-- The true R1 right-label law on the ordinary-open follower/follower lane.


The extra left-follower and `PreparedOrdinaryOpen` premises are exactly the
domain of `B6LocalRulerE.r1_ordinary_label_or_leader`
(`Leader/Wu/Entrance/LocalRulerExceptional.lean:1013-1028`).  The open predicate is the exact
prepared deletion-priority gate (`Leader/Wu/Birth/ShortDoneTerminalOrdinaryLabel.lean:36-43`).
-/
def RightLabelLaw
    (hpsi : 0 < psi)
    (host : HostRow (Phys psi kappa tau)) : Prop :=
  ∀ l r : Phys psi kappa tau,
    leader l = false →
    leader r = false →
    BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi l r →
      let q := host.row l r
      leader q.1 = true ∨
        leader q.2 = true ∨
        label q.2 = B6LocalRuler.nextLabel hpsi (label l)


/-- Width-two R1 satisfies the true right-label law directly from the
exceptional-class theorem. -/
theorem r1Host_right_label_law
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) :
    RightLabelLaw hpsi
      (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2) := by
  intro l r hl hr hopen
  change l.core.core.leader = false at hl
  change r.core.core.leader = false at hr
  change
    (BirthCheckPermitRepair.row
        hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader = true ∨
      (BirthCheckPermitRepair.row
        hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader = true ∨
      (BirthCheckPermitRepair.row
        hpsi (by decide : 0 < 2) h2 l r).2.core.core.label =
        B6LocalRuler.nextLabel hpsi l.core.core.label
  have h := B6LocalRulerE.r1_ordinary_label_or_leader
    (kappa := kappa) (tau := tau)
    hpsi h2 l r hl hr hopen
  dsimp only at h
  rcases h with hL | hR | hlabels
  · exact Or.inl hL
  · exact Or.inr (Or.inl hR)
  · exact Or.inr (Or.inr hlabels.2)



/-- Corrected HOST-leaf physical summary, using no new RiskView coordinate.
On the no-birth ordinary-open lane, RightLabelLaw makes output-right equality
to the old responder equivalent to the old pair being aligned.  In a birth
case the true law intentionally says nothing about that equality, so retain
the already-observed host bit. -/
def absHostPhys (v : RiskView) : AbsPairPhys :=
  { leaderL := v.hostLeaderL
    leaderR := v.hostLeaderR
    aligned := v.alignedHost
    labelEqL := v.hostLabelEqL
    labelEqR :=
      if v.hostLeaderL || v.hostLeaderR then
        v.hostLabelEqR
      else
        v.alignedBefore }


/-- Eliminate the birth disjuncts when both selected HOST outputs are
followers. -/
theorem rightLabel_eq_next_of_no_output_leader
    (hpsi : 0 < psi)
    (host : HostRow (Phys psi kappa tau))
    (hLaw : RightLabelLaw hpsi host)
    (l r : Phys psi kappa tau)
    (hl : leader l = false) (hr : leader r = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi l r)
    (hOL : leader (host.row l r).1 = false)
    (hOR : leader (host.row l r).2 = false) :
    label (host.row l r).2 =
      B6LocalRuler.nextLabel hpsi (label l) := by
  have h := hLaw l r hl hr hopen
  dsimp only at h
  rcases h with hL | hR | hnext
  · rw [hOL] at hL
    cases hL
  · rw [hOR] at hR
    cases hR
  · exact hnext


/-- If the selected HOST responder has the ruler label, equality with the old
responder is exactly the old alignment predicate. -/
theorem rightLabel_eq_old_iff_aligned
    (hpsi : 0 < psi)
    (l r outR : Phys psi kappa tau)
    (hnext : label outR =
      B6LocalRuler.nextLabel hpsi (label l)) :
    label outR = label r ↔ B9Host.Aligned l r := by
  constructor
  · intro hEq
    unfold B9Host.Aligned
    have h := congrArg Fin.val (hEq.symm.trans hnext)
    simpa [B6LocalRuler.nextLabel] using h
  · intro hA
    have hR : label r =
        B6LocalRuler.nextLabel hpsi (label l) := by
      apply Fin.ext
      simpa [B9Host.Aligned, B6LocalRuler.nextLabel] using hA
    exact hnext.trans hR.symm


/-- Boolean form needed by AbsPairPhys: on the follower/follower no-birth
ordinary HOST leaf, concrete `labelEqR` is exactly `alignedBefore`. -/
theorem host_right_labelEqR_decide_eq_alignedBefore
    (hpsi : 0 < psi)
    (host : HostRow (Phys psi kappa tau))
    (hLaw : RightLabelLaw hpsi host)
    (l r : Phys psi kappa tau)
    (hl : leader l = false) (hr : leader r = false)
    (hopen : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi l r)
    (hOL : leader (host.row l r).1 = false)
    (hOR : leader (host.row l r).2 = false) :
    decide (label (host.row l r).2 = label r) =
      decide (B9Host.Aligned l r) := by
  have hnext := rightLabel_eq_next_of_no_output_leader
    hpsi host hLaw l r hl hr hopen hOL hOR
  have hiff := rightLabel_eq_old_iff_aligned
    hpsi l r (host.row l r).2 hnext
  by_cases hA : B9Host.Aligned l r
  · have hEq := hiff.mpr hA
    simp [hA, hEq]
  · have hNe : label (host.row l r).2 ≠ label r := by
      intro hEq
      exact hA (hiff.mp hEq)
    simp [hA, hNe]


theorem host_leaf_phys_projection
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
      absHostPhys (B9RiskAbstraction.riskViewOf host hpsi l r) := by
  classical
  unfold B9RiskAbstraction.concreteOutPhys absHostPhys
  unfold B9RiskAbstraction.riskViewOf
  dsimp only
  rw [hwL, hwR]
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
        simpa [hOL0, hOR0] using hEq


end B9HostRightLabelLaw


