import Leader.Wu.Splice.HoldRepairFirstRow
import Leader.Wu.Splice.HoldRepairGlobalProgress

set_option autoImplicit false
set_option Elab.async false

/-! # V10j with leaders: an amortized potential that every non-physical change lowers

The cell weight `cellWJ` (by role, pending bit and ticket: neutral 0; fence, settled unticketed predecessor and
settled unticketed front 1; pending unticketed predecessor and settled unticketed victim 3; every other shape 2)
and the edge bonus `bonusJ` (3 or 4 on a settled unticketed predecessor facing a reserved front, unticketed or
ticketed, across a prepared barrier) give

  `PsiJ C = Σ_i (cellWJ (C i) + (4 - bonusJ (C i) (C (i+1))))`,  with `PsiJ C ≤ 7 n`.

`row_amortized`: for a served pair whose cells satisfy the V7 ticket shape, the V10j row is physical, or leaves
the pair unchanged, or lowers the local potential of the pair strictly while never taking a reserved front off the
left cell or changing a settled unticketed predecessor on the right cell (so the two neighbouring edge bonuses do
not decrease).  `psiJ_drop`: on a ring with at least three sites, every V10j service from a `SpliceSafeV7g`
configuration that is not physical and changes the configuration lowers `PsiJ`.  `chain_length_le`: along any
word of such services the number of services is at most `PsiJ C ≤ 7 n`; so between two physical services a V10j
run makes at most `7 n` non-stutter services.  The weights were found by linear programming over the exhaustive
non-physical move census of `run/verification/probes/V10jFeatureDeltas.lean`. -/

namespace B9SpliceV10jAmortizedPotential

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j
  B9SpliceV10jHoldRing B9SpliceV10eRowPotential B9SpliceV10eHandoffFollowUp B9SpliceV10ePhysicalHoldNoBirth
  B9SpliceV10jRowProgress B9SpliceV10jFirstRow B9SpliceV10hControllerRowsSafe B9SpliceV10eTransparency

variable {psi width kappa tau : Nat}

/-! ## Weights -/

def cellTable : SpliceRole → Bool → Bool → Nat
  | .none, false, false => 0
  | .none, false, true => 1
  | .predecessorArmed, false, false => 1
  | .predecessorArmed, true, false => 3
  | .victimArmed, false, false => 3
  | .front, false, false => 1
  | _, _, _ => 2

def cellWJ (u : R1AgentStateV6 psi kappa tau) : Nat :=
  cellTable (role u.carrier) u.carrier.repairPending u.acquireTicket

/-- A settled unticketed predecessor. -/
def PAFF (u : R1AgentStateV6 psi kappa tau) : Prop :=
  role u.carrier = .predecessorArmed ∧ u.carrier.repairPending = false ∧ u.acquireTicket = false

noncomputable def bonusJ (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) : Nat := by
  classical
  exact if PAFF l ∧ ReservedFrontHoldGuard r.carrier ∧ LocalPreparedBarrier hpsi l.carrier r.carrier then
    (if r.acquireTicket = true then 4 else 3) else 0

/-- Local potential of a served pair: both cell weights and the served edge term. -/
noncomputable def LocalJ (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) : Nat :=
  cellWJ l + cellWJ r + (4 - bonusJ hpsi l r)

theorem cellWJ_le (u : R1AgentStateV6 psi kappa tau) : cellWJ u ≤ 3 := by
  unfold cellWJ
  cases role u.carrier <;> cases u.carrier.repairPending <;> cases u.acquireTicket <;> decide

theorem cellWJ_of (u : R1AgentStateV6 psi kappa tau) {x : SpliceRole} {p t : Bool}
    (h1 : role u.carrier = x) (h2 : u.carrier.repairPending = p) (h3 : u.acquireTicket = t) :
    cellWJ u = cellTable x p t := by
  unfold cellWJ; rw [h1, h2, h3]

theorem cellWJ_pos_of_role (u : R1AgentStateV6 psi kappa tau) (h : role u.carrier ≠ .none) : 1 ≤ cellWJ u := by
  unfold cellWJ
  cases hr : role u.carrier <;> cases u.carrier.repairPending <;> cases u.acquireTicket <;>
    first | decide | exact absurd hr h

theorem cellWJ_pos_of_pending (u : R1AgentStateV6 psi kappa tau) (h : u.carrier.repairPending = true) :
    1 ≤ cellWJ u := by
  unfold cellWJ
  rw [h]
  cases role u.carrier <;> cases u.acquireTicket <;> decide

theorem cellWJ_RF (u : R1AgentStateV6 psi kappa tau) (h : ReservedFrontHoldGuard u.carrier) : cellWJ u = 2 := by
  unfold cellWJ
  rw [h.1, h.2]
  cases u.acquireTicket <;> rfl

theorem cellWJ_clear (u : R1AgentStateV6 psi kappa tau) : cellWJ (clearControlV6 u) = 0 := rfl
theorem cellWJ_fence (u : R1AgentStateV6 psi kappa tau) : cellWJ (fenceV6 u) = 1 := rfl
theorem cellWJ_settle (u : R1AgentStateV6 psi kappa tau) : cellWJ (settleV6 u) = 1 := rfl

theorem bonusJ_le (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) : bonusJ hpsi l r ≤ 4 := by
  unfold bonusJ
  split
  · split <;> decide
  · decide

theorem bonusJ_left_zero (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) (h : ¬ PAFF l) :
    bonusJ hpsi l r = 0 := by
  unfold bonusJ
  rw [if_neg (fun hc => h hc.1)]

theorem bonusJ_right_zero (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau)
    (h : ¬ ReservedFrontHoldGuard r.carrier) : bonusJ hpsi l r = 0 := by
  unfold bonusJ
  rw [if_neg (fun hc => h hc.2.1)]

theorem not_PAFF_of_role (u : R1AgentStateV6 psi kappa tau) (h : role u.carrier ≠ .predecessorArmed) : ¬ PAFF u :=
  fun hc => h hc.1

theorem not_PAFF_of_pending (u : R1AgentStateV6 psi kappa tau) (h : u.carrier.repairPending = true) : ¬ PAFF u := by
  intro hc; rw [hc.2.1] at h; exact absurd h (by decide)

theorem not_RF_of_role (u : R1AgentStateV6 psi kappa tau) (h : role u.carrier ≠ .front) :
    ¬ ReservedFrontHoldGuard u.carrier := fun hc => h hc.1

theorem not_RF_of_settled (u : R1AgentStateV6 psi kappa tau) (h : u.carrier.repairPending = false) :
    ¬ ReservedFrontHoldGuard u.carrier := by
  intro hc; rw [hc.2] at h; exact absurd h (by decide)

theorem notPAFF_clear (u : R1AgentStateV6 psi kappa tau) : ¬ PAFF (clearControlV6 u) := fun h => by
  have h' : SpliceRole.none = .predecessorArmed := h.1
  cases h'

theorem notPAFF_fence (u : R1AgentStateV6 psi kappa tau) : ¬ PAFF (fenceV6 u) := fun h => by
  have h' : SpliceRole.none = .predecessorArmed := h.1
  cases h'

theorem notRF_clear (u : R1AgentStateV6 psi kappa tau) : ¬ ReservedFrontHoldGuard (clearControlV6 u).carrier :=
  fun h => by
    have h' : SpliceRole.none = .front := h.1
    cases h'

theorem notRF_fence (u : R1AgentStateV6 psi kappa tau) : ¬ ReservedFrontHoldGuard (fenceV6 u).carrier := fun h => by
  have h' : SpliceRole.none = .front := h.1
  cases h'

theorem notRF_settle (u : R1AgentStateV6 psi kappa tau) : ¬ ReservedFrontHoldGuard (settleV6 u).carrier := fun h => by
  have h' : SpliceRole.predecessorArmed = .front := h.1
  cases h'

theorem bonus_clear_right (hpsi : 0 < psi) (l u : R1AgentStateV6 psi kappa tau) :
    bonusJ hpsi l (clearControlV6 u) = 0 := bonusJ_right_zero hpsi l _ (notRF_clear u)

theorem bonus_fence_right (hpsi : 0 < psi) (l u : R1AgentStateV6 psi kappa tau) :
    bonusJ hpsi l (fenceV6 u) = 0 := bonusJ_right_zero hpsi l _ (notRF_fence u)

theorem bonus_settle_right (hpsi : 0 < psi) (l u : R1AgentStateV6 psi kappa tau) :
    bonusJ hpsi l (settleV6 u) = 0 := bonusJ_right_zero hpsi l _ (notRF_settle u)

theorem bonus_clear_left (hpsi : 0 < psi) (u r : R1AgentStateV6 psi kappa tau) :
    bonusJ hpsi (clearControlV6 u) r = 0 := bonusJ_left_zero hpsi _ r (notPAFF_clear u)

theorem bonus_fence_left (hpsi : 0 < psi) (u r : R1AgentStateV6 psi kappa tau) :
    bonusJ hpsi (fenceV6 u) r = 0 := bonusJ_left_zero hpsi _ r (notPAFF_fence u)

/-! ## Row outcome -/

def AmortOut (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) : Prop :=
  PhysRow hpsi hwidth hle l r w ∨ w = (l, r) ∨
  (LocalJ hpsi w.1 w.2 < LocalJ hpsi l r ∧
    (w.1 = l ∨ ¬ ReservedFrontHoldGuard l.carrier) ∧ (w.2 = r ∨ ¬ PAFF r))

theorem out_same (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) :
    AmortOut hpsi hwidth hle l r (l, r) := Or.inr (Or.inl rfl)

/-- A right-cell write with no bonus before or after. -/
theorem out_right (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r b : R1AgentStateV6 psi kappa tau)
    (hb0 : bonusJ hpsi l r = 0) (hb1 : bonusJ hpsi l b = 0) (hw : cellWJ b < cellWJ r) (hf : ¬ PAFF r) :
    AmortOut hpsi hwidth hle l r (l, b) := by
  right; right
  refine ⟨?_, Or.inl rfl, Or.inr hf⟩
  unfold LocalJ; dsimp only; rw [hb0, hb1]; omega

/-- A left-cell write with no bonus before or after. -/
theorem out_left (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r a : R1AgentStateV6 psi kappa tau)
    (hb0 : bonusJ hpsi l r = 0) (hb1 : bonusJ hpsi a r = 0) (hw : cellWJ a < cellWJ l)
    (hf : ¬ ReservedFrontHoldGuard l.carrier) :
    AmortOut hpsi hwidth hle l r (a, r) := by
  right; right
  refine ⟨?_, Or.inr hf, Or.inl rfl⟩
  unfold LocalJ; dsimp only; rw [hb0, hb1]; omega

/-- A two-cell write with no bonus before or after. -/
theorem out_pair (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r a b : R1AgentStateV6 psi kappa tau)
    (hb0 : bonusJ hpsi l r = 0) (hb1 : bonusJ hpsi a b = 0) (hw : cellWJ a + cellWJ b < cellWJ l + cellWJ r)
    (hf1 : ¬ ReservedFrontHoldGuard l.carrier) (hf2 : ¬ PAFF r) :
    AmortOut hpsi hwidth hle l r (a, b) := by
  right; right
  refine ⟨?_, Or.inr hf1, Or.inr hf2⟩
  unfold LocalJ; dsimp only; rw [hb0, hb1]; omega

/-! ## The stutter branch of `rowV10g` -/

theorem stutter_amortized (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (htr : TicketShapeV7 r)
    (hq : rowV10dg hpsi hwidth hle l r = (l, r)) :
    AmortOut hpsi hwidth hle l r (rowV10g hpsi hwidth hle l r) := by
  classical
  have hw := rowV10g.eq_1 hpsi hwidth hle l r
  dsimp only at hw
  rw [if_pos hq] at hw
  rw [hw]
  by_cases h0 : role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true
  · rw [if_pos h0]; exact out_same hpsi hwidth hle l r
  rw [if_neg h0]
  by_cases h1 : VictimRightScrubGuardV6 r
  · rw [if_pos h1]
    exact out_right hpsi hwidth hle l r _ (bonusJ_right_zero hpsi l r (not_RF_of_role r (by rw [h1.1]; decide)))
      (bonus_clear_right hpsi l r) (by rw [cellWJ_clear]; exact cellWJ_pos_of_role r (by rw [h1.1]; decide))
      (not_PAFF_of_role r (by rw [h1.1]; decide))
  rw [if_neg h1]
  by_cases h2 : FrontRightScrubGuardV6 r
  · rw [if_pos h2]
    exact out_right hpsi hwidth hle l r _ (bonusJ_right_zero hpsi l r (not_RF_of_settled r h2.2))
      (bonus_clear_right hpsi l r) (by rw [cellWJ_clear]; exact cellWJ_pos_of_role r (by rw [h2.1]; decide))
      (not_PAFF_of_role r (by rw [h2.1]; decide))
  rw [if_neg h2]
  by_cases h3 : MalformedRightPendingGuardV6 r
  · rw [if_pos h3]
    exact out_right hpsi hwidth hle l r _ (bonusJ_right_zero hpsi l r (not_RF_of_role r h3.2.2.1))
      (bonus_clear_right hpsi l r) (by rw [cellWJ_clear]; exact cellWJ_pos_of_pending r h3.1)
      (not_PAFF_of_pending r h3.1)
  rw [if_neg h3]
  by_cases h4 : role r.carrier = .predecessorArmed
  · rw [if_pos h4]
    by_cases h5 : r.carrier.repairPending = true
    · rw [if_pos h5]
      have hrt : r.acquireTicket = false :=
        ticket_false_of_shape r htr (by rw [h4]; decide) (by rw [h4]; decide)
      have hr3 : cellWJ r = 3 := by rw [cellWJ_of r h4 h5 hrt]; rfl
      have hbr : bonusJ hpsi l r = 0 := bonusJ_right_zero hpsi l r (not_RF_of_role r (by rw [h4]; decide))
      by_cases h6 : ReservedFrontHoldGuard l.carrier
      · rw [if_pos h6]
        exact out_right hpsi hwidth hle l r _ hbr (bonus_settle_right hpsi l r) (by rw [cellWJ_settle, hr3]; decide)
          (not_PAFF_of_pending r h5)
      rw [if_neg h6]
      by_cases h7 : LeftScrubGuardV10e l
      · rw [if_pos h7]
        refine out_left hpsi hwidth hle l r _ hbr (bonus_clear_left hpsi l r) ?_ h6
        rw [cellWJ_clear]
        rcases h7 with hv | hf | hm
        · exact cellWJ_pos_of_role l (by rw [hv.1]; decide)
        · exact cellWJ_pos_of_role l (by rw [hf.1]; decide)
        · exact cellWJ_pos_of_pending l hm.1
      rw [if_neg h7]
      exact out_same hpsi hwidth hle l r
    · rw [if_neg h5]
      left
      exact phys_fence hpsi hwidth hle l r
  · rw [if_neg h4]
    left
    exact phys_hold hpsi hwidth hle l r

/-! ## The V7 table under the V10j prefix guards -/

theorem rowV7_amortized (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (htl : TicketShapeV7 l) (htr : TicketShapeV7 r)
    (hdel : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice)
    (hD1 : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier)
    (hHO : ¬ HostFenceAdvanceGuardV10b hpsi l r) :
    AmortOut hpsi hwidth hle l r (rowV7 hpsi hwidth hle l r) := by
  classical
  have hw := rowV7.eq_1 hpsi hwidth hle l r
  rw [hw]
  by_cases hfL : HostFenceShapeV7 l
  · rw [if_pos hfL]
    by_cases hbar : LocalPreparedBarrier hpsi l.carrier r.carrier
    · rw [if_pos hbar]
      by_cases htc : HostFenceTargetClearV7 r
      · exact absurd ⟨hfL, hbar, htc⟩ hHO
      · rw [if_neg htc]; exact out_same hpsi hwidth hle l r
    · rw [if_neg hbar]
      show AmortOut hpsi hwidth hle l r (clearTicketV6 l, r)
      have hl1 : cellWJ l = 1 := by rw [cellWJ_of l hfL.1 hfL.2.1 hfL.2.2]; rfl
      have hl0 : cellWJ (clearTicketV6 l) = 0 := by
        rw [cellWJ_of (clearTicketV6 l) hfL.1 hfL.2.1 rfl]; rfl
      exact out_left hpsi hwidth hle l r _ (bonusJ_left_zero hpsi l r (not_PAFF_of_role l (by rw [hfL.1]; decide)))
        (bonusJ_left_zero hpsi _ r (not_PAFF_of_role (clearTicketV6 l)
          (by show role l.carrier ≠ SpliceRole.predecessorArmed; rw [hfL.1]; decide)))
        (by rw [hl1, hl0]; decide) (not_RF_of_role l (by rw [hfL.1]; decide))
  rw [if_neg hfL]
  by_cases hfR : HostFenceShapeV7 r
  · rw [if_pos hfR]; exact out_same hpsi hwidth hle l r
  rw [if_neg hfR]
  by_cases hmaf : MoveAcquireFrontGuardV6 hpsi l r
  · exact absurd ⟨hmaf.2.2.2.1, by rw [hmaf.1.1]; decide⟩ hD1
  rw [if_neg hmaf]
  by_cases hA : ArmAGuard hpsi hwidth hle l.carrier r.carrier
  · exact absurd hA.2.2.2.2 hdel
  rw [if_neg hA]
  by_cases hB : ArmBGuard l.carrier r.carrier
  · rw [if_pos hB]
    show AmortOut hpsi hwidth hle l r (setControlV6 l .predecessorArmed false, setControlV6 r .front false)
    have hlt : l.acquireTicket = false := by
      cases ht : l.acquireTicket
      · rfl
      · exact absurd ⟨hB.1, hB.2.1, ht⟩ hfL
    have hrt : r.acquireTicket = false :=
      ticket_false_of_shape r htr (by rw [hB.2.2.1]; decide) (by rw [hB.2.2.1]; decide)
    have hl0 : cellWJ l = 0 := by rw [cellWJ_of l hB.1 hB.2.1 hlt]; rfl
    have hr3 : cellWJ r = 3 := by rw [cellWJ_of r hB.2.2.1 hB.2.2.2.1 hrt]; rfl
    refine out_pair hpsi hwidth hle l r _ _ (bonusJ_left_zero hpsi l r (not_PAFF_of_role l (by rw [hB.1]; decide)))
      (bonusJ_right_zero hpsi _ _ (not_RF_of_settled _ rfl)) ?_ (not_RF_of_role l (by rw [hB.1]; decide))
      (not_PAFF_of_role r (by rw [hB.2.2.1]; decide))
    have ha1 : cellWJ (setControlV6 l .predecessorArmed false) = 1 := rfl
    have hb1 : cellWJ (setControlV6 r .front false) = 1 := rfl
    rw [hl0, hr3, ha1, hb1]; decide
  rw [if_neg hB]
  by_cases hDel : DeleteGuard hpsi hwidth hle l.carrier r.carrier
  · exact absurd hDel.2.2.2.2 hdel
  rw [if_neg hDel]
  by_cases hPH : PendingHoldGuard hpsi hwidth hle l.carrier r.carrier
  · exact absurd hPH.2.2.2.2 hdel
  rw [if_neg hPH]
  by_cases hPA : PendingAbortGuard hpsi hwidth hle l.carrier r.carrier
  · rw [if_pos hPA]
    show AmortOut hpsi hwidth hle l r (clearControlV6 l, clearControlV6 r)
    refine out_pair hpsi hwidth hle l r _ _ (bonusJ_left_zero hpsi l r (not_PAFF_of_role l (by rw [hPA.1]; decide)))
      (bonus_clear_left hpsi l _) ?_ (not_RF_of_role l (by rw [hPA.1]; decide)) (not_PAFF_of_role r (by rw [hPA.2.1]; decide))
    rw [cellWJ_clear, cellWJ_clear]
    have := cellWJ_pos_of_role l (by rw [hPA.1]; decide)
    omega
  rw [if_neg hPA]
  by_cases hMC : MoveCommitGuard l.carrier r.carrier
  · rw [if_pos hMC]
    show AmortOut hpsi hwidth hle l r (clearControlV6 l,
      withCarrierClearTicketV6 r (setControl (repairResponder hpsi l.carrier r.carrier) .predecessorArmed false))
    have hrt : r.acquireTicket = false :=
      ticket_false_of_shape r htr (by rw [hMC.2.2.1]; decide) (by rw [hMC.2.2.1]; decide)
    have hr3 : cellWJ r = 3 := by rw [cellWJ_of r hMC.2.2.1 hMC.2.2.2.1 hrt]; rfl
    refine out_pair hpsi hwidth hle l r _ _
      (bonusJ_right_zero hpsi l r (not_RF_of_role r (by rw [hMC.2.2.1]; decide)))
      (bonus_clear_left hpsi l _) ?_
      (not_RF_of_role l (by rw [hMC.1]; decide)) (not_PAFF_of_pending r hMC.2.2.2.1)
    have h1 : cellWJ (withCarrierClearTicketV6 r
        (setControl (repairResponder hpsi l.carrier r.carrier) .predecessorArmed false)) = 1 := rfl
    rw [cellWJ_clear, h1, hr3]
    omega
  rw [if_neg hMC]
  by_cases hMS : MoveStopGuardV3 hpsi l.carrier r.carrier
  · rw [if_pos hMS]
    have hb0 : bonusJ hpsi l r = 0 := by
      unfold bonusJ; rw [if_neg (fun hc => hMS.2.2.2 hc.2.2)]
    have hr2 := cellWJ_RF r hMS.2.2.1
    have hl1 := cellWJ_pos_of_role l (by rw [hMS.1]; decide)
    by_cases hjl : r.carrier.splice.base.core.core.leader = true
    · have hmw : moveStopWriteV6 l r = (clearControlV6 l, clearControlV6 r) := by
        unfold moveStopWriteV6; rw [if_pos hjl]
      rw [hmw]
      refine out_pair hpsi hwidth hle l r _ _ hb0 (bonus_clear_left hpsi l _) ?_ (not_RF_of_role l (by rw [hMS.1]; decide))
        (not_PAFF_of_role r (by rw [hMS.2.2.1.1]; decide))
      rw [cellWJ_clear, cellWJ_clear]; omega
    · have hmw : moveStopWriteV6 l r = (clearControlV6 l, clearTicketV6 r) := by
        unfold moveStopWriteV6; rw [if_neg hjl]
      rw [hmw]
      refine out_pair hpsi hwidth hle l r _ _ hb0 (bonus_clear_left hpsi l _) ?_
        (not_RF_of_role l (by rw [hMS.1]; decide)) (not_PAFF_of_role r (by rw [hMS.2.2.1.1]; decide))
      have hr2' : cellWJ (clearTicketV6 r) = 2 := cellWJ_RF (clearTicketV6 r) hMS.2.2.1
      rw [cellWJ_clear, hr2', hr2]; omega
  rw [if_neg hMS]
  by_cases hSK : MoveSeekGuardV3 hpsi l.carrier r.carrier
  · rw [if_pos hSK]
    cases ht : r.acquireTicket
    · show AmortOut hpsi hwidth hle l r (l, setTicketV6 r true)
      have hlt : l.acquireTicket = false :=
        ticket_false_of_shape l htl (by rw [hSK.1]; decide) (by rw [hSK.1]; decide)
      have hP : PAFF l := ⟨hSK.1, hSK.2.1, hlt⟩
      have hb0 : bonusJ hpsi l r = 3 := by
        unfold bonusJ; rw [if_pos ⟨hP, hSK.2.2.1, hSK.2.2.2⟩, ht]; try rfl
      have hb1 : bonusJ hpsi l (setTicketV6 r true) = 4 := by
        unfold bonusJ; rw [if_pos ⟨hP, hSK.2.2.1, hSK.2.2.2⟩]; try rfl
      right; right
      refine ⟨?_, Or.inl rfl, Or.inr (not_PAFF_of_role r (by rw [hSK.2.2.1.1]; decide))⟩
      unfold LocalJ; dsimp only
      rw [hb0, hb1, cellWJ_RF r hSK.2.2.1, cellWJ_RF (setTicketV6 r true) hSK.2.2.1]
      omega
    · show AmortOut hpsi hwidth hle l r (l, setTicketV6 r true)
      rw [setTicket_self r ht]; exact out_same hpsi hwidth hle l r
  rw [if_neg hSK]
  by_cases hSKH : MoveSeekHoldGuardV3 l.carrier r.carrier
  · rw [if_pos hSKH]; exact out_same hpsi hwidth hle l r
  rw [if_neg hSKH]
  by_cases hPOA : PendingOwnerAbortGuardV3 l.carrier r.carrier
  · rw [if_pos hPOA]
    show AmortOut hpsi hwidth hle l r (l, clearTicketV6 r)
    rw [clearTicket_self r (ticket_false_of_shape r htr (by rw [hPOA.1]; decide) (by rw [hPOA.1]; decide))]
    exact out_same hpsi hwidth hle l r
  rw [if_neg hPOA]
  by_cases hPP : role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true
  · rw [if_pos hPP]; exact out_same hpsi hwidth hle l r
  rw [if_neg hPP]
  by_cases hMAL : MoveAcquireLegacyGuardV6 l r
  · exact absurd ⟨hMAL.1.2.2.2, by rw [hMAL.1.1]; decide⟩ hD1
  rw [if_neg hMAL]
  by_cases hMAA : MoveAcquireAbortGuardV3 l.carrier r.carrier
  · rw [if_pos hMAA]
    show AmortOut hpsi hwidth hle l r (clearTicketV6 l, r)
    rw [clearTicket_self l (ticket_false_of_shape l htl (by rw [hMAA.1]; decide) (by rw [hMAA.1]; decide))]
    exact out_same hpsi hwidth hle l r
  rw [if_neg hMAA]
  by_cases hORF : OrphanReservedFrontGuardV3 l.carrier r.carrier
  · exact absurd hORF hD1
  rw [if_neg hORF]
  by_cases hRFH : ReservedFrontHoldGuard l.carrier
  · rw [if_pos hRFH]; exact out_same hpsi hwidth hle l r
  rw [if_neg hRFH]
  by_cases hVR : VictimRightScrubGuardV6 r
  · rw [if_pos hVR]
    show AmortOut hpsi hwidth hle l r (l, clearControlV6 r)
    exact out_right hpsi hwidth hle l r _ (bonusJ_right_zero hpsi l r (not_RF_of_role r (by rw [hVR.1]; decide)))
      (bonus_clear_right hpsi l r) (by rw [cellWJ_clear]; exact cellWJ_pos_of_role r (by rw [hVR.1]; decide))
      (not_PAFF_of_role r (by rw [hVR.1]; decide))
  rw [if_neg hVR]
  by_cases hVL : VictimLeftScrubGuardV6 l
  · rw [if_pos hVL]
    show AmortOut hpsi hwidth hle l r (clearControlV6 l, r)
    exact out_left hpsi hwidth hle l r _ (bonusJ_left_zero hpsi l r (not_PAFF_of_role l (by rw [hVL.1]; decide)))
      (bonus_clear_left hpsi l r)
      (by rw [cellWJ_clear]; exact cellWJ_pos_of_role l (by rw [hVL.1]; decide))
      (not_RF_of_role l (by rw [hVL.1]; decide))
  rw [if_neg hVL]
  by_cases hFR : FrontRightScrubGuardV6 r
  · rw [if_pos hFR]
    show AmortOut hpsi hwidth hle l r (l, clearControlV6 r)
    exact out_right hpsi hwidth hle l r _ (bonusJ_right_zero hpsi l r (not_RF_of_settled r hFR.2))
      (bonus_clear_right hpsi l r) (by rw [cellWJ_clear]; exact cellWJ_pos_of_role r (by rw [hFR.1]; decide))
      (not_PAFF_of_role r (by rw [hFR.1]; decide))
  rw [if_neg hFR]
  by_cases hML : MalformedLeftPendingGuardV6 l
  · rw [if_pos hML]
    show AmortOut hpsi hwidth hle l r (clearPendingV6 l, r)
    have hnone : role l.carrier = .none :=
      B9SpliceV10cWholeStepLeaderless.role_none_of_not _ hML.2.1 hML.2.2.1 hML.2.2.2
    rw [B9SpliceV10cRowCertFreeLeft.clearPending_eq_clearControl l hnone]
    exact out_left hpsi hwidth hle l r _ (bonusJ_left_zero hpsi l r (not_PAFF_of_role l (by rw [hnone]; decide)))
      (bonus_clear_left hpsi l r)
      (by rw [cellWJ_clear]; exact cellWJ_pos_of_pending l hML.1)
      (not_RF_of_role l (by rw [hnone]; decide))
  rw [if_neg hML]
  by_cases hMR : MalformedRightPendingGuardV6 r
  · rw [if_pos hMR]
    show AmortOut hpsi hwidth hle l r (l, clearPendingV6 r)
    have hnone : role r.carrier = .none :=
      B9SpliceV10cWholeStepLeaderless.role_none_of_not _ hMR.2.1 hMR.2.2.1 hMR.2.2.2
    rw [B9SpliceV10cRowCertFreeLeft.clearPending_eq_clearControl r hnone]
    exact out_right hpsi hwidth hle l r _ (bonusJ_right_zero hpsi l r (not_RF_of_role r (by rw [hnone]; decide)))
      (bonus_clear_right hpsi l r) (by rw [cellWJ_clear]; exact cellWJ_pos_of_pending r hMR.1)
      (not_PAFF_of_pending r hMR.1)
  rw [if_neg hMR]
  by_cases hpl : role l.carrier = .predecessorArmed
  · rw [if_pos hpl]
    show AmortOut hpsi hwidth hle l r (clearControlV6 l, r)
    have hlp : l.carrier.repairPending = false := by
      cases hp : l.carrier.repairPending
      · rfl
      · exact absurd ⟨hpl, hp⟩ hPP
    have hnRF : ¬ ReservedFrontHoldGuard r.carrier := by
      intro hrf
      by_cases hb : LocalPreparedBarrier hpsi l.carrier r.carrier
      · exact hSK ⟨hpl, hlp, hrf, hb⟩
      · exact hMS ⟨hpl, hlp, hrf, hb⟩
    exact out_left hpsi hwidth hle l r _ (bonusJ_right_zero hpsi l r hnRF) (bonusJ_right_zero hpsi _ r hnRF)
      (by rw [cellWJ_clear]; exact cellWJ_pos_of_role l (by rw [hpl]; decide))
      (not_RF_of_role l (by rw [hpl]; decide))
  rw [if_neg hpl]
  by_cases hlf : role l.carrier = .front
  · rw [if_pos hlf]; exact out_same hpsi hwidth hle l r
  rw [if_neg hlf]
  by_cases hmk : MarkedHoldGuardV6 l r
  · rw [if_pos hmk]; exact out_same hpsi hwidth hle l r
  rw [if_neg hmk]
  left
  exact phys_ordinary hpsi hwidth hle l r

/-! ## The non-stutter branch of `rowV10g` -/

theorem nonstutter_amortized (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (htl : TicketShapeV7 l) (htr : TicketShapeV7 r)
    (hdel : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice)
    (hq : rowV10dg hpsi hwidth hle l r ≠ (l, r)) :
    AmortOut hpsi hwidth hle l r (rowV10dg hpsi hwidth hle l r) := by
  classical
  have hd := rowV10dg.eq_1 hpsi hwidth hle l r
  by_cases hD1 : OrphanReservedFrontGuardV3 l.carrier r.carrier
  · rw [hd, if_pos hD1]
    exact out_right hpsi hwidth hle l r _ (bonusJ_left_zero hpsi l r (not_PAFF_of_role l hD1.2))
      (bonusJ_left_zero hpsi l _ (not_PAFF_of_role l hD1.2))
      (by rw [cellWJ_fence, cellWJ_RF r hD1.1]; decide) (not_PAFF_of_role r (by rw [hD1.1.1]; decide))
  rw [if_neg hD1] at hd
  by_cases hD2 : OrphanVictimGuard l r
  · rw [hd, if_pos hD2]
    exact out_right hpsi hwidth hle l r _ (bonusJ_right_zero hpsi l r (not_RF_of_role r (by rw [hD2.1]; decide)))
      (bonus_clear_right hpsi l r) (by rw [cellWJ_clear]; exact cellWJ_pos_of_role r (by rw [hD2.1]; decide))
      (not_PAFF_of_role r (by rw [hD2.1]; decide))
  rw [if_neg hD2] at hd
  by_cases hD3 : OwnedPendingVictimGuard l r
  · rw [hd, if_pos hD3]
    have hlt : l.acquireTicket = false :=
      ticket_false_of_shape l htl (by rw [hD3.1]; decide) (by rw [hD3.1]; decide)
    have hrt : r.acquireTicket = false :=
      ticket_false_of_shape r htr (by rw [hD3.2.2.1]; decide) (by rw [hD3.2.2.1]; decide)
    have hl1 : cellWJ l = 1 := by rw [cellWJ_of l hD3.1 hD3.2.1 hlt]; rfl
    have hr2 : cellWJ r = 2 := by rw [cellWJ_of r hD3.2.2.1 hD3.2.2.2 hrt]; rfl
    refine out_pair hpsi hwidth hle l r _ _
      (bonusJ_right_zero hpsi l r (not_RF_of_role r (by rw [hD3.2.2.1]; decide)))
      (bonus_fence_left hpsi l _) ?_
      (not_RF_of_role l (by rw [hD3.1]; decide)) (not_PAFF_of_role r (by rw [hD3.2.2.1]; decide))
    rw [cellWJ_fence, cellWJ_fence, hl1, hr2]; decide
  rw [if_neg hD3] at hd
  by_cases hD4 : OwnerlessPendingPredGuard l r
  · rw [hd, if_pos hD4]
    have hrt : r.acquireTicket = false :=
      ticket_false_of_shape r htr (by rw [hD4.2.1]; decide) (by rw [hD4.2.1]; decide)
    have hr3 : cellWJ r = 3 := by rw [cellWJ_of r hD4.2.1 hD4.2.2 hrt]; rfl
    refine out_pair hpsi hwidth hle l r _ _
      (bonusJ_left_zero hpsi l r (not_PAFF_of_role l (by rw [hD4.1]; decide)))
      (bonus_fence_left hpsi l _) ?_
      (not_RF_of_role l (by rw [hD4.1]; decide)) (not_PAFF_of_pending r hD4.2.2)
    rw [cellWJ_fence, cellWJ_settle, hr3]; omega
  rw [if_neg hD4] at hd
  rw [hd]
  rw [hd] at hq
  have hc := rowV10c.eq_1 hpsi hwidth hle l r
  by_cases hZR : ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r
  · rw [if_pos hZR] at hc; exact absurd hc hq
  rw [if_neg hZR] at hc
  rw [hc]
  have hb := rowV10b.eq_1 hpsi hwidth hle l r
  by_cases hHO : HostFenceAdvanceGuardV10b hpsi l r
  · rw [hb, if_pos hHO]
    show AmortOut hpsi hwidth hle l r (setControlV6 l .predecessorArmed false, setControlV6 r .front true)
    have hl1 : cellWJ l = 1 := by rw [cellWJ_of l hHO.1.1 hHO.1.2.1 hHO.1.2.2]; rfl
    have hr1 : cellWJ r ≤ 1 := by
      unfold cellWJ; rw [hHO.2.2.1, hHO.2.2.2]; cases r.acquireTicket <;> decide
    have hb0 : bonusJ hpsi l r = 0 := bonusJ_left_zero hpsi l r (not_PAFF_of_role l (by rw [hHO.1.1]; decide))
    have hb1 : bonusJ hpsi (setControlV6 l .predecessorArmed false) (setControlV6 r .front true) = 3 := by
      unfold bonusJ
      rw [if_pos ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, hHO.2.1⟩]
      try rfl
    right; right
    refine ⟨?_, Or.inr (not_RF_of_role l (by rw [hHO.1.1]; decide)),
      Or.inr (not_PAFF_of_role r (by rw [hHO.2.2.1]; decide))⟩
    unfold LocalJ; dsimp only
    have h1 : cellWJ (setControlV6 l .predecessorArmed false) = 1 := rfl
    have h2 : cellWJ (setControlV6 r .front true) = 2 := rfl
    rw [hb0, hb1, h1, h2, hl1]
    omega
  rw [if_neg hHO] at hb
  rw [hb]
  rw [hc, hb] at hq
  have h9 := rowV9.eq_1 hpsi hwidth hle l r
  by_cases hBF : HostFenceBusyFrontGuardV9 hpsi l r
  · exact absurd ⟨hBF.2.2, by rw [hBF.1.1]; decide⟩ hD1
  rw [if_neg hBF] at h9
  rw [h9]
  rw [h9] at hq
  have h8 := rowV8.eq_1 hpsi hwidth hle l r
  by_cases hSP8 : RightStalePredecessorHoldGuardV8 l r
  · rw [if_pos hSP8] at h8; exact absurd h8 hq
  rw [if_neg hSP8] at h8
  rw [h8]
  exact rowV7_amortized hpsi hwidth hle l r htl htr hdel hD1 hHO

/-! ## The whole V10j row -/

theorem row_amortized (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (htl : TicketShapeV7 l) (htr : TicketShapeV7 r) :
    AmortOut hpsi hwidth hle l r (rowV10j hpsi hwidth hle l r) := by
  classical
  rw [rowV10j.eq_1]
  by_cases hd : LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice
  · rw [if_pos hd]
    by_cases hrf : ReservedFrontHoldGuard l.carrier
    · rw [if_pos hrf, holdRepairV10j.eq_1]
      have hbl : ∀ b : R1AgentStateV6 psi kappa tau, bonusJ hpsi l b = 0 :=
        fun b => bonusJ_left_zero hpsi l b (not_PAFF_of_role l (by rw [hrf.1]; decide))
      by_cases h1 : ReservedFrontHoldGuard r.carrier
      · rw [if_pos h1]
        exact out_right hpsi hwidth hle l r _ (hbl r) (hbl _) (by rw [cellWJ_fence, cellWJ_RF r h1]; decide)
          (not_PAFF_of_role r (by rw [h1.1]; decide))
      rw [if_neg h1]
      by_cases h2 : role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true
      · rw [if_pos h2]
        have hrt : r.acquireTicket = false :=
          ticket_false_of_shape r htr (by rw [h2.1]; decide) (by rw [h2.1]; decide)
        have hr3 : cellWJ r = 3 := by rw [cellWJ_of r h2.1 h2.2 hrt]; rfl
        exact out_right hpsi hwidth hle l r _ (hbl r) (hbl _) (by rw [cellWJ_settle, hr3]; decide)
          (not_PAFF_of_pending r h2.2)
      rw [if_neg h2]
      by_cases h3 : role r.carrier = .victimArmed ∧ r.carrier.repairPending = true
      · rw [if_pos h3]
        exact out_right hpsi hwidth hle l r _ (hbl r) (hbl _)
          (by rw [cellWJ_clear]; exact cellWJ_pos_of_role r (by rw [h3.1]; decide))
          (not_PAFF_of_role r (by rw [h3.1]; decide))
      rw [if_neg h3]
      by_cases h4 : VictimRightScrubGuardV6 r ∨ FrontRightScrubGuardV6 r ∨ MalformedRightPendingGuardV6 r
      · rw [if_pos h4]
        rcases h4 with hv | hf | hm
        · exact out_right hpsi hwidth hle l r _ (hbl r) (hbl _)
            (by rw [cellWJ_clear]; exact cellWJ_pos_of_role r (by rw [hv.1]; decide))
            (not_PAFF_of_role r (by rw [hv.1]; decide))
        · exact out_right hpsi hwidth hle l r _ (hbl r) (hbl _)
            (by rw [cellWJ_clear]; exact cellWJ_pos_of_role r (by rw [hf.1]; decide))
            (not_PAFF_of_role r (by rw [hf.1]; decide))
        · exact out_right hpsi hwidth hle l r _ (hbl r) (hbl _)
            (by rw [cellWJ_clear]; exact cellWJ_pos_of_pending r hm.1)
            (not_PAFF_of_pending r hm.1)
      rw [if_neg h4]
      exact out_same hpsi hwidth hle l r
    · rw [if_neg hrf]
      left
      exact phys_delete hpsi hwidth hle l r
  · rw [if_neg hd]
    by_cases hq : rowV10dg hpsi hwidth hle l r = (l, r)
    · exact stutter_amortized hpsi hwidth hle l r htr hq
    · rw [rowV10g_of_change hpsi hwidth hle l r hq]
      exact nonstutter_amortized hpsi hwidth hle l r htl htr hd hq

end B9SpliceV10jAmortizedPotential
