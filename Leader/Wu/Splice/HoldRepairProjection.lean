import Leader.Wu.Splice.HoldRepairRowVocabulary
import Leader.Wu.Splice.HoldRepairGlobalProgress

set_option autoImplicit false
set_option Elab.async false

/-! # V10j row trichotomy on physical bases, with or without leaders

Every V10j row leaves both physical bases unchanged, or is physical (both bases take the host row), or is a
relabel (the left base is unchanged and the right base is `repairResponder` of the pair: MOVE-COMMIT, and the
dead V9 busy-front repair) (`rowV10j_trichotomy`).  No hypothesis on leaders, roles or safety.  A relabel keeps
both leader bits (`relabel_leader`), so a V10j service changes the leader bits only when it is physical
(`rowV10j_leaders_of_not_physical`). -/

namespace B9SpliceV10jProjection

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j
  B9SpliceV10jRowProgress

variable {psi width kappa tau : Nat}

/-- Base effect of a candidate write `w` on the pair `(l, r)`. -/
def TriRow (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) : Prop :=
  (w.1.carrier.splice.base = l.carrier.splice.base ∧ w.2.carrier.splice.base = r.carrier.splice.base) ∨
  PhysRow hpsi hwidth hle l r w ∨
  (w.1.carrier.splice.base = l.carrier.splice.base ∧
    w.2.carrier.splice.base = (repairResponder hpsi l.carrier r.carrier).splice.base)

theorem tri_keep (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau)
    (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau)
    (h1 : w.1.carrier.splice.base = l.carrier.splice.base) (h2 : w.2.carrier.splice.base = r.carrier.splice.base) :
    TriRow hpsi hwidth hle l r w := Or.inl ⟨h1, h2⟩

theorem tri_relabel (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau)
    (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau)
    (h1 : w.1.carrier.splice.base = l.carrier.splice.base)
    (h2 : w.2.carrier.splice.base = (repairResponder hpsi l.carrier r.carrier).splice.base) :
    TriRow hpsi hwidth hle l r w := Or.inr (Or.inr ⟨h1, h2⟩)

theorem tri_ite (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau)
    (c : Prop) [Decidable c] (a b : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau)
    (ha : TriRow hpsi hwidth hle l r a) (hb : TriRow hpsi hwidth hle l r b) :
    TriRow hpsi hwidth hle l r (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem rowV7_tri (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) :
    TriRow hpsi hwidth hle l r (rowV7 hpsi hwidth hle l r) := by
  classical
  unfold rowV7
  repeat' apply tri_ite
  all_goals first
    | exact tri_keep hpsi hwidth hle l r _ rfl rfl
    | exact tri_relabel hpsi hwidth hle l r _ rfl rfl
    | exact Or.inr (Or.inl (phys_ordinary hpsi hwidth hle l r))
    | exact Or.inr (Or.inl (phys_delete hpsi hwidth hle l r))
    | (unfold moveStopWriteV6; apply tri_ite <;> exact tri_keep hpsi hwidth hle l r _ rfl rfl)

theorem rowV10dg_tri (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) :
    TriRow hpsi hwidth hle l r (rowV10dg hpsi hwidth hle l r) := by
  classical
  unfold rowV10dg rowV10c rowV10b rowV9 rowV8
  repeat' apply tri_ite
  all_goals first
    | exact tri_keep hpsi hwidth hle l r _ rfl rfl
    | exact tri_relabel hpsi hwidth hle l r _ rfl rfl
    | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | (unfold moveStopWriteV6; apply tri_ite <;> exact tri_keep hpsi hwidth hle l r _ rfl rfl)

theorem rowV10g_tri (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) :
    TriRow hpsi hwidth hle l r (rowV10g hpsi hwidth hle l r) := by
  classical
  have hw := rowV10g.eq_1 hpsi hwidth hle l r
  dsimp only at hw
  rw [hw]
  by_cases hq : rowV10dg hpsi hwidth hle l r = (l, r)
  · rw [if_pos hq]
    repeat' apply tri_ite
    all_goals first
      | exact tri_keep hpsi hwidth hle l r _ rfl rfl
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rw [if_neg hq]
    exact rowV10dg_tri hpsi hwidth hle l r

theorem rowV10j_trichotomy (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) :
    TriRow hpsi hwidth hle l r (rowV10j hpsi hwidth hle l r) := by
  classical
  rw [rowV10j.eq_1]
  by_cases hd : LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice
  · rw [if_pos hd]
    by_cases hrf : ReservedFrontHoldGuard l.carrier
    · rw [if_pos hrf, holdRepairV10j.eq_1]
      repeat' apply tri_ite
      all_goals exact tri_keep hpsi hwidth hle l r _ rfl rfl
    · rw [if_neg hrf]
      exact Or.inr (Or.inl (phys_delete hpsi hwidth hle l r))
  · rw [if_neg hd]
    exact rowV10g_tri hpsi hwidth hle l r

/-- A relabel keeps both leader bits. -/
theorem relabel_leader (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    (repairResponder hpsi l.carrier r.carrier).splice.base.core.core.leader = r.carrier.splice.base.core.core.leader := rfl

/-- Outside physical services a V10j row keeps both leader bits. -/
theorem rowV10j_leaders_of_not_physical (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hnp : ¬ PhysRow hpsi hwidth hle l r (rowV10j hpsi hwidth hle l r)) :
    (rowV10j hpsi hwidth hle l r).1.carrier.splice.base.core.core.leader = l.carrier.splice.base.core.core.leader ∧
    (rowV10j hpsi hwidth hle l r).2.carrier.splice.base.core.core.leader = r.carrier.splice.base.core.core.leader := by
  rcases rowV10j_trichotomy hpsi hwidth hle l r with ⟨h1, h2⟩ | hp | ⟨h1, h2⟩
  · rw [h1, h2]; exact ⟨rfl, rfl⟩
  · exact absurd hp hnp
  · rw [h1, h2]; exact ⟨rfl, rfl⟩

/-- Configuration level: a V10j service that is not physical keeps every leader bit, so births and deletions
of leaders happen only at physical services. -/
theorem stepV10j_leaders_of_not_physical {n : Nat} (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hnp : ¬ B9SpliceV10eTransparency.PhysicalServiceAt hpsi hwidth hle ring C
      (stepV10j hpsi hwidth hle ring C e) e) (i : Fin n) :
    (stepV10j hpsi hwidth hle ring C e i).carrier.splice.base.core.core.leader =
      (C i).carrier.splice.base.core.core.leader := by
  classical
  by_cases hself : ring.rightNeighbor e = e
  · unfold stepV10j; rw [if_pos hself]
  have hstep : stepV10j hpsi hwidth hle ring C e =
      B9SpliceV10hControllerRowsSafe.writeAt ring C e (rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) := by
    unfold stepV10j; rw [if_neg hself]
  have hrow : ¬ PhysRow hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
      (rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) := by
    intro hp
    apply hnp
    rw [hstep]
    have hw := B9SpliceV10jGlobalProgress.physical_of_row hpsi hwidth hle ring C e hself
      (C e, C (ring.rightNeighbor e)) (rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) hp
    rw [B9SpliceV10hWholeStepSafe.writeAt_self] at hw
    exact hw
  obtain ⟨h1, h2⟩ := rowV10j_leaders_of_not_physical hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) hrow
  rw [hstep]
  by_cases hie : i = e
  · rw [hie, B9SpliceV10hControllerRowsSafe.writeAt_e]; exact h1
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij, B9SpliceV10hControllerRowsSafe.writeAt_j ring C e _ hself]; exact h2
    · rw [B9SpliceV10hControllerRowsSafe.writeAt_other ring C e _ i hie hij]

end B9SpliceV10jProjection
