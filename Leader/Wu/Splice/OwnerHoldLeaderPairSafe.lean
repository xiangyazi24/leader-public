import Leader.Wu.Splice.CertifiedDeleteSafe
import Leader.Wu.Birth.ShortDoneTerminalRowRightLeader
import Leader.Wu.Splice.PhysicalHoldBirthSafe
import Leader.Wu.Splice.PhysicalHoldNoBirthSafe

set_option autoImplicit false

/-! # The physical hold with a leader present preserves `SpliceSafeV7g`

`physHoldAt ring C e` performs `physicalHoldV6` on the served pair (both bases take the terminal host row,
every controller field is kept, a relabelled neutral right follower gets a host-fence ticket).
`physHoldAt_preserves_spliceSafeV7g_leader`: if `C` is `SpliceSafeV7g`, one served cell is a leader, a left
leader is not deleted by the row, and the right cell is neutral-unpending or a reserved front (the shapes on
which V10e/V10h run the plain physical hold), then `physHoldAt C e` is `SpliceSafeV7g`.

* a surviving left leader makes the incoming and served edges non-dangerous; a right leader survives the
  row (`row_right_leader`) and makes the served and outgoing edges non-dangerous;
* with a left follower, its label is unchanged (`left_follower_label_frame`), so the incoming edge keeps its
  danger status and, the controllers being unchanged, its protection;
* on the outgoing edge of a right follower: a relabelled neutral follower becomes a host fence; a reserved
  front protects its outgoing edge; an unrelabelled neutral follower keeps its label and hence the old danger
  status and protection. -/

namespace B9SpliceV10hPhysicalHoldLeaderSafe

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g B9SpliceCertifiedDelete
  B9SpliceV10ePhysicalHoldNoBirth

variable {n psi kappa tau width : Nat}

def physHoldAt (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  let w := physicalHoldV6 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  fun i => if i = e then w.1 else if i = ring.rightNeighbor e then w.2 else C i

section Fields

variable (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau)

abbrev hostOut := BirthShortDoneTerminalHost.row hpsi hwidth hle l.carrier.splice.base r.carrier.splice.base

theorem ph1_base : (physicalHoldV6 hpsi hwidth hle l r).1.carrier.splice.base = (hostOut hpsi hwidth hle l r).1 := by
  unfold physicalHoldV6; dsimp only; split <;> rfl
theorem ph1_role : role (physicalHoldV6 hpsi hwidth hle l r).1.carrier = role l.carrier := by
  unfold physicalHoldV6; dsimp only; split <;> rfl
theorem ph1_pending : (physicalHoldV6 hpsi hwidth hle l r).1.carrier.repairPending = l.carrier.repairPending := by
  unfold physicalHoldV6; dsimp only; split <;> rfl
theorem ph1_ticket : (physicalHoldV6 hpsi hwidth hle l r).1.acquireTicket = l.acquireTicket := by
  unfold physicalHoldV6; dsimp only; split <;> rfl
theorem ph2_base : (physicalHoldV6 hpsi hwidth hle l r).2.carrier.splice.base = (hostOut hpsi hwidth hle l r).2 := by
  unfold physicalHoldV6; dsimp only; split <;> rfl
theorem ph2_role : role (physicalHoldV6 hpsi hwidth hle l r).2.carrier = role r.carrier := by
  unfold physicalHoldV6; dsimp only; split <;> rfl
theorem ph2_pending : (physicalHoldV6 hpsi hwidth hle l r).2.carrier.repairPending = r.carrier.repairPending := by
  unfold physicalHoldV6; dsimp only; split <;> rfl

/-- The right ticket either is kept or becomes true on a relabelled neutral unpending follower. -/
theorem ph2_ticket_cases :
    ((physicalHoldV6 hpsi hwidth hle l r).2.acquireTicket = r.acquireTicket ∧
        ¬ (role r.carrier = .none ∧ r.carrier.repairPending = false ∧
          (hostOut hpsi hwidth hle l r).2.core.core.leader = false ∧
          (hostOut hpsi hwidth hle l r).2.core.core.label ≠ r.carrier.splice.base.core.core.label)) ∨
      ((physicalHoldV6 hpsi hwidth hle l r).2.acquireTicket = true ∧
        role r.carrier = .none ∧ r.carrier.repairPending = false ∧
        (hostOut hpsi hwidth hle l r).2.core.core.leader = false) := by
  unfold physicalHoldV6
  dsimp only
  split
  · rename_i h
    unfold rightFollowerRelabelledV7 at h
    simp only [decide_eq_true_eq] at h
    exact Or.inr ⟨rfl, h.1, h.2.1, h.2.2.1⟩
  · rename_i h
    unfold rightFollowerRelabelledV7 at h
    simp only [decide_eq_true_eq] at h
    exact Or.inl ⟨rfl, h⟩

end Fields

/-- Protection depends only on the roles, pending bits and tickets of the two cells. -/
theorem protected_congr_ctrl (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau) (x : Fin n)
    (hr1 : role (D x).carrier = role (C x).carrier)
    (hp1 : (D x).carrier.repairPending = (C x).carrier.repairPending)
    (ht1 : (D x).acquireTicket = (C x).acquireTicket)
    (hr2 : role (D (ring.rightNeighbor x)).carrier = role (C (ring.rightNeighbor x)).carrier)
    (hp2 : (D (ring.rightNeighbor x)).carrier.repairPending = (C (ring.rightNeighbor x)).carrier.repairPending)
    (ht2 : (D (ring.rightNeighbor x)).acquireTicket = (C (ring.rightNeighbor x)).acquireTicket) :
    ProtectedSpliceEdgeV7g ring D x ↔ ProtectedSpliceEdgeV7g ring C x := by
  unfold ProtectedSpliceEdgeV7g ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 HostFenceShapeV7
    PendingOwnerHoldShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only
  rw [hr1, hp1, ht1, hr2, hp2, ht2]

theorem ticketShape_congr (u v : R1AgentStateV6 psi kappa tau)
    (hr : role u.carrier = role v.carrier) (hp : u.carrier.repairPending = v.carrier.repairPending)
    (ht : u.acquireTicket = v.acquireTicket) : TicketShapeV7 u ↔ TicketShapeV7 v := by
  unfold TicketShapeV7 ReservedFrontHoldGuard HostFenceShapeV7
  rw [hr, hp, ht]

theorem physHoldAt_preserves_spliceSafeV7g_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hlead : (C e).carrier.splice.base.core.core.leader = true ∨
      (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = true)
    (hkeep : (C e).carrier.splice.base.core.core.leader = true →
      (hostOut hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).1.core.core.leader = true)
    (hrshape : (role (C (ring.rightNeighbor e)).carrier = .none ∧
        (C (ring.rightNeighbor e)).carrier.repairPending = false) ∨
      ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7g hpsi ring (physHoldAt hpsi hwidth hle ring C e) := by
  classical
  let j := ring.rightNeighbor e
  let D := physHoldAt hpsi hwidth hle ring C e
  have hDe : D e = (physicalHoldV6 hpsi hwidth hle (C e) (C j)).1 := by simp [D, j, physHoldAt]
  have hDj : D j = (physicalHoldV6 hpsi hwidth hle (C e) (C j)).2 := by simp [D, j, physHoldAt, hself]
  have hDo : ∀ i, i ≠ e → i ≠ j → D i = C i := by
    intro i h1 h2; simp [D, j, physHoldAt, h1, h2]
  -- leader facts after the row
  have hEleadAfter : (C e).carrier.splice.base.core.core.leader = true →
      (D e).carrier.splice.base.core.core.leader = true := by
    intro h; rw [hDe, ph1_base]; exact hkeep h
  have hJleadAfter : (C j).carrier.splice.base.core.core.leader = true →
      (D j).carrier.splice.base.core.core.leader = true := by
    intro h; rw [hDj, ph2_base]
    exact BirthShortDoneTerminalRowRightLeader.row_right_leader hpsi hwidth hle _ _ h
  have hsj : ring.rightNeighbor j ≠ j := fun h => hself (rightNeighbor_inj ring h)
  refine local_preservation hpsi ring C D e hself hDo hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- incoming edge
    intro x hre hdx
    have hdp := (danger_iff_physical hpsi ring D x).1 hdx
    rw [hre] at hdp
    rcases hlead with hle' | hlj
    · exact absurd (hEleadAfter hle') (by rw [hdp.2.1]; decide)
    · by_cases hxj : x = j
      · -- ring of two: x = j is a surviving leader
        rw [hxj] at hdp
        exact absurd (hJleadAfter hlj) (by rw [hdp.1]; decide)
      have hxe : x ≠ e := by intro h; rw [h] at hre; exact hself hre
      have hDx := hDo x hxe hxj
      -- C e is a follower: otherwise D e would be a leader
      have hef : (C e).carrier.splice.base.core.core.leader = false := by
        cases h : (C e).carrier.splice.base.core.core.leader
        · rfl
        · exact absurd (hEleadAfter h) (by rw [hdp.2.1]; decide)
      have hlab : (D e).carrier.splice.base.core.core.label = (C e).carrier.splice.base.core.core.label := by
        rw [hDe, ph1_base]
        exact B9SpliceV10ePhysicalHoldBirth.left_follower_label_frame hpsi hwidth hle _ _ hef
      have hdC : PreparedDangerAt hpsi ring (projectV6 C) x := by
        refine (danger_iff_physical hpsi ring C x).2 ⟨?_, ?_, ?_⟩
        · have := hdp.1; rwa [hDx] at this
        · rw [hre]; exact hef
        · have := hdp.2.2; rw [hDx, hlab] at this; rw [hre]; exact this
      have hp := hS.1 x hdC
      refine (protected_congr_ctrl ring C D x (by rw [hDx]) (by rw [hDx]) (by rw [hDx]) ?_ ?_ ?_).2 hp
      · rw [hre, hDe, ph1_role]
      · rw [hre, hDe, ph1_pending]
      · rw [hre, hDe, ph1_ticket]
  · -- served edge
    intro hdx
    have hdp := (danger_iff_physical hpsi ring D e).1 hdx
    rcases hlead with hle' | hlj
    · exact absurd (hEleadAfter hle') (by rw [hdp.1]; decide)
    · exact absurd (hJleadAfter hlj) (by rw [hdp.2.1]; decide)
  · -- outgoing edge
    intro hdx
    have hdp := (danger_iff_physical hpsi ring D j).1 hdx
    by_cases hlj : (C j).carrier.splice.base.core.core.leader = true
    · exact absurd (hJleadAfter hlj) (by rw [hdp.1]; decide)
    have hjf : (C j).carrier.splice.base.core.core.leader = false := by
      cases h : (C j).carrier.splice.base.core.core.leader
      · rfl
      · exact absurd h hlj
    rcases hrshape with ⟨hnone, hnp⟩ | hRF
    · rcases ph2_ticket_cases hpsi hwidth hle (C e) (C j) with ⟨hkeep2, hnot⟩ | ⟨htrue, _, _, _⟩
      · -- not relabelled: the label is unchanged (the cell is a neutral follower after the row)
        have hlabj : (D j).carrier.splice.base.core.core.label = (C j).carrier.splice.base.core.core.label := by
          by_cases hEq : (D j).carrier.splice.base.core.core.label = (C j).carrier.splice.base.core.core.label
          · exact hEq
          · exfalso
            apply hnot
            refine ⟨hnone, hnp, ?_, ?_⟩
            · have := hdp.1; rwa [hDj, ph2_base] at this
            · intro heq; apply hEq; rw [hDj, ph2_base]; exact heq
        have hs_ne_j : ring.rightNeighbor j ≠ j := hsj
        by_cases hse : ring.rightNeighbor j = e
        · -- ring of two: the right endpoint of the outgoing edge is e
          -- D e keeps its controller; its label may change only if e is a leader, which blocks danger
          rcases hlead with hle' | hlj'
          · have := hdp.2.1; rw [hse] at this; exact absurd (hEleadAfter hle') (by rw [this]; decide)
          · exact absurd hlj' hlj
        have hDs := hDo _ hse hs_ne_j
        have hdC : PreparedDangerAt hpsi ring (projectV6 C) j := by
          refine (danger_iff_physical hpsi ring C j).2 ⟨hjf, ?_, ?_⟩
          · have := hdp.2.1; rwa [hDs] at this
          · have := hdp.2.2; rw [hDs, hlabj] at this; exact this
        have hp := hS.1 j hdC
        exact (protected_congr_ctrl ring C D j (by rw [hDj, ph2_role]) (by rw [hDj, ph2_pending])
          (by rw [hDj, hkeep2]) (by rw [hDs]) (by rw [hDs]) (by rw [hDs])).2 hp
      · -- relabelled neutral follower: a host fence
        left; right
        refine ⟨?_, ?_, ?_⟩
        · rw [hDj, ph2_role]; exact hnone
        · rw [hDj, ph2_pending]; exact hnp
        · rw [hDj]; exact htrue
    · -- reserved front on the left of the outgoing edge
      left; left
      unfold R1ProtectedSpliceEdgeV3 projectV6
      dsimp only
      refine Or.inl ⟨?_, ?_⟩
      · rw [hDj, ph2_role]; exact hRF.1
      · rw [hDj, ph2_pending]; exact hRF.2
  · -- ticket shape at e
    rw [ticketShape_congr (D e) (C e) (by rw [hDe, ph1_role]) (by rw [hDe, ph1_pending]) (by rw [hDe, ph1_ticket])]
    exact hS.2.1 e
  · -- ticket shape at j
    rcases ph2_ticket_cases hpsi hwidth hle (C e) (C j) with ⟨hkeep2, _⟩ | ⟨htrue, hnone, hnp, _⟩
    · rw [ticketShape_congr (D j) (C j) (by rw [hDj, ph2_role]) (by rw [hDj, ph2_pending]) (by rw [hDj, hkeep2])]
      exact hS.2.1 j
    · intro _
      exact Or.inr ⟨by rw [hDj, ph2_role]; exact hnone, by rw [hDj, ph2_pending]; exact hnp, by rw [hDj]; exact htrue⟩
  · -- a pending predecessor entering e keeps its backing (e keeps its controller and ticket)
    intro x hre _ hrole hpend
    have hb := hS.2.2 x hrole hpend
    rw [hre] at hb
    refine ⟨?_, ?_⟩
    · rw [hDe]; unfold ReservedFrontHoldGuard; rw [ph1_role, ph1_pending]; exact hb.1
    · rw [hDe, ph1_ticket]; exact hb.2
  · -- a pending predecessor at e keeps its backing at j (a reserved front is never relabelled)
    intro hrole hpend
    have hrole' : role (C e).carrier = .predecessorArmed := by rw [hDe, ph1_role] at hrole; exact hrole
    have hpend' : (C e).carrier.repairPending = true := by rw [hDe, ph1_pending] at hpend; exact hpend
    have hb := hS.2.2 e hrole' hpend'
    have hjRF : ReservedFrontHoldGuard (C j).carrier := hb.1
    refine ⟨?_, ?_⟩
    · rw [hDj]; unfold ReservedFrontHoldGuard; rw [ph2_role, ph2_pending]; exact hjRF
    · rcases ph2_ticket_cases hpsi hwidth hle (C e) (C j) with ⟨hkeep2, _⟩ | ⟨_, hnone, _, _⟩
      · rw [hDj, hkeep2]; exact hb.2
      · exact absurd (hjRF.1.symm.trans hnone) (by decide)
  · -- j is neutral or a reserved front, never a predecessor
    intro hrole _
    rw [hDj, ph2_role] at hrole
    rcases hrshape with ⟨hnone, _⟩ | hRF
    · exact absurd (hrole.symm.trans hnone) (by decide)
    · exact absurd (hrole.symm.trans hRF.1) (by decide)

/-- Physical step then fence on a settled right predecessor (the V10e/V10h row for a settled predecessor
on the right). -/
def physFenceAt (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  let w := physicalHoldV6 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  fun i => if i = e then w.1 else if i = ring.rightNeighbor e then fenceV6 w.2 else C i

theorem physFenceAt_preserves_spliceSafeV7g_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hlead : (C e).carrier.splice.base.core.core.leader = true ∨
      (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = true)
    (hkeep : (C e).carrier.splice.base.core.core.leader = true →
      (hostOut hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).1.core.core.leader = true)
    (hSP : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed ∧
      (C (ring.rightNeighbor e)).carrier.repairPending = false) :
    SpliceSafeV7g hpsi ring (physFenceAt hpsi hwidth hle ring C e) := by
  classical
  let j := ring.rightNeighbor e
  let D := physFenceAt hpsi hwidth hle ring C e
  have hDe : D e = (physicalHoldV6 hpsi hwidth hle (C e) (C j)).1 := by simp [D, j, physFenceAt]
  have hDj : D j = fenceV6 (physicalHoldV6 hpsi hwidth hle (C e) (C j)).2 := by
    simp [D, j, physFenceAt, hself]
  have hDo : ∀ i, i ≠ e → i ≠ j → D i = C i := by
    intro i h1 h2; simp [D, j, physFenceAt, h1, h2]
  have hEleadAfter : (C e).carrier.splice.base.core.core.leader = true →
      (D e).carrier.splice.base.core.core.leader = true := by
    intro h; rw [hDe, ph1_base]; exact hkeep h
  have hJleadAfter : (C j).carrier.splice.base.core.core.leader = true →
      (D j).carrier.splice.base.core.core.leader = true := by
    intro h; rw [hDj, fence_base, ph2_base]
    exact BirthShortDoneTerminalRowRightLeader.row_right_leader hpsi hwidth hle _ _ h
  refine local_preservation hpsi ring C D e hself hDo hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- incoming edge (as for the physical hold)
    intro x hre hdx
    have hdp := (danger_iff_physical hpsi ring D x).1 hdx
    rw [hre] at hdp
    rcases hlead with hle' | hlj
    · exact absurd (hEleadAfter hle') (by rw [hdp.2.1]; decide)
    · by_cases hxj : x = j
      · rw [hxj] at hdp
        exact absurd (hJleadAfter hlj) (by rw [hdp.1]; decide)
      have hxe : x ≠ e := by intro h; rw [h] at hre; exact hself hre
      have hDx := hDo x hxe hxj
      have hef : (C e).carrier.splice.base.core.core.leader = false := by
        cases h : (C e).carrier.splice.base.core.core.leader
        · rfl
        · exact absurd (hEleadAfter h) (by rw [hdp.2.1]; decide)
      have hlab : (D e).carrier.splice.base.core.core.label = (C e).carrier.splice.base.core.core.label := by
        rw [hDe, ph1_base]
        exact B9SpliceV10ePhysicalHoldBirth.left_follower_label_frame hpsi hwidth hle _ _ hef
      have hdC : PreparedDangerAt hpsi ring (projectV6 C) x := by
        refine (danger_iff_physical hpsi ring C x).2 ⟨?_, ?_, ?_⟩
        · have := hdp.1; rwa [hDx] at this
        · rw [hre]; exact hef
        · have := hdp.2.2; rw [hDx, hlab] at this; rw [hre]; exact this
      have hp := hS.1 x hdC
      refine (protected_congr_ctrl ring C D x (by rw [hDx]) (by rw [hDx]) (by rw [hDx]) ?_ ?_ ?_).2 hp
      · rw [hre, hDe, ph1_role]
      · rw [hre, hDe, ph1_pending]
      · rw [hre, hDe, ph1_ticket]
  · -- served edge
    intro hdx
    have hdp := (danger_iff_physical hpsi ring D e).1 hdx
    rcases hlead with hle' | hlj
    · exact absurd (hEleadAfter hle') (by rw [hdp.1]; decide)
    · exact absurd (hJleadAfter hlj) (by rw [hdp.2.1]; decide)
  · -- outgoing edge: host fence
    intro _
    left; right
    rw [hDj]; exact fence_shape _
  · -- ticket shape at e
    rw [ticketShape_congr (D e) (C e) (by rw [hDe, ph1_role]) (by rw [hDe, ph1_pending]) (by rw [hDe, ph1_ticket])]
    exact hS.2.1 e
  · -- ticket shape at j: fence
    rw [hDj]; intro _; exact Or.inr (fence_shape _)
  · -- backing for a pending predecessor entering e
    intro x hre _ hrole hpend
    have hb := hS.2.2 x hrole hpend
    rw [hre] at hb
    refine ⟨?_, ?_⟩
    · rw [hDe]; unfold ReservedFrontHoldGuard; rw [ph1_role, ph1_pending]; exact hb.1
    · rw [hDe, ph1_ticket]; exact hb.2
  · -- a pending predecessor at e would need j to be a reserved front, but j is a settled predecessor
    intro hrole hpend
    have hrole' : role (C e).carrier = .predecessorArmed := by rw [hDe, ph1_role] at hrole; exact hrole
    have hpend' : (C e).carrier.repairPending = true := by rw [hDe, ph1_pending] at hpend; exact hpend
    have hb := hS.2.2 e hrole' hpend'
    exact absurd (hb.1.1.symm.trans hSP.1) (by decide)
  · -- j is a fence
    intro hrole _
    rw [hDj] at hrole
    have hn : role (fenceV6 (physicalHoldV6 hpsi hwidth hle (C e) (C j)).2).carrier = .none := rfl
    rw [hn] at hrole
    exact absurd hrole (by decide)

/-- With both old tickets false, the V7 ordinary host write is the physical hold. -/
theorem ordinaryHostWriteV7_eq_physicalHoldV6 (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (hl : l.acquireTicket = false) (hr : r.acquireTicket = false) :
    ordinaryHostWriteV7 hpsi hwidth hle l r = physicalHoldV6 hpsi hwidth hle l r := by
  cases l with
  | mk lc lt =>
    cases r with
    | mk rc rt =>
      simp only at hl hr
      subst hl; subst hr
      rfl

def ordinaryAt (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  let w := ordinaryHostWriteV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  fun i => if i = e then w.1 else if i = ring.rightNeighbor e then w.2 else C i

/-- The V7 ordinary host row on an unticketed pair with a neutral right cell, with a leader present and no
left deletion, preserves `SpliceSafeV7g`. -/
theorem ordinaryAt_preserves_spliceSafeV7g_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hlead : (C e).carrier.splice.base.core.core.leader = true ∨
      (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = true)
    (hkeep : (C e).carrier.splice.base.core.core.leader = true →
      (hostOut hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).1.core.core.leader = true)
    (hlt : (C e).acquireTicket = false) (hrt : (C (ring.rightNeighbor e)).acquireTicket = false)
    (hrneutral : role (C (ring.rightNeighbor e)).carrier = .none ∧
      (C (ring.rightNeighbor e)).carrier.repairPending = false) :
    SpliceSafeV7g hpsi ring (ordinaryAt hpsi hwidth hle ring C e) := by
  have hEq : ordinaryAt hpsi hwidth hle ring C e = physHoldAt hpsi hwidth hle ring C e := by
    unfold ordinaryAt physHoldAt
    rw [ordinaryHostWriteV7_eq_physicalHoldV6 hpsi hwidth hle _ _ hlt hrt]
  rw [hEq]
  exact physHoldAt_preserves_spliceSafeV7g_leader hpsi hwidth hle ring C e hself hS hlead hkeep
    (Or.inl hrneutral)

def armBAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  let w := armBWriteV6 (C e) (C (ring.rightNeighbor e))
  fun i => if i = e then w.1 else if i = ring.rightNeighbor e then w.2 else C i

/-- ARM-B (neutral left cell, right victim that is a leader) preserves `SpliceSafeV7g`. -/
theorem armBAt_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hG : ArmBGuard (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7g hpsi ring (armBAt ring C e) := by
  classical
  let j := ring.rightNeighbor e
  let D := armBAt ring C e
  have hDe : D e = setControlV6 (C e) .predecessorArmed false := by simp [D, j, armBAt, armBWriteV6]
  have hDj : D j = setControlV6 (C j) .front false := by simp [D, j, armBAt, armBWriteV6, hself]
  have hDo : ∀ i, i ≠ e → i ≠ j → D i = C i := by
    intro i h1 h2; simp [D, j, armBAt, h1, h2]
  have hbaseE : (D e).carrier.splice.base = (C e).carrier.splice.base := by rw [hDe]; rfl
  have hbaseJ : (D j).carrier.splice.base = (C j).carrier.splice.base := by rw [hDj]; rfl
  have hjlead : (D j).carrier.splice.base.core.core.leader = true := by rw [hbaseJ]; exact hG.2.2.2.2
  refine local_preservation hpsi ring C D e hself hDo hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- incoming edge: its protection came from the left cell only
    intro x hre hdx
    by_cases hxj : x = j
    · have hdp := (danger_iff_physical hpsi ring D x).1 hdx
      rw [hxj] at hdp
      exact absurd hjlead (by rw [hdp.1]; decide)
    have hxe : x ≠ e := by intro h; rw [h] at hre; exact hself hre
    have hDx := hDo x hxe hxj
    have hdC := (danger_congr hpsi ring C D x (by rw [hDx]) (by rw [hre, hbaseE])).1 hdx
    rcases hS.1 x hdC with hv | hpoh
    · rcases hv with hv3 | hf
      · unfold R1ProtectedSpliceEdgeV3 projectV6 at hv3
        dsimp only at hv3
        rw [hre] at hv3
        rcases hv3 with h31 | h32 | h33
        · left; left
          unfold R1ProtectedSpliceEdgeV3 projectV6
          dsimp only
          rw [hDx]
          exact Or.inl h31
        · exact absurd (h32.1.symm.trans hG.1) (by decide)
        · rcases h33.2.2 with hr1 | hr2 | hr3
          · exact absurd (hr1.1.symm.trans hG.1) (by decide)
          · exact absurd (hr2.1.symm.trans hG.1) (by decide)
          · exact absurd (hr3.1.symm.trans hG.1) (by decide)
      · left; right
        rw [hDx]; exact hf
    · have := hpoh.2.2.1.1
      rw [hre] at this
      exact absurd (this.symm.trans hG.1) (by decide)
  · -- served edge: right leader
    intro hdx
    have hdp := (danger_iff_physical hpsi ring D e).1 hdx
    exact absurd hjlead (by rw [hdp.2.1]; decide)
  · -- outgoing edge: left leader
    intro hdx
    have hdp := (danger_iff_physical hpsi ring D j).1 hdx
    exact absurd hjlead (by rw [hdp.1]; decide)
  · rw [hDe]; intro ht
    have h0 : (setControlV6 (C e) .predecessorArmed false).acquireTicket = false := rfl
    rw [h0] at ht; exact absurd ht (by decide)
  · rw [hDj]; intro ht
    have h0 : (setControlV6 (C j) .front false).acquireTicket = false := rfl
    rw [h0] at ht; exact absurd ht (by decide)
  · intro x hre _ hrole hpend
    have hb := hS.2.2 x hrole hpend
    rw [hre] at hb
    exact absurd (hb.1.1.symm.trans hG.1) (by decide)
  · intro _ hpend
    rw [hDe] at hpend
    have h0 : (setControlV6 (C e) .predecessorArmed false).carrier.repairPending = false := rfl
    rw [h0] at hpend; exact absurd hpend (by decide)
  · intro hrole _
    rw [hDj] at hrole
    have h0 : role (setControlV6 (C j) .front false).carrier = .front := rfl
    rw [h0] at hrole; exact absurd hrole (by decide)

end B9SpliceV10hPhysicalHoldLeaderSafe
