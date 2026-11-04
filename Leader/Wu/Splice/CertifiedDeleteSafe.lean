import Leader.Wu.Splice.CertifiedDeleteTable
import Leader.Wu.Splice.ShapeClearInvariant

set_option autoImplicit false

/-! # The certified DELETE write preserves `SpliceSafeV7g`

`deleteAt ring C e` applies `deleteWriteV6` to the served pair `(e, j)`, `j = rightNeighbor e`: both
physical bases take the host-row output, the left cell becomes a pending predecessor and the right cell a
reserved front, both tickets are cleared.  Main theorem `deleteAt_preserves_spliceSafeV7g`: from any
`SpliceSafeV7g` configuration whose left served cell is not a reserved front, `deleteAt` is again
`SpliceSafeV7g`, whatever the controllers of the two cells were and whatever the physical row did.

* the incoming edge `(p, e)` is protected by V3 disjunct 2 (its right cell is a pending predecessor);
* the served edge `(e, j)` by the new shape `PendingOwnerHoldShapeV7`;
* the outgoing edge `(j, s)` by V3 disjunct 1 (its left cell is a reserved front);
* every other edge keeps both cells, hence its danger status and its protection;
* the created pending predecessor is backed by the unticketed reserved front at `j`, and no other pending
  predecessor loses its backing: a predecessor at `p` would need `C e` to be a reserved front, which is
  excluded by hypothesis.

This is the new safety argument of V10h (`B9SpliceTableV10h`): its deletion branch is `deleteAt` and its
reserved-front branch is the identity (`stepV10h_deletion_branch`, `stepV10h_hold_branch`). -/

namespace B9SpliceCertifiedDelete

open Q11593SpliceControllerDesign
  B9SpliceControllerR1Table
  B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3
  B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7
  B9OrphanToFence
  B9SpliceTableV10g
  B9SpliceTableV10h

variable {n psi kappa tau width : Nat}

/-- The certified deletion applied at edge `e`. -/
def deleteAt (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  if ring.rightNeighbor e = e then C
  else
    let w := deleteWriteV6 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
    fun i =>
      if i = e then w.1
      else if i = ring.rightNeighbor e then w.2
      else C i

section Cells

variable (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
  (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)

theorem at_e (hself : ring.rightNeighbor e ≠ e) :
    deleteAt hpsi hwidth hle ring C e e =
      (deleteWriteV6 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).1 := by
  simp [deleteAt, hself]

theorem at_j (hself : ring.rightNeighbor e ≠ e) :
    deleteAt hpsi hwidth hle ring C e (ring.rightNeighbor e) =
      (deleteWriteV6 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).2 := by
  simp [deleteAt, hself]

theorem at_other (hself : ring.rightNeighbor e ≠ e) (i : Fin n) (hie : i ≠ e)
    (hij : i ≠ ring.rightNeighbor e) : deleteAt hpsi hwidth hle ring C e i = C i := by
  simp [deleteAt, hself, hie, hij]

end Cells

section Shapes

variable (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
  (l r : R1AgentStateV6 psi kappa tau)

theorem left_role : role (deleteWriteV6 hpsi hwidth hle l r).1.carrier = .predecessorArmed := rfl
theorem left_pending : (deleteWriteV6 hpsi hwidth hle l r).1.carrier.repairPending = true := rfl
theorem left_ticket : (deleteWriteV6 hpsi hwidth hle l r).1.acquireTicket = false := rfl
theorem right_role : role (deleteWriteV6 hpsi hwidth hle l r).2.carrier = .front := rfl
theorem right_pending : (deleteWriteV6 hpsi hwidth hle l r).2.carrier.repairPending = true := rfl
theorem right_ticket : (deleteWriteV6 hpsi hwidth hle l r).2.acquireTicket = false := rfl

theorem right_reserved : ReservedFrontHoldGuard (deleteWriteV6 hpsi hwidth hle l r).2.carrier :=
  ⟨rfl, rfl⟩

end Shapes

/-- Danger at an edge depends only on the two physical bases of that edge. -/
theorem danger_congr (hpsi : 0 < psi) (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau)
    (x : Fin n)
    (h1 : (D x).carrier.splice.base = (C x).carrier.splice.base)
    (h2 : (D (ring.rightNeighbor x)).carrier.splice.base = (C (ring.rightNeighbor x)).carrier.splice.base) :
    PreparedDangerAt hpsi ring (projectV6 D) x ↔ PreparedDangerAt hpsi ring (projectV6 C) x := by
  unfold PreparedDangerAt PreparedBarrierAt preparedR1 prepared projectSpliceConfig projectV6
  dsimp only
  rw [h1, h2]

/-- Protection at an edge depends only on the two cells of that edge. -/
theorem protected_congr (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau) (x : Fin n)
    (h1 : D x = C x) (h2 : D (ring.rightNeighbor x) = C (ring.rightNeighbor x)) :
    ProtectedSpliceEdgeV7g ring D x ↔ ProtectedSpliceEdgeV7g ring C x := by
  unfold ProtectedSpliceEdgeV7g ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 projectV6
  dsimp only
  rw [h1, h2]

theorem deleteAt_preserves_spliceSafeV7g (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7g hpsi ring C)
    (hnotRF : ¬ ReservedFrontHoldGuard (C e).carrier) :
    SpliceSafeV7g hpsi ring (deleteAt hpsi hwidth hle ring C e) := by
  by_cases hself : ring.rightNeighbor e = e
  · have hD : deleteAt hpsi hwidth hle ring C e = C := by simp [deleteAt, hself]
    rw [hD]
    exact hS
  have hDe := at_e hpsi hwidth hle ring C e hself
  have hDj := at_j hpsi hwidth hle ring C e hself
  refine ⟨?_, ?_, ?_⟩
  · -- danger coverage
    intro x hdx
    by_cases hxe : x = e
    · -- served edge: the new shape
      subst hxe
      right
      unfold PendingOwnerHoldShapeV7
      rw [hDe, hDj]
      exact ⟨left_role .., left_pending .., right_reserved .., left_ticket .., right_ticket ..⟩
    by_cases hxj : x = ring.rightNeighbor e
    · -- outgoing edge: reserved front on the left
      subst hxj
      left; left
      unfold R1ProtectedSpliceEdgeV3 projectV6
      dsimp only
      rw [hDj]
      exact Or.inl (right_reserved ..)
    by_cases hre : ring.rightNeighbor x = e
    · -- incoming edge: pending predecessor on the right
      left; left
      unfold R1ProtectedSpliceEdgeV3 projectV6
      dsimp only
      rw [hre, hDe]
      exact Or.inr (Or.inl ⟨left_role .., left_pending ..⟩)
    · -- far edge: both cells unchanged
      have hrj : ring.rightNeighbor x ≠ ring.rightNeighbor e := by
        intro h
        exact hxe (rightNeighbor_inj ring h)
      have h1 : deleteAt hpsi hwidth hle ring C e x = C x :=
        at_other hpsi hwidth hle ring C e hself x hxe hxj
      have h2 : deleteAt hpsi hwidth hle ring C e (ring.rightNeighbor x) = C (ring.rightNeighbor x) :=
        at_other hpsi hwidth hle ring C e hself _ hre hrj
      have hdC := (danger_congr hpsi ring C (deleteAt hpsi hwidth hle ring C e) x
        (by rw [h1]) (by rw [h2])).1 hdx
      exact (protected_congr ring C (deleteAt hpsi hwidth hle ring C e) x h1 h2).2 (hS.1 x hdC)
  · -- ticket shape
    intro i
    by_cases hie : i = e
    · subst hie
      rw [hDe]
      intro ht
      exact absurd ht (by rw [left_ticket]; decide)
    by_cases hij : i = ring.rightNeighbor e
    · subst hij
      rw [hDj]
      intro ht
      exact absurd ht (by rw [right_ticket]; decide)
    · rw [at_other hpsi hwidth hle ring C e hself i hie hij]
      exact hS.2.1 i
  · -- pending predecessors keep an unticketed reserved front
    intro i hrole hpend
    by_cases hie : i = e
    · subst hie
      rw [hDj]
      exact ⟨right_reserved .., right_ticket ..⟩
    by_cases hij : i = ring.rightNeighbor e
    · subst hij
      rw [hDj, right_role] at hrole
      exact absurd hrole (by decide)
    · rw [at_other hpsi hwidth hle ring C e hself i hie hij] at hrole hpend
      have hback := hS.2.2 i hrole hpend
      by_cases hre : ring.rightNeighbor i = e
      · rw [hre] at hback
        exact absurd hback.1 hnotRF
      · have hrj : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
          intro h
          exact hie (rightNeighbor_inj ring h)
        rw [at_other hpsi hwidth hle ring C e hself _ hre hrj]
        exact hback

/-- The deletion branch of V10h is `deleteAt`. -/
theorem stepV10h_deletion_branch (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hdel : LeftDeletionCandidate hpsi hwidth hle (C e).carrier.splice (C (ring.rightNeighbor e)).carrier.splice)
    (hnotRF : ¬ ReservedFrontHoldGuard (C e).carrier) :
    stepV10h hpsi hwidth hle ring C e = deleteAt hpsi hwidth hle ring C e := by
  classical
  unfold stepV10h deleteAt rowV10h
  simp only [if_pos hdel, if_neg hnotRF]

/-- The reserved-front branch of V10h is the identity. -/
theorem stepV10h_hold_branch (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hdel : LeftDeletionCandidate hpsi hwidth hle (C e).carrier.splice (C (ring.rightNeighbor e)).carrier.splice)
    (hRF : ReservedFrontHoldGuard (C e).carrier) :
    stepV10h hpsi hwidth hle ring C e = C := by
  classical
  unfold stepV10h rowV10h
  simp only [if_pos hdel, if_pos hRF]
  funext i
  split
  · rfl
  · dsimp only
    split
    · rename_i h; subst h; rfl
    · split
      · rename_i h; rw [h]
      · rfl

/-- Both deletion-candidate branches of V10h preserve `SpliceSafeV7g`. -/
theorem stepV10h_deletionCandidate_preserves (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7g hpsi ring C)
    (hdel : LeftDeletionCandidate hpsi hwidth hle (C e).carrier.splice (C (ring.rightNeighbor e)).carrier.splice) :
    SpliceSafeV7g hpsi ring (stepV10h hpsi hwidth hle ring C e) := by
  classical
  by_cases hRF : ReservedFrontHoldGuard (C e).carrier
  · rw [stepV10h_hold_branch hpsi hwidth hle ring C e hdel hRF]
    exact hS
  · rw [stepV10h_deletion_branch hpsi hwidth hle ring C e hdel hRF]
    exact deleteAt_preserves_spliceSafeV7g hpsi hwidth hle ring C e hS hRF

/-- Leaderless ShapeClear phase: V10h preserves `SpliceSafeV7g` and `ShapeClear` (it is V10e there). -/
theorem stepV10h_preserves_leaderless_shapeClear (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hlead : B9SpliceV10eAssembly.Leaderless C) (hS : SpliceSafeV7g hpsi ring C)
    (hSC : B9SpliceComposedEvents.ShapeClear C) :
    SpliceSafeV7g hpsi ring (stepV10h hpsi hwidth hle ring C e) ∧
      B9SpliceComposedEvents.ShapeClear (stepV10h hpsi hwidth hle ring C e) := by
  have hS7 : SpliceSafeV7 hpsi ring C := (spliceSafeV7_iff_V7g_of_shapeClear hpsi ring C hSC).2 hS
  rw [stepV10h_eq_stepV10e_of_leaderless_shapeClear hpsi hwidth hle ring C hlead hSC e]
  have hS' := B9SpliceV10eAssembly.stepV10e_preserves_spliceSafeV7_leaderless_final
    hpsi hwidth hle ring C e hlead hS7
  have hSC' := B9SpliceShapeClear.stepV10e_preserves_shapeClear hpsi hwidth hle ring C e hlead hS7 hSC
  exact ⟨spliceSafeV7g_of_spliceSafeV7 hpsi ring _ hS', hSC'⟩

/-- L0 (collapse): under the provenance clause, every pending predecessor sits in the fourth protected
shape with its right neighbour.  So an edge whose left cell is a pending predecessor is always protected. -/
theorem pendingOwnerHold_of_provenance (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (hP : ProvenanceSafeV7 ring C) (x : Fin n)
    (hrole : role (C x).carrier = .predecessorArmed) (hpend : (C x).carrier.repairPending = true) :
    PendingOwnerHoldShapeV7 (C x) (C (ring.rightNeighbor x)) := by
  have hback := hP.2 x hrole hpend
  have hticket : (C x).acquireTicket = false := by
    cases ht : (C x).acquireTicket
    · rfl
    · exfalso
      rcases hP.1 x ht with hrf | hfence
      · have := hrf.1
        rw [hrole] at this
        exact absurd this (by decide)
      · have := hfence.1
        rw [hrole] at this
        exact absurd this (by decide)
  exact ⟨hrole, hpend, hback.1, hticket, hback.2⟩

theorem protected_of_pending_left (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (hP : ProvenanceSafeV7 ring C) (x : Fin n)
    (hrole : role (C x).carrier = .predecessorArmed) (hpend : (C x).carrier.repairPending = true) :
    ProtectedSpliceEdgeV7g ring C x :=
  Or.inr (pendingOwnerHold_of_provenance ring C hP x hrole hpend)

/-- Reduction: `SpliceSafeV7g` follows from provenance plus V7 coverage of every danger whose left cell is not
a pending predecessor (L0 covers the others). -/
theorem spliceSafeV7g_of_provenance_and_nonpending (hpsi : 0 < psi) (ring : DirectedRing n)
    (D : R1ConfigV6 n psi kappa tau) (hP : ProvenanceSafeV7 ring D)
    (hcov : ∀ x, PreparedDangerAt hpsi ring (projectV6 D) x →
      ¬ (role (D x).carrier = .predecessorArmed ∧ (D x).carrier.repairPending = true) →
      ProtectedSpliceEdgeV7 ring D x) :
    SpliceSafeV7g hpsi ring D := by
  refine ⟨fun x hx => ?_, hP⟩
  by_cases hpp : role (D x).carrier = .predecessorArmed ∧ (D x).carrier.repairPending = true
  · exact protected_of_pending_left ring D hP x hpp.1 hpp.2
  · exact Or.inl (hcov x hx hpp)

/-- Conversely, a `SpliceSafeV7g` configuration has V7 coverage at every danger whose left cell is not a
pending predecessor. -/
theorem nonpending_coverage_of_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C) (x : Fin n)
    (hx : PreparedDangerAt hpsi ring (projectV6 C) x)
    (hnp : ¬ (role (C x).carrier = .predecessorArmed ∧ (C x).carrier.repairPending = true)) :
    ProtectedSpliceEdgeV7 ring C x := by
  rcases hS.1 x hx with h | h
  · exact h
  · exact absurd ⟨h.1, h.2.1⟩ hnp

/-- Local preservation.  If `D` differs from `C` only at `e` and `j = rightNeighbor e`, then
`SpliceSafeV7g D` follows from `SpliceSafeV7g C` and six local facts: coverage at the three edges touching
`e` or `j` (the incoming edge is the one whose right neighbour is `e`), the ticket shape of the two written
cells, and the pending-predecessor backing clause at the incoming cell and the two written cells. -/
theorem local_preservation (hpsi : 0 < psi) (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau)
    (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hframe : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i)
    (hS : SpliceSafeV7g hpsi ring C)
    (hcovIn : ∀ x, ring.rightNeighbor x = e →
      PreparedDangerAt hpsi ring (projectV6 D) x → ProtectedSpliceEdgeV7g ring D x)
    (hcovE : PreparedDangerAt hpsi ring (projectV6 D) e → ProtectedSpliceEdgeV7g ring D e)
    (hcovJ : PreparedDangerAt hpsi ring (projectV6 D) (ring.rightNeighbor e) →
      ProtectedSpliceEdgeV7g ring D (ring.rightNeighbor e))
    (htE : TicketShapeV7 (D e)) (htJ : TicketShapeV7 (D (ring.rightNeighbor e)))
    (hbIn : ∀ x, ring.rightNeighbor x = e → x ≠ ring.rightNeighbor e →
      role (C x).carrier = .predecessorArmed → (C x).carrier.repairPending = true →
      ReservedFrontHoldGuard (D e).carrier ∧ (D e).acquireTicket = false)
    (hbE : role (D e).carrier = .predecessorArmed → (D e).carrier.repairPending = true →
      ReservedFrontHoldGuard (D (ring.rightNeighbor e)).carrier ∧
        (D (ring.rightNeighbor e)).acquireTicket = false)
    (hbJ : role (D (ring.rightNeighbor e)).carrier = .predecessorArmed →
      (D (ring.rightNeighbor e)).carrier.repairPending = true →
      ReservedFrontHoldGuard (D (ring.rightNeighbor (ring.rightNeighbor e))).carrier ∧
        (D (ring.rightNeighbor (ring.rightNeighbor e))).acquireTicket = false) :
    SpliceSafeV7g hpsi ring D := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hdx
    by_cases hxe : x = e
    · subst hxe; exact hcovE hdx
    by_cases hxj : x = ring.rightNeighbor e
    · subst hxj; exact hcovJ hdx
    by_cases hre : ring.rightNeighbor x = e
    · exact hcovIn x hre hdx
    · have hrj : ring.rightNeighbor x ≠ ring.rightNeighbor e := fun h => hxe (rightNeighbor_inj ring h)
      have h1 := hframe x hxe hxj
      have h2 := hframe _ hre hrj
      have hdC := (danger_congr hpsi ring C D x (by rw [h1]) (by rw [h2])).1 hdx
      exact (protected_congr ring C D x h1 h2).2 (hS.1 x hdC)
  · intro i
    by_cases hie : i = e
    · subst hie; exact htE
    by_cases hij : i = ring.rightNeighbor e
    · subst hij; exact htJ
    · rw [hframe i hie hij]; exact hS.2.1 i
  · intro i hrole hpend
    by_cases hie : i = e
    · subst hie; exact hbE hrole hpend
    by_cases hij : i = ring.rightNeighbor e
    · subst hij; exact hbJ hrole hpend
    · rw [hframe i hie hij] at hrole hpend
      by_cases hre : ring.rightNeighbor i = e
      · rw [hre]
        exact hbIn i hre hij hrole hpend
      · have hrj : ring.rightNeighbor i ≠ ring.rightNeighbor e := fun h => hie (rightNeighbor_inj ring h)
        rw [hframe _ hre hrj]
        exact hS.2.2 i hrole hpend

end B9SpliceCertifiedDelete
