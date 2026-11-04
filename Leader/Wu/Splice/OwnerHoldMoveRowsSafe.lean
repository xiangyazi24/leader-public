import Leader.Wu.Splice.MoveStopSafe
import Leader.Wu.Splice.MoveSeekSafe
import Leader.Wu.Splice.OwnerHoldGarbageRowsSafe

set_option autoImplicit false

/-! # MOVE-STOP and MOVE-SEEK preserve `SpliceSafeV7g`

Controller-only rows on a settled predecessor `e` with a reserved front `j` on its right:
* MOVE-STOP (no local prepared barrier), follower branch `(clearControlV6 l, clearTicketV6 r)`
  (`moveStopAt_preserves_spliceSafeV7g`) and leader branch `(clearControlV6 l, clearControlV6 r)` when the
  front is a leader (`moveStopLeaderAt_preserves_spliceSafeV7g`);
* MOVE-SEEK (a local prepared barrier) `(l, setTicketV6 r true)` (`moveSeekAt_preserves_spliceSafeV7g`).
With or without leaders elsewhere. -/

namespace B9SpliceMoveRowsSafeV7g

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence B9SpliceTableV10g B9SpliceCertifiedDelete B9SpliceV10dRowsSafeV7g
  B9SpliceV10ePhysicalHoldNoBirth

variable {n psi kappa tau : Nat}

/-- On an edge whose right cell is a settled predecessor, protection comes from the left cell alone. -/
theorem protection_from_left_of_right_settled (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau)
    (x : Fin n) (hDx : D x = C x)
    (hrole : role (C (ring.rightNeighbor x)).carrier = .predecessorArmed)
    (hset : (C (ring.rightNeighbor x)).carrier.repairPending = false)
    (hp : ProtectedSpliceEdgeV7g ring C x) : ProtectedSpliceEdgeV7g ring D x := by
  rcases hp with hv | hpoh
  · rcases hv with hv3 | hf
    · unfold R1ProtectedSpliceEdgeV3 projectV6 at hv3
      dsimp only at hv3
      rcases hv3 with h31 | h32 | h33
      · left; left
        unfold R1ProtectedSpliceEdgeV3 projectV6
        dsimp only
        rw [hDx]; exact Or.inl h31
      · exact absurd (h32.2.symm.trans hset) (by decide)
      · rcases h33.2.2 with hr1 | hr2 | hr3
        · exact absurd (hr1.1.symm.trans hrole) (by decide)
        · exact absurd (hr2.1.symm.trans hrole) (by decide)
        · exact absurd (hr3.2.symm.trans hset) (by decide)
    · left; right; rw [hDx]; exact hf
  · exact absurd (hpoh.2.2.1.1.symm.trans hrole) (by decide)

theorem moveStopAt_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hG : MoveStopGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7g hpsi ring (B9SpliceV10cRowMoveStop.moveStopAt ring C e) := by
  classical
  let D := B9SpliceV10cRowMoveStop.moveStopAt ring C e
  have hDe : D e = clearControlV6 (C e) := B9SpliceV10cRowMoveStop.ms_at_e ring C e
  have hDj : D (ring.rightNeighbor e) = clearTicketV6 (C (ring.rightNeighbor e)) :=
    B9SpliceV10cRowMoveStop.ms_at_j ring C e hself
  have hDo : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i :=
    fun i h1 h2 => B9SpliceV10cRowMoveStop.ms_at_other ring C e i h1 h2
  have hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base :=
    B9SpliceV10cRowMoveStop.ms_base_eq ring C e
  have hjRF : ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier := hG.2.2.1
  refine local_preservation hpsi ring C D e hself hDo hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hre hdx
    by_cases hxj : x = ring.rightNeighbor e
    · left; left
      unfold R1ProtectedSpliceEdgeV3 projectV6
      dsimp only
      rw [hxj, hDj]
      exact Or.inl ⟨hjRF.1, hjRF.2⟩
    have hxe : x ≠ e := by intro h; rw [h] at hre; exact hself hre
    have hdC := (danger_of_bases hpsi ring C D hb x).1 hdx
    exact protection_from_left_of_right_settled ring C D x (hDo x hxe hxj)
      (by rw [hre]; exact hG.1) (by rw [hre]; exact hG.2.1) (hS.1 x hdC)
  · intro hdx
    have hdC := (danger_of_bases hpsi ring C D hb e).1 hdx
    exact absurd (B9SpliceV10cRowMoveStop.danger_e_barrier hpsi ring C e hdC) hG.2.2.2
  · intro _
    left; left
    unfold R1ProtectedSpliceEdgeV3 projectV6
    dsimp only
    rw [hDj]
    exact Or.inl ⟨hjRF.1, hjRF.2⟩
  · rw [hDe]; intro ht
    have h0 : (clearControlV6 (C e)).acquireTicket = false := rfl
    rw [h0] at ht; exact absurd ht (by decide)
  · rw [hDj]; intro ht
    rw [B9SpliceV10cRowMoveStop.ms_ticket_j] at ht; exact absurd ht (by decide)
  · intro x hre _ hrole hpend
    have hbk := hS.2.2 x hrole hpend
    rw [hre] at hbk
    exact absurd (hbk.1.1.symm.trans hG.1) (by decide)
  · intro hrole _
    rw [hDe] at hrole
    have hn : role (clearControlV6 (C e)).carrier = .none := rfl
    rw [hn] at hrole; exact absurd hrole (by decide)
  · intro hrole _
    rw [hDj, B9SpliceV10cRowMoveStop.ms_role_j] at hrole
    exact absurd (hrole.symm.trans hjRF.1) (by decide)

theorem moveSeekAt_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hG : MoveSeekGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7g hpsi ring (B9SpliceV10cRowMoveSeek.moveSeekAt ring C e) := by
  classical
  let D := B9SpliceV10cRowMoveSeek.moveSeekAt ring C e
  have hDj : D (ring.rightNeighbor e) = setTicketV6 (C (ring.rightNeighbor e)) true :=
    B9SpliceV10cRowMoveSeek.sk_at_j ring C e
  have hDo : ∀ i, i ≠ ring.rightNeighbor e → D i = C i :=
    fun i h => B9SpliceV10cRowMoveSeek.sk_at_other ring C e i h
  have hDe : D e = C e := hDo e (Ne.symm hself)
  have hcar : ∀ i, (D i).carrier = (C i).carrier := B9SpliceV10cRowMoveSeek.sk_carrier ring C e
  have hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base := fun i => by rw [hcar i]
  have hjRF : ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier := hG.2.2.1
  have hjRF' : ReservedFrontHoldGuard (D (ring.rightNeighbor e)).carrier := by rw [hcar]; exact hjRF
  refine local_preservation hpsi ring C D e hself (fun i _ hij => hDo i hij) hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hre hdx
    by_cases hxj : x = ring.rightNeighbor e
    · left; left
      unfold R1ProtectedSpliceEdgeV3 projectV6
      dsimp only
      rw [hxj]; exact Or.inl hjRF'
    have hdC := (danger_of_bases hpsi ring C D hb x).1 hdx
    exact (protected_congr ring C D x (hDo x hxj) (by rw [hre, hDe])).2 (hS.1 x hdC)
  · intro _
    left; left
    unfold R1ProtectedSpliceEdgeV3 projectV6
    dsimp only
    rw [hDe]
    exact Or.inr (Or.inr ⟨hG.1, hG.2.1, Or.inl hjRF'⟩)
  · intro _
    left; left
    unfold R1ProtectedSpliceEdgeV3 projectV6
    dsimp only
    exact Or.inl hjRF'
  · rw [hDe]; exact hS.2.1 e
  · intro _
    exact Or.inl hjRF'
  · intro x hre _ hrole hpend
    have hbk := hS.2.2 x hrole hpend
    rw [hre] at hbk
    exact absurd (hbk.1.1.symm.trans hG.1) (by decide)
  · intro _ hpend
    rw [hDe] at hpend
    exact absurd (hpend.symm.trans hG.2.1) (by decide)
  · intro hrole _
    have := hjRF'.1
    rw [hrole] at this
    exact absurd this (by decide)

/-- MOVE-STOP, leader branch: both controllers cleared when the front is a leader. -/
def moveStopLeaderAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = e then clearControlV6 (C e)
    else if i = ring.rightNeighbor e then clearControlV6 (C (ring.rightNeighbor e)) else C i

theorem moveStopLeaderAt_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hG : MoveStopGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier)
    (hjlead : (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = true) :
    SpliceSafeV7g hpsi ring (moveStopLeaderAt ring C e) := by
  classical
  let D := moveStopLeaderAt ring C e
  have hDe : D e = clearControlV6 (C e) := by simp [D, moveStopLeaderAt]
  have hDj : D (ring.rightNeighbor e) = clearControlV6 (C (ring.rightNeighbor e)) := by
    simp [D, moveStopLeaderAt, hself]
  have hDo : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i := by
    intro i h1 h2; simp [D, moveStopLeaderAt, h1, h2]
  have hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base := by
    intro i
    by_cases h1 : i = e
    · rw [h1, hDe]; rfl
    · by_cases h2 : i = ring.rightNeighbor e
      · rw [h2, hDj]; rfl
      · rw [hDo i h1 h2]
  have hjleadD : (D (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = true := by
    rw [hb]; exact hjlead
  refine local_preservation hpsi ring C D e hself hDo hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hre hdx
    by_cases hxj : x = ring.rightNeighbor e
    · have hdp := (danger_iff_physical hpsi ring D x).1 hdx
      rw [hxj] at hdp
      exact absurd hjleadD (by rw [hdp.1]; decide)
    have hxe : x ≠ e := by intro h; rw [h] at hre; exact hself hre
    have hdC := (danger_of_bases hpsi ring C D hb x).1 hdx
    exact protection_from_left_of_right_settled ring C D x (hDo x hxe hxj)
      (by rw [hre]; exact hG.1) (by rw [hre]; exact hG.2.1) (hS.1 x hdC)
  · intro hdx
    have hdp := (danger_iff_physical hpsi ring D e).1 hdx
    exact absurd hjleadD (by rw [hdp.2.1]; decide)
  · intro hdx
    have hdp := (danger_iff_physical hpsi ring D _).1 hdx
    exact absurd hjleadD (by rw [hdp.1]; decide)
  · rw [hDe]; intro ht
    have h0 : (clearControlV6 (C e)).acquireTicket = false := rfl
    rw [h0] at ht; exact absurd ht (by decide)
  · rw [hDj]; intro ht
    have h0 : (clearControlV6 (C (ring.rightNeighbor e))).acquireTicket = false := rfl
    rw [h0] at ht; exact absurd ht (by decide)
  · intro x hre _ hrole hpend
    have hbk := hS.2.2 x hrole hpend
    rw [hre] at hbk
    exact absurd (hbk.1.1.symm.trans hG.1) (by decide)
  · intro hrole _
    rw [hDe] at hrole
    have hn : role (clearControlV6 (C e)).carrier = .none := rfl
    rw [hn] at hrole; exact absurd hrole (by decide)
  · intro hrole _
    rw [hDj] at hrole
    have hn : role (clearControlV6 (C (ring.rightNeighbor e))).carrier = .none := rfl
    rw [hn] at hrole; exact absurd hrole (by decide)

end B9SpliceMoveRowsSafeV7g
