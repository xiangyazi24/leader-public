import Leader.Wu.Splice.OwnerHoldMoveRowsSafe
import Leader.Wu.Splice.FenceHandoffTable
import Leader.Wu.Splice.CertFreeLeftSafe

set_option autoImplicit false

/-! # The remaining controller-only rows of V10h preserve `SpliceSafeV7g`

All writes are stated on the served pair through `writeAt ring C e w` (cell `e` gets `w.1`, its right
neighbour gets `w.2`, every other cell is kept), with or without leaders elsewhere:
* the V10b handoff `(settled predecessor, reserved front)` from a left host fence
  (`handoff_preserves_spliceSafeV7g`);
* the V7 fence STOP `(clearTicketV6 l, r)` without a local barrier (`fenceStop_preserves_spliceSafeV7g`);
* PendingAbort `(clearControlV6 l, clearControlV6 r)` (`pendingAbort_preserves_spliceSafeV7g`);
* clearing a certificate-free right cell (`clearRight_preserves_spliceSafeV7g`: the victim, front and
  malformed right scrubs);
* clearing a left cell that certifies nothing on its incoming edge and whose settled-predecessor
  certificate on the served edge, if any, is idle because the right cell is a leader
  (`clearLeft_preserves_spliceSafeV7g`: the victim and malformed left scrubs, the V10e left scrub and the
  predecessor-left scrub).
Two transfer lemmas locate the protection of an edge in one endpoint:
`protection_from_left_of_right_unowning` and `protection_from_right_of_left_inert`. -/

namespace B9SpliceV10hControllerRowsSafe

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV10b B9OrphanToFence B9SpliceTableV10g B9SpliceCertifiedDelete
  B9SpliceV10dRowsSafeV7g B9SpliceV10ePhysicalHoldNoBirth

variable {n psi kappa tau : Nat}

/-- Write a pair of states on the served edge. -/
def writeAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) : R1ConfigV6 n psi kappa tau :=
  fun i => if i = e then w.1 else if i = ring.rightNeighbor e then w.2 else C i

theorem writeAt_e (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) : writeAt ring C e w e = w.1 := by
  simp [writeAt]

theorem writeAt_j (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) (hself : ring.rightNeighbor e ≠ e) :
    writeAt ring C e w (ring.rightNeighbor e) = w.2 := by
  simp [writeAt, hself]

theorem writeAt_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) (i : Fin n) (h1 : i ≠ e)
    (h2 : i ≠ ring.rightNeighbor e) : writeAt ring C e w i = C i := by
  simp [writeAt, h1, h2]

theorem writeAt_base (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) (hself : ring.rightNeighbor e ≠ e)
    (h1 : w.1.carrier.splice.base = (C e).carrier.splice.base)
    (h2 : w.2.carrier.splice.base = (C (ring.rightNeighbor e)).carrier.splice.base) (i : Fin n) :
    (writeAt ring C e w i).carrier.splice.base = (C i).carrier.splice.base := by
  by_cases hie : i = e
  · rw [hie, writeAt_e]; exact h1
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij, writeAt_j ring C e w hself]; exact h2
    · rw [writeAt_other ring C e w i hie hij]

theorem rightRight_ne (ring : DirectedRing n) (e : Fin n) (hself : ring.rightNeighbor e ≠ e) :
    ring.rightNeighbor (ring.rightNeighbor e) ≠ ring.rightNeighbor e := by
  intro h
  exact hself (rightNeighbor_inj ring h)

/-- If the right cell owns no certificate shape, the protection of the edge lives in its left cell. -/
theorem protection_from_left_of_right_unowning (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau)
    (x : Fin n) (hDx : D x = C x)
    (hnRF : ¬ ReservedFrontHoldGuard (C (ring.rightNeighbor x)).carrier)
    (hnPV : ¬ (role (C (ring.rightNeighbor x)).carrier = .victimArmed ∧
      (C (ring.rightNeighbor x)).carrier.repairPending = true))
    (hnPP : ¬ (role (C (ring.rightNeighbor x)).carrier = .predecessorArmed ∧
      (C (ring.rightNeighbor x)).carrier.repairPending = true))
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
      · exact absurd h32 hnPP
      · rcases h33.2.2 with hr1 | hr2 | hr3
        · exact absurd hr1 hnRF
        · exact absurd hr2 hnPV
        · exact absurd hr3 hnPP
    · left; right; rw [hDx]; exact hf
  · exact absurd hpoh.2.2.1 hnRF

/-- If the left cell owns no left-endpoint certificate, the protection of the edge lives in its right cell. -/
theorem protection_from_right_of_left_inert (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau)
    (x : Fin n) (hDy : D (ring.rightNeighbor x) = C (ring.rightNeighbor x))
    (hnRF : ¬ ReservedFrontHoldGuard (C x).carrier)
    (hnPP : ¬ (role (C x).carrier = .predecessorArmed ∧ (C x).carrier.repairPending = true))
    (hnF : ¬ HostFenceShapeV7 (C x))
    (hnSP : role (C x).carrier = .predecessorArmed → (C x).carrier.repairPending = false →
      (ReservedFrontHoldGuard (C (ring.rightNeighbor x)).carrier ∨
        (role (C (ring.rightNeighbor x)).carrier = .victimArmed ∧
          (C (ring.rightNeighbor x)).carrier.repairPending = true) ∨
        (role (C (ring.rightNeighbor x)).carrier = .predecessorArmed ∧
          (C (ring.rightNeighbor x)).carrier.repairPending = true)) → False)
    (hp : ProtectedSpliceEdgeV7g ring C x) : ProtectedSpliceEdgeV7g ring D x := by
  rcases hp with hv | hpoh
  · rcases hv with hv3 | hf
    · unfold R1ProtectedSpliceEdgeV3 projectV6 at hv3
      dsimp only at hv3
      rcases hv3 with h31 | h32 | h33
      · exact absurd h31 hnRF
      · left; left
        unfold R1ProtectedSpliceEdgeV3 projectV6
        dsimp only
        rw [hDy]; exact Or.inr (Or.inl h32)
      · exact (hnSP h33.1 h33.2.1 h33.2.2).elim
    · exact absurd hf hnF
  · exact absurd ⟨hpoh.1, hpoh.2.1⟩ hnPP

/-! ## Handoff -/

theorem handoff_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hG : HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (hostFenceHandoffWriteV10b (C e) (C (ring.rightNeighbor e)))) := by
  classical
  let w := hostFenceHandoffWriteV10b (C e) (C (ring.rightNeighbor e))
  let D := writeAt ring C e w
  have hDe : D e = setControlV6 (C e) .predecessorArmed false := writeAt_e ring C e w
  have hDj : D (ring.rightNeighbor e) = setControlV6 (C (ring.rightNeighbor e)) .front true :=
    writeAt_j ring C e w hself
  have hDo : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i := writeAt_other ring C e w
  have hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base :=
    writeAt_base ring C e w hself rfl rfl
  have heNone : role (C e).carrier = .none := hG.1.1
  have hDeRole : role (D e).carrier = .predecessorArmed := by rw [hDe]; rfl
  have hDePend : (D e).carrier.repairPending = false := by rw [hDe]; rfl
  have hDeTicket : (D e).acquireTicket = false := by rw [hDe]; rfl
  have hDjRF : ReservedFrontHoldGuard (D (ring.rightNeighbor e)).carrier := by rw [hDj]; exact ⟨rfl, rfl⟩
  have hDjTicket : (D (ring.rightNeighbor e)).acquireTicket = false := by rw [hDj]; rfl
  refine local_preservation hpsi ring C D e hself hDo hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hre hdx
    by_cases hxj : x = ring.rightNeighbor e
    · left; left
      unfold R1ProtectedSpliceEdgeV3 projectV6
      dsimp only
      rw [hxj]; exact Or.inl hDjRF
    have hxe : x ≠ e := by intro h; rw [h] at hre; exact hself hre
    have hdC := (danger_of_bases hpsi ring C D hb x).1 hdx
    refine protection_from_left_of_right_unowning ring C D x (hDo x hxe hxj) ?_ ?_ ?_ (hS.1 x hdC)
    · rw [hre]; intro h; have h1 := h.1; rw [heNone] at h1; exact absurd h1 (by decide)
    · rw [hre, heNone]; intro h; exact absurd h.1 (by decide)
    · rw [hre, heNone]; intro h; exact absurd h.1 (by decide)
  · intro _
    left; left
    unfold R1ProtectedSpliceEdgeV3 projectV6
    dsimp only
    exact Or.inr (Or.inr ⟨hDeRole, hDePend, Or.inl hDjRF⟩)
  · intro _
    left; left
    unfold R1ProtectedSpliceEdgeV3 projectV6
    dsimp only
    exact Or.inl hDjRF
  · intro ht; rw [hDeTicket] at ht; exact absurd ht (by decide)
  · intro ht; rw [hDjTicket] at ht; exact absurd ht (by decide)
  · intro x hre _ hrole hpend
    have hbk := hS.2.2 x hrole hpend
    rw [hre] at hbk
    exact absurd (hbk.1.1.symm.trans heNone) (by decide)
  · intro _ hpend
    rw [hDePend] at hpend; exact absurd hpend (by decide)
  · intro hrole _
    have := hDjRF.1
    rw [hrole] at this
    exact absurd this (by decide)

/-! ## Fence STOP -/

theorem fenceStop_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hfL : HostFenceShapeV7 (C e))
    (hbar : ¬ LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (hostFenceLeftStopWriteV7 (C e) (C (ring.rightNeighbor e)))) := by
  classical
  let w := hostFenceLeftStopWriteV7 (C e) (C (ring.rightNeighbor e))
  let D := writeAt ring C e w
  have hDe : D e = clearTicketV6 (C e) := writeAt_e ring C e w
  have hDj : D (ring.rightNeighbor e) = C (ring.rightNeighbor e) := writeAt_j ring C e w hself
  have hDo : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i := writeAt_other ring C e w
  have hDne : ∀ i, i ≠ e → D i = C i := by
    intro i hi
    by_cases hij : i = ring.rightNeighbor e
    · rw [hij]; exact hDj
    · exact hDo i hi hij
  have hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base :=
    writeAt_base ring C e w hself rfl rfl
  have heNone : role (C e).carrier = .none := hfL.1
  have hunown : ∀ x, ring.rightNeighbor x = e →
      ¬ ReservedFrontHoldGuard (C (ring.rightNeighbor x)).carrier ∧
      ¬ (role (C (ring.rightNeighbor x)).carrier = .victimArmed ∧
        (C (ring.rightNeighbor x)).carrier.repairPending = true) ∧
      ¬ (role (C (ring.rightNeighbor x)).carrier = .predecessorArmed ∧
        (C (ring.rightNeighbor x)).carrier.repairPending = true) := by
    intro x hre
    rw [hre, heNone]
    refine ⟨?_, ?_, ?_⟩
    · intro h; have h1 := h.1; rw [heNone] at h1; exact absurd h1 (by decide)
    · intro h; exact absurd h.1 (by decide)
    · intro h; exact absurd h.1 (by decide)
  refine local_preservation hpsi ring C D e hself hDo hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hre hdx
    have hxe : x ≠ e := by intro h; rw [h] at hre; exact hself hre
    have hdC := (danger_of_bases hpsi ring C D hb x).1 hdx
    obtain ⟨h1, h2, h3⟩ := hunown x hre
    exact protection_from_left_of_right_unowning ring C D x (hDne x hxe) h1 h2 h3 (hS.1 x hdC)
  · intro hdx
    have hdC := (danger_of_bases hpsi ring C D hb e).1 hdx
    exact absurd (B9SpliceV10cRowMoveStop.danger_e_barrier hpsi ring C e hdC) hbar
  · intro hdx
    have hdC := (danger_of_bases hpsi ring C D hb _).1 hdx
    by_cases hs : ring.rightNeighbor (ring.rightNeighbor e) = e
    · obtain ⟨h1, h2, h3⟩ := hunown _ hs
      exact protection_from_left_of_right_unowning ring C D _ hDj h1 h2 h3 (hS.1 _ hdC)
    · exact (protected_congr ring C D _ hDj (hDo _ hs (rightRight_ne ring e hself))).2 (hS.1 _ hdC)
  · rw [hDe]; intro ht
    have h0 : (clearTicketV6 (C e)).acquireTicket = false := rfl
    rw [h0] at ht; exact absurd ht (by decide)
  · rw [hDj]; exact hS.2.1 _
  · intro x hre _ hrole hpend
    have hbk := hS.2.2 x hrole hpend
    rw [hre] at hbk
    exact absurd (hbk.1.1.symm.trans heNone) (by decide)
  · intro hrole _
    rw [hDe] at hrole
    have hr : role (clearTicketV6 (C e)).carrier = role (C e).carrier := rfl
    rw [hr, heNone] at hrole
    exact absurd hrole (by decide)
  · intro hrole hpend
    rw [hDj] at hrole hpend
    have hbk := hS.2.2 _ hrole hpend
    by_cases hs : ring.rightNeighbor (ring.rightNeighbor e) = e
    · rw [hs] at hbk
      exact absurd (hbk.1.1.symm.trans heNone) (by decide)
    · rw [hDo _ hs (rightRight_ne ring e hself)]; exact hbk

/-! ## PendingAbort -/

theorem pendingAbort_preserves_spliceSafeV7g (hpsi : 0 < psi) {width : Nat} (hwidth : 0 < width)
    (hle : width ≤ psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hG : PendingAbortGuard hpsi hwidth hle (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (pendingAbortWriteV6 (C e) (C (ring.rightNeighbor e)))) := by
  classical
  let w := pendingAbortWriteV6 (C e) (C (ring.rightNeighbor e))
  let D := writeAt ring C e w
  have hDe : D e = clearControlV6 (C e) := writeAt_e ring C e w
  have hDj : D (ring.rightNeighbor e) = clearControlV6 (C (ring.rightNeighbor e)) := writeAt_j ring C e w hself
  have hDo : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i := writeAt_other ring C e w
  have hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base :=
    writeAt_base ring C e w hself rfl rfl
  have heLead : (D e).carrier.splice.base.core.core.leader = true := by rw [hb]; exact hG.2.2.2.2.1
  have hjFront : role (C (ring.rightNeighbor e)).carrier = .front := hG.2.1
  have hjPend : (C (ring.rightNeighbor e)).carrier.repairPending = false := hG.2.2.2.1
  refine local_preservation hpsi ring C D e hself hDo hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hre hdx
    have hd := (danger_iff_physical hpsi ring D x).1 hdx
    have h2 := hd.2.1
    rw [hre, heLead] at h2
    exact absurd h2 (by decide)
  · intro hdx
    have hd := (danger_iff_physical hpsi ring D e).1 hdx
    have h1 := hd.1
    rw [heLead] at h1
    exact absurd h1 (by decide)
  · intro hdx
    have hd := (danger_iff_physical hpsi ring D _).1 hdx
    by_cases hs : ring.rightNeighbor (ring.rightNeighbor e) = e
    · have h2 := hd.2.1
      rw [hs, heLead] at h2
      exact absurd h2 (by decide)
    · have hdC := (danger_of_bases hpsi ring C D hb _).1 hdx
      refine protection_from_right_of_left_inert ring C D _ (hDo _ hs (rightRight_ne ring e hself))
        ?_ ?_ ?_ ?_ (hS.1 _ hdC)
      · intro h; have h2 := h.2; rw [hjPend] at h2; exact absurd h2 (by decide)
      · intro h; rw [hjFront] at h; exact absurd h.1 (by decide)
      · intro h; have := h.1; rw [hjFront] at this; exact absurd this (by decide)
      · intro h; rw [hjFront] at h; exact absurd h (by decide)
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

/-! ## Clearing a certificate-free right cell -/

theorem clearRight_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hF : CertFreeV7 (C (ring.rightNeighbor e))) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (C e, clearControlV6 (C (ring.rightNeighbor e)))) := by
  classical
  obtain ⟨hnRF, hnPred, hnPV, hnF⟩ := hF
  let w := (C e, clearControlV6 (C (ring.rightNeighbor e)))
  let D := writeAt ring C e w
  have hDe : D e = C e := writeAt_e ring C e w
  have hDj : D (ring.rightNeighbor e) = clearControlV6 (C (ring.rightNeighbor e)) := writeAt_j ring C e w hself
  have hDo : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i := writeAt_other ring C e w
  have hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base :=
    writeAt_base ring C e w hself rfl rfl
  have hnPP : ¬ (role (C (ring.rightNeighbor e)).carrier = .predecessorArmed ∧
      (C (ring.rightNeighbor e)).carrier.repairPending = true) := fun h => hnPred h.1
  have hjInert : ∀ (h : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed), False := hnPred
  have hDjs : D (ring.rightNeighbor (ring.rightNeighbor e)) = C (ring.rightNeighbor (ring.rightNeighbor e)) := by
    by_cases hs : ring.rightNeighbor (ring.rightNeighbor e) = e
    · rw [hs]; exact hDe
    · exact hDo _ hs (rightRight_ne ring e hself)
  refine local_preservation hpsi ring C D e hself hDo hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hre hdx
    have hdC := (danger_of_bases hpsi ring C D hb x).1 hdx
    by_cases hxj : x = ring.rightNeighbor e
    · rw [hxj] at hdC ⊢
      exact protection_from_right_of_left_inert ring C D _ hDjs hnRF hnPP hnF
        (fun h _ _ => hjInert h) (hS.1 _ hdC)
    · have hxe : x ≠ e := by intro h; rw [h] at hre; exact hself hre
      exact (protected_congr ring C D x (hDo x hxe hxj) (by rw [hre]; exact hDe)).2 (hS.1 x hdC)
  · intro hdx
    have hdC := (danger_of_bases hpsi ring C D hb e).1 hdx
    exact protection_from_left_of_right_unowning ring C D e hDe hnRF hnPV hnPP (hS.1 e hdC)
  · intro hdx
    have hdC := (danger_of_bases hpsi ring C D hb _).1 hdx
    exact protection_from_right_of_left_inert ring C D _ hDjs hnRF hnPP hnF
      (fun h _ _ => hjInert h) (hS.1 _ hdC)
  · rw [hDe]; exact hS.2.1 e
  · rw [hDj]; intro ht
    have h0 : (clearControlV6 (C (ring.rightNeighbor e))).acquireTicket = false := rfl
    rw [h0] at ht; exact absurd ht (by decide)
  · intro x hre _ hrole hpend
    have hbk := hS.2.2 x hrole hpend
    rw [hre] at hbk
    rw [hDe]; exact hbk
  · intro hrole hpend
    rw [hDe] at hrole hpend
    exact absurd (hS.2.2 e hrole hpend).1 hnRF
  · intro hrole _
    rw [hDj] at hrole
    have hn : role (clearControlV6 (C (ring.rightNeighbor e))).carrier = .none := rfl
    rw [hn] at hrole; exact absurd hrole (by decide)

/-! ## Clearing a left cell -/

theorem clearLeft_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hnRF : ¬ ReservedFrontHoldGuard (C e).carrier)
    (hnPP : ¬ (role (C e).carrier = .predecessorArmed ∧ (C e).carrier.repairPending = true))
    (hnPV : ¬ (role (C e).carrier = .victimArmed ∧ (C e).carrier.repairPending = true))
    (hnF : ¬ HostFenceShapeV7 (C e))
    (hown : role (C e).carrier = .predecessorArmed → (C e).carrier.repairPending = false →
      (ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier ∨
        (role (C (ring.rightNeighbor e)).carrier = .victimArmed ∧
          (C (ring.rightNeighbor e)).carrier.repairPending = true) ∨
        (role (C (ring.rightNeighbor e)).carrier = .predecessorArmed ∧
          (C (ring.rightNeighbor e)).carrier.repairPending = true)) →
      (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = true) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (clearControlV6 (C e), C (ring.rightNeighbor e))) := by
  classical
  let w := (clearControlV6 (C e), C (ring.rightNeighbor e))
  let D := writeAt ring C e w
  have hDe : D e = clearControlV6 (C e) := writeAt_e ring C e w
  have hDj : D (ring.rightNeighbor e) = C (ring.rightNeighbor e) := writeAt_j ring C e w hself
  have hDo : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i := writeAt_other ring C e w
  have hDne : ∀ i, i ≠ e → D i = C i := by
    intro i hi
    by_cases hij : i = ring.rightNeighbor e
    · rw [hij]; exact hDj
    · exact hDo i hi hij
  have hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base :=
    writeAt_base ring C e w hself rfl rfl
  refine local_preservation hpsi ring C D e hself hDo hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hre hdx
    have hxe : x ≠ e := by intro h; rw [h] at hre; exact hself hre
    have hdC := (danger_of_bases hpsi ring C D hb x).1 hdx
    exact protection_from_left_of_right_unowning ring C D x (hDne x hxe)
      (by rw [hre]; exact hnRF) (by rw [hre]; exact hnPV) (by rw [hre]; exact hnPP) (hS.1 x hdC)
  · intro hdx
    have hdC := (danger_of_bases hpsi ring C D hb e).1 hdx
    have hjF := ((danger_iff_physical hpsi ring C e).1 hdC).2.1
    refine protection_from_right_of_left_inert ring C D e hDj hnRF hnPP hnF ?_ (hS.1 e hdC)
    intro h1 h2 h3
    have := hown h1 h2 h3
    rw [hjF] at this
    exact absurd this (by decide)
  · intro hdx
    have hdC := (danger_of_bases hpsi ring C D hb _).1 hdx
    by_cases hs : ring.rightNeighbor (ring.rightNeighbor e) = e
    · exact protection_from_left_of_right_unowning ring C D _ hDj
        (by rw [hs]; exact hnRF) (by rw [hs]; exact hnPV) (by rw [hs]; exact hnPP) (hS.1 _ hdC)
    · exact (protected_congr ring C D _ hDj (hDo _ hs (rightRight_ne ring e hself))).2 (hS.1 _ hdC)
  · rw [hDe]; intro ht
    have h0 : (clearControlV6 (C e)).acquireTicket = false := rfl
    rw [h0] at ht; exact absurd ht (by decide)
  · rw [hDj]; exact hS.2.1 _
  · intro x hre _ hrole hpend
    have hbk := hS.2.2 x hrole hpend
    rw [hre] at hbk
    exact absurd hbk.1 hnRF
  · intro hrole _
    rw [hDe] at hrole
    have hn : role (clearControlV6 (C e)).carrier = .none := rfl
    rw [hn] at hrole; exact absurd hrole (by decide)
  · intro hrole hpend
    rw [hDj] at hrole hpend
    have hbk := hS.2.2 _ hrole hpend
    by_cases hs : ring.rightNeighbor (ring.rightNeighbor e) = e
    · rw [hs] at hbk
      exact absurd hbk.1 hnRF
    · rw [hDo _ hs (rightRight_ne ring e hself)]; exact hbk

end B9SpliceV10hControllerRowsSafe
