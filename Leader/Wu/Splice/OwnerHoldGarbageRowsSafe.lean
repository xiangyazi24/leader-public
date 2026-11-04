import Leader.Wu.Splice.CertifiedDeleteSafe
import Leader.Wu.Splice.PhysicalHoldNoBirthSafe

set_option autoImplicit false

/-! # The V10d garbage rows preserve `SpliceSafeV7g`

The three controller-only garbage rows of V10d (kept in V10g/V10h) preserve the extended invariant, with or
without leaders; none of them changes a physical base, so every edge keeps its danger status.
* orphan reserved front `(l, fenceV6 r)` (`orphanToFenceAt_preserves_spliceSafeV7g`);
* orphan pending victim `(l, clearControlV6 r)` (`orphanVictimClearAt_preserves_spliceSafeV7g`);
* owned pending victim `(fenceV6 l, fenceV6 r)` (`fenceFenceAt_preserves_spliceSafeV7g`).
Each is an instance of `B9SpliceCertifiedDelete.local_preservation`. -/

namespace B9SpliceV10dRowsSafeV7g

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence B9SpliceTableV10g B9SpliceCertifiedDelete

variable {n psi kappa tau : Nat}

/-- Controller-only writes keep every danger status. -/
theorem danger_of_bases (hpsi : 0 < psi) (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau)
    (hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base) (x : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 D) x ↔ PreparedDangerAt hpsi ring (projectV6 C) x :=
  danger_congr hpsi ring C D x (hb x) (hb _)

theorem orphanToFenceAt_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hO : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7g hpsi ring (orphanToFenceAt ring C e) := by
  classical
  let D := orphanToFenceAt ring C e
  have hDe : D e = C e := at_other ring C e e (Ne.symm hself)
  have hDj : D (ring.rightNeighbor e) = fenceV6 (C (ring.rightNeighbor e)) := at_j ring C e
  have hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base := base_eq ring C e
  refine local_preservation hpsi ring C D e hself
    (fun i _ hij => at_other ring C e i hij) hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hre hdx
    by_cases hxj : x = ring.rightNeighbor e
    · left; right; rw [hxj, hDj]; exact fence_shape _
    · have hDx : D x = C x := at_other ring C e x hxj
      have hdC := (danger_of_bases hpsi ring C D hb x).1 hdx
      exact (protected_congr ring C D x hDx (by rw [hre, hDe])).2 (hS.1 x hdC)
  · intro hdx
    have hdC := (danger_of_bases hpsi ring C D hb e).1 hdx
    rcases hS.1 e hdC with hv | hpoh
    · rcases hv with hv3 | hf
      · unfold R1ProtectedSpliceEdgeV3 projectV6 at hv3
        dsimp only at hv3
        rcases hv3 with h31 | h32 | h33
        · left; left
          unfold R1ProtectedSpliceEdgeV3 projectV6
          dsimp only
          rw [hDe]; exact Or.inl h31
        · exact absurd (h32.1.symm.trans hO.1.1) (by decide)
        · exact absurd h33.1 hO.2
      · left; right; rw [hDe]; exact hf
    · exact absurd hpoh.1 hO.2
  · intro _
    left; right; rw [hDj]; exact fence_shape _
  · rw [hDe]; exact hS.2.1 e
  · rw [hDj]; intro _; exact Or.inr (fence_shape _)
  · intro x hre _ hrole hpend
    have hbk := hS.2.2 x hrole hpend
    rw [hre] at hbk
    rw [hDe]; exact hbk
  · intro hrole _
    rw [hDe] at hrole
    exact absurd hrole hO.2
  · intro hrole _
    rw [hDj] at hrole
    have hn : role (fenceV6 (C (ring.rightNeighbor e))).carrier = .none := rfl
    rw [hn] at hrole
    exact absurd hrole (by decide)

theorem orphanVictimClearAt_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hG : OrphanVictimGuard (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7g hpsi ring (orphanVictimClearAt ring C e) := by
  classical
  let D := orphanVictimClearAt ring C e
  have hDo : ∀ i, i ≠ ring.rightNeighbor e → D i = C i := by
    intro i h; simp [D, orphanVictimClearAt, h]
  have hDe : D e = C e := hDo e (Ne.symm hself)
  have hDj : D (ring.rightNeighbor e) = clearControlV6 (C (ring.rightNeighbor e)) := vc_at_j ring C e
  have hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base := by
    intro i
    by_cases h : i = ring.rightNeighbor e
    · rw [h, hDj]; rfl
    · rw [hDo i h]
  have hjPV : role (C (ring.rightNeighbor e)).carrier = .victimArmed := hG.1
  refine local_preservation hpsi ring C D e hself (fun i _ hij => hDo i hij) hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hre hdx
    have hdC := (danger_of_bases hpsi ring C D hb x).1 hdx
    by_cases hxj : x = ring.rightNeighbor e
    · -- ring of two: the edge (j, e); its protection can only come from e as a pending predecessor
      subst hxj
      rcases hS.1 _ hdC with hv | hpoh
      · rcases hv with hv3 | hf
        · unfold R1ProtectedSpliceEdgeV3 projectV6 at hv3
          dsimp only at hv3
          rcases hv3 with h31 | h32 | h33
          · exact absurd (h31.1.symm.trans hjPV) (by decide)
          · left; left
            unfold R1ProtectedSpliceEdgeV3 projectV6
            dsimp only
            rw [hre, hDe]; rw [hre] at h32; exact Or.inr (Or.inl h32)
          · exact absurd (h33.1.symm.trans hjPV) (by decide)
        · exact absurd (hf.1.symm.trans hjPV) (by decide)
      · exact absurd (hpoh.1.symm.trans hjPV) (by decide)
    · exact (protected_congr ring C D x (hDo x hxj) (by rw [hre, hDe])).2 (hS.1 x hdC)
  · intro hdx
    have hdC := (danger_of_bases hpsi ring C D hb e).1 hdx
    rcases hS.1 e hdC with hv | hpoh
    · rcases hv with hv3 | hf
      · unfold R1ProtectedSpliceEdgeV3 projectV6 at hv3
        dsimp only at hv3
        rcases hv3 with h31 | h32 | h33
        · left; left
          unfold R1ProtectedSpliceEdgeV3 projectV6
          dsimp only
          rw [hDe]; exact Or.inl h31
        · exact absurd (h32.1.symm.trans hjPV) (by decide)
        · exact absurd ⟨h33.1, h33.2.1⟩ hG.2.2
      · left; right; rw [hDe]; exact hf
    · exact absurd (hpoh.2.2.1.1.symm.trans hjPV) (by decide)
  · intro hdx
    have hdC := (danger_of_bases hpsi ring C D hb _).1 hdx
    have hs_ne_j : ring.rightNeighbor (ring.rightNeighbor e) ≠ ring.rightNeighbor e :=
      fun h => hself (rightNeighbor_inj ring h)
    rcases hS.1 _ hdC with hv | hpoh
    · rcases hv with hv3 | hf
      · unfold R1ProtectedSpliceEdgeV3 projectV6 at hv3
        dsimp only at hv3
        rcases hv3 with h31 | h32 | h33
        · exact absurd (h31.1.symm.trans hjPV) (by decide)
        · left; left
          unfold R1ProtectedSpliceEdgeV3 projectV6
          dsimp only
          rw [hDo _ hs_ne_j]; exact Or.inr (Or.inl h32)
        · exact absurd (h33.1.symm.trans hjPV) (by decide)
      · exact absurd (hf.1.symm.trans hjPV) (by decide)
    · exact absurd (hpoh.1.symm.trans hjPV) (by decide)
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
    have hbk := hS.2.2 e hrole hpend
    exact absurd (hbk.1.1.symm.trans hjPV) (by decide)
  · intro hrole _
    rw [hDj] at hrole
    have hn : role (clearControlV6 (C (ring.rightNeighbor e))).carrier = .none := rfl
    rw [hn] at hrole
    exact absurd hrole (by decide)

theorem fenceFenceAt_preserves_spliceSafeV7g (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hG : OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7g hpsi ring (fenceFenceAt ring C e) := by
  classical
  let D := fenceFenceAt ring C e
  have hDe : D e = fenceV6 (C e) := ff_at_e ring C e
  have hDj : D (ring.rightNeighbor e) = fenceV6 (C (ring.rightNeighbor e)) := by
    simp [D, fenceFenceAt, hself]
  have hDo : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i := by
    intro i h1 h2; simp [D, fenceFenceAt, h1, h2]
  have hb : ∀ i, (D i).carrier.splice.base = (C i).carrier.splice.base := by
    intro i
    by_cases h1 : i = e
    · rw [h1, hDe]; rfl
    · by_cases h2 : i = ring.rightNeighbor e
      · rw [h2, hDj]; rfl
      · rw [hDo i h1 h2]
  have hePred : role (C e).carrier = .predecessorArmed := hG.1
  have heSet : (C e).carrier.repairPending = false := hG.2.1
  refine local_preservation hpsi ring C D e hself hDo hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hre hdx
    by_cases hxj : x = ring.rightNeighbor e
    · left; right; rw [hxj, hDj]; exact fence_shape _
    have hxe : x ≠ e := by intro h; rw [h] at hre; exact hself hre
    have hDx := hDo x hxe hxj
    have hdC := (danger_of_bases hpsi ring C D hb x).1 hdx
    rcases hS.1 x hdC with hv | hpoh
    · rcases hv with hv3 | hf
      · unfold R1ProtectedSpliceEdgeV3 projectV6 at hv3
        dsimp only at hv3
        rw [hre] at hv3
        rcases hv3 with h31 | h32 | h33
        · left; left
          unfold R1ProtectedSpliceEdgeV3 projectV6
          dsimp only
          rw [hDx]; exact Or.inl h31
        · exact absurd (h32.2.symm.trans heSet) (by decide)
        · rcases h33.2.2 with hr1 | hr2 | hr3
          · exact absurd (hr1.1.symm.trans hePred) (by decide)
          · exact absurd (hr2.1.symm.trans hePred) (by decide)
          · exact absurd (hr3.2.symm.trans heSet) (by decide)
      · left; right; rw [hDx]; exact hf
    · have := hpoh.2.2.1.1
      rw [hre] at this
      exact absurd (this.symm.trans hePred) (by decide)
  · intro _; left; right; rw [hDe]; exact fence_shape _
  · intro _; left; right; rw [hDj]; exact fence_shape _
  · rw [hDe]; intro _; exact Or.inr (fence_shape _)
  · rw [hDj]; intro _; exact Or.inr (fence_shape _)
  · intro x hre _ hrole hpend
    have hbk := hS.2.2 x hrole hpend
    rw [hre] at hbk
    exact absurd (hbk.1.1.symm.trans hePred) (by decide)
  · intro hrole _
    rw [hDe] at hrole
    have hn : role (fenceV6 (C e)).carrier = .none := rfl
    rw [hn] at hrole; exact absurd hrole (by decide)
  · intro hrole _
    rw [hDj] at hrole
    have hn : role (fenceV6 (C (ring.rightNeighbor e))).carrier = .none := rfl
    rw [hn] at hrole; exact absurd hrole (by decide)

end B9SpliceV10dRowsSafeV7g
