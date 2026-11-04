import Leader.AAFJ.Centered.Sanitation

/-!
# Pathwise rank monotonicity for centered AAFJ renewal

The cut-order `Dangerous` predicate and `Phi = max 1 (L + D)` are the ones
defined in `AAFJSingleBarrierSanitation`: a leader at the tail is a valid
strictly-later shielding witness.  The source Protocol-6 proof already covers
every nonexceptional centered transition.  This file proves the one additional
phase-one/head-probe branch and lifts the resulting cut theorem back to a
physical one-barrier configuration.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace Rank

open BarrierAlgebra
open SingleBarrierSanitation

set_option autoImplicit false

/-- The post-step view is cut at the unique successor barrier. -/
def cutSuccessor {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (X : Fin n → State k) (e : Fin n) : Fin n → State k :=
  let D : Fin n → State k :=
    fun j => ((CenteredRenewal.protocol k hk).step ring X e) j
  if CenteredRenewal.AdvanceReady hk ring X e then rotateCut ring D else D

/-- Away from the centered-only branch, the packaged configuration step agrees
pointwise with the source Protocol-6 step. -/
theorem step_eq_source_of_not_exceptional {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (X : Fin n → State k) (e : Fin n)
    (hex : ¬ Sanitation.Exceptional hk (X e) (X (ring.rightNeighbor e))) :
    (CenteredRenewal.protocol k hk).step ring X e = (AAFJPK.protocol k hk).step ring X e := by
  funext i
  have hlocal := Sanitation.transition_eq_source_of_not_exceptional hk
    (X e) (X (ring.rightNeighbor e)) hex
  have hre := rightNeighbor_ne_self ring hn2 e
  by_cases hie : i = e
  · subst i
    simp [PopulationProtocol.step, CenteredRenewal.protocol, AAFJPK.protocol, hlocal]
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simp [PopulationProtocol.step, CenteredRenewal.protocol, AAFJPK.protocol, hlocal, hre]
    · simp [PopulationProtocol.step, CenteredRenewal.protocol, AAFJPK.protocol, hie, hir]

/-- In the nonexceptional branch, centered and source readiness coincide. -/
theorem advanceReady_iff_source_of_not_exceptional {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (X : Fin n → State k) (e : Fin n)
    (hex : ¬ Sanitation.Exceptional hk (X e) (X (ring.rightNeighbor e))) :
    CenteredRenewal.AdvanceReady hk ring X e ↔ BarrierAlgebra.AdvanceReady hk ring X e := by
  unfold CenteredRenewal.AdvanceReady CenteredRenewal.PairAdvanceReady BarrierAlgebra.AdvanceReady
    BarrierAlgebra.PairAdvanceReady
  constructor
  · intro h
    refine ⟨h.1, h.2, ?_⟩
    cases hp : (X (ring.rightNeighbor e)).probe
    · rfl
    · exact False.elim (hex ⟨h.1, h.2, hp⟩)
  · intro h
    exact ⟨h.1, h.2.1⟩

/-- Cut reindexing commutes with the centered packaged transition. -/
theorem cutView_step_at_cutPos {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (barrier : Fin n)
    (C : Fin n → State k) (e : Fin n) :
    cutView ring barrier
        ((CenteredRenewal.protocol k hk).step ring C (cutPos ring barrier e)) =
      (CenteredRenewal.protocol k hk).step ring (cutView ring barrier C) e := by
  funext i
  have hinj := cutPos_injective ring barrier
  simp only [cutView, PopulationProtocol.step, CenteredRenewal.protocol]
  rw [cutPos_rightNeighbor]
  by_cases hie : i = e
  · subst i
    simp
  · have hpos : cutPos ring barrier i ≠ cutPos ring barrier e := by
      intro h
      exact hie (hinj h)
    by_cases hir : i = ring.rightNeighbor e
    · subst i
      have hphys : ring.rightNeighbor (cutPos ring barrier e) ≠
          cutPos ring barrier e := by
        intro h
        apply hie
        apply hinj
        rw [cutPos_rightNeighbor]
        exact h
      simp [hie, hphys, cutPos_rightNeighbor]
    · have hposr : cutPos ring barrier i ≠
          ring.rightNeighbor (cutPos ring barrier e) := by
        rw [← cutPos_rightNeighbor]
        intro h
        exact hir (hinj h)
      simp [hie, hir, hpos, hposr]

/-- A centered local birth changes no other leader bit. -/
theorem centered_step_leaderCount_birth_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (X : Fin n → State k)
    (e : Fin n)
    (hborn :
      (CenteredRenewal.transition hk (X e) (X (ring.rightNeighbor e))).1.leader = true)
    (hr : (CenteredRenewal.transition hk (X e) (X (ring.rightNeighbor e))).2.leader =
      (X (ring.rightNeighbor e)).leader) :
    leaderCount ((CenteredRenewal.protocol k hk).step ring X e) ≤ leaderCount X + 1 := by
  apply bitCount_single_birth_le
    (fun i => (X i).leader)
    (fun i => (((CenteredRenewal.protocol k hk).step ring X e) i).leader) e
  · have hre := rightNeighbor_ne_self ring hn2 e
    simpa [PopulationProtocol.step, CenteredRenewal.protocol, hre] using hborn
  · intro i hie
    have hre := rightNeighbor_ne_self ring hn2 e
    by_cases hir : i = ring.rightNeighbor e
    · subst i
      simpa [PopulationProtocol.step, CenteredRenewal.protocol, hre, hie] using hr
    · simp [PopulationProtocol.step, CenteredRenewal.protocol, hie, hir]

/-- The centered-only phase-one/head-probe branch is monotone.  The new tail
is probe-free by definition; if a tail probe becomes a leader, its old danger
charge pays for that possible birth. -/
theorem exceptional_phi_step_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (X : Fin n → State k) (hbar : CanonicalOneBarrier hk ring X)
    (e : Fin n)
    (hex : Sanitation.Exceptional hk (X e) (X (ring.rightNeighbor e))) :
    Phi (cutSuccessor hk ring X e) ≤ Phi X := by
  have hn2 : 1 < n := by omega
  let t := tailCoord ring
  have het : e = t := by
    apply (hbar e).1
    exact hex.1
  subst e
  have htailEq : tailCoord ring = t := rfl
  have hBarrier : IsBarrier hk (X t) (X (ring.rightNeighbor t)) :=
    (hbar t).2 rfl
  have hphase : (X t).phase = true := hex.2.1
  have hheadProbe : (X (ring.rightNeighbor t)).probe = true := hex.2.2
  have hready : CenteredRenewal.AdvanceReady hk ring X t := ⟨hBarrier, hphase⟩
  have hrt : ring.rightNeighbor t = (⟨0, ring.hn⟩ : Fin n) := by
    simp [t, rightNeighbor_tailCoord]
  have hzeroTail : (⟨0, ring.hn⟩ : Fin n) ≠ t := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = n - 1 at hv
    omega
  have hpair : CenteredRenewal.transition hk (X t) (X (ring.rightNeighbor t)) =
      (probeHitsBarrier (X t),
        { X (ring.rightNeighbor t) with
          label := succLabel hk (X t).label
          phase := false
          bullet := false
          probe := false }) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hBarrier]
    exact CenteredRenewal.barrierStep_phase_one hk _ _ hphase
  unfold cutSuccessor
  simp only [hready]
  cases htailProbe : (X t).probe with
  | false =>
      have hframes := Sanitation.exceptional_step_frames hk ring hn2 X t hex htailProbe
      have hleadersD := hframes.1
      apply phi_mono_of_same_leaderCount X
        (rotateCut ring ((CenteredRenewal.protocol k hk).step ring X t))
      · calc
          leaderCount (rotateCut ring ((CenteredRenewal.protocol k hk).step ring X t)) =
              leaderCount ((CenteredRenewal.protocol k hk).step ring X t) :=
            leaderCount_rotateCut ring _
          _ = leaderCount X := leaderCount_eq_of_leaders_eq X _ hleadersD
      · intro hsafe
        apply not_dangerous_rotate_of_head_probe_free ring
        · simpa [hrt] using hframes.2.2.2
        · apply not_dangerous_of_leaders_eq_probes_subset X
            ((CenteredRenewal.protocol k hk).step ring X t) hleadersD
          · intro i hi
            have hre := rightNeighbor_ne_self ring hn2 t
            by_cases hit : i = t
            · subst i
              simp [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
                probeHitsBarrier, htailProbe] at hi
            · by_cases hir : i = ring.rightNeighbor t
              · subst i
                simp [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
                  hre] at hi
              · simpa [PopulationProtocol.step, CenteredRenewal.protocol,
                  hit, hir] using hi
          · exact hsafe
  | true =>
      have hOldDanger := dangerous_of_tail_probe ring X htailProbe
      have hcountD := centered_step_leaderCount_birth_le hk ring hn2 X t
        (by simp [hpair, probeHitsBarrier, htailProbe])
        (by simp [hpair])
      have hcount : leaderCount (rotateCut ring ((CenteredRenewal.protocol k hk).step ring X t)) ≤
          leaderCount X + 1 := by
        calc
          leaderCount (rotateCut ring ((CenteredRenewal.protocol k hk).step ring X t)) =
              leaderCount ((CenteredRenewal.protocol k hk).step ring X t) :=
            leaderCount_rotateCut ring _
          _ ≤ leaderCount X + 1 := hcountD
      apply phi_mono_of_birth_consumes_danger X
        (rotateCut ring ((CenteredRenewal.protocol k hk).step ring X t)) hcount hOldDanger
      apply not_dangerous_rotate_of_tail_birth ring
      · simp [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
          probeHitsBarrier, htailProbe, htailEq]
      · simp [PopulationProtocol.step, CenteredRenewal.protocol, hpair,
          probeHitsBarrier, htailProbe, htailEq]
      · have hre := rightNeighbor_ne_self ring hn2 t
        have hhead :
            (((CenteredRenewal.protocol k hk).step ring X t)
              (ring.rightNeighbor t)).probe = false := by
          simp [PopulationProtocol.step, CenteredRenewal.protocol, hpair, hre]
        simpa [hrt] using hhead

/-- Full literal centered one-step monotonicity in canonical cut coordinates. -/
theorem canonical_phi_step_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (X : Fin n → State k) (hbar : CanonicalOneBarrier hk ring X)
    (e : Fin n) : Phi (cutSuccessor hk ring X e) ≤ Phi X := by
  have hn2 : 1 < n := by omega
  by_cases hex : Sanitation.Exceptional hk (X e) (X (ring.rightNeighbor e))
  · exact exceptional_phi_step_le hk ring hn3 X hbar e hex
  · have hstep := step_eq_source_of_not_exceptional hk ring hn2 X e hex
    have hready := advanceReady_iff_source_of_not_exceptional hk ring X e hex
    have hsource := SingleBarrierSanitation.canonical_phi_step_le
      hk ring hn3 X hbar e
    unfold cutSuccessor
    rw [hstep]
    unfold SingleBarrierSanitation.cutSuccessor at hsource
    split <;> split at hsource <;> simp_all

/-- Physical pathwise rank monotonicity for an exactly-one-barrier centered
configuration.  The barrier witness is advanced exactly on `CenteredRenewal.AdvanceReady`. -/
theorem oneBarrier_phi_step_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b e : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b) :
    let D := (CenteredRenewal.protocol k hk).step ring C e
    let b' := if CenteredRenewal.AdvanceReady hk ring C e then ring.rightNeighbor b else b
    OneBarrierAt hk ring D b' ∧ PhiAt ring b' D ≤ PhiAt ring b C := by
  let D := (CenteredRenewal.protocol k hk).step ring C e
  let b' := if CenteredRenewal.AdvanceReady hk ring C e then ring.rightNeighbor b else b
  have hn2 : 1 < n := by omega
  have hnext : OneBarrierAt hk ring D b' := by
    dsimp only [D, b']
    exact Sanitation.oneBarrierAt_step hk ring hn2 C b e hndvd hone
  refine ⟨hnext, ?_⟩
  let i := cutCoord ring b e
  let X := cutView ring b C
  have hpos : cutPos ring b i = e := by simp [i]
  have hview : cutView ring b D = (CenteredRenewal.protocol k hk).step ring X i := by
    dsimp only [D, X]
    simpa [hpos] using Rank.cutView_step_at_cutPos hk ring b C i
  have hcanon : CanonicalOneBarrier hk ring X :=
    canonicalOneBarrier_cutView hk ring C b hone
  have hreadyIff : CenteredRenewal.AdvanceReady hk ring X i ↔ CenteredRenewal.AdvanceReady hk ring C e := by
    change IsBarrier hk (C (cutPos ring b i))
        (C (cutPos ring b (ring.rightNeighbor i))) ∧
        (C (cutPos ring b i)).phase = true ↔
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) ∧ (C e).phase = true
    rw [cutPos_rightNeighbor, hpos]
  have hmono := canonical_phi_step_le hk ring hn3 X hcanon i
  by_cases hready : CenteredRenewal.AdvanceReady hk ring C e
  · have hreadyX : CenteredRenewal.AdvanceReady hk ring X i := hreadyIff.2 hready
    dsimp only [b', PhiAt]
    simp only [hready, if_true]
    change Phi (cutView ring (ring.rightNeighbor b) D) ≤ Phi X
    rw [cutView_nextBarrier ring b D, hview]
    unfold cutSuccessor at hmono
    simpa [hreadyX] using hmono
  · have hreadyX : ¬ CenteredRenewal.AdvanceReady hk ring X i := fun h => hready (hreadyIff.1 h)
    dsimp only [b', PhiAt]
    simp only [hready, if_false]
    rw [hview]
    unfold cutSuccessor at hmono
    simpa [hreadyX] using hmono

end Rank
end CenteredRenewal
end AAFJPK
