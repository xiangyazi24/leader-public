import Leader.Wu.Coherence.WriterLease
import Leader.Wu.Splice.ControllerRecoveryMass
import Leader.Core.FiniteUniformStoppingTree


set_option autoImplicit false
set_option Elab.async false


namespace R2WriterLeaseMass


open BirthTwoStageEscape FiniteUniformStoppingTree
open R2WriterLease


variable {n ψ κ τ : Nat}


/-- `scrubMassOne` omits a writerless residual lease. -/
def scrubLeaseCorrection (u : Cell ψ κ τ) : Nat :=
  if writerMaterial (raw u) then 0 else u.lease.val


/-- Trust is part of `WriterCleanCell`, so it must be charged too. -/
def scrubTrustCharge (u : Cell ψ κ τ) : Nat :=
  if u.trusted then 1 else 0


/-- Corrected local scrub rank.  On a material cell the first summand is
`lease+1`; on a writerless cell the second summand charges any residual lease. -/
def scrubRankOne (u : Cell ψ κ τ) : Nat :=
  scrubMassOne u + scrubLeaseCorrection u + scrubTrustCharge u


def scrubRank (C : FC n ψ κ τ) : Nat :=
  (List.ofFn (fun i => scrubRankOne (C i))).sum


theorem scrubRankOne_eq_zero_iff (u : Cell ψ κ τ) :
    scrubRankOne u = 0 ↔ WriterCleanCell u := by
  cases hm : writerMaterial (raw u) with
  | false =>
      cases ht : u.trusted <;>
        simp [scrubRankOne, scrubLeaseCorrection, scrubTrustCharge,
          scrubMassOne, WriterCleanCell, hm, ht]
  | true =>
      cases ht : u.trusted <;>
        simp [scrubRankOne, scrubLeaseCorrection, scrubTrustCharge,
          scrubMassOne, WriterCleanCell, hm, ht]


theorem scrubRankOne_le (u : Cell ψ κ τ) :
    scrubRankOne u ≤ leaseCap ψ + 2 := by
  have hlt := u.lease.isLt
  cases hm : writerMaterial (raw u) <;>
    cases ht : u.trusted <;>
    simp [scrubRankOne, scrubLeaseCorrection, scrubTrustCharge,
      scrubMassOne, hm, ht] <;> omega


/-- After one scrub, the metadata corrections are zero; the corrected rank is
exactly the old physical-material mass. -/
theorem scrubRankOne_scrub_eq_mass (u : Cell ψ κ τ) :
    scrubRankOne (scrubCell u) = scrubMassOne (scrubCell u) := by
  cases hm : writerMaterial (raw u) with
  | false =>
      have hraw : raw (scrubCell u) = raw u :=
        scrubCell_raw u (Or.inl hm)
      have hout : writerMaterial (raw (scrubCell u)) = false := by
        rw [hraw]
        exact hm
      have hl : (scrubCell u).lease.val = 0 := by
        simp [scrubCell, hm]
      have ht : (scrubCell u).trusted = false := by
        simp [scrubCell, hm]
      simp [scrubRankOne, scrubLeaseCorrection, scrubTrustCharge,
        hout, hl, ht]
  | true =>
      by_cases hz : u.lease.val = 0
      · have hc := scrubCell_clears_of_material_zero u hm hz
        have hout : writerMaterial (raw (scrubCell u)) = false := by
          rcases hc.1 with ⟨hp3, hw, hs⟩
          simp [writerMaterial, hp3, hw, hs,
            WriterProducerRepair.producerActive]
        have hl : (scrubCell u).lease.val = 0 := hc.2
        have ht : (scrubCell u).trusted = false := by
          simp [scrubCell, hm, hz]
        simp [scrubRankOne, scrubLeaseCorrection, scrubTrustCharge,
          hout, hl, ht]
      · have hraw : raw (scrubCell u) = raw u :=
          scrubCell_raw u (Or.inr hz)
        have hout : writerMaterial (raw (scrubCell u)) = true := by
          rw [hraw]
          exact hm
        have ht : (scrubCell u).trusted = false := by
          simp [scrubCell, hm, hz]
        simp [scrubRankOne, scrubLeaseCorrection, scrubTrustCharge,
          hout, ht]


theorem scrubRankOne_lt_of_dirty
    (u : Cell ψ κ τ) (hdirty : ¬ WriterCleanCell u) :
    scrubRankOne (scrubCell u) < scrubRankOne u := by
  rw [scrubRankOne_scrub_eq_mass]
  cases hm : writerMaterial (raw u) with
  | false =>
      have hle := scrubMassOne_le u
      have hin0 : scrubMassOne u = 0 := by
        simp [scrubMassOne, hm]
      have hout0 : scrubMassOne (scrubCell u) = 0 := by
        rw [hin0] at hle
        omega
      rw [hout0]
      have hne : scrubRankOne u ≠ 0 := by
        intro hz
        exact hdirty ((scrubRankOne_eq_zero_iff u).1 hz)
      omega
  | true =>
      have hs := scrubMassOne_lt_of_material u hm
      have hle : scrubMassOne u ≤ scrubRankOne u := by
        unfold scrubRankOne
        omega
      exact Nat.lt_of_lt_of_le hs hle


theorem scrubRankOne_scrub_le (u : Cell ψ κ τ) :
    scrubRankOne (scrubCell u) ≤ scrubRankOne u := by
  by_cases hc : WriterCleanCell u
  · have hr0 : scrubRankOne u = 0 :=
      (scrubRankOne_eq_zero_iff u).2 hc
    have hm0 : scrubMassOne u = 0 := by
      simp [scrubMassOne, hc.1]
    have hle := scrubMassOne_le u
    have hout0 : scrubMassOne (scrubCell u) = 0 := by
      rw [hm0] at hle
      omega
    rw [scrubRankOne_scrub_eq_mass, hout0, hr0]
    exact Nat.zero_le 0
  · exact Nat.le_of_lt (scrubRankOne_lt_of_dirty u hc)



/-- Definitional shape of the pure scrub population-protocol step. -/
theorem scrubStep_apply (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n) :
    scrubStep ring C e i =
      if i = e then scrubCell (C e)
      else if i = ring.rightNeighbor e then
        scrubCell (C (ring.rightNeighbor e))
      else C i := by
  rfl


theorem scrubRankOne_step_le (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n) :
    scrubRankOne (scrubStep ring C e i) ≤ scrubRankOne (C i) := by
  rw [scrubStep_apply]
  by_cases hie : i = e
  · rw [if_pos hie]
    subst i
    exact scrubRankOne_scrub_le (C e)
  · rw [if_neg hie]
    by_cases hij : i = ring.rightNeighbor e
    · rw [if_pos hij]
      subst i
      exact scrubRankOne_scrub_le (C (ring.rightNeighbor e))
    · rw [if_neg hij]
      exact Nat.le_refl _



/-- No scheduler edge raises the corrected global scrub rank. -/
theorem scrubRank_step_le (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) :
    scrubRank (scrubStep ring C e) ≤ scrubRank C := by
  unfold scrubRank
  exact FiniteUniformStoppingTree.ofFn_sum_le _ _
    (fun i => scrubRankOne_step_le ring C e i)


/-- Serving a dirty cell as the left endpoint strictly lowers global rank. -/
theorem scrubRank_step_lt_of_left_dirty (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hdirty : ¬ WriterCleanCell (C e)) :
    scrubRank (scrubStep ring C e) < scrubRank C := by
  have hs := B9SpliceTableV10d.ofFn_sum_split
    (fun i : Fin n => scrubRankOne (scrubStep ring C e i))
    (fun i : Fin n => scrubRankOne (C i)) e
    (fun i _ => scrubRankOne_step_le ring C e i)
  have he :
      scrubRankOne (scrubStep ring C e e) < scrubRankOne (C e) := by
    rw [scrubStep_apply, if_pos rfl]
    exact scrubRankOne_lt_of_dirty (C e) hdirty
  unfold scrubRank
  omega


private theorem dirty_exists_of_not_clean
    (C : FC n ψ κ τ) (hC : ¬ WriterClean C) :
    ∃ i : Fin n, ¬ WriterCleanCell (C i) := by
  apply Classical.byContradiction
  intro hnone
  apply hC
  intro i
  apply Classical.byContradiction
  intro hi
  exact hnone ⟨i, hi⟩



/-- Every non-clean configuration has at least one scheduler edge with a
strict corrected-rank decrease. -/
theorem scrub_descent (ring : DirectedRing n)
    (C : FC n ψ κ τ) (hC : ¬ WriterClean C) :
    ∃ e : Fin n, scrubRank (scrubStep ring C e) < scrubRank C := by
  obtain ⟨e, he⟩ := dirty_exists_of_not_clean C hC
  exact ⟨e, scrubRank_step_lt_of_left_dirty ring C e he⟩


namespace ScrubBellman


abbrev Active (n ψ κ τ : Nat) :=
  { C : FC n ψ κ τ // ¬ WriterClean C }


noncomputable def stopStep (ring : DirectedRing n) :
    Active n ψ κ τ → Fin n → StopNode (Active n ψ κ τ) := by
  classical
  intro X e
  let D := scrubStep ring X.1 e
  exact if hD : WriterClean D then .success else .active ⟨D, hD⟩


def stopRank : StopNode (Active n ψ κ τ) → Nat
  | .active X => scrubRank X.1
  | .success => 0
  | .failure => 0


def bellmanPotential : StopNode (Active n ψ κ τ) → Nat :=
  fun x => n * stopRank x


theorem scrubRank_le (C : FC n ψ κ τ) :
    scrubRank C ≤ n * (leaseCap ψ + 2) := by
  unfold scrubRank
  calc
    (List.ofFn (fun i : Fin n => scrubRankOne (C i))).sum ≤
        (List.ofFn (fun _ : Fin n => leaseCap ψ + 2)).sum :=
      FiniteUniformStoppingTree.ofFn_sum_le _ _
        (fun i => scrubRankOne_le (C i))
    _ = n * (leaseCap ψ + 2) :=
      FiniteUniformStoppingTree.ofFn_sum_const n (leaseCap ψ + 2)


private theorem scrubRank_eq_zero_of_clean
    (C : FC n ψ κ τ) (hC : WriterClean C) : scrubRank C = 0 := by
  unfold scrubRank
  calc
    (List.ofFn (fun i : Fin n => scrubRankOne (C i))).sum =
        (List.ofFn (fun _ : Fin n => 0)).sum :=
      FiniteUniformStoppingTree.ofFn_sum_eq _ _
        (fun i => (scrubRankOne_eq_zero_iff (C i)).2 (hC i))
    _ = 0 := by
      rw [FiniteUniformStoppingTree.ofFn_sum_const]
      simp


private theorem stopRank_step (ring : DirectedRing n)
    (X : Active n ψ κ τ) (e : Fin n) :
    stopRank (stopStep ring X e) = scrubRank (scrubStep ring X.1 e) := by
  classical
  unfold stopStep
  dsimp only
  by_cases hD : WriterClean (scrubStep ring X.1 e)
  · rw [dif_pos hD]
    simp [stopRank, scrubRank_eq_zero_of_clean _ hD]
  · rw [dif_neg hD]
    rfl


private theorem rank_row_sum (ring : DirectedRing n)
    (X : Active n ψ κ τ) :
    (List.ofFn (fun e : Fin n => scrubRank (scrubStep ring X.1 e))).sum + 1 ≤
      n * scrubRank X.1 := by
  obtain ⟨e, he⟩ := scrub_descent ring X.1 X.2
  have hs := B9SpliceTableV10d.ofFn_sum_split
    (fun i : Fin n => scrubRank (scrubStep ring X.1 i))
    (fun _ : Fin n => scrubRank X.1) e
    (fun i _ => scrubRank_step_le ring X.1 i)
  rw [FiniteUniformStoppingTree.ofFn_sum_const] at hs
  omega


theorem natBellman (ring : DirectedRing n) :
    NatBellmanSuperSolution (stopStep ring) 1
      (bellmanPotential (n := n) (ψ := ψ) (κ := κ) (τ := τ)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro X
  have hs := rank_row_sum ring X
  have heq :
      (List.ofFn (fun e : Fin n =>
        stopRank (stopStep ring X e))).sum =
      (List.ofFn (fun e : Fin n =>
        scrubRank (scrubStep ring X.1 e))).sum :=
    FiniteUniformStoppingTree.ofFn_sum_eq _ _
      (fun e => stopRank_step ring X e)
  unfold bellmanPotential
  rw [FiniteUniformStoppingTree.ofFn_sum_mul_left, heq]
  simp only [Nat.one_mul]
  calc
    n + n * (List.ofFn (fun e : Fin n =>
        scrubRank (scrubStep ring X.1 e))).sum =
      n * (1 + (List.ofFn (fun e : Fin n =>
        scrubRank (scrubStep ring X.1 e))).sum) := by
        rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * scrubRank X.1) :=
      Nat.mul_le_mul_left n (by simpa [Nat.add_comm] using hs)


private theorem bellmanPotential_le
    (x : StopNode (Active n ψ κ τ)) :
    bellmanPotential (n := n) x ≤ n * n * (leaseCap ψ + 2) := by
  cases x with
  | success => simp [bellmanPotential, stopRank]
  | failure => simp [bellmanPotential, stopRank]
  | active X =>
      have hr := scrubRank_le X.1
      unfold bellmanPotential stopRank
      calc
        n * scrubRank X.1 ≤ n * (n * (leaseCap ψ + 2)) :=
          Nat.mul_le_mul_left n hr
        _ = n * n * (leaseCap ψ + 2) := by ac_rfl


private theorem activeCount_eq_avoidCount (ring : DirectedRing n) :
    ∀ (X : Active n ψ κ τ) (T : Nat),
      activeCount (stopStep ring) (.active X) T =
      avoidCount (scrubStep ring) (fun _ => True) WriterClean X.1 T := by
  intro X T
  induction T generalizing X with
  | zero =>
      rw [avoidCount_zero
        (scrubStep ring) (fun _ : FC n ψ κ τ => True)
        WriterClean X.1 ⟨trivial, X.2⟩]
      rfl
  | succ T ih =>
      rw [avoidCount_succ
        (scrubStep ring) (fun _ : FC n ψ κ τ => True)
        WriterClean X.1 ⟨trivial, X.2⟩ T]
      unfold activeCount
      simp only [treeWeight, stepNode]
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      let D := scrubStep ring X.1 e
      by_cases hD : WriterClean D
      · have hz := avoidCount_zero_of
          (scrubStep ring) (fun _ : FC n ψ κ τ => True)
          WriterClean D (fun h => h.2 hD) T
        have hstop : stopStep ring X e = StopNode.success := by
          unfold stopStep
          dsimp only
          rw [dif_pos hD]
        rw [hstop, FiniteUniformStoppingTree.treeWeight_success]
        simp only [FiniteUniformStoppingTree.activeWeight]
        exact hz.symm
      · have hstop :
          stopStep ring X e = StopNode.active ⟨D, hD⟩ := by
          unfold stopStep
          dsimp only
          rw [dif_neg hD]
        rw [hstop]
        change activeCount (stopStep ring) (.active ⟨D, hD⟩) T = _
        exact ih ⟨D, hD⟩



/-- The existing `scrubB` is already more than large enough. -/
theorem active_half_at_scrubB (ring : DirectedRing n)
    (X : Active n ψ κ τ) :
    2 * activeCount (stopStep ring) (.active X) (scrubB n ψ) ≤
      n ^ (scrubB n ψ) := by
  let B := n * n * (leaseCap ψ + 2)
  let H := scrubB n ψ
  have hcost0 :=
    FiniteUniformStoppingTree.truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (stopStep ring) 1
      (bellmanPotential (n := n) (ψ := ψ) (κ := κ) (τ := τ))
      (natBellman (ψ := ψ) (κ := κ) (τ := τ) ring) (.active X) H
  have hcost :
      1 * FiniteUniformStoppingTree.truncatedActiveCostNumerator
        (stopStep ring) (.active X) H ≤ B * n ^ H := by
    calc
      1 * FiniteUniformStoppingTree.truncatedActiveCostNumerator
          (stopStep ring) (.active X) H ≤
        n ^ H * bellmanPotential (n := n) (.active X) := hcost0
      _ ≤ n ^ H * B := Nat.mul_le_mul_left _
        (by simpa [B] using
          (bellmanPotential_le (n := n) (ψ := ψ) (κ := κ) (τ := τ)
            (.active X)))
      _ = B * n ^ H := Nat.mul_comm _ _
  have hH : 0 < H := by
    have hc : 0 < leaseCap ψ + 1 := by omega
    dsimp [H]
    unfold scrubB
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 4) ring.hn) ring.hn) hc
  have hsmall :
      2 * (leaseCap ψ + 2) ≤ 4 * (leaseCap ψ + 1) := by
    omega
  have hmul := Nat.mul_le_mul_left (n * n) hsmall
  have hscale : 2 * B ≤ H * 1 := by
    dsimp [B, H]
    simp only [scrubB, Nat.mul_one]
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  exact FiniteUniformStoppingTree.two_mul_activeCount_le_pow_of_scaled_cost
    (stopStep ring) (.active X) hH (by decide : 0 < 1) hcost hscale


/-- Discharges the named conditional obligation in `R2WriterLease`. -/
theorem scrubHalfMassObligation (ring : DirectedRing n) :
    R2WriterLease.ScrubHalfMassObligation
      (ψ := ψ) (κ := κ) (τ := τ) ring := by
  unfold R2WriterLease.ScrubHalfMassObligation
  intro C
  by_cases hC : WriterClean C
  · have hz := avoidCount_zero_of
      (scrubStep ring) (fun _ : FC n ψ κ τ => True)
      WriterClean C (fun h => h.2 hC) (scrubB n ψ)
    rw [hz]
    simp [scrubQ]
  · let X : Active n ψ κ τ := ⟨C, hC⟩
    have h := active_half_at_scrubB ring X
    rw [activeCount_eq_avoidCount ring X (scrubB n ψ)] at h
    simpa [X, scrubQ] using h


/-- Public unconditional form of the skeleton theorem. -/
theorem writerScrub_half_mass_unconditional
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    2 * avoidCount (scrubStep ring) (fun _ => True) WriterClean
      C (scrubB n ψ) ≤ n ^ (scrubB n ψ) := by
  exact R2WriterLease.writerScrub_half_mass
    (ψ := ψ) (κ := κ) (τ := τ) ring
    (scrubHalfMassObligation (ψ := ψ) (κ := κ) (τ := τ) ring) C


end ScrubBellman


namespace R2FProducerAudit


open WriterProducerRepair


variable {n ψ κ τ : Nat}


/-- The new R2F root-start guard itself cannot fire at a follower. -/
theorem producerStarts_false_of_follower
    (u : BoundedAgentState ψ κ) (h : u.leader = false) :
    producerStarts u = false := by
  simp [producerStarts, h]


/-- Exact first missing local invariant for the producer-mass proof.


It is deliberately stated on the complete R2F step, not merely on
`stationaryProducerRow`: the accepted proof must cover CHECK, permit handling,
the before-writer suffix, the legacy stationary writer, birth marking,
expiry/normalization, and the final physical tail.  The leaderless-child premise
matches first-hit counting: branches that create a leader are not counted by
`avoidCount ... Leaderless ...`. -/
def InactiveEdgeNoRearm
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : R2F.FC n ψ κ τ) (e : Fin n),
    R2F.Leaderless C →
    producerActive (C e).base.core.core = false →
    producerActive (C (ring.rightNeighbor e)).base.core.core = false →
    let D := R2F.step hψ h2 ring C e
    R2F.Leaderless D →
      producerActive (D e).base.core.core = false ∧
      producerActive (D (ring.rightNeighbor e)).base.core.core = false


/-- After `InactiveEdgeNoRearm`, this is the weighted row inequality that closes
the intended base-3 recovery argument.  Target/leader-producing children are
stopped at weight zero, exactly as in the scrub Bellman construction. -/
noncomputable def ProducerRowDrift
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop := by
  classical
  exact ∀ C : R2F.FC n ψ κ τ,
    R2F.Leaderless C → ¬ R2F.NoProducer C →
      let childWeight := fun e : Fin n =>
        let D := R2F.step hψ h2 ring C e
        if R2F.Leaderless D ∧ ¬ R2F.NoProducer D
        then R2F.producerPotential D else 0
      3 * (List.ofFn childWeight).sum ≤
        (3 * n - 1) * R2F.producerPotential C


/-- This is the exact configuration-level no-rearm corollary one would derive
from `InactiveEdgeNoRearm` plus the step frame.  It is useful to keep the
remaining proof obligation named separately. -/
def NoProducerLeaderlessClosed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : R2F.FC n ψ κ τ) (e : Fin n),
    R2F.Leaderless C → R2F.NoProducer C →
    let D := R2F.step hψ h2 ring C e
    R2F.Leaderless D → R2F.NoProducer D


/-- Source-level audit result: the conditional theorem remains blocked at the
named local invariants above.  In particular, this file intentionally does not
manufacture an assumption-free inhabitant of `R2F.ProducerRecoveryHalfMass`. -/
def ProducerRecoveryMissingInvariant
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  InactiveEdgeNoRearm (κ := κ) (τ := τ) hψ h2 ring ∧
  ProducerRowDrift (κ := κ) (τ := τ) hψ h2 ring


end R2FProducerAudit


end R2WriterLeaseMass
