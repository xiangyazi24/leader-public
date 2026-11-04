import Leader.AAFJ.Centered.Protocol
import Leader.AAFJ.OneBarrier.Sanitation

/-!
# Clean closure for the centered-renewal AAFJ variant

This module reuses the protocol-independent cut geometry and clean predicate
from `AAFJSingleBarrierSanitation`.  The centered transition differs from the
source transition only at a phase-one barrier whose responder already carries
a probe.  The source transition waits there; the centered transition advances
the barrier and clears that responder probe.  The exceptional branch therefore
preserves clean data by deletion of a mark followed by the existing cut
rotation lemma.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace Sanitation

open BarrierAlgebra
open SingleBarrierSanitation

set_option autoImplicit false

/-- The only local state in which the centered and source transitions differ. -/
def Exceptional {k : Nat} (hk : 0 < k) (u v : State k) : Prop :=
  IsBarrier hk u v ∧ u.phase = true ∧ v.probe = true

instance instDecidableAdvanceReady {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (e : Fin n) :
    Decidable (AAFJPK.CenteredRenewal.AdvanceReady hk ring C e) := by
  unfold AAFJPK.CenteredRenewal.AdvanceReady
    AAFJPK.CenteredRenewal.PairAdvanceReady
  infer_instance

theorem transition_eq_source_of_not_exceptional {k : Nat} (hk : 0 < k)
    (u v : State k) (h : ¬ Exceptional hk u v) :
    CenteredRenewal.transition hk u v = AAFJPK.transition hk u v := by
  by_cases hbar : IsBarrier hk u v
  · cases hphase : u.phase with
    | false =>
        rw [AAFJPK.CenteredRenewal.transition_of_barrier hk u v hbar,
          AAFJPK.transition_of_barrier hk u v hbar,
          AAFJPK.CenteredRenewal.barrierStep_phase_zero hk u v hphase,
          AAFJPK.barrierStep_phase_zero hk u v hphase]
    | true =>
        have hprobe : v.probe = false := by
          cases hv : v.probe
          · rfl
          · exact False.elim (h ⟨hbar, hphase, hv⟩)
        rw [AAFJPK.CenteredRenewal.transition_of_barrier hk u v hbar,
          AAFJPK.transition_of_barrier hk u v hbar,
          AAFJPK.CenteredRenewal.barrierStep_phase_one hk u v hphase,
          AAFJPK.barrierStep_phase_one_probe_free hk u v hphase hprobe]
        simp [hprobe]
  · rw [AAFJPK.CenteredRenewal.transition_of_nonbarrier hk u v hbar,
      AAFJPK.transition_of_nonbarrier hk u v hbar]

/-- Exact next-barrier location for one centered step. -/
theorem oneBarrierAt_step {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b e : Fin n)
    (hndvd : ¬ k ∣ n) (hone : OneBarrierAt hk ring C b) :
    let D := (AAFJPK.CenteredRenewal.protocol k hk).step ring C e
    OneBarrierAt hk ring D
      (if AAFJPK.CenteredRenewal.AdvanceReady hk ring C e then
        ring.rightNeighbor b else b) := by
  let D : Fin n → State k :=
    fun j => ((AAFJPK.CenteredRenewal.protocol k hk).step ring C e) j
  have hcountC := oneBarrierAt_barrierCount_eq_one hk ring C b hone
  have hcountD := AAFJPK.CenteredRenewal.protocol_step_preserves_oneBarrier
    hk ring hn2 C e hndvd hcountC
  by_cases hready : AAFJPK.CenteredRenewal.AdvanceReady hk ring C e
  · have heb : e = b := by
      apply (hone e).1
      exact (barrierAt_labelsOf_iff hk ring C e).2 hready.1
    subst e
    simp only [hready, if_true]
    apply oneBarrierAt_of_count_one_of_unique hk ring D
      (ring.rightNeighbor b) hcountD
    intro j hj
    by_cases hjb : j = b
    · subst j
      have hlabels := CenteredRenewal.labelsOf_step_eq_advance_of_ready
        hk ring hn2 C b hready
      have hj' := hj
      rw [hlabels] at hj'
      exact False.elim
        ((advance_repairs_edge hk ring hn2 (labelsOf C) b) hj')
    · by_cases hjr : j = ring.rightNeighbor b
      · exact hjr
      · have hlabels := CenteredRenewal.labelsOf_step_eq_advance_of_ready
            hk ring hn2 C b hready
        have hsame := defect_advance_other hk ring (labelsOf C) b j hjb hjr
        have hnew : defect hk ring (labelsOf D) j ≠ zeroResidue hk := hj
        have hold : defect hk ring (labelsOf C) j ≠ zeroResidue hk := by
          intro hz
          apply hnew
          rw [hlabels, hsame, hz]
        exact False.elim (hjb ((hone j).1 hold))
  · simp only [hready, if_false]
    have hlabels := CenteredRenewal.labelsOf_step_eq_self_of_not_ready
      hk ring C e hready
    intro j
    rw [← hone j]
    unfold BarrierAt
    rw [hlabels]

theorem cleanData_of_leaders_eq_marks_subset {n k : Nat}
    {X Y : Fin n → State k} {ell : Fin n}
    (hclean : CleanData X ell)
    (hleaders : ∀ i, (Y i).leader = (X i).leader)
    (hmarks : ∀ i, Marked (Y i) → Marked (X i)) :
    CleanData Y ell := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hleaders]
    exact hclean.1
  · intro i hi
    apply hclean.2.1 i
    rw [← hleaders i]
    exact hi
  · intro i hi
    exact hclean.2.2 i (hmarks i hi)

/-- In the exceptional centered branch, leaders are unchanged and marks only
disappear. -/
theorem exceptional_step_frames {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hex : Exceptional hk (C e) (C (ring.rightNeighbor e)))
    (htailProbe : (C e).probe = false) :
    let D := (AAFJPK.CenteredRenewal.protocol k hk).step ring C e
    (∀ i, (D i).leader = (C i).leader) ∧
      (∀ i, Marked (D i) → Marked (C i)) ∧
      (D (ring.rightNeighbor e)).bullet = false ∧
      (D (ring.rightNeighbor e)).probe = false := by
  let D := (CenteredRenewal.protocol k hk).step ring C e
  have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
  rcases hex with ⟨hbar, hphase, hheadProbe⟩
  have hpair := CenteredRenewal.barrierStep_phase_one hk
    (C e) (C (ring.rightNeighbor e)) hphase
  have htrans : CenteredRenewal.transition hk
      (C e) (C (ring.rightNeighbor e)) =
      (probeHitsBarrier (C e),
        { C (ring.rightNeighbor e) with
          label := succLabel hk (C e).label
          phase := false
          bullet := false
          probe := false }) := by
    rw [CenteredRenewal.transition_of_barrier hk _ _ hbar]
    exact hpair
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hie : i = e
    · subst i
      simp [D, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
        probeHitsBarrier, htailProbe, hre]
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        simp [D, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
          hre]
      · simp [D, PopulationProtocol.step, CenteredRenewal.protocol,
          hie, hir]
  · intro i hi
    by_cases hie : i = e
    · subst i
      simpa [D, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
        probeHitsBarrier, htailProbe, hre] using hi
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        simp [Marked, D, PopulationProtocol.step, CenteredRenewal.protocol,
          htrans, hre] at hi
      · simpa [D, PopulationProtocol.step, CenteredRenewal.protocol,
          hie, hir] using hi
  · simp [D, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      hre]
  · simp [D, PopulationProtocol.step, CenteredRenewal.protocol, htrans,
      hre]

/-- Clean closure with the same physical leader for one centered step. -/
theorem cleanAt_step_sameLeader {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b ell e : Fin n)
    (hndvd : ¬ k ∣ n) (hclean : CleanAt hk ring C b ell) :
    let D := (CenteredRenewal.protocol k hk).step ring C e
    let b' := if AAFJPK.CenteredRenewal.AdvanceReady hk ring C e then
      ring.rightNeighbor b else b
    CleanAt hk ring D b' ell := by
  let D : Fin n → State k :=
    fun j => ((AAFJPK.CenteredRenewal.protocol k hk).step ring C e) j
  let b' := if AAFJPK.CenteredRenewal.AdvanceReady hk ring C e then
    ring.rightNeighbor b else b
  have hn2 : 1 < n := by omega
  have honeD : OneBarrierAt hk ring D b' := by
    dsimp only [D, b']
    exact oneBarrierAt_step hk ring hn2 C b e hndvd hclean.1
  refine ⟨honeD, ?_⟩
  by_cases hex : Exceptional hk (C e) (C (ring.rightNeighbor e))
  · rcases hex with ⟨hbar, hphase, hheadProbe⟩
    have heb : e = b := by
      exact (hclean.1 e).1 ((barrierAt_labelsOf_iff hk ring C e).2 hbar)
    subst e
    have hready : AAFJPK.CenteredRenewal.AdvanceReady hk ring C b :=
      ⟨hbar, hphase⟩
    simp only [b', hready, if_true]
    have htailFree := cleanData_tail_markFree ring hclean.2
    have htailProbe : (C b).probe = false := by
      have hpos := cutPos_tailCoord ring b
      simpa [cutView, hpos] using htailFree.2
    have hframes := exceptional_step_frames hk ring hn2 C b
      ⟨hbar, hphase, hheadProbe⟩ htailProbe
    have hdataOld : CleanData (cutView ring b D)
        (cutCoord ring b ell) := by
      apply cleanData_of_leaders_eq_marks_subset hclean.2
      · intro i
        exact hframes.1 (cutPos ring b i)
      · intro i hi
        exact hframes.2.1 (cutPos ring b i) hi
    have hheadFree :
        ((cutView ring b D) ⟨0, ring.hn⟩).bullet = false ∧
        ((cutView ring b D) ⟨0, ring.hn⟩).probe = false := by
      have hheadPos : cutPos ring b ⟨0, ring.hn⟩ = ring.rightNeighbor b :=
        cutPos_zero ring b
      simpa [cutView, hheadPos] using hframes.2.2
    have hrot := cleanData_rotateCut ring (cutView ring b D)
      (cutCoord ring b ell) hdataOld hheadFree
    change CleanData (cutView ring (ring.rightNeighbor b) D)
      (cutCoord ring (ring.rightNeighbor b) ell)
    rw [SingleBarrierSanitation.cutCoord_nextBarrier ring b ell]
    rw [SingleBarrierSanitation.cutView_nextBarrier ring b D]
    exact hrot
  · have hlocal := transition_eq_source_of_not_exceptional hk
      (C e) (C (ring.rightNeighbor e)) hex
    have hstepEq : D = (AAFJPK.protocol k hk).step ring C e := by
      funext i
      have hre := BarrierAlgebra.rightNeighbor_ne_self ring hn2 e
      by_cases hie : i = e
      · subst i
        simp [D, PopulationProtocol.step, CenteredRenewal.protocol,
          AAFJPK.protocol, hlocal, hre]
      · by_cases hir : i = ring.rightNeighbor e
        · subst i
          simp [D, PopulationProtocol.step, CenteredRenewal.protocol,
            AAFJPK.protocol, hlocal, hre]
        · simp [D, PopulationProtocol.step, CenteredRenewal.protocol,
            AAFJPK.protocol, hie, hir]
    have hreadyIff :
        AAFJPK.CenteredRenewal.AdvanceReady hk ring C e ↔
          BarrierAlgebra.AdvanceReady hk ring C e := by
      unfold AAFJPK.CenteredRenewal.AdvanceReady
        AAFJPK.CenteredRenewal.PairAdvanceReady
        BarrierAlgebra.AdvanceReady BarrierAlgebra.PairAdvanceReady
      constructor
      · intro h
        refine ⟨h.1, h.2, ?_⟩
        cases hp : (C (ring.rightNeighbor e)).probe
        · rfl
        · exact False.elim (hex ⟨h.1, h.2, hp⟩)
      · intro h
        exact ⟨h.1, h.2.1⟩
    have hsource := SingleBarrierSanitation.cleanAt_step_sameLeader
      hk ring hn3 C b ell e hndvd hclean
    dsimp only at hsource
    have hbEq :
        (if AAFJPK.CenteredRenewal.AdvanceReady hk ring C e then
          ring.rightNeighbor b else b) =
        (if BarrierAlgebra.AdvanceReady hk ring C e then
          ring.rightNeighbor b else b) := by
      by_cases hc : AAFJPK.CenteredRenewal.AdvanceReady hk ring C e
      · have hs : BarrierAlgebra.AdvanceReady hk ring C e := hreadyIff.1 hc
        simp [hc, hs]
      · have hs : ¬ BarrierAlgebra.AdvanceReady hk ring C e := by
          exact fun h => hc (hreadyIff.2 h)
        simp [hc, hs]
    change CleanData (cutView ring b' D) (cutCoord ring b' ell)
    rw [hstepEq]
    rw [show b' =
        (if BarrierAlgebra.AdvanceReady hk ring C e then
          ring.rightNeighbor b else b) by exact hbEq]
    exact hsource.2

/-- The fixed-physical-leader clean slice is closed for the centered protocol. -/
theorem cleanForLeader_step {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (ell : Fin n) (C : Fin n → State k)
    (hclean : CleanForLeader hk ring ell C) (e : Fin n) :
    CleanForLeader hk ring ell
      ((AAFJPK.CenteredRenewal.protocol k hk).step ring C e) := by
  obtain ⟨b, hb⟩ := hclean
  refine ⟨if AAFJPK.CenteredRenewal.AdvanceReady hk ring C e then
    ring.rightNeighbor b else b, ?_⟩
  simpa using cleanAt_step_sameLeader hk ring hn3 C b ell e hndvd hb

theorem cleanForLeader_closed {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (ell : Fin n) :
    PopulationProtocol.ClosedPred (AAFJPK.CenteredRenewal.protocol k hk) ring
      (CleanForLeader hk ring ell) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  exact cleanForLeader_step hk ring hn3 hndvd ell C hC e

theorem cleanForLeader_reachable {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (ell : Fin n) {C C' : Fin n → State k}
    (hC : CleanForLeader hk ring ell C)
    (hr : PopulationProtocol.Reachable
      (AAFJPK.CenteredRenewal.protocol k hk) ring C C') :
    CleanForLeader hk ring ell C' := by
  exact (cleanForLeader_closed hk ring hn3 hndvd ell).reachable hC hr

theorem clean_step {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (hclean : Clean hk ring C) (e : Fin n) :
    Clean hk ring ((AAFJPK.CenteredRenewal.protocol k hk).step ring C e) := by
  obtain ⟨ell, hell⟩ := hclean
  exact ⟨ell, cleanForLeader_step hk ring hn3 hndvd ell C hell e⟩

theorem clean_closed {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n) :
    PopulationProtocol.ClosedPred (AAFJPK.CenteredRenewal.protocol k hk) ring
      (Clean hk ring) := by
  intro C hC C' hstep
  obtain ⟨e, rfl⟩ := hstep
  exact clean_step hk ring hn3 hndvd C hC e

/-- A centered clean witness already gives the repository's semantic safety
predicate, with the same physical leader throughout every continuation. -/
theorem cleanAt_isSafe {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b ell : Fin n)
    (hclean : CleanAt hk ring C b ell) :
    PopulationProtocol.IsSafe (AAFJPK.CenteredRenewal.protocol k hk) ring C
      (fun bit => bit) := by
  constructor
  · refine ⟨ell, cleanAt_physical_leader hk ring C b ell hclean, ?_⟩
    intro i hi
    exact cleanAt_unique_physical_leader hk ring C b ell i hclean hi
  · intro C' hr i
    obtain ⟨b', hclean'⟩ := cleanForLeader_reachable hk ring hn3 hndvd
      ell ⟨b, hclean⟩ hr
    change (C' i).leader = (C i).leader
    have hout := cleanAt_output_eq_of_sameLeader hk ring C C' b b' ell
      hclean hclean' i
    exact hout

theorem cleanForLeader_isSafe {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (ell : Fin n)
    (hclean : CleanForLeader hk ring ell C) :
    PopulationProtocol.IsSafe (AAFJPK.CenteredRenewal.protocol k hk) ring C
      (fun bit => bit) := by
  obtain ⟨b, hb⟩ := hclean
  exact cleanAt_isSafe hk ring hn3 hndvd C b ell hb

/-- The existential clean predicate is already a semantic safety certificate. -/
theorem clean_isSafe {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (hclean : Clean hk ring C) :
    PopulationProtocol.IsSafe (AAFJPK.CenteredRenewal.protocol k hk) ring C
      (fun bit => bit) := by
  obtain ⟨ell, hell⟩ := hclean
  exact cleanForLeader_isSafe hk ring hn3 hndvd C ell hell

end Sanitation
end CenteredRenewal
end AAFJPK
