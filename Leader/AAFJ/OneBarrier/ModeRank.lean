import Leader.AAFJ.OneBarrier.OddZeroModeDebt
import Leader.AAFJ.OneBarrier.SelectedMultipleUniqueSafe
import Leader.AAFJ.OneBarrier.PhaseAwareMacroRank

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.OneBarrierModeRankConsumer

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.SingleBarrierSanitation
open AAFJPK.SingleBarrierSanitation.DirtyTailBellman
open AAFJPK.OriginalNonbarrierWord
open AAFJPK.OriginalUniqueLeaderCleanup
open AAFJPK.OriginalDangerousProbeChase
open AAFJPK.OriginalMultipleLeaderOneBarrier
open AAFJPK.SelectedMultipleUniqueSafe
open AAFJPK.OddZeroPhiFamily
open AAFJPK.OddZeroModeDebt
open AAFJPK.CenteredRenewal.OneBarrierCleanup

/-!
This consumer records exactly the three state observables currently connected
by accepted original-Protocol-6 producers.  `PhiAt` pays for every strict
potential edge.  `zeroModeDebt` pays for the odd zero-leader birth plateau.
The finite mode coordinate distinguishes a dangerous unique leader from the
multiple state created by its selected tail hit.  `dirtyCtl` is retained as
the final, local history coordinate.

The order is intentionally explicit.  It is a certificate for the connected
producer edges proved below, rather than a total transition relation.
-/

/-- Finite control-mode rank: safe Unique is `0`, Zero or Multiple is `1`,
and dangerous Unique is `2`. -/
def finiteModeRank {n k : Nat} (ring : DirectedRing n) (b : Fin n)
    (C : Fin n → State k) : Nat :=
  if leaderCount C = 1 then
    if Dangerous (cutView ring b C) then 2 else 0
  else 1

/-- The one-barrier consumer payload. -/
def modeHistoryRank {n k : Nat} (ring : DirectedRing n) (b : Fin n)
    (C : Fin n → State k) : Nat × Nat × Nat × Nat :=
  (PhiAt ring b C, zeroModeDebt C, finiteModeRank ring b C, dirtyCtl C b)

/-- Strict lexicographic decrease of the displayed four coordinates. -/
def StrictRankDrop {n k : Nat} (ring : DirectedRing n)
    (b : Fin n) (C : Fin n → State k)
    (b' : Fin n) (D : Fin n → State k) : Prop :=
  PhiAt ring b' D < PhiAt ring b C ∨
    (PhiAt ring b' D = PhiAt ring b C ∧
      (zeroModeDebt D < zeroModeDebt C ∨
        (zeroModeDebt D = zeroModeDebt C ∧
          (finiteModeRank ring b' D < finiteModeRank ring b C ∨
            (finiteModeRank ring b' D = finiteModeRank ring b C ∧
              dirtyCtl D b' < dirtyCtl C b)))))

/-- The accepted odd-family birth is the first generic strict edge: `PhiAt`
stays at one, while the zero-leader debt is paid. -/
theorem oddZero_selected_birth_rank_drop
    {m : Nat} (hm : 1 ≤ m) :
    ∃ w b' ell,
      w.length ≤ (2 * m + 1) + 2 ∧
      OneBarrierAt OddZeroPhiFamily.hk2 (oddRing m)
        (rawRun OddZeroPhiFamily.hk2 (oddRing m) (oddZero m) w) b' ∧
      UniqueLeaderAt
        (rawRun OddZeroPhiFamily.hk2 (oddRing m) (oddZero m) w) ell ∧
      StrictRankDrop (oddRing m) (oddTail m) (oddZero m) b'
        (rawRun OddZeroPhiFamily.hk2 (oddRing m) (oddZero m) w) := by
  obtain ⟨w, b', ell, hw, hB, hphi, hU, hdebt⟩ :=
    oddZero_selected_birth_decreases hm
  refine ⟨w, b', ell, hw, hB, hU, Or.inr ⟨?_, Or.inl hdebt⟩⟩
  exact hphi.trans (oddZero_phi_one hm).symm

/-- If the literal parked-sweep/discharge endpoint selected by the Multiple
producer is Unique, the accepted endpoint theorem makes it a strict rank edge
by lowering `PhiAt` to one.  No existence claim for that branch is added. -/
theorem multiple_selected_unique_rank_drop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hmulti : OriginalMultipleLeaderOneBarrier.MultipleLeaders C) :
    let ws := parkedSweepWord ring b
    let S := rawRun hk ring C ws
    let wd := endpointDischargeWord S b
    let b' := endpointDischargeBarrier ring S b
    let D := rawRun hk ring S wd
    ∀ _hunique : ∃ ell, UniqueLeaderAt D ell,
      ¬ Dangerous (cutView ring b' D) ∧
      StrictRankDrop ring b C b' D := by
  dsimp
  intro _hunique
  have hsafe := multiple_selected_unique_endpoint_safe
    hk ring hn3 hndvd C b hone hmulti _hunique
  have hdrop := multiple_selected_unique_endpoint_phi_drop
    hk ring hn3 hndvd C b hone hmulti _hunique
  exact ⟨hsafe.1, Or.inl hdrop⟩

/-! The following two fixtures are not arbitrary raw transitions.  The first
is the exact `macroWord` chosen by the dangerous-probe chase.  Its Multiple
endpoint is then fed to the exact parked-sweep/discharge word of the selected
Multiple producer. -/

open AAFJPK.OriginalPhaseAwareMacroRank

theorem dangerous_chase_fixture_rank_drop :
    macroWord ring3 (2 : Fin 3) (2 : Fin 3) = [2] ∧
      rawRun OriginalPhaseAwareMacroRank.hk2 ring3 U0
        (macroWord ring3 (2 : Fin 3) (2 : Fin 3)) = U1 ∧
      StrictRankDrop ring3 2 U0 2 U1 := by
  refine ⟨dangerous_tail_macroWord_is_source_word.1,
    dangerous_tail_macroWord_is_source_word.2.2, ?_⟩
  unfold StrictRankDrop finiteModeRank zeroModeDebt
  decide +kernel

theorem dangerous_then_selected_multiple_fixture_rank_drop :
    U1MacroWord = parkedSweepWord ring3 (2 : Fin 3) ++
        endpointDischargeWord U1S (2 : Fin 3) ∧
      (∃ ell, UniqueLeaderAt U1D ell) ∧
      StrictRankDrop ring3 2 U1
        (endpointDischargeBarrier ring3 U1S (2 : Fin 3)) U1D := by
  have hmulti : OriginalMultipleLeaderOneBarrier.MultipleLeaders U1 := by
    refine ⟨1, 2, by decide, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  refine ⟨rfl, multiple_macro_U1_endpoint.2.1, ?_⟩
  exact Or.inl (multiple_selected_unique_endpoint_phi_drop
    OriginalPhaseAwareMacroRank.hk2 ring3 (by decide)
    (by decide) U1 2 (by decide +kernel) hmulti
    multiple_macro_U1_endpoint.2.1)

/-- Local dirty-tail order used by the existing two-service history macro. -/
def DirtyRankDrop {n k : Nat} (ring : DirectedRing n)
    (b : Fin n) (C : Fin n → State k)
    (b' : Fin n) (D : Fin n → State k) : Prop :=
  PhiAt ring b' D < PhiAt ring b C ∨
    (PhiAt ring b' D = PhiAt ring b C ∧ dirtyCtl D b' < dirtyCtl C b)

/-- The existing dirty-tail macro is a real strict edge of its local history
order: two literal incoming services keep `PhiAt = 1` and clear the tail debt. -/
theorem dirtyTail_two_incoming_dirty_rank_drop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hphi : PhiAt ring b C = 1)
    (hbullet : (C b).bullet = true) :
    let p := ring.leftNeighbor b
    let D := rawRun hk ring C [p, p]
    CurrentNonbarrierWord hk ring C [p, p] ∧
      OneBarrierAt hk ring D b ∧ DirtyRankDrop ring b C b D := by
  obtain ⟨hword, hB, hphiD, hclear, _⟩ :=
    dirtyTail_two_incoming_clear hk ring hn3 hndvd C b hone hphi hbullet
  refine ⟨hword, hB, Or.inr ⟨hphiD.trans hphi.symm, ?_⟩⟩
  have hclear' : (rawRun hk ring C
      [ring.leftNeighbor b, ring.leftNeighbor b] b).bullet = false := by
    simpa only [rawRun] using hclear
  simp only [dirtyCtl, hclear', hbullet, Bool.false_eq_true, if_false,
    if_true]
  have ha : 0 ≤ (if (C b).leader = true then 1 else 0) := Nat.zero_le _
  have hp : 0 ≤ (if (C b).probe = true then 1 else 0) := Nat.zero_le _
  omega

/-- The dirty edge embeds in the four-coordinate rank exactly when the earlier
zero and finite-mode coordinates are stable.  These hypotheses identify the
remaining connector obligation without asserting that all dirty endpoints
preserve them. -/
theorem dirtyRankDrop_to_rankDrop_of_mode_stable
    {n k : Nat} (ring : DirectedRing n)
    (b : Fin n) (C D : Fin n → State k)
    (hdirty : DirtyRankDrop ring b C b D)
    (hzero : zeroModeDebt D = zeroModeDebt C)
    (hmode : finiteModeRank ring b D = finiteModeRank ring b C) :
    StrictRankDrop ring b C b D := by
  rcases hdirty with hphi | ⟨hphi, hctl⟩
  · exact Or.inl hphi
  · exact Or.inr ⟨hphi, Or.inr ⟨hzero, Or.inr ⟨hmode, hctl⟩⟩⟩

/-! The maximal connected subgraph above cannot yet include the accepted safe
Unique cleanup edge.  That literal endpoint preserves `PhiAt` but has zero
leaders, so `zeroModeDebt` rises from `0` to `1`.  This concrete theorem is the
exact obstruction; it does not deny that a larger history-sensitive rank may
orient the edge. -/
theorem safe_cleanup_is_exact_missing_rank_edge :
    SafeEndpoint = rawRun OriginalPhaseAwareMacroRank.hk2 ring3 SafeUnique
        [2, 0, 0, 2] ∧
      OneBarrierAt OriginalPhaseAwareMacroRank.hk2 ring3 SafeEndpoint 0 ∧
      zeroModeDebt SafeUnique = 0 ∧
      zeroModeDebt SafeEndpoint = 1 ∧
      PhiAt ring3 0 SafeEndpoint = PhiAt ring3 2 SafeUnique ∧
      ¬ StrictRankDrop ring3 2 SafeUnique 0 SafeEndpoint := by
  have h := safe_branch_mode_loss
  have hsource : zeroModeDebt SafeUnique = 0 := by
    unfold zeroModeDebt
    have hc : leaderCount SafeUnique = 1 := by decide +kernel
    simp [hc]
  have hend : zeroModeDebt SafeEndpoint = 1 := by
    unfold zeroModeDebt
    simp [h.2.2.2.2.1]
  refine ⟨rfl, h.2.2.2.1, hsource, hend, h.2.2.2.2.2.2.2.2, ?_⟩
  intro hdrop
  unfold StrictRankDrop at hdrop
  rw [h.2.2.2.2.2.2.2.2, hsource, hend] at hdrop
  omega

#print axioms oddZero_selected_birth_rank_drop
#print axioms multiple_selected_unique_rank_drop
#print axioms dangerous_chase_fixture_rank_drop
#print axioms dangerous_then_selected_multiple_fixture_rank_drop
#print axioms dirtyTail_two_incoming_dirty_rank_drop
#print axioms dirtyRankDrop_to_rankDrop_of_mode_stable
#print axioms safe_cleanup_is_exact_missing_rank_edge

end AAFJPK.OneBarrierModeRankConsumer
