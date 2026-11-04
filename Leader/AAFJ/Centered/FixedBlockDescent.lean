import Leader.AAFJ.Centered.RankBlockBind
import Leader.AAFJ.Centered.ComplexityConstants
import Leader.Wu.Scheduler.FixedBlockStrongRankDescent

/-!
# Fixed-block descent consumer for the centered AAFJ protocol

This module instantiates the generic block-rounded recurrence at the literal
one-barrier process.  The endpoint-retaining bridge in
`AAFJCenteredRankBlockBind` identifies the padded semantic success mass with
actual raw scheduler words whose fixed-block endpoint has smaller `Phi`.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace CenteredFixedBlockDescent

open SingleBarrierSanitation
open RankBlockBind
open FixedBlockStrongRankDescent

set_option autoImplicit false

abbrev LiteralState {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) :=
  LiteralOneBarrierState hk ring

/-- The physical cut rank carried by the literal one-barrier endpoint. -/
def literalPhiRank {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (state : LiteralState hk ring) : Nat :=
  PhiAt ring state.barrier state.config

/-- Rank above the terminal lane.  This is zero exactly when `Phi = 1`, since
`PhiAt` is always at least one. -/
def literalExcessRank {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (state : LiteralState hk ring) : Nat :=
  literalPhiRank state - 1

/-- One literal raw interaction, including the moving barrier witness. -/
def literalStep {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    LiteralState hk ring -> Fin n -> LiteralState hk ring :=
  fun state edge => state.next hn3 hndvd edge

theorem literalPhiRank_one_le {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (state : LiteralState hk ring) :
    1 <= literalPhiRank state := by
  change 1 <= Phi (cutView ring state.barrier state.config)
  exact Nat.le_max_left _ _

theorem literalExcessRank_pos_iff {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (state : LiteralState hk ring) :
    0 < literalExcessRank state <-> 1 < literalPhiRank state := by
  have hone := literalPhiRank_one_le state
  simp only [literalExcessRank]
  omega

theorem literalExcessRank_lt_iff_phi_lt {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (before after : LiteralState hk ring) :
    literalExcessRank after < literalExcessRank before <->
      literalPhiRank after < literalPhiRank before := by
  have hbefore := literalPhiRank_one_le before
  have hafter := literalPhiRank_one_le after
  simp only [literalExcessRank]
  omega

/-- Literal multiplicity of padded raw words whose actual endpoint has
strictly smaller physical `Phi`. -/
def literalPhiDropMass {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (H : Nat) (state : LiteralState hk ring) : Nat :=
  ((allSchedules n H).map (fun word =>
    let endpoint := runWord (literalStep hn3 hndvd) state word
    if literalPhiRank endpoint < literalPhiRank state then 1 else 0)).sum

/-- Subtracting the terminal floor does not change which literal block
endpoints are strict drops. -/
theorem literalPhiDropMass_eq_excessDropMass
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) (H : Nat)
    (state : LiteralState hk ring) :
    literalPhiDropMass hn3 hndvd H state =
      blockDropMass (literalStep hn3 hndvd) literalExcessRank H state := by
  unfold literalPhiDropMass blockDropMass
  apply congrArg List.sum
  apply List.map_congr_left
  intro word hword
  let endpoint := runWord (literalStep hn3 hndvd) state word
  have hiff := literalExcessRank_lt_iff_phi_lt state endpoint
  by_cases hdrop : literalPhiRank endpoint < literalPhiRank state
  · have hexcess : literalExcessRank endpoint < literalExcessRank state :=
      hiff.mpr hdrop
    simp [endpoint, hdrop, hexcess]
  · have hexcess : ¬ literalExcessRank endpoint < literalExcessRank state :=
      fun h => hdrop (hiff.mp h)
    simp [endpoint, hdrop, hexcess]

/-- The literal excess rank is pathwise nonincreasing on every raw edge. -/
theorem literalStep_excessRank_le
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) (edge : Fin n) :
    literalExcessRank (literalStep hn3 hndvd state edge) <=
      literalExcessRank state := by
  apply Nat.sub_le_sub_right
  exact state.next_rank_le hn3 hndvd edge

private theorem countP_eq_sum_indicator {A : Type} (xs : List A)
    (p : A -> Bool) :
    xs.countP p = (xs.map (fun x => if p x then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
      cases p x <;> simp [Nat.add_comm]

theorem literalRun_config_eq_runLocalSchedule
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) : forall word : List (Fin n),
    (runWord (literalStep hn3 hndvd) state word).config =
      PPLLResearchFormulation.runLocalSchedule ring
        (CenteredRenewal.transition hk)
        state.config word := by
  intro word
  induction word generalizing state with
  | nil => rfl
  | cons edge suffix ih =>
      rw [runWord, PPLLResearchFormulation.runLocalSchedule]
      rw [ih (literalStep hn3 hndvd state edge)]
      congr 1

/-- The raw-endpoint mass used by the generic recurrence is exactly the
physical fixed-horizon mass exported by `RankBlockBind`. -/
theorem literalPhiDropMass_eq_rankBlockMass
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) (H : Nat)
    (state : LiteralState hk ring) :
    literalPhiDropMass hn3 hndvd H state =
      RankBlockBind.literalPhiDropMass hk ring (literalPhiRank state)
        state.config H := by
  unfold literalPhiDropMass RankBlockBind.literalPhiDropMass
  rw [countP_eq_sum_indicator]
  apply congrArg List.sum
  apply List.map_congr_left
  intro word hword
  change (if literalPhiRank (runWord (literalStep hn3 hndvd) state word) <
      literalPhiRank state then 1 else 0) =
    (if physicalRankDropTest hk ring (literalPhiRank state)
      (PPLLResearchFormulation.runLocalSchedule ring
        (CenteredRenewal.transition hk)
        state.config word) then 1 else 0)
  have hconfig := literalRun_config_eq_runLocalSchedule
    hn3 hndvd state word
  have htest : physicalRankDropTest hk ring (literalPhiRank state)
        (PPLLResearchFormulation.runLocalSchedule ring
          (CenteredRenewal.transition hk) state.config word) = true ↔
      literalPhiRank (runWord (literalStep hn3 hndvd) state word) <
        literalPhiRank state := by
    rw [← hconfig]
    exact physicalRankDropTest_at_oneBarrier
      (runWord (literalStep hn3 hndvd) state word).config
      (runWord (literalStep hn3 hndvd) state word).barrier
      (runWord (literalStep hn3 hndvd) state word).oneBarrier
  by_cases hdrop : literalPhiRank
      (runWord (literalStep hn3 hndvd) state word) < literalPhiRank state
  · have htrue : physicalRankDropTest hk ring (literalPhiRank state)
        (PPLLResearchFormulation.runLocalSchedule ring
          (CenteredRenewal.transition hk)
          state.config word) = true := htest.mpr hdrop
    simp [hdrop, htrue]
  · have hfalse : physicalRankDropTest hk ring (literalPhiRank state)
        (PPLLResearchFormulation.runLocalSchedule ring
          (CenteredRenewal.transition hk)
          state.config word) = false := by
      cases h : physicalRankDropTest hk ring (literalPhiRank state)
          (PPLLResearchFormulation.runLocalSchedule ring
            (CenteredRenewal.transition hk)
            state.config word)
      · rfl
      · exact False.elim (hdrop (htest.mp h))
    simp [hdrop, hfalse]

/-- Unconditional capstone for the strict-rank phase.  Every semantic block
success is already bridged to a literal scheduler word ending at lower `Phi`.
-/
theorem centeredPaddedRankDescent_truncatedCost_le
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) :
    forall (state : LiteralState hk ring) J,
      truncatedRoundedCostNumerator
          (literalStep hn3 hndvd) literalExcessRank
          (AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n)
          state J <=
        (n ^ AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n) ^ J *
          (32 * AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n *
            literalExcessRank state) := by
  apply truncatedRoundedCostNumerator_le_of_dropMass
    (literalStep hn3 hndvd) literalExcessRank
    (AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n) 32
    (literalStep_excessRank_le hn3 hndvd)
  intro state hpositive
  have hr1 : 1 < literalPhiRank state :=
    (literalExcessRank_pos_iff state).mp hpositive
  have hraw := literalPhiDropMass_one_over_thirty_two_padded_horizon
    hk ring hn3 hndvd state.config state.barrier state.oneBarrier rfl hr1
  change n ^ AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n <=
    32 * RankBlockBind.literalPhiDropMass hk ring (literalPhiRank state)
      state.config
        (AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n) at hraw
  rw [← literalPhiDropMass_eq_rankBlockMass hn3 hndvd
    (AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n) state]
    at hraw
  have hrawH :
      n ^ AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n <=
        32 * literalPhiDropMass hn3 hndvd
          (AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n)
          state := by
    simpa [AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon]
      using hraw
  simpa [literalPhiDropMass_eq_excessDropMass hn3 hndvd
    (AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n) state]
    using hrawH

private theorem bitCount_le_size {n : Nat} (bits : Fin n -> Bool) :
    bitCount bits <= n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      rw [bitCount_succ]
      have htail := ih (fun i : Fin n => bits i.succ)
      split <;> omega

/-- Every literal one-barrier state has excess rank at most the ring size. -/
theorem literalExcessRank_le_size
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (state : LiteralState hk ring) : literalExcessRank state <= n := by
  have hleaders : leaderCount (cutView ring state.barrier state.config) <= n :=
    bitCount_le_size _
  have hdanger := dangerBit_le_one (cutView ring state.barrier state.config)
  simp only [literalExcessRank, literalPhiRank, PhiAt, Phi]
  omega

/-- The Bellman potential is bounded by the published strict-rank budget
`32 * n * (16*n^2+2*n)` for every literal starting state. -/
theorem centeredPaddedRankDescent_truncatedCost_le_publishedBudget
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (state : LiteralState hk ring) (J : Nat) :
    truncatedRoundedCostNumerator
        (literalStep hn3 hndvd) literalExcessRank
        (AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n)
        state J <=
      (n ^ AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n) ^ J *
        AAFJPK.CenteredRenewal.ComplexityConstants.rankDescentBudget n := by
  have hmain := centeredPaddedRankDescent_truncatedCost_le
    hk ring hn3 hndvd state J
  refine Nat.le_trans hmain (Nat.mul_le_mul_left _ ?_)
  unfold AAFJPK.CenteredRenewal.ComplexityConstants.rankDescentBudget
  calc
    32 * AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n *
          literalExcessRank state <=
        32 * AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n * n :=
      Nat.mul_le_mul_left
        (32 * AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n)
        (literalExcessRank_le_size state)
    _ = 32 * n *
        AAFJPK.CenteredRenewal.ComplexityConstants.rankBlockHorizon n := by
      ac_rfl

end CenteredFixedBlockDescent
end CenteredRenewal
end AAFJPK
