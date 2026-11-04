import Leader.AAFJ.OneBarrier.HistoryCreditConsumer

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.SafeUniqueTailDirty

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.SingleBarrierSanitation
open AAFJPK.SingleBarrierSanitation.DirtyTailBellman
open AAFJPK.OddZeroModeDebt
open AAFJPK.OddZeroPhiFamily
open AAFJPK.GenericOneBarrierHistoryCredit
open AAFJPK.OneBarrierModeHistoryCredit
open AAFJPK.OneBarrierModeRankConsumer
open AAFJPK.OriginalNonbarrierWord
open AAFJPK.OriginalPushOne
open AAFJPK.OriginalUniqueLeaderCleanup
open AAFJPK.OriginalPhaseAwareMacroRank

/-!
The live-bullet counterexample does not require another history bit.  In its
actual Protocol-6 word `[2,0,0,2]`, the barrier moves from `2` to `0` and the
phase-one advance clears the old incoming bullet at the new tail.  The
existing local observable `dirtyCtl` therefore pays the edge after the four
earlier history coordinates are held fixed.
-/

/-- The final local dirty-tail coordinate orients an edge once all earlier
coordinates in `HistoryModeDrop` are equal. -/
theorem historyModeDrop_of_prefix_eq_dirtyCtl_lt
    {n k : Nat} (ring : DirectedRing n)
    (b b' : Fin n) (C D : Fin n → State k)
    (hphi : PhiAt ring b' D = PhiAt ring b C)
    (hcredit : historyCredit D = historyCredit C)
    (hdebt : zeroModeDebt D = zeroModeDebt C)
    (hmode : finiteModeRank ring b' D = finiteModeRank ring b C)
    (hdirty : dirtyCtl D b' < dirtyCtl C b) :
    HistoryModeDrop ring b C b' D := by
  unfold HistoryModeDrop historyModeList
  simp [lexNat, hphi, hcredit, hdebt, hmode, hdirty]

/-! The public exact-word producer already exposes the physical fact needed by
this coordinate: a one-barrier push puts a bullet-free head at the successor
barrier.  If the source tail is carrying a bullet, `dirtyCtl` therefore drops
without any history invariant or endpoint classification. -/

theorem pushWord_dirtyCtl_drop_of_tail_bullet
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hbullet : (C b).bullet = true) :
    dirtyCtl
      (rawRun hk ring C (OriginalPushOne.pushWord hk ring C b))
      (ring.rightNeighbor b) < dirtyCtl C b := by
  have hfresh := OriginalUniqueLeaderCleanup.pushWord_oneBarrier_fresh
    hk ring hn3 hndvd C b hB
  obtain ⟨_, _, hclear, _⟩ := hfresh
  simp [dirtyCtl, hclear, hbullet]
  omega

theorem safe_unique_tail_bullet_pushWord_is_actual_word :
    OriginalPushOne.pushWord phaseHk2 phaseRing3 SafeUniqueTailBullet 2 =
      [2, 0, 0, 2] := by
  have hready : ¬ AdvanceReady phaseHk2 phaseRing3
      SafeUniqueTailBullet 2 := by
    decide +kernel
  have hnext : phaseRing3.rightNeighbor 2 = 0 := by
    simp [DirectedRing.rightNeighbor]
  simp [OriginalPushOne.pushWord, hready, hnext]

theorem safe_unique_tail_bullet_pushWord_dirty_drop :
    dirtyCtl SafeUniqueTailBulletEndpoint 0 <
      dirtyCtl SafeUniqueTailBullet 2 := by
  have hB : OneBarrierAt phaseHk2 phaseRing3 SafeUniqueTailBullet 2 := by
    decide +kernel
  have hbullet : (SafeUniqueTailBullet 2).bullet = true := by
    decide +kernel
  have hdrop := pushWord_dirtyCtl_drop_of_tail_bullet
    phaseHk2 phaseRing3 (by decide) (by decide)
    SafeUniqueTailBullet 2 hB hbullet
  have hnext : phaseRing3.rightNeighbor 2 = 0 := by
    simp [DirectedRing.rightNeighbor]
  simpa [SafeUniqueTailBulletEndpoint,
    safe_unique_tail_bullet_pushWord_is_actual_word, hnext] using hdrop

/-- Exact profile of the source-grounded `[2,0,0,2]` safe-Unique fixture.
The live-bullet credit is unchanged; the old barrier tail carries dirty debt
`2`, while the new tail is clean with debt `0`. -/
theorem safe_unique_tail_bullet_coordinate_profile :
    PhiAt phaseRing3 0 SafeUniqueTailBulletEndpoint =
        PhiAt phaseRing3 2 SafeUniqueTailBullet ∧
      historyCredit SafeUniqueTailBulletEndpoint =
        historyCredit SafeUniqueTailBullet ∧
      zeroModeDebt SafeUniqueTailBulletEndpoint =
        zeroModeDebt SafeUniqueTailBullet ∧
      finiteModeRank phaseRing3 0 SafeUniqueTailBulletEndpoint =
        finiteModeRank phaseRing3 2 SafeUniqueTailBullet ∧
      dirtyCtl SafeUniqueTailBulletEndpoint 0 = 0 ∧
      dirtyCtl SafeUniqueTailBullet 2 = 2 := by
  decide +kernel

/-- The actual counterexample edge is strictly oriented by the existing
`dirtyCtl` coordinate, with no additional history state. -/
theorem safe_unique_tail_bullet_history_mode_drop :
    HistoryModeDrop phaseRing3 2 SafeUniqueTailBullet
      0 SafeUniqueTailBulletEndpoint := by
  apply historyModeDrop_of_prefix_eq_dirtyCtl_lt
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact safe_unique_tail_bullet_pushWord_dirty_drop

/-! The coordinate is compatible with the already proved producer edges: the
same five-coordinate order is used, and each existing edge is paid by its
previous strict coordinate or by `dirtyCtl` itself. -/

theorem safe_unique_tail_bullet_compatible_producer_edges :
    HistoryModeDrop phaseRing3 2 SafeUniqueTailBullet
        0 SafeUniqueTailBulletEndpoint ∧
      HistoryModeDrop (oddRing 1) (oddTail 1)
        AAFJPK.OneBarrierModeHistoryCredit.oddZero3
        0 AAFJPK.OneBarrierModeHistoryCredit.oddZero3BirthEnd ∧
      HistoryModeDrop phaseRing3 2 U0 2 U1 ∧
      HistoryModeDrop phaseRing3 2 U1 U1EndBarrier U1D ∧
      HistoryModeDrop phaseRing3 2 DirtyZero 2 DirtyZeroEnd := by
  exact ⟨safe_unique_tail_bullet_history_mode_drop,
    AAFJPK.OneBarrierModeHistoryCredit.odd_zero_birth_history_mode_drop,
    AAFJPK.OneBarrierModeHistoryCredit.dangerous_chase_history_mode_drop,
    AAFJPK.OneBarrierModeHistoryCredit.selected_multiple_unique_safe_history_mode_drop,
    (AAFJPK.OneBarrierModeHistoryCredit.dirty_tail_history_mode_drop).2.2.2.2⟩

#print axioms historyModeDrop_of_prefix_eq_dirtyCtl_lt
#print axioms pushWord_dirtyCtl_drop_of_tail_bullet
#print axioms safe_unique_tail_bullet_pushWord_is_actual_word
#print axioms safe_unique_tail_bullet_pushWord_dirty_drop
#print axioms safe_unique_tail_bullet_coordinate_profile
#print axioms safe_unique_tail_bullet_history_mode_drop
#print axioms safe_unique_tail_bullet_compatible_producer_edges

end AAFJPK.SafeUniqueTailDirty
