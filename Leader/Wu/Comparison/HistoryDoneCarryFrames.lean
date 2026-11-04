import Leader.Wu.Comparison.HistoryDoneMove


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace PPLLComparisonHistory


open PPLL PPLLRepair
open PPLLWallSweepHistory
open BirthSingleUseReleaseRepair


variable {n ψ : Nat}


private theorem pCarryHistoryTrusted_of_frame
    (old out : MarkedAgentState n ψ)
    (hold : PCarryHistoryTrusted old.concrete old.history)
    (hp : out.concrete.p_carry = old.concrete.p_carry)
    (hh : out.history.pCarry = old.history.pCarry) :
    PCarryHistoryTrusted out.concrete out.history := by
  unfold PCarryHistoryTrusted
  rw [hp, hh]
  exact hold


private theorem
    markedSigMoveLeaderPreclear_preserves_fullLocalHistoryTrusted_local
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedSigMoveLeaderPreclear hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedSigMoveLeaderPreclear
  dsimp only
  split
  · split
    · exact ⟨markedClearComparisonSignal_fullLocalHistoryTrusted l,
        markedClearComparisonSignal_fullLocalHistoryTrusted r⟩
    · exact ⟨markedClearComparisonSignal_fullLocalHistoryTrusted l, hr⟩
  · split
    · exact ⟨hl, markedClearComparisonSignal_fullLocalHistoryTrusted r⟩
    · exact ⟨hl, hr⟩


/-! ## Local pCarry frames for the DONE transfer prefix -/


private theorem markedCaptureStep1_pCarry_frame
    (l r : MarkedAgentState n ψ) :
    let q := markedCaptureStep1 l r
    q.1.concrete.p_carry = l.concrete.p_carry ∧
      q.2.concrete.p_carry = r.concrete.p_carry ∧
      q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry := by
  unfold markedCaptureStep1
  dsimp only
  split
  next pathLabel pathBit hlpath hrpath =>
    split
    next hstate =>
      split
      next hdest =>
        split
        next halign =>
          simp [BirthArrivalCaptureRepair.captureStep1,
            hlpath, hrpath, hstate, hdest, halign]
        next halign =>
          simp [BirthArrivalCaptureRepair.captureStep1,
            hlpath, hrpath, hstate, hdest, halign]
      next hdest =>
        simp [BirthArrivalCaptureRepair.captureStep1,
          hlpath, hrpath, hstate, hdest]
    next hstate =>
      simp [BirthArrivalCaptureRepair.captureStep1,
        hlpath, hrpath, hstate]
  next hother =>
    have hq : BirthArrivalCaptureRepair.captureStep1
        l.concrete r.concrete = (l.concrete, r.concrete) := by
      unfold BirthArrivalCaptureRepair.captureStep1
      cases hlp : l.concrete.path with
      | bot => rfl
      | some label bit =>
        cases hrp : r.concrete.path with
        | bot => exact (hother label bit hlp hrp).elim
        | some _ _ => rfl
    rw [hq]
    exact ⟨rfl, rfl, rfl, rfl⟩


private theorem markedHoldDoneStep1_pCarry_frame
    (l r : MarkedAgentState n ψ) :
    let q := markedHoldDoneStep1 l r
    q.1.concrete.p_carry = l.concrete.p_carry ∧
      q.2.concrete.p_carry = r.concrete.p_carry ∧
      q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry := by
  unfold markedHoldDoneStep1
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact markedCaptureStep1_pCarry_frame l r


private theorem markedSigMoveStep2_pCarry_frame
    (l r : MarkedAgentState n ψ) :
    let q := markedSigMoveStep2 l r
    q.1.concrete.p_carry = l.concrete.p_carry ∧
      q.2.concrete.p_carry = r.concrete.p_carry ∧
      q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry := by
  unfold markedSigMoveStep2
  dsimp only
  split
  next p2 hp2 =>
    split
    next hmove =>
      simp [sigMoveStep2, hp2, hmove]
    next hmove =>
      simp [sigMoveStep2, hp2, hmove]
  next hp2 =>
    simp [sigMoveStep2, hp2]


private theorem markedSigMoveStep3_pCarry_frame
    (l r : MarkedAgentState n ψ) :
    let q := markedSigMoveStep3 l r
    q.1.concrete.p_carry = l.concrete.p_carry ∧
      q.2.concrete.p_carry = r.concrete.p_carry ∧
      q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry := by
  unfold markedSigMoveStep3
  dsimp only
  split
  next p2 hp2 =>
    split
    next hmove =>
      simp [sigMoveStep3, hp2, hmove]
    next hmove =>
      simp [sigMoveStep3, hp2, hmove]
  next hp2 =>
    simp [sigMoveStep3, hp2]


private theorem markedSigMoveStep4_pCarry_frame
    (l r : MarkedAgentState n ψ) :
    let q := markedSigMoveStep4 l r
    q.1.concrete.p_carry = l.concrete.p_carry ∧
      q.2.concrete.p_carry = r.concrete.p_carry ∧
      q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry := by
  unfold markedSigMoveStep4
  dsimp only
  split
  next p2 hp2 =>
    split
    next hmove =>
      simp [sigMoveStep4, hp2, hmove]
    next hmove =>
      simp [sigMoveStep4, hp2, hmove]
  next hp2 =>
    simp [sigMoveStep4, hp2]


private theorem markedSigMoveStep5_pCarry_frame
    (l r : MarkedAgentState n ψ) :
    let q := markedSigMoveStep5 l r
    q.1.concrete.p_carry = l.concrete.p_carry ∧
      q.2.concrete.p_carry = r.concrete.p_carry ∧
      q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry := by
  unfold markedSigMoveStep5
  dsimp only
  split
  next p2 hp2 =>
    split
    next hmove =>
      simp [sigMoveStep5, hp2, hmove]
    next hmove =>
      simp [sigMoveStep5, hp2, hmove]
  next hp2 =>
    simp [sigMoveStep5, hp2]


/-- Held/captured Step 1 followed by rows 2--5 preserves pCarry by chaining
five local frame equalities. -/
private theorem markedDoneTransfers_pCarry_frame
    (l r : MarkedAgentState n ψ) :
    let q := markedDoneTransfers l r
    q.1.concrete.p_carry = l.concrete.p_carry ∧
      q.2.concrete.p_carry = r.concrete.p_carry ∧
      q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry := by
  let q1 := markedHoldDoneStep1 l r
  have h1 := markedHoldDoneStep1_pCarry_frame l r
  change q1.1.concrete.p_carry = l.concrete.p_carry ∧
    q1.2.concrete.p_carry = r.concrete.p_carry ∧
    q1.1.history.pCarry = l.history.pCarry ∧
    q1.2.history.pCarry = r.history.pCarry at h1

  let q2 := markedSigMoveStep2 q1.1 q1.2
  have h2 := markedSigMoveStep2_pCarry_frame q1.1 q1.2
  change q2.1.concrete.p_carry = q1.1.concrete.p_carry ∧
    q2.2.concrete.p_carry = q1.2.concrete.p_carry ∧
    q2.1.history.pCarry = q1.1.history.pCarry ∧
    q2.2.history.pCarry = q1.2.history.pCarry at h2

  let q3 := markedSigMoveStep3 q2.1 q2.2
  have h3 := markedSigMoveStep3_pCarry_frame q2.1 q2.2
  change q3.1.concrete.p_carry = q2.1.concrete.p_carry ∧
    q3.2.concrete.p_carry = q2.2.concrete.p_carry ∧
    q3.1.history.pCarry = q2.1.history.pCarry ∧
    q3.2.history.pCarry = q2.2.history.pCarry at h3

  let q4 := markedSigMoveStep4 q3.1 q3.2
  have h4 := markedSigMoveStep4_pCarry_frame q3.1 q3.2
  change q4.1.concrete.p_carry = q3.1.concrete.p_carry ∧
    q4.2.concrete.p_carry = q3.2.concrete.p_carry ∧
    q4.1.history.pCarry = q3.1.history.pCarry ∧
    q4.2.history.pCarry = q3.2.history.pCarry at h4

  let q5 := markedSigMoveStep5 q4.1 q4.2
  have h5 := markedSigMoveStep5_pCarry_frame q4.1 q4.2
  change q5.1.concrete.p_carry = q4.1.concrete.p_carry ∧
    q5.2.concrete.p_carry = q4.2.concrete.p_carry ∧
    q5.1.history.pCarry = q4.1.history.pCarry ∧
    q5.2.history.pCarry = q4.2.history.pCarry at h5

  change q5.1.concrete.p_carry = l.concrete.p_carry ∧
    q5.2.concrete.p_carry = r.concrete.p_carry ∧
    q5.1.history.pCarry = l.history.pCarry ∧
    q5.2.history.pCarry = r.history.pCarry
  exact ⟨
    h5.1.trans (h4.1.trans (h3.1.trans (h2.1.trans h1.1))),
    h5.2.1.trans (h4.2.1.trans (h3.2.1.trans (h2.2.1.trans h1.2.1))),
    h5.2.2.1.trans
      (h4.2.2.1.trans (h3.2.2.1.trans (h2.2.2.1.trans h1.2.2.1))),
    h5.2.2.2.trans
      (h4.2.2.2.trans (h3.2.2.2.trans (h2.2.2.2.trans h1.2.2.2)) )⟩


/-! ## Local pCarry frames for the single-use control tail -/


private theorem markedSigMoveApplyControl_pCarry_frame
    (hψ : ψ > 0) (u : MarkedAgentState n ψ) :
    (markedSigMoveApplyControl hψ u).concrete.p_carry =
        u.concrete.p_carry ∧
      (markedSigMoveApplyControl hψ u).history.pCarry =
        u.history.pCarry := by
  unfold markedSigMoveApplyControl
  dsimp only
  split
  next p2 hp2 =>
    split
    next hcontrol =>
      simp [sigMoveApplyControl, hp2]
    next hcontrol =>
      simp [sigMoveApplyControl, hp2]
  next hp2 =>
    simp [sigMoveApplyControl, hp2]


private theorem markedSingleUseApplyControl_pCarry_frame
    (hψ : ψ > 0) (u : MarkedAgentState n ψ) :
    (markedSingleUseApplyControl hψ u).concrete.p_carry =
        u.concrete.p_carry ∧
      (markedSingleUseApplyControl hψ u).history.pCarry =
        u.history.pCarry := by
  constructor
  · rw [erase_markedSingleUseApplyControl hψ u]
    unfold singleUseApplyControl
    dsimp only
    repeat (first | rfl | split)
  · have hh := (markedSigMoveApplyControl_pCarry_frame hψ u).2
    let v := markedSigMoveApplyControl hψ u
    have hv : v.history.pCarry = u.history.pCarry := by
      simpa [v] using hh
    have hsingle :
        markedSingleUseApplyControl hψ u =
          match v.concrete.path2 with
          | some p2 =>
              if _hrelease :
                  v.concrete.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧
                    p2.action = 5 then
                ⟨clearTerminalRelease hψ v.concrete,
                  { v.history with path2 := .absent }⟩
              else v
          | none => v := by
      unfold markedSingleUseApplyControl
      rfl
    cases hpath : v.concrete.path2 with
    | none =>
        simpa only [hsingle, hpath] using hv
    | some p2 =>
        by_cases hrelease :
            v.concrete.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧
              p2.action = 5
        · simpa [hsingle, hpath, hrelease] using hv
        · simpa [hsingle, hpath, hrelease] using hv


private theorem markedSigMoveDepart_pCarry_frame
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ) :
    let q := markedSigMoveDepart hψ l r
    q.1.concrete.p_carry = l.concrete.p_carry ∧
      q.2.concrete.p_carry = r.concrete.p_carry ∧
      q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry := by
  unfold markedSigMoveDepart
  dsimp only
  repeat (first | exact ⟨rfl, rfl, rfl, rfl⟩ | split)


/-- The two local single-use controls and final backward departure preserve
pCarry by a three-link composition. -/
private theorem markedSingleUseControlTail_pCarry_frame
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ) :
    let q := markedSingleUseControlTail hψ l r
    q.1.concrete.p_carry = l.concrete.p_carry ∧
      q.2.concrete.p_carry = r.concrete.p_carry ∧
      q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry := by
  let l6 := markedSingleUseApplyControl hψ l
  let r6 := markedSingleUseApplyControl hψ r
  have hl6 := markedSingleUseApplyControl_pCarry_frame hψ l
  have hr6 := markedSingleUseApplyControl_pCarry_frame hψ r
  change l6.concrete.p_carry = l.concrete.p_carry ∧
    l6.history.pCarry = l.history.pCarry at hl6
  change r6.concrete.p_carry = r.concrete.p_carry ∧
    r6.history.pCarry = r.history.pCarry at hr6

  let q7 := markedSigMoveDepart hψ l6 r6
  have h7 := markedSigMoveDepart_pCarry_frame hψ l6 r6
  change q7.1.concrete.p_carry = l6.concrete.p_carry ∧
    q7.2.concrete.p_carry = r6.concrete.p_carry ∧
    q7.1.history.pCarry = l6.history.pCarry ∧
    q7.2.history.pCarry = r6.history.pCarry at h7

  change q7.1.concrete.p_carry = l.concrete.p_carry ∧
    q7.2.concrete.p_carry = r.concrete.p_carry ∧
    q7.1.history.pCarry = l.history.pCarry ∧
    q7.2.history.pCarry = r.history.pCarry
  exact ⟨
    h7.1.trans hl6.1,
    h7.2.1.trans hr6.1,
    h7.2.2.1.trans hl6.2,
    h7.2.2.2.trans hr6.2⟩


/-- Full four-field DONE preservation. Relative to the existing audit theorem,
the only additional assumptions are the two incoming pCarry trust conjuncts. -/
theorem markedDoneCaptureSigMove_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hlCarry : PCarryHistoryTrusted l.concrete l.history)
    (hrCarry : PCarryHistoryTrusted r.concrete r.history)
    (hcompat : CurrentDoneMoveCompatible hψ l r) :
    let q := markedDoneCaptureSigMove hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  have hlFull : FullLocalHistoryTrusted l.concrete l.history :=
    ⟨hl, hlCarry⟩
  have hrFull : FullLocalHistoryTrusted r.concrete r.history :=
    ⟨hr, hrCarry⟩

  let p := markedSigMoveLeaderPreclear hψ l r
  have hp :=
    markedSigMoveLeaderPreclear_preserves_fullLocalHistoryTrusted_local
      hψ l r hlFull hrFull
  change FullLocalHistoryTrusted p.1.concrete p.1.history ∧
    FullLocalHistoryTrusted p.2.concrete p.2.history at hp

  let moved := markedDoneTransfers p.1 p.2
  have hma :=
    markedDoneTransfers_preserves_auditLocalHistoryTrusted_unconditional
      p.1 p.2 hp.1.1 hp.2.1
  change AuditLocalHistoryTrusted moved.1.concrete moved.1.history ∧
    AuditLocalHistoryTrusted moved.2.concrete moved.2.history at hma
  have hmf := markedDoneTransfers_pCarry_frame p.1 p.2
  change moved.1.concrete.p_carry = p.1.concrete.p_carry ∧
    moved.2.concrete.p_carry = p.2.concrete.p_carry ∧
    moved.1.history.pCarry = p.1.history.pCarry ∧
    moved.2.history.pCarry = p.2.history.pCarry at hmf
  have hmc :
      PCarryHistoryTrusted moved.1.concrete moved.1.history ∧
        PCarryHistoryTrusted moved.2.concrete moved.2.history :=
    ⟨pCarryHistoryTrusted_of_frame p.1 moved.1 hp.1.2
        hmf.1 hmf.2.2.1,
      pCarryHistoryTrusted_of_frame p.2 moved.2 hp.2.2
        hmf.2.1 hmf.2.2.2⟩
  have hm :
      FullLocalHistoryTrusted moved.1.concrete moved.1.history ∧
        FullLocalHistoryTrusted moved.2.concrete moved.2.history :=
    ⟨⟨hma.1, hmc.1⟩, ⟨hma.2, hmc.2⟩⟩

  let wall := PPLLWallSweepHistory.markedComparisonLeaderWall
    moved.1 moved.2
  have hw :=
    PPLLWallSweepHistory.markedComparisonLeaderWall_preserves_fullLocalHistoryTrusted
      moved.1 moved.2 hm.1 hm.2
  change FullLocalHistoryTrusted wall.1.concrete wall.1.history ∧
    FullLocalHistoryTrusted wall.2.concrete wall.2.history at hw

  have hcompat' :
      let l6 := markedSingleUseApplyControl hψ wall.1
      let r6 := markedSingleUseApplyControl hψ wall.2
      SigMoveDepartCompatible hψ l6 r6 := by
    simpa [CurrentDoneMoveCompatible, p, moved, wall] using hcompat

  let tail := markedSingleUseControlTail hψ wall.1 wall.2
  have hta :=
    markedSingleUseControlTail_preserves_auditLocalHistoryTrusted
      hψ wall.1 wall.2 hw.1.1 hw.2.1 hcompat'
  change AuditLocalHistoryTrusted tail.1.concrete tail.1.history ∧
    AuditLocalHistoryTrusted tail.2.concrete tail.2.history at hta
  have htf := markedSingleUseControlTail_pCarry_frame hψ wall.1 wall.2
  change tail.1.concrete.p_carry = wall.1.concrete.p_carry ∧
    tail.2.concrete.p_carry = wall.2.concrete.p_carry ∧
    tail.1.history.pCarry = wall.1.history.pCarry ∧
    tail.2.history.pCarry = wall.2.history.pCarry at htf
  have htc :
      PCarryHistoryTrusted tail.1.concrete tail.1.history ∧
        PCarryHistoryTrusted tail.2.concrete tail.2.history :=
    ⟨pCarryHistoryTrusted_of_frame wall.1 tail.1 hw.1.2
        htf.1 htf.2.2.1,
      pCarryHistoryTrusted_of_frame wall.2 tail.2 hw.2.2
        htf.2.1 htf.2.2.2⟩
  have ht :
      FullLocalHistoryTrusted tail.1.concrete tail.1.history ∧
        FullLocalHistoryTrusted tail.2.concrete tail.2.history :=
    ⟨⟨hta.1, htc.1⟩, ⟨hta.2, htc.2⟩⟩
  simpa [tail, markedDoneCaptureSigMove, p, moved, wall] using ht


end PPLLComparisonHistory


#print axioms PPLLComparisonHistory.markedDoneCaptureSigMove_preserves_fullLocalHistoryTrusted
