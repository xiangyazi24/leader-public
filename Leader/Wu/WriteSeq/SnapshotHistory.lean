import Leader.Wu.WriteSeq.RulerHistory

/-!
# Snapshot-parametric ruler history for generated writers

Algorithm 18 stores each writer payload bit before applying its binary increment
to the physical source group.  Consequently a real generated writer is tied to
a frozen pre-generation source snapshot, not in general to the current source
group.  This repair-lane module threads that fixed reference configuration
through the existing source-tagged carrier and ruler-flag recurrence.
-/

namespace PPLLWriteSeqSnapshotHistory

open PPLL PPLLWriteSeqPersistenceRepair PPLLWriteSeqPersistenceRegression
  PPLLWriteSeqRelocation PPLLWriteSeqRulerBridge PPLLWriteSeqRulerHistory

/-! ## Executable generation/snapshot regression -/

/-- Two zero bits with a generation request at label zero. -/
def snapshotBirthLeft : AgentState 2 :=
  { PPLLCounterexample.state2 0 with gen_ws := true }

def snapshotBirthRight : AgentState 2 :=
  PPLLCounterexample.state2 1

def snapshotBirthPair : AgentState 2 × AgentState 2 :=
  gensigWriteseq (by omega) snapshotBirthLeft snapshotBirthRight

def snapshotBirthBefore (i : Fin 2) : AgentState 2 :=
  if i = 0 then snapshotBirthLeft else snapshotBirthRight

def snapshotBirthAfter (i : Fin 2) : AgentState 2 :=
  if i = 0 then snapshotBirthPair.1 else snapshotBirthPair.2

/-- Algorithm 18's concrete width-two birth records payload `00` and then
increments the physical source from `00` to `01`.  Hence authentication to the
pre-birth snapshot succeeds while authentication to the current source would
identify the wrong numeric payload. -/
theorem snapshotBirth_payload_precedes_physical_increment :
    snapshotBirthPair.1.path3 = some ⟨0, 0, 1⟩ ∧
      snapshotBirthPair.2.path3 = some ⟨1, 0, 1⟩ ∧
      groupID (⟨by omega⟩ : DirectedRing 2).hn snapshotBirthBefore 0 = 0 ∧
      overwritingSignalIDAt (⟨by omega⟩ : DirectedRing 2)
        snapshotBirthAfter 0 = 0 ∧
      groupID (⟨by omega⟩ : DirectedRing 2).hn snapshotBirthAfter 0 = 1 := by
  decide

/-- A source-tagged carrier whose source bits are read from a fixed reference
configuration and whose flag is the ruler state before its current target. -/
structure SnapshotRulerOverwritingHistory {ψ n : Nat}
    (ring : DirectedRing n) (signalC referenceC : Fin n → AgentState ψ)
    (leaderPos : Fin n)
    (carrier : SourceTaggedCompleteOverwritingCarrier
      ring signalC referenceC leaderPos) : Prop where
  target_pos : 0 < carrier.route.target
  flag_before_target : carrier.flag =
    if rulerWriterFlagBefore carrier.route.payload carrier.route.target
      then 1 else 0

namespace SnapshotRulerOverwritingHistory

/-- Processing the current target updates the snapshot-authenticated writer
flag to the exact ruler state before the next target. -/
theorem flag_after_target {ψ n : Nat} (ring : DirectedRing n)
    (signalC referenceC : Fin n → AgentState ψ) (leaderPos : Fin n)
    (carrier : SourceTaggedCompleteOverwritingCarrier
      ring signalC referenceC leaderPos)
    (history : SnapshotRulerOverwritingHistory ring signalC referenceC
      leaderPos carrier) :
    (if carrier.route.payload ≤ trailingZeros carrier.route.target then
        1 - carrier.flag else carrier.flag) =
      if rulerWriterFlagBefore carrier.route.payload
          (carrier.route.target + 1) then 1 else 0 := by
  rw [history.flag_before_target,
    rulerWriterFlagBefore_succ _ _ history.target_pos]
  by_cases hle : carrier.route.payload ≤ trailingZeros carrier.route.target
  · simp only [if_pos hle]
    cases hflag : rulerWriterFlagBefore carrier.route.payload
        carrier.route.target <;> simp
  · simp only [if_neg hle]

/-- One physical group step preserves the fixed source reference while the
signal configuration changes. -/
theorem advance {ψ n : Nat} (ring : DirectedRing n)
    (C D referenceC : Fin n → AgentState ψ) (leaderPos : Fin n)
    (carrier : SourceTaggedCompleteOverwritingCarrier
      ring C referenceC leaderPos)
    (next : SourceTaggedCompleteOverwritingCarrier
      ring D referenceC leaderPos)
    (history : SnapshotRulerOverwritingHistory ring C referenceC leaderPos
      carrier)
    (hpayload : next.route.payload = carrier.route.payload)
    (htarget : next.route.target = carrier.route.target + 1)
    (hflag : next.flag =
      if carrier.route.payload ≤ trailingZeros carrier.route.target then
        1 - carrier.flag else carrier.flag) :
    SnapshotRulerOverwritingHistory ring D referenceC leaderPos next := by
  refine ⟨?_, ?_⟩
  · rw [htarget]
    omega
  · rw [hflag, hpayload, htarget]
    exact history.flag_after_target ring C referenceC leaderPos carrier

end SnapshotRulerOverwritingHistory

/-- The existing same-configuration certificate is a special case of the
snapshot-parametric certificate. -/
theorem RulerOverwritingHistory.toSnapshot {ψ n : Nat}
    (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (leaderPos : Fin n)
    (carrier : SourceTaggedCompleteOverwritingCarrier ring C C leaderPos)
    (history : RulerOverwritingHistory ring C leaderPos carrier) :
    SnapshotRulerOverwritingHistory ring C C leaderPos carrier :=
  ⟨history.target_pos, history.flag_before_target⟩

/-- A snapshot-certified carrier cannot be free at its current target once
that target's current physical group ID is the ruler value.  No assertion about
the current source group ID is needed. -/
theorem snapshotSourceTaggedOverwriting_not_free_at_target
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C referenceC : Fin n → AgentState ψ) (leaderPos : Fin n)
    (carrier : SourceTaggedCompleteOverwritingCarrier
      ring C referenceC leaderPos)
    (history : SnapshotRulerOverwritingHistory ring C referenceC leaderPos
      carrier)
    (htargetID : groupID ring.hn C
      (stableGroupStart ring leaderPos ψ carrier.route.target) =
        trailingZeros carrier.route.target) :
    ¬isFreeOverwritingSignalAt ring C leaderPos carrier.route.target := by
  intro hfree
  change
    isAlignedOverwritingSignalAt ring C
        (stableGroupStart ring leaderPos ψ carrier.route.target) 1 ∧
      overwritingSignalIDAt ring C
          (stableGroupStart ring leaderPos ψ carrier.route.target) ≠
        trailingZeros carrier.route.target ∧
      groupID ring.hn C
          (stableGroupStart ring leaderPos ψ carrier.route.target) >
        overwritingSignalIDAt ring C
          (stableGroupStart ring leaderPos ψ carrier.route.target)
    at hfree
  have hsignal := carrier.signalID_eq_payload ring C referenceC leaderPos
  have hgreater : carrier.route.payload < trailingZeros carrier.route.target := by
    rw [← htargetID, ← hsignal]
    exact hfree.2.2
  have hflagFalse := rulerWriterFlagBefore_false_of_payload_lt_target
    carrier.route.target carrier.route.payload history.target_pos hgreater
  have hcarrierZero : carrier.flag = 0 := by
    simpa [hflagFalse] using history.flag_before_target
  obtain ⟨pFree, hpFree, _, _, hpFreeFlag⟩ := hfree.1.2 0 hψ
  obtain ⟨pCarrier, hpCarrier, _, _, hpCarrierFlag⟩ :=
    carrier.components.2 0 hψ
  rw [hpCarrier] at hpFree
  cases hpFree
  have hcarrierOne : carrier.flag = 1 := by omega
  omega

end PPLLWriteSeqSnapshotHistory
