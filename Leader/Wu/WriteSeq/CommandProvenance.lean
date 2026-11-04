import Leader.Wu.Protocol.DomainClosure

/-!
# Operational provenance for pending write commands

This module starts below the global overwriting-signal invariant.  It records a
falsifiable local fact: an `increment_group` command may be created by
Algorithm 16 only from a present path3 component whose flag requests the final
increment.  The T8 orphan command fails this predicate.
-/

namespace PPLLWriteProvenance

open PPLL

/-- Local support required for a pending group-increment command. -/
def IncrementCommandSupported {ψ : Nat} (u : AgentState ψ) : Prop :=
  u.write = .increment_group →
    ∃ p : Path3Info, u.path3 = some p ∧ p.flag ≠ 1

private theorem writeSeqSetWriteReady_write_path3 {ψ : Nat}
    (u : AgentState ψ) :
    (writeSeqSetWriteReady u).write = u.write ∧
      (writeSeqSetWriteReady u).path3 = u.path3 := by
  simp only [writeSeqSetWriteReady]
  repeat (first | constructor | rfl | split)

private theorem writeSeqCheckBit_write_path3 {ψ : Nat} (u : AgentState ψ) :
    (writeSeqCheckBit u).write = u.write ∧
      (writeSeqCheckBit u).path3 = u.path3 := by
  simp only [writeSeqCheckBit]
  repeat (first | constructor | rfl | split)

/-- `writeSeqSetWriteAct` may create overwrite/move actions, but never creates
an increment action. -/
theorem writeSeqSetWriteAct_increment_origin {ψ : Nat} (u : AgentState ψ)
    (h : (writeSeqSetWriteAct u).write = .increment_group) :
    u.write = .increment_group := by
  by_cases hlarger : u.write_state = .larger
  · cases hp : u.path3
    · simpa [writeSeqSetWriteAct, hlarger, hp] using h
    · rename_i p
      by_cases hflag : p.flag = 1
      · simp [writeSeqSetWriteAct, hlarger, hp, hflag] at h
      · simp [writeSeqSetWriteAct, hlarger, hp, hflag] at h
  · by_cases hless : u.write_state = .less
    · simp [writeSeqSetWriteAct, hless] at h
    · simpa [writeSeqSetWriteAct, hlarger, hless] using h

private theorem writeSeqSetWriteAct_path3 {ψ : Nat} (u : AgentState ψ) :
    (writeSeqSetWriteAct u).path3 = u.path3 := by
  simp only [writeSeqSetWriteAct]
  repeat (first | rfl | split)

/-- Algorithm 16's final responder command either preserves an old increment
or creates one from a present path3 component with non-write flag. -/
theorem writeSeqFinalR_increment_origin {ψ : Nat} (u : AgentState ψ)
    (h : (writeSeqFinalR u).write = .increment_group) :
    u.write = .increment_group ∨
      ∃ p : Path3Info, u.path3 = some p ∧ p.flag ≠ 1 := by
  cases hp : u.path3 with
  | none =>
    left
    simpa [writeSeqFinalR, hp] using h
  | some p =>
    by_cases hf : p.flag = 1
    · simp [writeSeqFinalR, hp, hf] at h
    · right
      exact ⟨p, rfl, hf⟩

private theorem writeSeqFinalR_path3 {ψ : Nat} (u : AgentState ψ) :
    (writeSeqFinalR u).path3 = u.path3 := by
  simp only [writeSeqFinalR]
  repeat (first | rfl | split)

private theorem writeSeqSetWriteReady_preserves {ψ : Nat} (u : AgentState ψ)
    (h : IncrementCommandSupported u) :
    IncrementCommandSupported (writeSeqSetWriteReady u) := by
  intro hinc
  have hf := writeSeqSetWriteReady_write_path3 u
  have hold : u.write = .increment_group := hf.1.symm.trans hinc
  obtain ⟨p, hp, hflag⟩ := h hold
  exact ⟨p, hf.2.trans hp, hflag⟩

private theorem writeSeqCheckBit_preserves {ψ : Nat} (u : AgentState ψ)
    (h : IncrementCommandSupported u) :
    IncrementCommandSupported (writeSeqCheckBit u) := by
  intro hinc
  have hf := writeSeqCheckBit_write_path3 u
  have hold : u.write = .increment_group := hf.1.symm.trans hinc
  obtain ⟨p, hp, hflag⟩ := h hold
  exact ⟨p, hf.2.trans hp, hflag⟩

private theorem writeSeqSetWriteAct_preserves {ψ : Nat} (u : AgentState ψ)
    (h : IncrementCommandSupported u) :
    IncrementCommandSupported (writeSeqSetWriteAct u) := by
  intro hinc
  have hold := writeSeqSetWriteAct_increment_origin u hinc
  obtain ⟨p, hp, hflag⟩ := h hold
  exact ⟨p, (writeSeqSetWriteAct_path3 u).trans hp, hflag⟩

private theorem writeSeqFinalR_preserves {ψ : Nat} (u : AgentState ψ)
    (h : IncrementCommandSupported u) :
    IncrementCommandSupported (writeSeqFinalR u) := by
  intro hinc
  rcases writeSeqFinalR_increment_origin u hinc with hold | hnew
  · obtain ⟨p, hp, hflag⟩ := h hold
    exact ⟨p, (writeSeqFinalR_path3 u).trans hp, hflag⟩
  · obtain ⟨p, hp, hflag⟩ := hnew
    exact ⟨p, (writeSeqFinalR_path3 u).trans hp, hflag⟩

/-- The command-preparation portion of Algorithm 16 preserves local increment
support on both agents. -/
theorem writeSeqPrepare_increment_supported {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hl : IncrementCommandSupported l) (hr : IncrementCommandSupported r) :
    IncrementCommandSupported (writeSeqPrepare hψ l r).1 ∧
      IncrementCommandSupported (writeSeqPrepare hψ l r).2 := by
  let q0 := writeSeqReady l r
  have hl0 := writeSeqSetWriteReady_preserves l hl
  have hr0 := writeSeqSetWriteReady_preserves r hr
  let r1a := if q0.2.label = ⟨0, hψ⟩ ∧ q0.2.write_state = .ready then
      writeSeqCheckBit q0.2 else q0.2
  have hr1a : IncrementCommandSupported r1a := by
    dsimp only [r1a]
    split
    · exact writeSeqCheckBit_preserves q0.2 hr0
    · exact hr0
  let r1 := if q0.1.label.val < ψ - 1 ∧ q0.1.write_state = .equal ∧
      r1a.write_state = .ready then writeSeqCheckBit r1a else r1a
  have hr1 : IncrementCommandSupported r1 := by
    dsimp only [r1]
    split
    · exact writeSeqCheckBit_preserves r1a hr1a
    · exact hr1a
  let q1 := writeSeqCompare hψ q0.1 q0.2
  have hq1 : q1 = (q0.1, r1) := by rfl
  have hl1 : IncrementCommandSupported q1.1 := by
    rw [hq1]
    exact hl0
  have hr1' : IncrementCommandSupported q1.2 := by
    rw [hq1]
    exact hr1
  let l2 := writeSeqSetWriteAct q1.1
  let r2a := writeSeqSetWriteAct q1.2
  have hl2 : IncrementCommandSupported l2 :=
    writeSeqSetWriteAct_preserves q1.1 hl1
  have hr2a : IncrementCommandSupported r2a :=
    writeSeqSetWriteAct_preserves q1.2 hr1'
  let r2 := if r2a.label = ⟨ψ - 1, by omega⟩ ∧
      r2a.write_state = .equal then writeSeqFinalR r2a else r2a
  have hr2 : IncrementCommandSupported r2 := by
    dsimp only [r2]
    split
    · exact writeSeqFinalR_preserves r2a hr2a
    · exact hr2a
  let q2 := writeSeqCommands hψ q1.1 q1.2
  have hq2 : q2 = (l2, r2) := by rfl
  change IncrementCommandSupported q2.1 ∧ IncrementCommandSupported q2.2
  rw [hq2]
  exact ⟨hl2, hr2⟩

end PPLLWriteProvenance
