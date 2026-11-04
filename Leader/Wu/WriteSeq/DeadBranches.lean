import Leader.Wu.Protocol.Algorithm

/-!
# Dead branches in literal Algorithm 16

Algorithm 16 lines 7--11 assign every endpoint's `write_state` to either
`ready` or `none` before line 14 tests whether the initiator is `equal`.
Consequently lines 14--15 are unreachable for every `ψ`.  Equality can then be
created only at responder label zero by lines 12--13; on `ψ ≥ 2` it cannot occur
at the terminal responder label `ψ-1`, so lines 24--28 are unreachable as well.
In particular, command preparation cannot create `increment_group` for
`ψ ≥ 2`; any such output command was already an arbitrary input command.

These are source-level control-flow theorems for the audited transcription,
not properties of a repaired write lifecycle.  They formalize the mismatch
between printed Algorithm 16 (thesis p.35 / PDF p.48) and the overwrite/
increment behavior promised in the prose on p.33 / PDF p.46.
-/

namespace PPLLWriteSeqDeadBranches

open PPLL

variable {ψ : Nat}

/-- Lines 7--11 leave only `ready` or `none`, erasing every comparison result
that may have existed at interaction entry. -/
theorem setWriteReady_ready_or_none (u : AgentState ψ) :
    (writeSeqSetWriteReady u).write_state = .ready ∨
      (writeSeqSetWriteReady u).write_state = .none := by
  cases h : u.path3 with
  | none => simp [writeSeqSetWriteReady, h]
  | some p3 =>
    by_cases hc : u.label.val = p3.label ∧ u.write_state ≠ .depart
    · simp [writeSeqSetWriteReady, h, hc]
    · simp [writeSeqSetWriteReady, h, hc]

private theorem setWriteReady_frame (u : AgentState ψ) :
    (writeSeqSetWriteReady u).label = u.label ∧
      (writeSeqSetWriteReady u).write = u.write := by
  cases h : u.path3 with
  | none => simp [writeSeqSetWriteReady, h]
  | some p3 =>
    by_cases hc : u.label.val = p3.label ∧ u.write_state ≠ .depart
    · simp [writeSeqSetWriteReady, h, hc]
    · simp [writeSeqSetWriteReady, h, hc]

private theorem checkBit_frame (u : AgentState ψ) :
    (writeSeqCheckBit u).label = u.label ∧
      (writeSeqCheckBit u).write = u.write := by
  cases h : u.path3 with
  | none => simp [writeSeqCheckBit, h]
  | some p3 => simp [writeSeqCheckBit, h]

/-- **Algorithm 16 lines 14--15 are unreachable.**  The equality is an exact
normal form for `writeSeqCompare`: only the label-zero responder comparison in
lines 12--13 can execute. -/
theorem writeSeqCompare_second_branch_dead
    (hψ : ψ > 0) (l r : AgentState ψ) :
    writeSeqCompare hψ (writeSeqSetWriteReady l)
        (writeSeqSetWriteReady r) =
      (writeSeqSetWriteReady l,
        if (writeSeqSetWriteReady r).label = ⟨0, hψ⟩ ∧
            (writeSeqSetWriteReady r).write_state = .ready then
          writeSeqCheckBit (writeSeqSetWriteReady r)
        else writeSeqSetWriteReady r) := by
  have hl := setWriteReady_ready_or_none l
  unfold writeSeqCompare
  simp only
  rw [if_neg]
  intro h
  rcases hl with hl | hl <;> rw [hl] at h <;>
    exact absurd h.2.1 (by simp)

private theorem setWriteAct_frame (u : AgentState ψ) :
    (writeSeqSetWriteAct u).label = u.label ∧
      (writeSeqSetWriteAct u).write_state = u.write_state := by
  unfold writeSeqSetWriteAct
  cases h : u.path3 with
  | none =>
    by_cases h1 : u.write_state = .larger <;>
      by_cases h2 : u.write_state = .less <;> simp [h, h1, h2]
  | some p3 =>
    by_cases h1 : u.write_state = .larger <;>
      by_cases h2 : u.write_state = .less <;>
      by_cases h3 : p3.flag = 1 <;> simp [h, h1, h2, h3]

private theorem setWriteAct_no_increment (u : AgentState ψ)
    (h : (writeSeqSetWriteAct u).write = .increment_group) :
    u.write = .increment_group := by
  unfold writeSeqSetWriteAct at h
  cases hp : u.path3 with
  | none =>
    by_cases h1 : u.write_state = .larger <;>
      by_cases h2 : u.write_state = .less <;>
      simp [hp, h1, h2] at h <;> exact h
  | some p3 =>
    by_cases h1 : u.write_state = .larger <;>
      by_cases h2 : u.write_state = .less <;>
      by_cases h3 : p3.flag = 1 <;>
      simp [hp, h1, h2, h3] at h <;> exact h

private theorem responderCommands_increment_is_input
    (hψ : ψ > 0) (u : AgentState ψ)
    (hne : ¬(u.label = ⟨ψ - 1, by omega⟩ ∧
      u.write_state = .equal))
    (h : (if (writeSeqSetWriteAct u).label = ⟨ψ - 1, by omega⟩ ∧
            (writeSeqSetWriteAct u).write_state = .equal then
          writeSeqFinalR (writeSeqSetWriteAct u)
        else writeSeqSetWriteAct u).write = .increment_group) :
    u.write = .increment_group := by
  rw [(setWriteAct_frame u).1, (setWriteAct_frame u).2, if_neg hne] at h
  exact setWriteAct_no_increment u h

/-- **For `ψ ≥ 2`, lines 7--28 never create `increment_group`.**  Any
increment command after `writeSeqPrepare` was already present on the same input
endpoint. -/
theorem writeSeqPrepare_increment_is_input
    (hψ : ψ > 0) (h2 : 2 ≤ ψ) (l r : AgentState ψ) :
    ((writeSeqPrepare hψ l r).2.write = .increment_group →
      r.write = .increment_group) ∧
    ((writeSeqPrepare hψ l r).1.write = .increment_group →
      l.write = .increment_group) := by
  have hcmp := writeSeqCompare_second_branch_dead hψ l r
  unfold writeSeqPrepare writeSeqReady
  simp only
  rw [hcmp]
  simp only [writeSeqCommands]
  constructor
  · intro h
    by_cases hz : (writeSeqSetWriteReady r).label = ⟨0, hψ⟩ ∧
        (writeSeqSetWriteReady r).write_state = .ready
    · rw [if_pos hz] at h
      have hne : ¬((writeSeqCheckBit
          (writeSeqSetWriteReady r)).label = ⟨ψ - 1, by omega⟩ ∧
          (writeSeqCheckBit
            (writeSeqSetWriteReady r)).write_state = .equal) := by
        intro hc
        rw [(checkBit_frame _).1, hz.1] at hc
        have hv := congrArg Fin.val hc.1
        simp at hv
        omega
      have horigin := responderCommands_increment_is_input hψ _ hne h
      rw [(checkBit_frame _).2, (setWriteReady_frame _).2] at horigin
      exact horigin
    · rw [if_neg hz] at h
      have hne : ¬((writeSeqSetWriteReady r).label =
          ⟨ψ - 1, by omega⟩ ∧
          (writeSeqSetWriteReady r).write_state = .equal) := by
        intro hc
        rcases setWriteReady_ready_or_none r with hr | hr <;>
          rw [hr] at hc <;> cases hc.2
      have horigin := responderCommands_increment_is_input hψ _ hne h
      rw [(setWriteReady_frame _).2] at horigin
      exact horigin
  · intro h
    have horigin := setWriteAct_no_increment _ h
    rw [(setWriteReady_frame _).2] at horigin
    exact horigin

/-- **For `ψ ≥ 2`, Algorithm 16 lines 24--28 are unreachable.**  The responder
presented to `writeSeqFinalR` can never simultaneously have terminal label and
state `equal`. -/
theorem writeSeqPrepare_finalR_dead
    (hψ : ψ > 0) (h2 : 2 ≤ ψ) (l r : AgentState ψ) :
    let q := writeSeqCompare hψ
      (writeSeqSetWriteReady l) (writeSeqSetWriteReady r)
    ¬((writeSeqSetWriteAct q.2).label = ⟨ψ - 1, by omega⟩ ∧
      (writeSeqSetWriteAct q.2).write_state = .equal) := by
  intro q hc
  rw [(setWriteAct_frame _).1, (setWriteAct_frame _).2] at hc
  have hcmp := writeSeqCompare_second_branch_dead hψ l r
  simp only [q] at hc
  rw [hcmp] at hc
  simp only at hc
  by_cases hz : (writeSeqSetWriteReady r).label = ⟨0, hψ⟩ ∧
      (writeSeqSetWriteReady r).write_state = .ready
  · rw [if_pos hz] at hc
    rw [(checkBit_frame _).1, hz.1] at hc
    have hv := congrArg Fin.val hc.1
    simp at hv
    omega
  · rw [if_neg hz] at hc
    rcases setWriteReady_ready_or_none r with hr | hr <;>
      rw [hr] at hc <;> cases hc.2

end PPLLWriteSeqDeadBranches
