import Leader.Wu.Birth.GenerationDone
import Leader.Wu.Comparison.HistoryStages

set_option autoImplicit false

namespace PPLLComparisonHistory

open PPLL PPLLRepair

variable {n ψ : Nat}

/-- Current captured Step 1.  On a successful aligned capture, both the
receiver path and its newly derived CHECK-ready state inherit the source of the
sender's old path.  A successful misaligned capture still moves that path, but
the receiver state is none and therefore receives an absent state mark. -/
def markedCaptureStep1 (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := BirthArrivalCaptureRepair.captureStep1 l.concrete r.concrete
  match l.concrete.path, r.concrete.path with
  | .some pathLabel _, .bot =>
    if _hstate : l.concrete.state ≠ .lock ∧
        l.concrete.state ≠ .compare1 ∧
        l.concrete.state ≠ .CHECK_ready then
      if _hdest : r.concrete.state ≠ .produce ∨ pathLabel ≠ ψ - 1 then
        let lHistory :=
          { l.history with state := .absent, path := .absent }
        if _halign : r.concrete.label.val = pathLabel then
          let rHistory :=
            { r.history with
              state := l.history.path
              path := l.history.path
              path2 := .absent }
          (⟨q.1, lHistory⟩, ⟨q.2, rHistory⟩)
        else
          let rHistory :=
            { r.history with
              state := .absent
              path := l.history.path
              path2 := .absent }
          (⟨q.1, lHistory⟩, ⟨q.2, rHistory⟩)
      else
        (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)
    else
      (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)
  | _, _ =>
    (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

/-- The marked current Step 1 erases exactly to the current physical
`captureStep1`, including its receiver path2 reset and state repair. -/
theorem erase_markedCaptureStep1 (l r : MarkedAgentState n ψ) :
    let q := markedCaptureStep1 l r
    (q.1.concrete, q.2.concrete) =
      BirthArrivalCaptureRepair.captureStep1 l.concrete r.concrete := by
  unfold markedCaptureStep1
  repeat (first | rfl | split)

/-- Current captured Step 1 preserves fieldwise audit trust.  No source-join
premise is needed: every newly active receiver field on the transfer branch is
derived from the single already-authenticated sender path. -/
theorem markedCaptureStep1_preserves_auditLocalHistoryTrusted
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedCaptureStep1 l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
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
          have hq : BirthArrivalCaptureRepair.captureStep1
              l.concrete r.concrete =
              ({ l.concrete with path := .bot, state := .none },
               { r.concrete with
                 path := l.concrete.path
                 path2 := none
                 state := .CHECK_ready }) := by
            simp [BirthArrivalCaptureRepair.captureStep1,
              hlpath, hrpath, hstate, hdest, halign]
          rw [hq]
          have hlPresent : l.concrete.path ≠ .bot := by
            rw [hlpath]
            intro hbad
            contradiction
          obtain ⟨source, hsource⟩ :=
            pathSource_of_present l.concrete l.history hl hlPresent
          constructor
          · unfold AuditLocalHistoryTrusted
            exact ⟨.inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, hl.2.2⟩
          · unfold AuditLocalHistoryTrusted
            exact ⟨
              .inr ⟨by simp, source, hsource⟩,
              .inr ⟨by
                rw [hlpath]
                intro hbad
                contradiction, source, hsource⟩,
              .inl ⟨rfl, rfl⟩⟩
        next halign =>
          have hq : BirthArrivalCaptureRepair.captureStep1
              l.concrete r.concrete =
              ({ l.concrete with path := .bot, state := .none },
               { r.concrete with
                 path := l.concrete.path
                 path2 := none
                 state := .none }) := by
            simp [BirthArrivalCaptureRepair.captureStep1,
              hlpath, hrpath, hstate, hdest, halign]
          rw [hq]
          have hlPresent : l.concrete.path ≠ .bot := by
            rw [hlpath]
            intro hbad
            contradiction
          obtain ⟨source, hsource⟩ :=
            pathSource_of_present l.concrete l.history hl hlPresent
          constructor
          · unfold AuditLocalHistoryTrusted
            exact ⟨.inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, hl.2.2⟩
          · unfold AuditLocalHistoryTrusted
            exact ⟨
              .inl ⟨rfl, rfl⟩,
              .inr ⟨by
                rw [hlpath]
                intro hbad
                contradiction, source, hsource⟩,
              .inl ⟨rfl, rfl⟩⟩
      next hdest =>
        have hq : BirthArrivalCaptureRepair.captureStep1
            l.concrete r.concrete = (l.concrete, r.concrete) := by
          simp [BirthArrivalCaptureRepair.captureStep1,
            hlpath, hrpath, hstate, hdest]
        rw [hq]
        exact ⟨hl, hr⟩
    next hstate =>
      have hq : BirthArrivalCaptureRepair.captureStep1
          l.concrete r.concrete = (l.concrete, r.concrete) := by
        simp [BirthArrivalCaptureRepair.captureStep1,
          hlpath, hrpath, hstate]
      rw [hq]
      exact ⟨hl, hr⟩
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
    exact ⟨hl, hr⟩

end PPLLComparisonHistory

#print axioms PPLLComparisonHistory.erase_markedCaptureStep1
#print axioms PPLLComparisonHistory.markedCaptureStep1_preserves_auditLocalHistoryTrusted
