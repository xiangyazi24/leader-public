import Leader.Wu.WriteSeq.PersistenceRepair

/-!
# Cross-algorithm write-lifecycle obstructions

Fixing Algorithm 16's ready reset is not enough to make the printed write
lifecycle executable.  Algorithm 19 line 19 sets the responder to `depart` on
every stable successor edge, so a comparison result created at label zero is
erased in the same interaction.  At the group boundary, Algorithm 19 lines 2--4
also replace the terminal initiator's state by `writeActionToState u.write`,
whose range excludes `depart`.  Consequently Algorithm 20's path-transfer guard
cannot hold when a path attempts to cross the terminal-to-zero edge.

The theorems below are source-level facts about the audited Algorithms 19--20.
They hold independently of the experimental line-8 persistence repair and
formalize why that prototype gains branch executability but no live write
route.
-/

namespace PPLLWriteSeqLifecycleObstructions

open PPLL

variable {ψ : Nat}

private theorem writeActionActivate_label
    (hψ : ψ > 0) (u : AgentState ψ) :
    (writeActionActivate hψ u).label = u.label := by
  unfold writeActionActivate
  split <;> rfl

/-- Algorithm 19 line 19 forces responder departure whenever its line-5
movement guard is true, regardless of the comparison state it received. -/
theorem writeAction_responder_departs_of_guard
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hguard : l.label < r.label ∨ r.label = ⟨0, hψ⟩) :
    (writeAction hψ l r).2.write_state = .depart := by
  rw [writeAction_eq_staged]
  unfold writeActionStaged
  let la := writeActionActivate hψ l
  let ra := writeActionActivate hψ r
  have hla : la.label = l.label := writeActionActivate_label hψ l
  have hra : ra.label = r.label := writeActionActivate_label hψ r
  change (writeActionExecute hψ la ra).2.write_state = .depart
  unfold writeActionExecute
  rw [if_pos]
  rw [hla, hra]
  exact hguard

/-- Every stable directed label edge satisfies Algorithm 19's movement guard:
it is increasing inside a group and wraps to label zero at the boundary. -/
theorem stable_successor_write_guard
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hsucc : r.label =
      ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) :
    l.label < r.label ∨ r.label = ⟨0, hψ⟩ := by
  by_cases hlt : l.label.val + 1 < ψ
  · left
    rw [hsucc]
    change l.label.val < (l.label.val + 1) % ψ
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · right
    rw [hsucc]
    apply Fin.ext
    dsimp only
    have heq : l.label.val + 1 = ψ := by omega
    rw [heq, Nat.mod_self]

/-- Hence every stable-edge responder leaves Algorithm 19 in `depart`; a newly
computed responder `equal` cannot survive the complete write action. -/
theorem writeAction_stable_successor_responder_departs
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hsucc : r.label =
      ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) :
    (writeAction hψ l r).2.write_state = .depart :=
  writeAction_responder_departs_of_guard hψ l r
    (stable_successor_write_guard hψ l r hsucc)

/-- Terminal activation maps every write action into a state other than
`depart`. Thus an incoming terminal departure marker is erased before
Algorithm 20 inspects it. -/
theorem writeActionActivate_terminal_not_depart
    (hψ : ψ > 0) (u : AgentState ψ)
    (hterm : u.label = ⟨ψ - 1, by omega⟩) :
    (writeActionActivate hψ u).write_state ≠ .depart := by
  unfold writeActionActivate
  rw [if_pos hterm]
  cases u.write <;> simp [writeActionToState]

private theorem writeActionApplyOverwrite_label (u : AgentState ψ) :
    (writeActionApplyOverwrite u).label = u.label := by
  unfold writeActionApplyOverwrite
  cases u.path3 <;> rfl

private theorem writeActionApplyMoveFlip_label (u : AgentState ψ) :
    (writeActionApplyMoveFlip u).label = u.label := by
  unfold writeActionApplyMoveFlip
  cases u.path3 <;> rfl

/-- On the terminal-to-zero edge, line 18 does not copy the responder state
back to the initiator, so terminal activation leaves the initiator non-depart. -/
theorem writeAction_terminal_wrap_initiator_not_depart
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.label = ⟨ψ - 1, by omega⟩)
    (hr : r.label = ⟨0, hψ⟩) :
    (writeAction hψ l r).1.write_state ≠ .depart := by
  rw [writeAction_eq_staged]
  unfold writeActionStaged
  let la := writeActionActivate hψ l
  let ra := writeActionActivate hψ r
  have hla : la.write_state ≠ .depart :=
    writeActionActivate_terminal_not_depart hψ l hl
  have hraLabel : ra.label = r.label := writeActionActivate_label hψ r
  have hraZero : ra.label = ⟨0, hψ⟩ := hraLabel.trans hr
  change (writeActionExecute hψ la ra).1.write_state ≠ .depart
  unfold writeActionExecute
  rw [if_pos (Or.inr hraZero)]
  simp [writeActionApplyOverwrite_label, writeActionApplyMoveFlip_label,
    hraZero, hla]

private theorem moveWsigStart_initiator_not_depart
    (l r : AgentState ψ) (hl : l.write_state ≠ .depart) :
    (moveWsigStart l r).1.write_state ≠ .depart := by
  unfold moveWsigStart
  split
  · simp
  · exact hl

private theorem moveWsigCheckLast_not_depart
    (l : AgentState ψ) (hl : l.write_state ≠ .depart) :
    (moveWsigCheckLast l).write_state ≠ .depart := by
  cases hp : l.path3 with
  | none => simpa [moveWsigCheckLast, hp] using hl
  | some p3 =>
    by_cases hcond : l.label.val = p3.label ∧ l.last = true
    · simp [moveWsigCheckLast, hp, hcond]
    · simpa [moveWsigCheckLast, hp, hcond] using hl

private theorem moveWsigTransfer_inert_of_left_not_depart
    (l r : AgentState ψ) (hl : l.write_state ≠ .depart) :
    moveWsigTransfer l r = (l, r) := by
  unfold moveWsigTransfer
  cases l.path3 <;> cases r.path3 <;> simp [hl]

/-- **Algorithm 20 path transfer is dead at every stable group boundary.**
After Algorithm 19 on a terminal-to-zero edge, neither leader handling nor the
line-7 check can recreate initiator `depart`; therefore the line-11 transfer
stage is exactly identity. -/
theorem terminal_wrap_transfer_stage_dead
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.label = ⟨ψ - 1, by omega⟩)
    (hr : r.label = ⟨0, hψ⟩) :
    let qa := writeAction hψ l r
    let q0 := moveWsigStart qa.1 qa.2
    let l0 := moveWsigCheckLast q0.1
    moveWsigTransfer l0 q0.2 = (l0, q0.2) := by
  let qa := writeAction hψ l r
  let q0 := moveWsigStart qa.1 qa.2
  let l0 := moveWsigCheckLast q0.1
  have ha : qa.1.write_state ≠ .depart :=
    writeAction_terminal_wrap_initiator_not_depart hψ l r hl hr
  have h0 : q0.1.write_state ≠ .depart :=
    moveWsigStart_initiator_not_depart qa.1 qa.2 ha
  have hl0 : l0.write_state ≠ .depart :=
    moveWsigCheckLast_not_depart q0.1 h0
  exact moveWsigTransfer_inert_of_left_not_depart l0 q0.2 hl0

end PPLLWriteSeqLifecycleObstructions
