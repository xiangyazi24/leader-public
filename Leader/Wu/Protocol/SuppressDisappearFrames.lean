import Leader.Wu.Protocol.Repairs

set_option autoImplicit false

/-!
# T0 frames for SUPPRESS_SIG, DISAPPEAR, and repaired Algorithm 15

Every leaf lemma unfolds exactly one subfunction with `simp only` and splits
only that subfunction's own branches.  The multi-stage theorems use the public
staged equalities and transitivity; they never unfold a whole chain.
-/

namespace ZZT0Suppress

open PPLL PPLLRepair

/-- The eight fields read by the T0 invariant. -/
structure T0EightFields (ψ : Nat) where
  leader : Bool
  label : Fin ψ
  bit : Bool
  state : MainState
  path : PathInfo
  path2 : Option Path2Info
  path3 : Option Path3Info
  write : WriteAction

namespace T0EightFields

abbrev ofState {ψ : Nat} (u : AgentState ψ) : T0EightFields ψ :=
  ⟨u.leader, u.label, u.bit, u.state,
    u.path, u.path2, u.path3, u.write⟩

end T0EightFields

/-- Pair projection for all eight T0 fields. -/
abbrev t0EightFieldPair {ψ : Nat}
    (q : AgentState ψ × AgentState ψ) :
    T0EightFields ψ × T0EightFields ψ :=
  (T0EightFields.ofState q.1, T0EightFields.ofState q.2)

/-- The seven DISAPPEAR-carry fields other than `state`. -/
structure T0CarryFields (ψ : Nat) where
  leader : Bool
  label : Fin ψ
  bit : Bool
  path : PathInfo
  path2 : Option Path2Info
  path3 : Option Path3Info
  write : WriteAction

namespace T0CarryFields

abbrev ofState {ψ : Nat} (u : AgentState ψ) : T0CarryFields ψ :=
  ⟨u.leader, u.label, u.bit,
    u.path, u.path2, u.path3, u.write⟩

end T0CarryFields

/-- Pair projection for the seven exact DISAPPEAR-carry frames. -/
abbrev t0CarryFieldPair {ψ : Nat}
    (q : AgentState ψ × AgentState ψ) :
    T0CarryFields ψ × T0CarryFields ψ :=
  (T0CarryFields.ofState q.1, T0CarryFields.ofState q.2)

/-- The seven T0 fields other than `leader`. -/
structure T0NonLeaderFields (ψ : Nat) where
  label : Fin ψ
  bit : Bool
  state : MainState
  path : PathInfo
  path2 : Option Path2Info
  path3 : Option Path3Info
  write : WriteAction

namespace T0NonLeaderFields

abbrev ofState {ψ : Nat} (u : AgentState ψ) :
    T0NonLeaderFields ψ :=
  ⟨u.label, u.bit, u.state,
    u.path, u.path2, u.path3, u.write⟩

end T0NonLeaderFields

/-- Pair projection for the seven exact Algorithm-15 frames. -/
abbrev t0NonLeaderFieldPair {ψ : Nat}
    (q : AgentState ψ × AgentState ψ) :
    T0NonLeaderFields ψ × T0NonLeaderFields ψ :=
  (T0NonLeaderFields.ofState q.1,
    T0NonLeaderFields.ofState q.2)

/-! ## SUPPRESS_SIG: five independent leaf frames -/

theorem suppressSigStart_t0_frame {ψ : Nat}
    (l r : AgentState ψ) :
    t0EightFieldPair (suppressSigStart l r) =
      t0EightFieldPair (l, r) := by
  simp only [suppressSigStart]
  repeat (first | rfl | split)

theorem suppressSigMoveReset_t0_frame {ψ : Nat}
    (l r : AgentState ψ) :
    t0EightFieldPair (suppressSigMoveReset l r) =
      t0EightFieldPair (l, r) := by
  simp only [suppressSigMoveReset]
  repeat (first | rfl | split)

theorem suppressSigTerminal_t0_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    t0EightFieldPair (suppressSigTerminal hψ l r) =
      t0EightFieldPair (l, r) := by
  simp only [suppressSigTerminal]
  repeat (first | rfl | split)

theorem suppressSigEcho_t0_frame {ψ : Nat}
    (l r : AgentState ψ) :
    t0EightFieldPair (suppressSigEcho l r) =
      t0EightFieldPair (l, r) := by
  simp only [suppressSigEcho]
  repeat (first | rfl | split)

theorem suppressSigFinish_t0_frame {ψ : Nat}
    (l r : AgentState ψ) :
    t0EightFieldPair (suppressSigFinish l r) =
      t0EightFieldPair (l, r) := by
  simp only [suppressSigFinish]
  repeat (first | rfl | split)

/-- SUPPRESS_SIG frames all eight T0 fields on both endpoints. -/
theorem suppressSig_t0_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    t0EightFieldPair (suppressSig hψ l r) =
      t0EightFieldPair (l, r) := by
  rw [suppressSig_eq_staged]
  let q0 := suppressSigStart l r
  let q1 := suppressSigMoveReset q0.1 q0.2
  let q2 := suppressSigTerminal hψ q1.1 q1.2
  let q3 := suppressSigEcho q2.1 q2.2
  let q4 := suppressSigFinish q3.1 q3.2
  have h0 := suppressSigStart_t0_frame l r
  have h1 := suppressSigMoveReset_t0_frame q0.1 q0.2
  have h2 := suppressSigTerminal_t0_frame hψ q1.1 q1.2
  have h3 := suppressSigEcho_t0_frame q2.1 q2.2
  have h4 := suppressSigFinish_t0_frame q3.1 q3.2
  change t0EightFieldPair q0 = t0EightFieldPair (l, r) at h0
  change t0EightFieldPair q1 = t0EightFieldPair q0 at h1
  change t0EightFieldPair q2 = t0EightFieldPair q1 at h2
  change t0EightFieldPair q3 = t0EightFieldPair q2 at h3
  change t0EightFieldPair q4 = t0EightFieldPair q3 at h4
  change t0EightFieldPair q4 = t0EightFieldPair (l, r)
  exact h4.trans (h3.trans (h2.trans (h1.trans h0)))

/-! ## DISAPPEAR leaf facts -/

/-- A responder outside `.toss` makes the responder-start stage identity. -/
theorem disappearStartR_ok {ψ : Nat}
    (hψ : ψ > 0) (l u : AgentState ψ)
    (hu : u.state ≠ .toss) :
    disappearStartR hψ l u = (l, u) := by
  simp only [disappearStartR]
  split
  · rename_i hguard
    exact (hu hguard.1).elim
  · rfl

/-- An initiator outside `.toss` makes the initiator-start stage identity. -/
theorem disappearStartL_ok {ψ : Nat}
    (hψ : ψ > 0) (u r : AgentState ψ)
    (hu : u.state ≠ .toss) :
    disappearStartL hψ u r = (u, r) := by
  simp only [disappearStartL]
  split
  · rename_i hguard
    exact (hu hguard.1).elim
  · rfl

/-- DISAPPEAR's carry stage frames the requested seven non-state fields. -/
theorem disappearCarry_t0_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    t0CarryFieldPair (disappearCarry hψ l r) =
      t0CarryFieldPair (l, r) := by
  simp only [disappearCarry]
  repeat (first | rfl | split)

/-- The left state is exact; the right state is exact or is overwritten by
`.eliminate_signal`, which is the only state assignment in this stage. -/
theorem disappearCarry_state {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := disappearCarry hψ l r
    q.1.state = l.state ∧
      (q.2.state = r.state ∨
        q.2.state = .eliminate_signal) := by
  simp only [disappearCarry]
  repeat
    (first
      | exact ⟨rfl, Or.inl rfl⟩
      | exact ⟨rfl, Or.inr rfl⟩
      | split)

/-! ## No-collision Algorithm 15: independent seven-field frames -/

theorem eliminateLeadersNoCollisionFire_t0_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    t0NonLeaderFieldPair
        (eliminateLeadersNoCollisionFire hψ l r) =
      t0NonLeaderFieldPair (l, r) := by
  simp only [eliminateLeadersNoCollisionFire]
  repeat (first | rfl | split)

theorem eliminateLeadersNoCollisionMove_t0_frame {ψ : Nat}
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    t0NonLeaderFieldPair
        (eliminateLeadersNoCollisionMove nextLabel l r) =
      t0NonLeaderFieldPair (l, r) := by
  simp only [eliminateLeadersNoCollisionMove]
  repeat (first | rfl | split)

theorem eliminateLeadersNoCollisionSignal_t0_frame {ψ : Nat}
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    t0NonLeaderFieldPair
        (eliminateLeadersNoCollisionSignal nextLabel l r) =
      t0NonLeaderFieldPair (l, r) := by
  simp only [eliminateLeadersNoCollisionSignal]
  repeat (first | rfl | split)

/-- The repaired Algorithm 15 frames label/bit/state/path/path2/path3/write. -/
theorem eliminateLeadersNoCollision_t0_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    t0NonLeaderFieldPair
        (eliminateLeadersNoCollision hψ l r) =
      t0NonLeaderFieldPair (l, r) := by
  rw [eliminateLeadersNoCollision_eq_staged]
  let nextLabel : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := eliminateLeadersNoCollisionMove nextLabel q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignal nextLabel q1.1 q1.2
  have h0 := eliminateLeadersNoCollisionFire_t0_frame hψ l r
  have h1 := eliminateLeadersNoCollisionMove_t0_frame
    nextLabel q0.1 q0.2
  have h2 := eliminateLeadersNoCollisionSignal_t0_frame
    nextLabel q1.1 q1.2
  change
    t0NonLeaderFieldPair q0 = t0NonLeaderFieldPair (l, r) at h0
  change
    t0NonLeaderFieldPair q1 = t0NonLeaderFieldPair q0 at h1
  change
    t0NonLeaderFieldPair q2 = t0NonLeaderFieldPair q1 at h2
  change
    t0NonLeaderFieldPair q2 = t0NonLeaderFieldPair (l, r)
  exact h2.trans (h1.trans h0)

/-! ## No-collision Algorithm 15: leader shape -/

/-- FIRE does not write the left leader field. -/
theorem eliminateLeadersNoCollisionFire_left_leader {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.leader =
      l.leader := by
  simp only [eliminateLeadersNoCollisionFire]
  repeat (first | rfl | split)

/-- FIRE does not write the right leader field. -/
theorem eliminateLeadersNoCollisionFire_right_leader {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).2.leader =
      r.leader := by
  simp only [eliminateLeadersNoCollisionFire]
  repeat (first | rfl | split)

/-- MOVE either preserves the left leader field or writes it to `false`. -/
theorem eliminateLeadersNoCollisionMove_left_leader {ψ : Nat}
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    let q := eliminateLeadersNoCollisionMove nextLabel l r
    q.1.leader = l.leader ∨ q.1.leader = false := by
  simp only [eliminateLeadersNoCollisionMove]
  repeat
    (first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | split)

/-- MOVE does not write the right leader field. -/
theorem eliminateLeadersNoCollisionMove_right_leader_frame {ψ : Nat}
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionMove nextLabel l r).2.leader =
      r.leader := by
  simp only [eliminateLeadersNoCollisionMove]
  repeat (first | rfl | split)

/-- SIGNAL does not write the left leader field. -/
theorem eliminateLeadersNoCollisionSignal_left_leader {ψ : Nat}
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignal nextLabel l r).1.leader =
      l.leader := by
  simp only [eliminateLeadersNoCollisionSignal]
  repeat (first | rfl | split)

/-- SIGNAL does not write the right leader field. -/
theorem eliminateLeadersNoCollisionSignal_right_leader {ψ : Nat}
    (nextLabel : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignal nextLabel l r).2.leader =
      r.leader := by
  simp only [eliminateLeadersNoCollisionSignal]
  repeat (first | rfl | split)

/-- Across the complete no-collision Algorithm 15, the right leader is an
exact frame and the left leader is either unchanged or `false`.  Hence this
transition never creates a `true` leader bit. -/
theorem eliminateLeadersNoCollision_leader_write {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := eliminateLeadersNoCollision hψ l r
    (q.1.leader = l.leader ∨ q.1.leader = false) ∧
      q.2.leader = r.leader := by
  rw [eliminateLeadersNoCollision_eq_staged]
  let nextLabel : Fin ψ :=
    ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := eliminateLeadersNoCollisionMove nextLabel q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignal nextLabel q1.1 q1.2
  have hfL := eliminateLeadersNoCollisionFire_left_leader hψ l r
  have hfR := eliminateLeadersNoCollisionFire_right_leader hψ l r
  have hmL := eliminateLeadersNoCollisionMove_left_leader
    nextLabel q0.1 q0.2
  have hmR := eliminateLeadersNoCollisionMove_right_leader_frame
    nextLabel q0.1 q0.2
  have hsL := eliminateLeadersNoCollisionSignal_left_leader
    nextLabel q1.1 q1.2
  have hsR := eliminateLeadersNoCollisionSignal_right_leader
    nextLabel q1.1 q1.2
  change q0.1.leader = l.leader at hfL
  change q0.2.leader = r.leader at hfR
  change
    (q1.1.leader = q0.1.leader ∨
      q1.1.leader = false) at hmL
  change q1.2.leader = q0.2.leader at hmR
  change q2.1.leader = q1.1.leader at hsL
  change q2.2.leader = q1.2.leader at hsR
  change
    (q2.1.leader = l.leader ∨ q2.1.leader = false) ∧
      q2.2.leader = r.leader
  constructor
  · rcases hmL with hsame | hfalse
    · exact Or.inl (hsL.trans (hsame.trans hfL))
    · exact Or.inr (hsL.trans hfalse)
  · exact hsR.trans (hmR.trans hfR)

end ZZT0Suppress

#print axioms ZZT0Suppress.suppressSigStart_t0_frame
#print axioms ZZT0Suppress.suppressSigMoveReset_t0_frame
#print axioms ZZT0Suppress.suppressSigTerminal_t0_frame
#print axioms ZZT0Suppress.suppressSigEcho_t0_frame
#print axioms ZZT0Suppress.suppressSigFinish_t0_frame
#print axioms ZZT0Suppress.suppressSig_t0_frame
#print axioms ZZT0Suppress.disappearStartR_ok
#print axioms ZZT0Suppress.disappearStartL_ok
#print axioms ZZT0Suppress.disappearCarry_t0_frame
#print axioms ZZT0Suppress.disappearCarry_state
#print axioms ZZT0Suppress.eliminateLeadersNoCollisionFire_t0_frame
#print axioms ZZT0Suppress.eliminateLeadersNoCollisionMove_t0_frame
#print axioms ZZT0Suppress.eliminateLeadersNoCollisionSignal_t0_frame
#print axioms ZZT0Suppress.eliminateLeadersNoCollision_t0_frame
#print axioms ZZT0Suppress.eliminateLeadersNoCollisionFire_left_leader
#print axioms ZZT0Suppress.eliminateLeadersNoCollisionFire_right_leader
#print axioms ZZT0Suppress.eliminateLeadersNoCollisionMove_left_leader
#print axioms ZZT0Suppress.eliminateLeadersNoCollisionMove_right_leader_frame
#print axioms ZZT0Suppress.eliminateLeadersNoCollisionSignal_left_leader
#print axioms ZZT0Suppress.eliminateLeadersNoCollisionSignal_right_leader
#print axioms ZZT0Suppress.eliminateLeadersNoCollision_leader_write
