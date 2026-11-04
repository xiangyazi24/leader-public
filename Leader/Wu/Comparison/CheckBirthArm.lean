import Leader.Wu.Birth.LeaderlessEscapeCleanBotRepairs

set_option autoImplicit false
set_option Elab.async false

namespace ZZStep7

open PPLL

/-- Shape lemma: expose only CHECK's final birth arm. -/
theorem checkSig_birth_arm_shape
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (checkSig hψ l r).2 =
      checkSigSetLeader hψ
        (checkSigSetResult
          (checkSigCheckR hψ
            (checkSigCheckL hψ (checkSigSetReady l))
            (checkSigSetReady r))) := by
  rw [checkSig_eq_staged]
  rfl

/-- The birth arm itself: terminal + equal selects the leader-setting branch. -/
theorem checkSigSetLeader_birth_shape
    {ψ : Nat} (hψ : ψ > 0) (r : AgentState ψ)
    (hlabel : r.label = ⟨ψ - 1, by omega⟩)
    (hstate : r.state = .equal) :
    checkSigSetLeader hψ r = { r with leader := true } := by
  unfold checkSigSetLeader
  rw [if_pos ⟨hlabel, hstate⟩]

/-- An already-equal responder cannot be rewritten to CHECK_ready. -/
private theorem checkSigSetReady_eq_of_equal
    {ψ : Nat} (u : AgentState ψ)
    (hstate : u.state = .equal) :
    checkSigSetReady u = u := by
  cases hpath : u.path with
  | bot =>
      simp only [checkSigSetReady, hpath]
  | some label bit =>
      simp only [checkSigSetReady, hpath]
      split
      · rename_i hguard
        exact (hguard.2.2.1 hstate).elim
      · rfl

/-- CheckR cannot rewrite an already-equal responder, because its write arm
requires responder state CHECK_ready. -/
private theorem checkSigCheckR_eq_of_equal
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hstate : r.state = .equal) :
    checkSigCheckR hψ l r = r := by
  cases hpath : r.path with
  | bot =>
      simp only [checkSigCheckR, hpath]
  | some pathLabel pathBit =>
      simp only [checkSigCheckR, hpath]
      split
      · split
        · rename_i hready
          have hbad : MainState.equal = MainState.CHECK_ready :=
            hstate.symm.trans hready
          cases hbad
        · rfl
      · rfl

/-- Result emission only handles larger/less, so equal is framed. -/
private theorem checkSigSetResult_eq_of_equal
    {ψ : Nat} (u : AgentState ψ)
    (hstate : u.state = .equal) :
    checkSigSetResult u = u := by
  have hlarge : u.state ≠ MainState.larger := by
    intro h
    have hbad : MainState.equal = MainState.larger :=
      hstate.symm.trans h
    cases hbad
  have hless : u.state ≠ MainState.less := by
    intro h
    have hbad : MainState.equal = MainState.less :=
      hstate.symm.trans h
    cases hbad
  unfold checkSigSetResult
  rw [if_neg hlarge]
  rw [if_neg hless]

/-- C5 step 7: a terminal responder already in .equal takes CHECK's birth arm
and leaves the complete CHECK stage with leader=true. -/
theorem checkSig_birth_of_terminal_equal
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlabel : r.label = ⟨ψ - 1, by omega⟩)
    (hstate : r.state = .equal) :
    (checkSig hψ l r).2.leader = true := by
  have hr0 : checkSigSetReady r = r :=
    checkSigSetReady_eq_of_equal r hstate

  have hr1 :
      checkSigCheckR hψ
        (checkSigCheckL hψ (checkSigSetReady l))
        (checkSigSetReady r) = r := by
    rw [hr0]
    exact checkSigCheckR_eq_of_equal hψ
      (checkSigCheckL hψ (checkSigSetReady l)) r hstate

  have hr2 :
      checkSigSetResult
        (checkSigCheckR hψ
          (checkSigCheckL hψ (checkSigSetReady l))
          (checkSigSetReady r)) = r := by
    rw [hr1]
    exact checkSigSetResult_eq_of_equal r hstate

  calc
    (checkSig hψ l r).2.leader =
        (checkSigSetLeader hψ
          (checkSigSetResult
            (checkSigCheckR hψ
              (checkSigCheckL hψ (checkSigSetReady l))
              (checkSigSetReady r)))).leader := by
      rw [checkSig_birth_arm_shape]
    _ = (checkSigSetLeader hψ r).leader := by
      rw [hr2]
    _ = true := by
      rw [checkSigSetLeader_birth_shape hψ r hlabel hstate]

#print axioms ZZStep7.checkSig_birth_arm_shape
#print axioms ZZStep7.checkSigSetLeader_birth_shape
#print axioms ZZStep7.checkSig_birth_of_terminal_equal

end ZZStep7
