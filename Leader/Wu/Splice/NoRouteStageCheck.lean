import Leader.Wu.Splice.NoRouteDoneStages

set_option autoImplicit false
set_option Elab.async false

namespace B9NoRouteStageCheck

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair
open BirthGenerationDone
open B9NoRouteStagesB

variable {psi : Nat}

private theorem ready_ne
    (u : AgentState psi) (h : u.state ≠ .equal) :
    (checkSigSetReady u).state ≠ .equal := by
  cases hp : u.path with
  | bot =>
      simpa only [checkSigSetReady, hp] using h
  | some label bit =>
      simp only [checkSigSetReady, hp]
      split
      · exact fun he => nomatch he
      · exact h

private theorem ready_path (u : AgentState psi) :
    (checkSigSetReady u).path = u.path := by
  cases hp : u.path with
  | bot =>
      simp only [checkSigSetReady, hp]
  | some label bit =>
      simp only [checkSigSetReady, hp]
      split
      · rfl
      · exact hp

private theorem left_check_ne
    (hpsi : 0 < psi) (u : AgentState psi)
    (hne : u.state ≠ .equal)
    (hz : ∀ b, u.path = .some 0 b → u.state = .depart) :
    (checkSigCheckL hpsi (checkSigSetReady u)).state ≠ .equal := by
  let u0 := checkSigSetReady u
  have h0 : u0.state ≠ .equal := ready_ne u hne
  cases hp : u.path with
  | bot =>
      have hp0 : u0.path = .bot := (ready_path u).trans hp
      have heq : checkSigCheckL hpsi u0 = u0 := by
        simp only [checkSigCheckL, hp0]
      rw [heq]
      exact h0
  | some label bit =>
      cases label with
      | zero =>
          have hdep : u.state = .depart := hz bit hp
          have hready : u0 = u := by
            have hg : ¬(u.label.val = 0 ∧ u.state ≠ .depart ∧
                u.state ≠ .equal ∧ u.state ≠ .larger ∧ u.state ≠ .less) := by
              intro hguard
              exact hguard.2.1 hdep
            unfold u0
            simp only [checkSigSetReady, hp, if_neg hg]
          have hcheck : checkSigCheckL hpsi u0 = u := by
            rw [hready]
            have hg : ¬(u.label = ⟨0, hpsi⟩ ∧ u.state = .CHECK_ready) := by
              intro hguard
              have hbad : (.depart : MainState) = .CHECK_ready :=
                hdep.symm.trans hguard.2
              cases hbad
            simp only [checkSigCheckL, hp, if_neg hg]
          rw [hcheck]
          exact hne
      | succ label =>
          have hp0 : u0.path = .some (Nat.succ label) bit :=
            (ready_path u).trans hp
          have hcheck : checkSigCheckL hpsi u0 = u0 := by
            simp only [checkSigCheckL, hp0]
          rw [hcheck]
          exact h0

private theorem right_check_eq
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : l.state ≠ .equal) :
    checkSigCheckR hpsi l r = r := by
  cases hp : r.path with
  | bot =>
      simp only [checkSigCheckR, hp]
  | some label bit =>
      have hg : ¬(l.label.val < psi - 1 ∧ l.state = .equal) := by
        intro hguard
        exact hl hguard.2
      simp only [checkSigCheckR, hp, if_neg hg]

private theorem result_state (u : AgentState psi) :
    (checkSigSetResult u).state = u.state := by
  unfold checkSigSetResult
  split <;> dsimp only <;> split <;> rfl

private theorem leader_state
    (hpsi : 0 < psi) (u : AgentState psi) :
    (checkSigSetLeader hpsi u).state = u.state := by
  unfold checkSigSetLeader
  split <;> rfl

/-- CHECK preserves absence of `.equal` when a label-zero left path is already
in `depart`; this is the stage-local invariant needed by the no-route proof. -/
theorem check_preserves_noEqual (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi)
    (h : NoEqualOnPair l.core r.core)
    (hz : LeftZeroDepart l.core) :
    let q := authorizedCheckSig hpsi l r
    NoEqualOnPair q.1.core q.2.core := by
  let a := l.core
  let b := r.core
  let a0 := checkSigSetReady a
  let b0 := checkSigSetReady b
  have ha0 : a0.state ≠ .equal := ready_ne a h.1
  have hb0 : b0.state ≠ .equal := ready_ne b h.2
  let a1 := checkSigCheckL hpsi a0
  have ha1 : a1.state ≠ .equal := left_check_ne hpsi a h.1 hz
  let b1 := checkSigCheckR hpsi a1 b0
  have hb1eq : b1 = b0 := right_check_eq hpsi a1 b0 ha1
  have hb1 : b1.state ≠ .equal := by
    rw [hb1eq]
    exact hb0
  let a2 := checkSigSetResult a1
  let b2 := checkSigSetResult b1
  have ha2 : a2.state ≠ .equal := by
    intro heq
    exact ha1 ((result_state a1).symm.trans heq)
  have hb2 : b2.state ≠ .equal := by
    intro heq
    exact hb1 ((result_state b1).symm.trans heq)
  let b3 := checkSigSetLeader hpsi b2
  have hb3 : b3.state ≠ .equal := by
    intro heq
    exact hb2 ((leader_state hpsi b2).symm.trans heq)
  change NoEqualOnPair (checkSig hpsi a b).1 (checkSig hpsi a b).2
  rw [checkSig_eq_staged hpsi a b]
  change a2.state ≠ .equal ∧ b3.state ≠ .equal
  exact ⟨ha2, hb3⟩

#print axioms B9NoRouteStageCheck.check_preserves_noEqual

end B9NoRouteStageCheck
