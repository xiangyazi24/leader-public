import Leader.Wu.Birth.MismatchDisposalProducer
import Leader.Wu.Coherence.NewEqualStatePathFrame


set_option autoImplicit false


namespace R2NewEqualPreimage2


open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLCompleteMultiLeaderCleanup
open R2NewEqualPreimage


variable {psi : Nat}


private theorem compareSigInit_equal_preimage
    (u : AgentState psi)
    (hout : (compareSigInit u).state = .equal) :
    u.state = .equal := by
  cases hp : u.path with
  | bot =>
      have hbad : MainState.none = MainState.equal := by
        simpa only [compareSigInit, hp] using hout
      cases hbad
  | some a b =>
      simpa only [compareSigInit, hp] using hout


private theorem cmpUpdateSetPath2_state
    (hpsi : psi > 0) (u : AgentState psi) :
    (cmpUpdateSetPath2 hpsi u).state = u.state := by
  cases hp : u.path with
  | bot =>
      simp only [cmpUpdateSetPath2, hp]
  | some a b =>
      simp only [cmpUpdateSetPath2, hp]
      split <;> rfl


private theorem cmpStart_equal_preimage
    (hpsi : psi > 0) (l : AuthorizedAgentState psi) :
    let lc :=
      if freshComparisonStart hpsi l && !comparisonActive l.core.state then
        { l.core with state := MainState.congest }
      else l.core
    lc.state = .equal → l.core.state = .equal := by
  dsimp only
  split
  · intro hbad
    cases hbad
  · intro h
    exact h


private theorem cmpUpdateReturnPriority_equal_preimage
    (hpsi : psi > 0) (l r : AgentState psi) :
    let q := cmpUpdateReturnPriority hpsi l r
    (q.1.state = .equal → l.state = .equal) ∧
      (q.2.state = .equal → r.state = .equal) := by
  dsimp only
  unfold cmpUpdateReturnPriority
  by_cases h1 : l.label = ⟨psi - 1, by omega⟩ ∧ r.state = .compare1
  · rw [if_pos h1]
    constructor
    · intro hbad
      cases hbad
    · intro h
      exact h
  · rw [if_neg h1]
    by_cases h2 : r.state = .compare1 ∨ r.state = .compare2
    · rw [if_pos h2]
      constructor
      · intro hbad
        rcases h2 with h2 | h2
        · rw [h2] at hbad
          cases hbad
        · rw [h2] at hbad
          cases hbad
      · intro h
        exact h
    · rw [if_neg h2]
      by_cases h3 : l.label = ⟨psi - 1, by omega⟩ ∧ l.state = .congest
      · rw [if_pos h3]
        constructor
        · intro h
          exact h
        · intro hbad
          cases hbad
      · rw [if_neg h3]
        by_cases h4 : r.label = ⟨psi - 1, by omega⟩ ∧ l.state = .lock
        · rw [if_pos h4]
          constructor
          · intro h
            exact h
          · intro hbad
            cases hbad
        · rw [if_neg h4]
          by_cases h5 : l.state = .congest ∨ l.state = .lock
          · rw [if_pos h5]
            constructor
            · intro h
              exact h
            · intro hbad
              rcases h5 with h5 | h5
              · rw [h5] at hbad
                cases hbad
              · rw [h5] at hbad
                cases hbad
          · rw [if_neg h5]
            exact ⟨(fun h => h), (fun h => h)⟩

private theorem authorizedCmpUpdate_equal_preimage
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    let q := authorizedCmpUpdate hpsi l r
    (q.1.core.state = .equal → l.core.state = .equal) ∧
      (q.2.core.state = .equal → r.core.state = .equal) := by
  let lc : AgentState psi :=
    if freshComparisonStart hpsi l && !comparisonActive l.core.state then
      { l.core with state := MainState.congest }
    else l.core
  let q := cmpUpdateReturnPriority hpsi lc r.core
  have hstart : lc.state = .equal → l.core.state = .equal := by
    exact cmpStart_equal_preimage hpsi l
  have hret := cmpUpdateReturnPriority_equal_preimage hpsi lc r.core
  have hset := cmpUpdateSetPath2_state hpsi q.1
  change
    ((cmpUpdateSetPath2 hpsi q.1).state = .equal →
      l.core.state = .equal) ∧
    (q.2.state = .equal → r.core.state = .equal)
  constructor
  · intro hout
    exact hstart (hret.1 (hset.symm.trans hout))
  · exact hret.2


private theorem compareBitUpdateL_state
    (hpsi : psi > 0) (u : AgentState psi) :
    (compareBitUpdateL hpsi u).state = u.state := by
  cases hp2 : u.path2 with
  | none =>
      simp only [compareBitUpdateL, hp2]
  | some p2 =>
      cases hp : u.path with
      | bot =>
          simp only [compareBitUpdateL, hp2, hp]
      | some a b =>
          simp only [compareBitUpdateL, hp2, hp]
          split <;> rfl


private theorem compareBitUpdateRActionOne_state
    (hpsi : psi > 0) (u : AgentState psi) :
    (PPLLRepair.compareBitUpdateRActionOne hpsi u).state = u.state := by
  cases hp : u.path2 with
  | none =>
      simp [PPLLRepair.compareBitUpdateRActionOne, hp]
  | some p2 =>
      simp only [PPLLRepair.compareBitUpdateRActionOne, hp]
      repeat (first | rfl | split)


private theorem compareSigDispatchActionOne_state_frame
    (hpsi : psi > 0) (l r : AgentState psi) :
    (compareSigDispatchActionOne hpsi l r).1.state = l.state ∧
      (compareSigDispatchActionOne hpsi l r).2.state = r.state := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [compareSigDispatchActionOne, hl, hr, compareBitActionOne]
  · exact ⟨True.intro, True.intro⟩
  all_goals exact
    ⟨compareBitUpdateL_state hpsi l,
      compareBitUpdateRActionOne_state hpsi r⟩

private theorem compareActionOne_equal_state_preimage
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    let q := authorizedCompareSigActionOne hpsi l r
    (q.1.core.state = .equal → l.core.state = .equal) ∧
      (q.2.core.state = .equal → r.core.state = .equal) := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState psi :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hinit : lCore.state = .equal → l.core.state = .equal := by
    unfold lCore
    exact compareSigInit_equal_preimage l.core
  have hu := authorizedCmpUpdate_equal_preimage hpsi l0 r
  have hd := compareSigDispatchActionOne_state_frame hpsi
    (authorizedCmpUpdate hpsi l0 r).1.core
    (authorizedCmpUpdate hpsi l0 r).2.core
  unfold authorizedCompareSigActionOne
  dsimp only
  split
  · exact ⟨hinit, (fun h => h)⟩
  · split
    · exact ⟨hinit, (fun h => h)⟩
    · constructor
      · intro hout
        exact hinit (hu.1 (hd.1.symm.trans hout))
      · intro hout
        exact hu.2 (hd.2.symm.trans hout)

/-- The former named Prop is now discharged using the public path/label anchor
plus the state-only preimage argument above. -/
theorem compareActionOne_equal_preimage_holds
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    compareActionOne_equal_preimage hpsi l r := by
  have hs := compareActionOne_equal_state_preimage hpsi l r
  dsimp only at hs
  have ha :=
    BirthMismatchDisposalProducer.compareActionOne_anchor_public hpsi l r
  have hpL :
      (authorizedCompareSigActionOne hpsi l r).1.core.path = l.core.path :=
    congrArg
      (fun x : Bool × Bool × Fin psi × PathInfo => x.2.2.2) ha.1
  have hpR :
      (authorizedCompareSigActionOne hpsi l r).2.core.path = r.core.path :=
    congrArg
      (fun x : Bool × Bool × Fin psi × PathInfo => x.2.2.2) ha.2
  have hlL :
      (authorizedCompareSigActionOne hpsi l r).1.core.label = l.core.label :=
    congrArg
      (fun x : Bool × Bool × Fin psi × PathInfo => x.2.2.1) ha.1
  have hlR :
      (authorizedCompareSigActionOne hpsi l r).2.core.label = r.core.label :=
    congrArg
      (fun x : Bool × Bool × Fin psi × PathInfo => x.2.2.1) ha.2
  unfold R2NewEqualPreimage.compareActionOne_equal_preimage
  dsimp only
  constructor
  · intro hout
    exact ⟨hs.1 hout, hpL.symm, hlL.symm⟩
  · intro hout
    exact ⟨hs.2 hout, hpR.symm, hlR.symm⟩


end R2NewEqualPreimage2
