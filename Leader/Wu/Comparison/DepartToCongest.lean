import Leader.Wu.Birth.LeaderlessEscapeCleanBotRepairs


set_option autoImplicit false
set_option Elab.async false


namespace ZZStep5


open PPLL PPLLRepair


/-- A present path is unchanged by the COMPARE initializer. -/
private theorem compareSigInit_eq_of_some
    {ψ : Nat} (l : AgentState ψ) (pathLabel pathBit : Nat)
    (hpath : l.path = PathInfo.some pathLabel pathBit) :
    compareSigInit l = l := by
  unfold compareSigInit
  rw [hpath]


/-- Algorithm 7's final path2 writer changes only path2, never state. -/
private theorem cmpUpdateSetPath2_state
    {ψ : Nat} (hψ : ψ > 0) (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).state = l.state := by
  cases hp : l.path with
  | bot =>
      simp only [cmpUpdateSetPath2, hp]
  | some pathLabel pathBit =>
      simp only [cmpUpdateSetPath2, hp]
      split <;> rfl


/-- Once the left endpoint is congested, Algorithm 7 propagation keeps its
left state congested. -/
private theorem cmpUpdatePropagate_left_congest
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.state = MainState.congest) :
    (cmpUpdatePropagate hψ l r).1.state = MainState.congest := by
  unfold cmpUpdatePropagate
  by_cases hlast : l.label = (⟨ψ - 1, by omega⟩ : Fin ψ)
  · rw [if_pos ⟨hlast, hl⟩]
    exact hl
  · rw [if_neg (by
      intro h
      exact hlast h.1)]
    have hnotLock : l.state ≠ MainState.lock := by
      intro hlock
      have hbad : MainState.congest = MainState.lock :=
        hl.symm.trans hlock
      cases hbad
    rw [if_neg (by
      intro h
      exact hnotLock h.2)]
    rw [if_neg (by
      intro h
      exact hlast h.1)]
    rw [if_pos (Or.inl hl)]
    exact hl


/-- COMPARE_BIT's left updater changes only path2, never state. -/
private theorem compareBitUpdateL_state
    {ψ : Nat} (hψ : ψ > 0) (l : AgentState ψ) :
    (compareBitUpdateL hψ l).state = l.state := by
  cases hp2 : l.path2 with
  | none =>
      simp only [compareBitUpdateL, hp2]
  | some p2 =>
      cases hp : l.path with
      | bot =>
          simp only [compareBitUpdateL, hp2, hp]
      | some pathLabel pathBit =>
          simp only [compareBitUpdateL, hp2, hp]
          split <;> rfl


/-- Therefore COMPARE_BIT preserves the left main state. -/
private theorem compareBit_left_state
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareBit hψ l r).1.state = l.state := by
  unfold compareBit
  exact compareBitUpdateL_state hψ l


/-- The final COMPARE dispatch either does nothing or runs COMPARE_BIT, so it
also preserves the left main state.  Split the two path2 matches explicitly;
this avoids leaving hidden match branches as unsolved goals. -/
private theorem compareSigDispatch_left_state
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).1.state = l.state := by
  cases hl : l.path2 with
  | none =>
      cases hr : r.path2 with
      | none =>
          simp only [compareSigDispatch, hl, hr]
      | some p2 =>
          simp only [compareSigDispatch, hl, hr]
          exact compareBit_left_state hψ l r
  | some p2 =>
      cases hr : r.path2 with
      | none =>
          simp only [compareSigDispatch, hl, hr]
          exact compareBit_left_state hψ l r
      | some p2r =>
          simp only [compareSigDispatch, hl, hr]
          exact compareBit_left_state hψ l r


/-- All8's weakened T9 guard re-arms a label-zero follower even when that
follower is currently in .depart. -/
private theorem cmpUpdateGuarded_depart_to_congest
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (hlLabel : l.label = ⟨0, hψ⟩)
    (hlLeader : l.leader = false)
    (_hlState : l.state = MainState.depart) :
    (ZZRepairAll8.cmpUpdateGuarded hψ l r).1.state =
      MainState.congest := by
  have hguard :
      l.label = ⟨0, hψ⟩ ∧
        (l.state ≠ MainState.depart ∨ l.leader = false) :=
    ⟨hlLabel, Or.inr hlLeader⟩
  let l0 :=
    if l.label = ⟨0, hψ⟩ ∧
        (l.state ≠ MainState.depart ∨ l.leader = false) then
      { l with state := MainState.congest }
    else l
  let q := cmpUpdatePropagate hψ l0 r
  have hl0 : l0.state = MainState.congest := by
    dsimp [l0]
    rw [if_pos hguard]
  have hq : q.1.state = MainState.congest := by
    dsimp [q]
    exact cmpUpdatePropagate_left_congest hψ l0 r hl0
  change (cmpUpdateSetPath2 hψ q.1).state = MainState.congest
  exact (cmpUpdateSetPath2_state hψ q.1).trans hq


/-- Local shape theorem for the two path-present branches of the All8
COMPARE wrapper.  This is the compile fix: discharge the two nested matches
in one controlled simp-only step instead of order-sensitive rewrites. -/
private theorem compareSigGuarded_eq_dispatch_of_some
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (lPathLabel lPathBit rPathLabel rPathBit : Nat)
    (hlPath : l.path = PathInfo.some lPathLabel lPathBit)
    (hrPath : r.path = PathInfo.some rPathLabel rPathBit) :
    ZZRepairAll8.compareSigGuarded hψ l r =
      compareSigDispatch hψ
        (ZZRepairAll8.cmpUpdateGuarded hψ l r).1
        (ZZRepairAll8.cmpUpdateGuarded hψ l r).2 := by
  simp only [ZZRepairAll8.compareSigGuarded,
    compareSigInit_eq_of_some l lPathLabel lPathBit hlPath,
    hlPath, hrPath]


/-- C5 step 5: in the actual All8 COMPARE wrapper, a label-zero follower in
.depart with both paths present exits COMPARE in .congest. -/
theorem depart_to_congest_after_compare
    {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ)
    (lPathLabel lPathBit rPathLabel rPathBit : Nat)
    (hlLabel : l.label = ⟨0, hψ⟩)
    (hlLeader : l.leader = false)
    (hlState : l.state = MainState.depart)
    (hlPath : l.path = PathInfo.some lPathLabel lPathBit)
    (hrPath : r.path = PathInfo.some rPathLabel rPathBit) :
    (ZZRepairAll8.compareSigGuarded hψ l r).1.state =
      MainState.congest := by
  have hshape :=
    compareSigGuarded_eq_dispatch_of_some
      hψ l r lPathLabel lPathBit rPathLabel rPathBit hlPath hrPath
  have hcmp :=
    cmpUpdateGuarded_depart_to_congest
      hψ l r hlLabel hlLeader hlState
  calc
    (ZZRepairAll8.compareSigGuarded hψ l r).1.state =
        (compareSigDispatch hψ
          (ZZRepairAll8.cmpUpdateGuarded hψ l r).1
          (ZZRepairAll8.cmpUpdateGuarded hψ l r).2).1.state := by
      exact congrArg (fun q => q.1.state) hshape
    _ = (ZZRepairAll8.cmpUpdateGuarded hψ l r).1.state :=
      compareSigDispatch_left_state hψ
        (ZZRepairAll8.cmpUpdateGuarded hψ l r).1
        (ZZRepairAll8.cmpUpdateGuarded hψ l r).2
    _ = MainState.congest := hcmp


#print axioms ZZStep5.depart_to_congest_after_compare


end ZZStep5
