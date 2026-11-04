import Leader.Wu.Protocol.Algorithm

set_option autoImplicit false
set_option Elab.async false

namespace ZZT0Compare

open PPLL

def A5 : Path2Info := ⟨0, 0, 1, 5⟩

def StateOK (s : MainState) : Prop :=
  s ≠ .larger ∧ s ≠ .less ∧ s ≠ .toss ∧
    s ≠ .compare1 ∧ s ≠ .compare2

/-! ## compareSigInit -/

theorem compareSigInit_state {ψ : Nat} (u : AgentState ψ) :
    (compareSigInit u).state = MainState.none ∨
      (compareSigInit u).state = u.state := by
  simp only [compareSigInit]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem compareSigInit_label {ψ : Nat} (u : AgentState ψ) :
    (compareSigInit u).label = u.label := by
  simp only [compareSigInit]
  repeat (first | rfl | split)

theorem compareSigInit_bit {ψ : Nat} (u : AgentState ψ) :
    (compareSigInit u).bit = u.bit := by
  simp only [compareSigInit]
  repeat (first | rfl | split)

theorem compareSigInit_path {ψ : Nat} (u : AgentState ψ) :
    (compareSigInit u).path = u.path := by
  simp only [compareSigInit]
  repeat (first | rfl | split)

theorem compareSigInit_path2 {ψ : Nat} (u : AgentState ψ) :
    (compareSigInit u).path2 = u.path2 := by
  simp only [compareSigInit]
  repeat (first | rfl | split)

theorem compareSigInit_path3 {ψ : Nat} (u : AgentState ψ) :
    (compareSigInit u).path3 = u.path3 := by
  simp only [compareSigInit]
  repeat (first | rfl | split)

theorem compareSigInit_leader {ψ : Nat} (u : AgentState ψ) :
    (compareSigInit u).leader = u.leader := by
  simp only [compareSigInit]
  repeat (first | rfl | split)

theorem compareSigInit_write {ψ : Nat} (u : AgentState ψ) :
    (compareSigInit u).write = u.write := by
  simp only [compareSigInit]
  repeat (first | rfl | split)

/-! ## cmpUpdatePropagate shape lemmas -/

theorem cmpUpdatePropagate_congest_zero
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlabel : l.label = ⟨0, hψ⟩)
    (hstate : l.state = MainState.congest)
    (hψ1 : ψ > 1) :
    (cmpUpdatePropagate hψ l r).1 = l ∧
      (cmpUpdatePropagate hψ l r).2.state = MainState.congest := by
  have hzero_ne_top :
      (⟨0, hψ⟩ : Fin ψ) ≠ ⟨ψ - 1, by omega⟩ := by
    intro h
    have hv : 0 = ψ - 1 := congrArg Fin.val h
    omega
  have hnotTop :
      l.label ≠ (⟨ψ - 1, by omega⟩ : Fin ψ) := by
    intro h
    exact hzero_ne_top (hlabel.symm.trans h)
  have hnotLock : l.state ≠ MainState.lock := by
    intro h
    have hbad : MainState.congest = MainState.lock :=
      hstate.symm.trans h
    cases hbad
  simp only [cmpUpdatePropagate]
  split
  · rename_i h
    exact (hnotTop h.1).elim
  · split
    · rename_i h
      exact (hnotLock h.2).elim
    · split
      · rename_i h
        exact (hnotTop h.1).elim
      · split
        · exact ⟨rfl, hstate⟩
        · rename_i h
          exact (h (Or.inl hstate)).elim

/-- The requested range without `.compare1` is false.  This is the strongest
simple output-range statement under exactly the supplied hypotheses. -/
theorem cmpUpdatePropagate_top
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hlabel : l.label = ⟨ψ - 1, by omega⟩)
    (hOK : StateOK r.state) :
    (cmpUpdatePropagate hψ l r).1.state = l.state ∧
      ((cmpUpdatePropagate hψ l r).2.state = MainState.lock ∨
       (cmpUpdatePropagate hψ l r).2.state = MainState.compare1 ∨
       (cmpUpdatePropagate hψ l r).2.state = r.state) := by
  have hnotCompare1 : r.state ≠ MainState.compare1 :=
    hOK.2.2.2.1
  have hnotCompare2 : r.state ≠ MainState.compare2 :=
    hOK.2.2.2.2
  simp only [cmpUpdatePropagate]
  split
  · exact ⟨rfl, Or.inl rfl⟩
  · rename_i hfirst
    split
    · exact ⟨rfl, Or.inr (Or.inl rfl)⟩
    · rename_i hsecond
      split
      · rename_i hthird
        exact (hnotCompare1 hthird.2).elim
      · rename_i hthird
        split
        · rename_i hfourth
          have hnotCongest : l.state ≠ MainState.congest := by
            intro hcongest
            exact hfirst ⟨hlabel, hcongest⟩
          have hlock : l.state = MainState.lock := by
            rcases hfourth with hcongest | hlock
            · exact (hnotCongest hcongest).elim
            · exact hlock
          exact ⟨rfl, Or.inl hlock⟩
        · rename_i hfourth
          split
          · rename_i hfifth
            rcases hfifth with hcompare1 | hcompare2
            · exact (hnotCompare1 hcompare1).elim
            · exact (hnotCompare2 hcompare2).elim
          · exact ⟨rfl, Or.inr (Or.inr rfl)⟩

/-! ## cmpUpdatePropagate frame lemmas -/

theorem cmpUpdatePropagate_label
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).1.label = l.label ∧
      (cmpUpdatePropagate hψ l r).2.label = r.label := by
  simp only [cmpUpdatePropagate]
  repeat (first | (exact ⟨rfl, rfl⟩) | split)

theorem cmpUpdatePropagate_bit
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).1.bit = l.bit ∧
      (cmpUpdatePropagate hψ l r).2.bit = r.bit := by
  simp only [cmpUpdatePropagate]
  repeat (first | (exact ⟨rfl, rfl⟩) | split)

theorem cmpUpdatePropagate_path
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).1.path = l.path ∧
      (cmpUpdatePropagate hψ l r).2.path = r.path := by
  simp only [cmpUpdatePropagate]
  repeat (first | (exact ⟨rfl, rfl⟩) | split)

theorem cmpUpdatePropagate_path2
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).1.path2 = l.path2 ∧
      (cmpUpdatePropagate hψ l r).2.path2 = r.path2 := by
  simp only [cmpUpdatePropagate]
  repeat (first | (exact ⟨rfl, rfl⟩) | split)

theorem cmpUpdatePropagate_path3
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).1.path3 = l.path3 ∧
      (cmpUpdatePropagate hψ l r).2.path3 = r.path3 := by
  simp only [cmpUpdatePropagate]
  repeat (first | (exact ⟨rfl, rfl⟩) | split)

theorem cmpUpdatePropagate_leader
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).1.leader = l.leader ∧
      (cmpUpdatePropagate hψ l r).2.leader = r.leader := by
  simp only [cmpUpdatePropagate]
  repeat (first | (exact ⟨rfl, rfl⟩) | split)

theorem cmpUpdatePropagate_write
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpUpdatePropagate hψ l r).1.write = l.write ∧
      (cmpUpdatePropagate hψ l r).2.write = r.write := by
  simp only [cmpUpdatePropagate]
  repeat (first | (exact ⟨rfl, rfl⟩) | split)

/-! ## cmpUpdateSetPath2 -/

theorem cmpUpdateSetPath2_ne
    {ψ : Nat} (hψ : ψ > 0) (l : AgentState ψ)
    (hstate : l.state ≠ MainState.compare2) :
    cmpUpdateSetPath2 hψ l = l := by
  cases hpath : l.path with
  | bot =>
      simp only [cmpUpdateSetPath2, hpath]
  | some pathLabel pathBit =>
      simp only [cmpUpdateSetPath2, hpath]
      split
      · rename_i hguard
        exact (hstate hguard.2).elim
      · rfl

/-! ## COMPARE_BIT helpers on the immortal action-5 token -/

theorem compareBitUpdateR_pos1
    {ψ : Nat} (hψ : ψ > 0) (r : AgentState ψ)
    (hpath2 : r.path2 = none ∨ r.path2 = some A5) :
    compareBitUpdateR hψ r = r := by
  rcases hpath2 with hnone | hA5
  · simp only [compareBitUpdateR, hnone]
  · have hpos : A5.position ≠ 0 := by
      decide
    simp only [compareBitUpdateR, hA5, if_neg hpos]

theorem compareBitUpdateL_notA2
    {ψ : Nat} (hψ : ψ > 0) (l : AgentState ψ)
    (hpath2 : l.path2 = none ∨ l.path2 = some A5) :
    compareBitUpdateL hψ l = l := by
  rcases hpath2 with hnone | hA5
  · simp only [compareBitUpdateL, hnone]
  · cases hpath : l.path with
    | bot =>
        simp only [compareBitUpdateL, hA5, hpath]
    | some pathLabel pathBit =>
        have haction : A5.action ≠ 2 := by
          decide
        have hguard :
            ¬ (A5.action = 2 ∧ A5.position = 0) := by
          intro h
          exact haction h.1
        simp only [compareBitUpdateL, hA5, hpath, if_neg hguard]

end ZZT0Compare

#print axioms ZZT0Compare.compareSigInit_state
#print axioms ZZT0Compare.compareSigInit_label
#print axioms ZZT0Compare.compareSigInit_bit
#print axioms ZZT0Compare.compareSigInit_path
#print axioms ZZT0Compare.compareSigInit_path2
#print axioms ZZT0Compare.compareSigInit_path3
#print axioms ZZT0Compare.compareSigInit_leader
#print axioms ZZT0Compare.compareSigInit_write
#print axioms ZZT0Compare.cmpUpdatePropagate_congest_zero
#print axioms ZZT0Compare.cmpUpdatePropagate_top
#print axioms ZZT0Compare.cmpUpdatePropagate_label
#print axioms ZZT0Compare.cmpUpdatePropagate_bit
#print axioms ZZT0Compare.cmpUpdatePropagate_path
#print axioms ZZT0Compare.cmpUpdatePropagate_path2
#print axioms ZZT0Compare.cmpUpdatePropagate_path3
#print axioms ZZT0Compare.cmpUpdatePropagate_leader
#print axioms ZZT0Compare.cmpUpdatePropagate_write
#print axioms ZZT0Compare.cmpUpdateSetPath2_ne
#print axioms ZZT0Compare.compareBitUpdateR_pos1
#print axioms ZZT0Compare.compareBitUpdateL_notA2
