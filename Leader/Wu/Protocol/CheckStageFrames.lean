import Leader.Wu.Protocol.Algorithm

set_option autoImplicit false
set_option Elab.async false

namespace ZZT0CheckSig

open PPLL

def pathBit0 : PathInfo → Bool
  | .bot => true
  | .some _ b => b == 0

def StateOK (s : MainState) : Prop :=
  s ≠ .larger ∧ s ≠ .less ∧ s ≠ .toss ∧
    s ≠ .compare1 ∧ s ≠ .compare2

/-! ## CHECK-ready preparation -/

theorem checkSigSetReady_depart
    {ψ : Nat} (u : AgentState ψ)
    (hstate : u.state = .depart) :
    checkSigSetReady u = u := by
  cases hpath : u.path with
  | bot =>
      simp only [checkSigSetReady, hpath]
  | some label bit =>
      simp only [checkSigSetReady, hpath]
      split
      · rename_i hguard
        exact (hguard.2.1 hstate).elim
      · rfl

theorem checkSigSetReady_state
    {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetReady u).state = .CHECK_ready ∨
      (checkSigSetReady u).state = u.state := by
  cases hpath : u.path with
  | bot =>
      have hfixed : checkSigSetReady u = u := by
        simp only [checkSigSetReady, hpath]
      exact Or.inr
        (congrArg (fun v : AgentState ψ => v.state) hfixed)
  | some label bit =>
      simp only [checkSigSetReady, hpath]
      split
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem checkSigSetReady_label
    {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetReady u).label = u.label := by
  simp only [checkSigSetReady]
  split <;> repeat (first | rfl | split)

theorem checkSigSetReady_bit
    {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetReady u).bit = u.bit := by
  simp only [checkSigSetReady]
  split <;> repeat (first | rfl | split)

theorem checkSigSetReady_path
    {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetReady u).path = u.path := by
  simp only [checkSigSetReady]
  split <;> repeat (first | rfl | split)

theorem checkSigSetReady_path2
    {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetReady u).path2 = u.path2 := by
  simp only [checkSigSetReady]
  split <;> repeat (first | rfl | split)

theorem checkSigSetReady_path3
    {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetReady u).path3 = u.path3 := by
  simp only [checkSigSetReady]
  split <;> repeat (first | rfl | split)

theorem checkSigSetReady_leader
    {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetReady u).leader = u.leader := by
  simp only [checkSigSetReady]
  split <;> repeat (first | rfl | split)

theorem checkSigSetReady_write
    {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetReady u).write = u.write := by
  simp only [checkSigSetReady]
  split <;> repeat (first | rfl | split)

/-! ## Left CHECK -/

theorem checkSigCheckL_bit0
    {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ)
    (hbit : u.bit = false)
    (hpath0 : pathBit0 u.path = true) :
    (checkSigCheckL hψ u).state = .equal ∨
      (checkSigCheckL hψ u).state = u.state := by
  cases hpath : u.path with
  | bot =>
      have hfixed : checkSigCheckL hψ u = u := by
        simp only [checkSigCheckL, hpath]
      exact Or.inr
        (congrArg (fun v : AgentState ψ => v.state) hfixed)
  | some label pathBit =>
      cases label with
      | zero =>
          cases pathBit with
          | zero =>
              simp only [checkSigCheckL, hpath]
              split
              · apply Or.inl
                rw [hbit]
                rfl
              · exact Or.inr rfl
          | succ pathBit =>
              rw [hpath] at hpath0
              change false = true at hpath0
              cases hpath0
      | succ label =>
          have hfixed : checkSigCheckL hψ u = u := by
            simp only [checkSigCheckL, hpath]
          exact Or.inr
            (congrArg (fun v : AgentState ψ => v.state) hfixed)

/-! ## Right CHECK -/

theorem checkSigCheckR_top
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (htop : l.label.val = ψ - 1) :
    checkSigCheckR hψ l r = r := by
  cases hpath : r.path with
  | bot =>
      simp only [checkSigCheckR, hpath]
  | some pathLabel pathBit =>
      simp only [checkSigCheckR, hpath]
      split
      · rename_i hguard
        have hlt : l.label.val < l.label.val := by
          calc
            l.label.val < ψ - 1 := hguard.1
            _ = l.label.val := htop.symm
        exact (Nat.lt_irrefl _ hlt).elim
      · rfl

theorem checkSigCheckR_depart
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hstate : r.state = .depart) :
    checkSigCheckR hψ l r = r := by
  cases hpath : r.path with
  | bot =>
      simp only [checkSigCheckR, hpath]
  | some pathLabel pathBit =>
      simp only [checkSigCheckR, hpath]
      split
      · split
        · rename_i hready
          have hbad : MainState.depart = MainState.CHECK_ready :=
            hstate.symm.trans hready
          cases hbad
        · rfl
      · rfl

/-! ## CHECK result and leader setters -/

theorem checkSigSetResult_ok
    {ψ : Nat} (u : AgentState ψ)
    (hok : StateOK u.state) :
    checkSigSetResult u = u := by
  simp only [checkSigSetResult, hok.1, hok.2.1, if_false, ite_false, reduceIte]

theorem checkSigSetLeader_ne
    {ψ : Nat} (hψ : ψ > 0) (r : AgentState ψ)
    (hstate : r.state ≠ .equal) :
    checkSigSetLeader hψ r = r := by
  simp only [checkSigSetLeader]
  split
  · rename_i hguard
    exact (hstate hguard.2).elim
  · rfl

theorem checkSigSetLeader_zero
    {ψ : Nat} (hψ : ψ > 0) (r : AgentState ψ)
    (hzero : r.label = ⟨0, hψ⟩)
    (hgt : ψ > 1) :
    checkSigSetLeader hψ r = r := by
  simp only [checkSigSetLeader]
  split
  · rename_i hguard
    have hval : (0 : Nat) = ψ - 1 := by
      exact congrArg (fun z : Fin ψ => z.val)
        (hzero.symm.trans hguard.1)
    omega
  · rfl

end ZZT0CheckSig

#print axioms ZZT0CheckSig.checkSigSetReady_depart
#print axioms ZZT0CheckSig.checkSigSetReady_state
#print axioms ZZT0CheckSig.checkSigSetReady_label
#print axioms ZZT0CheckSig.checkSigSetReady_bit
#print axioms ZZT0CheckSig.checkSigSetReady_path
#print axioms ZZT0CheckSig.checkSigSetReady_path2
#print axioms ZZT0CheckSig.checkSigSetReady_path3
#print axioms ZZT0CheckSig.checkSigSetReady_leader
#print axioms ZZT0CheckSig.checkSigSetReady_write
#print axioms ZZT0CheckSig.checkSigCheckL_bit0
#print axioms ZZT0CheckSig.checkSigCheckR_top
#print axioms ZZT0CheckSig.checkSigCheckR_depart
#print axioms ZZT0CheckSig.checkSigSetResult_ok
#print axioms ZZT0CheckSig.checkSigSetLeader_ne
#print axioms ZZT0CheckSig.checkSigSetLeader_zero
