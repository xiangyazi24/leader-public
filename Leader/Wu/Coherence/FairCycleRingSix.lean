import Leader.Wu.Coherence.Controller

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace ZZV31CycleWitness

private theorem h3 : 0 < 3 := by omega
private theorem h23 : 2 ≤ 3 := by omega
private def ring6 : DirectedRing 6 := ⟨by omega⟩

/-- A complete version of the private literal family used in
`FinalCandidateNormalizedShadow`. -/
private def cleanPhys (lab : Fin 3) : R2.Cell 3 3 48 :=
  let b : BoundedAgentState 3 3 :=
    { leader := false
      probe := false
      phase := false
      bit := false
      wait := true
      state := .none
      path := .bot
      reset := false
      carry := false
      count := 0
      label := lab
      h_field := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      signal_B := 0
      bullet := 0
      shield := false
      write_state := .none
      write := .none
      last := false
      last_set := false
      last_unset := false
      b_carry := false
      gen_ws := false
      ws_echo := false
      signal_ws := false }
  ⟨⟨⟨b, false⟩,
      PPLLExpiringComparisonRepair.freshStall 48⟩, 0⟩

/-- All `clearMain` calls occurring in the cycle are physically idempotent
on the chosen literal family. -/
private theorem cleanPhys_clearMain (lab : Fin 3) :
    R2Coherence.clearMainPhys (cleanPhys lab) = cleanPhys lab := by
  rfl

private def labAt (i : Fin 6) : Fin 3 :=
  ⟨i.val % 3, Nat.mod_lt _ h3⟩

private def ctlS : R2CoherenceV31.ControlV3 :=
  ⟨.sealed, .none⟩
private def ctlR : R2CoherenceV31.ControlV3 :=
  ⟨.releasing, .none⟩
private def ctlRr : R2CoherenceV31.ControlV3 :=
  ⟨.releasing, .release⟩
private def ctlRs : R2CoherenceV31.ControlV3 :=
  ⟨.releasing, .scrubL⟩
private def ctlC : R2CoherenceV31.ControlV3 :=
  ⟨.closing, .none⟩
private def ctlCq : R2CoherenceV31.ControlV3 :=
  ⟨.closing, .seek⟩
private def ctlCw : R2CoherenceV31.ControlV3 :=
  ⟨.closing, .sweep⟩
private def ctlCc : R2CoherenceV31.ControlV3 :=
  ⟨.closing, .commit⟩

private def cycleCtl (i : Fin 6) : R2CoherenceV31.ControlV3 :=
  if i.val % 3 = 2 then ctlRs else ctlR

private def cycleC : R2CoherenceV31.FC 6 3 3 48 :=
  fun i => ⟨cleanPhys (labAt i), cycleCtl i⟩

/-- Concrete six-position control selector. The `_` case is position 5;
other values are impossible for `Fin 6`. -/
private def ctlAt6
    (c0 c1 c2 c3 c4 c5 : R2CoherenceV31.ControlV3)
    (i : Fin 6) : R2CoherenceV31.ControlV3 :=
  match i.val with
  | 0 => c0
  | 1 => c1
  | 2 => c2
  | 3 => c3
  | 4 => c4
  | _ => c5

private def cfg6
    (c0 c1 c2 c3 c4 c5 : R2CoherenceV31.ControlV3) :
    R2CoherenceV31.FC 6 3 3 48 :=
  fun i => ⟨cleanPhys (labAt i), ctlAt6 c0 c1 c2 c3 c4 c5 i⟩

/-- Core-only finite case split, replacing unavailable `fin_cases`. -/
private theorem fin6_cases (i : Fin 6) :
    i = (0 : Fin 6) ∨ i = 1 ∨ i = 2 ∨
      i = 3 ∨ i = 4 ∨ i = 5 := by
  have hi : i.val < 6 := i.isLt
  have hv :
      i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
        i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by
    omega
  rcases hv with h | h | h | h | h | h
  · left
    apply Fin.ext
    omega
  · right; left
    apply Fin.ext
    omega
  · right; right; left
    apply Fin.ext
    omega
  · right; right; right; left
    apply Fin.ext
    omega
  · right; right; right; right; left
    apply Fin.ext
    omega
  · right; right; right; right; right
    apply Fin.ext
    omega

/-- Extensionality specialized to the concrete 6-ring. -/
private theorem cfg_ext6
    {C D : R2CoherenceV31.FC 6 3 3 48}
    (h0 : C 0 = D 0) (h1 : C 1 = D 1)
    (h2 : C 2 = D 2) (h3' : C 3 = D 3)
    (h4 : C 4 = D 4) (h5 : C 5 = D 5) : C = D := by
  funext i
  rcases fin6_cases i with h | h | h | h | h | h
  · subst i; exact h0
  · subst i; exact h1
  · subst i; exact h2
  · subst i; exact h3'
  · subst i; exact h4
  · subst i; exact h5

/-- Canonical expanded form of the requested modular initial configuration. -/
private def baseC : R2CoherenceV31.FC 6 3 3 48 :=
  cfg6 ctlR ctlR ctlRs ctlR ctlR ctlRs

private theorem cycleC_eq_baseC : cycleC = baseC := by
  apply cfg_ext6 <;> rfl

/-! First 3-cell group: labels 0,1,2. -/
private def a1 := cfg6 ctlR  ctlCq ctlRs ctlR ctlR ctlRs
private def a2 := cfg6 ctlCw ctlC  ctlRs ctlR ctlR ctlRs
private def a3 := cfg6 ctlC  ctlCw ctlRs ctlR ctlR ctlRs
private def a4 := cfg6 ctlC  ctlC  ctlCc ctlR ctlR ctlRs
private def a5 := cfg6 ctlC  ctlCc ctlS  ctlR ctlR ctlRs
private def a6 := cfg6 ctlS  ctlS  ctlS   ctlR ctlR ctlRs
private def a7 := cfg6 ctlRr ctlS  ctlS   ctlR ctlR ctlRs
private def a8 := cfg6 ctlR  ctlRr ctlS   ctlR ctlR ctlRs

/-! Second 3-cell group: labels 0,1,2 at positions 3,4,5. -/
private def b1 := cfg6 ctlR ctlR ctlRs ctlR  ctlCq ctlRs
private def b2 := cfg6 ctlR ctlR ctlRs ctlCw ctlC  ctlRs
private def b3 := cfg6 ctlR ctlR ctlRs ctlC  ctlCw ctlRs
private def b4 := cfg6 ctlR ctlR ctlRs ctlC  ctlC  ctlCc
private def b5 := cfg6 ctlR ctlR ctlRs ctlC  ctlCc ctlS
private def b6 := cfg6 ctlR ctlR ctlRs ctlS  ctlS  ctlS
private def b7 := cfg6 ctlR ctlR ctlRs ctlRr ctlS  ctlS
private def b8 := cfg6 ctlR ctlR ctlRs ctlR  ctlRr ctlS

/-! Boundary services.  The scrub token is on the LEFT endpoint, so neither
`rowV3`'s right-scrub guard nor `ordinaryStageV3`'s token-free guard fires. -/
private theorem step_boundary2 :
    R2CoherenceV31.stepV3 h3 h23 ring6 baseC 2 = baseC := by
  apply cfg_ext6 <;> rfl

private theorem step_boundary5 :
    R2CoherenceV31.stepV3 h3 h23 ring6 baseC 5 = baseC := by
  apply cfg_ext6 <;> rfl

/-! Nine letters on group 0. -/
private theorem step_a0 :
    R2CoherenceV31.stepV3 h3 h23 ring6 baseC 0 = a1 := by
  apply cfg_ext6 <;> rfl
private theorem step_a1 :
    R2CoherenceV31.stepV3 h3 h23 ring6 a1 0 = a2 := by
  apply cfg_ext6 <;> rfl
private theorem step_a2 :
    R2CoherenceV31.stepV3 h3 h23 ring6 a2 0 = a3 := by
  apply cfg_ext6 <;> rfl
private theorem step_a3 :
    R2CoherenceV31.stepV3 h3 h23 ring6 a3 1 = a4 := by
  apply cfg_ext6 <;> rfl
private theorem step_a4 :
    R2CoherenceV31.stepV3 h3 h23 ring6 a4 1 = a5 := by
  apply cfg_ext6 <;> rfl
private theorem step_a5 :
    R2CoherenceV31.stepV3 h3 h23 ring6 a5 0 = a6 := by
  apply cfg_ext6 <;> rfl
private theorem step_a6 :
    R2CoherenceV31.stepV3 h3 h23 ring6 a6 0 = a7 := by
  apply cfg_ext6 <;> rfl
private theorem step_a7 :
    R2CoherenceV31.stepV3 h3 h23 ring6 a7 0 = a8 := by
  apply cfg_ext6 <;> rfl
private theorem step_a8 :
    R2CoherenceV31.stepV3 h3 h23 ring6 a8 1 = baseC := by
  apply cfg_ext6 <;> rfl

/-! Nine letters on group 1. -/
private theorem step_b0 :
    R2CoherenceV31.stepV3 h3 h23 ring6 baseC 3 = b1 := by
  apply cfg_ext6 <;> rfl
private theorem step_b1 :
    R2CoherenceV31.stepV3 h3 h23 ring6 b1 3 = b2 := by
  apply cfg_ext6 <;> rfl
private theorem step_b2 :
    R2CoherenceV31.stepV3 h3 h23 ring6 b2 3 = b3 := by
  apply cfg_ext6 <;> rfl
private theorem step_b3 :
    R2CoherenceV31.stepV3 h3 h23 ring6 b3 4 = b4 := by
  apply cfg_ext6 <;> rfl
private theorem step_b4 :
    R2CoherenceV31.stepV3 h3 h23 ring6 b4 4 = b5 := by
  apply cfg_ext6 <;> rfl
private theorem step_b5 :
    R2CoherenceV31.stepV3 h3 h23 ring6 b5 3 = b6 := by
  apply cfg_ext6 <;> rfl
private theorem step_b6 :
    R2CoherenceV31.stepV3 h3 h23 ring6 b6 3 = b7 := by
  apply cfg_ext6 <;> rfl
private theorem step_b7 :
    R2CoherenceV31.stepV3 h3 h23 ring6 b7 3 = b8 := by
  apply cfg_ext6 <;> rfl
private theorem step_b8 :
    R2CoherenceV31.stepV3 h3 h23 ring6 b8 4 = baseC := by
  apply cfg_ext6 <;> rfl

private def fairPeriod : List (Fin 6) :=
  [2, 5] ++
    [0, 0, 0, 1, 1, 0, 0, 0, 1] ++
    [3, 3, 3, 4, 4, 3, 3, 3, 4]

/-- One fair period returns to the exact same full V3.1 configuration. -/
theorem v31_fair_cycle :
    fairPeriod.foldl (R2CoherenceV31.stepV3 h3 h23 ring6) cycleC =
      cycleC := by
  rw [cycleC_eq_baseC]
  simp [fairPeriod, List.foldl,
    step_boundary2, step_boundary5,
    step_a0, step_a1, step_a2, step_a3, step_a4,
    step_a5, step_a6, step_a7, step_a8,
    step_b0, step_b1, step_b2, step_b3, step_b4,
    step_b5, step_b6, step_b7, step_b8]

#print axioms ZZV31CycleWitness.v31_fair_cycle

end ZZV31CycleWitness
