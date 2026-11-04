import Leader.Wu.Protocol.WaitStaged

set_option autoImplicit false
set_option Elab.async false

namespace ZZT1GenSig

open PPLL
open ZZWaitStaged

/-! ## Matcher-free stages for Algorithm 4 -/

/-- GENSIG stage 1: start production at an eligible label-zero initiator. -/
def genSigStart {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  ((if l.leader = false ∧ l.label = ⟨0, hψ⟩ ∧
       l.wait = false ∧ l.path = .bot then
      { l with state := .produce }
    else l),
   r)

/-- GENSIG stage 2: propagate the production state to the responder. -/
def genSigPropagate {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  (l,
   if r.label ≠ ⟨0, hψ⟩ ∧ l.state = .produce ∧
      r.path = .bot then
     { r with state := .produce }
   else r)

/-- GENSIG stage 3: the terminal responder emits its own sub-signal. -/
def genSigEmitR {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  (l,
   if r.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .produce then
     { r with state := .done,
              path := .some r.label.val (if r.bit then 1 else 0) }
   else r)

/-- GENSIG stage 4: the initiator emits and the responder departs. -/
def genSigEmitL {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.label ≠ ⟨ψ - 1, by omega⟩ ∧ l.state = .produce ∧
     r.state = .done then
    ({ l with state := .done,
              path := .some l.label.val (if l.bit then 1 else 0) },
     { r with state := .depart })
  else
    (l, r)

/-- GENSIG stage 5: finish at label zero and re-arm WAIT. -/
def genSigFinish {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  ((if l.label = ⟨0, hψ⟩ ∧ l.state = .done then
      { l with state := .depart, wait := true }
    else l),
   r)

/-- Matcher-free staged presentation of Algorithm 4. -/
def genSigStaged {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q0 := wait hψ κ l r
  let q1 := genSigStart hψ q0.1 q0.2
  let q2 := genSigPropagate hψ q1.1 q1.2
  let q3 := genSigEmitR hψ q2.1 q2.2
  let q4 := genSigEmitL hψ q3.1 q3.2
  genSigFinish hψ q4.1 q4.2

/-- The staged presentation is definitionally equal to literal GENSIG. -/
theorem genSig_eq_staged {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    genSig hψ κ l r = genSigStaged hψ κ l r := by
  rfl

/-! ## Exact eight-field effects of the direct pair stages -/

theorem genSigStart_proj {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (trapProj (genSigStart hψ l r).1,
     trapProj (genSigStart hψ l r).2) =
      if l.leader = false ∧ l.label = ⟨0, hψ⟩ ∧
         l.wait = false ∧ l.path = .bot then
        (trapProj ({ l with state := .produce } : AgentState ψ),
         trapProj r)
      else
        (trapProj l, trapProj r) := by
  simp only [genSigStart]
  repeat (first | rfl | split)

theorem genSigPropagate_proj {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (trapProj (genSigPropagate hψ l r).1,
     trapProj (genSigPropagate hψ l r).2) =
      if r.label ≠ ⟨0, hψ⟩ ∧ l.state = .produce ∧
         r.path = .bot then
        (trapProj l,
         trapProj ({ r with state := .produce } : AgentState ψ))
      else
        (trapProj l, trapProj r) := by
  simp only [genSigPropagate]
  repeat (first | rfl | split)

theorem genSigEmitR_proj {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (trapProj (genSigEmitR hψ l r).1,
     trapProj (genSigEmitR hψ l r).2) =
      if r.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .produce then
        (trapProj l,
         trapProj
           ({ r with state := .done,
                     path := .some r.label.val
                       (if r.bit then 1 else 0) } : AgentState ψ))
      else
        (trapProj l, trapProj r) := by
  simp only [genSigEmitR]
  repeat (first | rfl | split)

theorem genSigEmitL_proj {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (trapProj (genSigEmitL hψ l r).1,
     trapProj (genSigEmitL hψ l r).2) =
      if l.label ≠ ⟨ψ - 1, by omega⟩ ∧ l.state = .produce ∧
         r.state = .done then
        (trapProj
           ({ l with state := .done,
                     path := .some l.label.val
                       (if l.bit then 1 else 0) } : AgentState ψ),
         trapProj ({ r with state := .depart } : AgentState ψ))
      else
        (trapProj l, trapProj r) := by
  simp only [genSigEmitL]
  repeat (first | rfl | split)

theorem genSigFinish_proj {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (trapProj (genSigFinish hψ l r).1,
     trapProj (genSigFinish hψ l r).2) =
      if l.label = ⟨0, hψ⟩ ∧ l.state = .done then
        (trapProj
           ({ l with state := .depart, wait := true } : AgentState ψ),
         trapProj r)
      else
        (trapProj l, trapProj r) := by
  simp only [genSigFinish]
  repeat (first | rfl | split)

/-! ## Fields framed by GENSIG -/

/-- Exactly the six requested fields that every post-WAIT GENSIG stage frames. -/
abbrev genSigFrameProj {ψ : Nat} (u : AgentState ψ) :=
  (u.leader, u.label, u.bit, u.path2, u.path3, u.write)

/-- Imported WAIT facts, collected once in the GENSIG frame projection. -/
theorem wait_genSigFrame {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (genSigFrameProj (wait hψ κ l r).1,
     genSigFrameProj (wait hψ κ l r).2) =
      (genSigFrameProj l, genSigFrameProj r) := by
  have hLeader := ZZWaitStaged.wait_leader hψ κ l r
  have hLabel := ZZWaitStaged.wait_label hψ κ l r
  have hBit := ZZWaitStaged.wait_bit hψ κ l r
  have hPath2 := ZZWaitStaged.wait_path2 hψ κ l r
  have hPath3 := ZZWaitStaged.wait_path3 hψ κ l r
  have hWrite := ZZWaitStaged.wait_write hψ κ l r
  apply Prod.ext
  · apply Prod.ext
    · exact hLeader.1
    · apply Prod.ext
      · exact hLabel.1
      · apply Prod.ext
        · exact hBit.1
        · apply Prod.ext
          · exact hPath2.1
          · apply Prod.ext
            · exact hPath3.1
            · exact hWrite.1
  · apply Prod.ext
    · exact hLeader.2
    · apply Prod.ext
      · exact hLabel.2
      · apply Prod.ext
        · exact hBit.2
        · apply Prod.ext
          · exact hPath2.2
          · apply Prod.ext
            · exact hPath3.2
            · exact hWrite.2

theorem genSigStart_frame {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (genSigFrameProj (genSigStart hψ l r).1,
     genSigFrameProj (genSigStart hψ l r).2) =
      (genSigFrameProj l, genSigFrameProj r) := by
  simp only [genSigStart]
  repeat (first | rfl | split)

theorem genSigPropagate_frame {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (genSigFrameProj (genSigPropagate hψ l r).1,
     genSigFrameProj (genSigPropagate hψ l r).2) =
      (genSigFrameProj l, genSigFrameProj r) := by
  simp only [genSigPropagate]
  repeat (first | rfl | split)

theorem genSigEmitR_frame {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (genSigFrameProj (genSigEmitR hψ l r).1,
     genSigFrameProj (genSigEmitR hψ l r).2) =
      (genSigFrameProj l, genSigFrameProj r) := by
  simp only [genSigEmitR]
  repeat (first | rfl | split)

theorem genSigEmitL_frame {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (genSigFrameProj (genSigEmitL hψ l r).1,
     genSigFrameProj (genSigEmitL hψ l r).2) =
      (genSigFrameProj l, genSigFrameProj r) := by
  simp only [genSigEmitL]
  repeat (first | rfl | split)

theorem genSigFinish_frame {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (genSigFrameProj (genSigFinish hψ l r).1,
     genSigFrameProj (genSigFinish hψ l r).2) =
      (genSigFrameProj l, genSigFrameProj r) := by
  simp only [genSigFinish]
  repeat (first | rfl | split)

/-- GENSIG frames leader, label, bit, path2, path3 and write on both ends. -/
theorem genSig_frame {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    let q := genSig hψ κ l r
    (genSigFrameProj q.1, genSigFrameProj q.2) =
      (genSigFrameProj l, genSigFrameProj r) := by
  dsimp only
  rw [genSig_eq_staged]
  let q0 := wait hψ κ l r
  let q1 := genSigStart hψ q0.1 q0.2
  let q2 := genSigPropagate hψ q1.1 q1.2
  let q3 := genSigEmitR hψ q2.1 q2.2
  let q4 := genSigEmitL hψ q3.1 q3.2
  let q5 := genSigFinish hψ q4.1 q4.2
  have h0 := wait_genSigFrame hψ κ l r
  have h1 := genSigStart_frame hψ q0.1 q0.2
  have h2 := genSigPropagate_frame hψ q1.1 q1.2
  have h3 := genSigEmitR_frame hψ q2.1 q2.2
  have h4 := genSigEmitL_frame hψ q3.1 q3.2
  have h5 := genSigFinish_frame hψ q4.1 q4.2
  change (genSigFrameProj q5.1, genSigFrameProj q5.2) =
    (genSigFrameProj l, genSigFrameProj r)
  exact h5.trans (h4.trans (h3.trans (h2.trans (h1.trans h0))))

theorem genSig_leader {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    let q := genSig hψ κ l r
    q.1.leader = l.leader ∧ q.2.leader = r.leader := by
  have h := genSig_frame hψ κ l r
  exact ⟨congrArg (fun z => z.1.1) h,
    congrArg (fun z => z.2.1) h⟩

theorem genSig_label {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    let q := genSig hψ κ l r
    q.1.label = l.label ∧ q.2.label = r.label := by
  have h := genSig_frame hψ κ l r
  exact ⟨congrArg (fun z => z.1.2.1) h,
    congrArg (fun z => z.2.2.1) h⟩

theorem genSig_bit {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    let q := genSig hψ κ l r
    q.1.bit = l.bit ∧ q.2.bit = r.bit := by
  have h := genSig_frame hψ κ l r
  exact ⟨congrArg (fun z => z.1.2.2.1) h,
    congrArg (fun z => z.2.2.2.1) h⟩

theorem genSig_path2 {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    let q := genSig hψ κ l r
    q.1.path2 = l.path2 ∧ q.2.path2 = r.path2 := by
  have h := genSig_frame hψ κ l r
  exact ⟨congrArg (fun z => z.1.2.2.2.1) h,
    congrArg (fun z => z.2.2.2.2.1) h⟩

theorem genSig_path3 {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    let q := genSig hψ κ l r
    q.1.path3 = l.path3 ∧ q.2.path3 = r.path3 := by
  have h := genSig_frame hψ κ l r
  exact ⟨congrArg (fun z => z.1.2.2.2.2.1) h,
    congrArg (fun z => z.2.2.2.2.2.1) h⟩

theorem genSig_write {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    let q := genSig hψ κ l r
    q.1.write = l.write ∧ q.2.write = r.write := by
  have h := genSig_frame hψ κ l r
  exact ⟨congrArg (fun z => z.1.2.2.2.2.2) h,
    congrArg (fun z => z.2.2.2.2.2.2) h⟩

/-! ## Exact state range -/

abbrev genStateFrom (before after : MainState) : Prop :=
  after = .produce ∨ after = .done ∨ after = .depart ∨ after = before

theorem genStateFrom_refl (s : MainState) : genStateFrom s s := by
  exact Or.inr (Or.inr (Or.inr rfl))

theorem genStateFrom_trans {s0 s1 s2 : MainState}
    (h01 : genStateFrom s0 s1) (h12 : genStateFrom s1 s2) :
    genStateFrom s0 s2 := by
  rcases h12 with hProduce | hDone | hDepart | hSame
  · exact Or.inl hProduce
  · exact Or.inr (Or.inl hDone)
  · exact Or.inr (Or.inr (Or.inl hDepart))
  · rw [hSame]
    exact h01

theorem wait_genSigState {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    genStateFrom l.state (wait hψ κ l r).1.state ∧
      genStateFrom r.state (wait hψ κ l r).2.state := by
  have h := ZZWaitStaged.wait_state hψ κ l r
  constructor
  · rw [h.1]
    exact genStateFrom_refl _
  · rw [h.2]
    exact genStateFrom_refl _

theorem genSigStart_state {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    genStateFrom l.state (genSigStart hψ l r).1.state ∧
      genStateFrom r.state (genSigStart hψ l r).2.state := by
  simp only [genSigStart]
  split
  · exact ⟨Or.inl rfl, genStateFrom_refl _⟩
  · exact ⟨genStateFrom_refl _, genStateFrom_refl _⟩

theorem genSigPropagate_state {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    genStateFrom l.state (genSigPropagate hψ l r).1.state ∧
      genStateFrom r.state (genSigPropagate hψ l r).2.state := by
  simp only [genSigPropagate]
  split
  · exact ⟨genStateFrom_refl _, Or.inl rfl⟩
  · exact ⟨genStateFrom_refl _, genStateFrom_refl _⟩

theorem genSigEmitR_state {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    genStateFrom l.state (genSigEmitR hψ l r).1.state ∧
      genStateFrom r.state (genSigEmitR hψ l r).2.state := by
  simp only [genSigEmitR]
  split
  · exact ⟨genStateFrom_refl _, Or.inr (Or.inl rfl)⟩
  · exact ⟨genStateFrom_refl _, genStateFrom_refl _⟩

theorem genSigEmitL_state {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    genStateFrom l.state (genSigEmitL hψ l r).1.state ∧
      genStateFrom r.state (genSigEmitL hψ l r).2.state := by
  simp only [genSigEmitL]
  split
  · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨genStateFrom_refl _, genStateFrom_refl _⟩

theorem genSigFinish_state {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    genStateFrom l.state (genSigFinish hψ l r).1.state ∧
      genStateFrom r.state (genSigFinish hψ l r).2.state := by
  simp only [genSigFinish]
  split
  · exact ⟨Or.inr (Or.inr (Or.inl rfl)), genStateFrom_refl _⟩
  · exact ⟨genStateFrom_refl _, genStateFrom_refl _⟩

/-- Final GENSIG states are produce, done, depart, or the input state. -/
theorem genSig_state {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    let q := genSig hψ κ l r
    genStateFrom l.state q.1.state ∧ genStateFrom r.state q.2.state := by
  dsimp only
  rw [genSig_eq_staged]
  let q0 := wait hψ κ l r
  let q1 := genSigStart hψ q0.1 q0.2
  let q2 := genSigPropagate hψ q1.1 q1.2
  let q3 := genSigEmitR hψ q2.1 q2.2
  let q4 := genSigEmitL hψ q3.1 q3.2
  let q5 := genSigFinish hψ q4.1 q4.2
  have h0 := wait_genSigState hψ κ l r
  have h1 := genSigStart_state hψ q0.1 q0.2
  have h2 := genSigPropagate_state hψ q1.1 q1.2
  have h3 := genSigEmitR_state hψ q2.1 q2.2
  have h4 := genSigEmitL_state hψ q3.1 q3.2
  have h5 := genSigFinish_state hψ q4.1 q4.2
  have hl1 := genStateFrom_trans h0.1 h1.1
  have hr1 := genStateFrom_trans h0.2 h1.2
  have hl2 := genStateFrom_trans hl1 h2.1
  have hr2 := genStateFrom_trans hr1 h2.2
  have hl3 := genStateFrom_trans hl2 h3.1
  have hr3 := genStateFrom_trans hr2 h3.2
  have hl4 := genStateFrom_trans hl3 h4.1
  have hr4 := genStateFrom_trans hr3 h4.2
  have hl5 := genStateFrom_trans hl4 h5.1
  have hr5 := genStateFrom_trans hr4 h5.2
  change genStateFrom l.state q5.1.state ∧
    genStateFrom r.state q5.2.state
  exact ⟨hl5, hr5⟩

/-! ## Exact path range and host consistency -/

/-- An endpoint either has a freshly host-consistent path or keeps its input path. -/
abbrev genPathFrom {ψ : Nat}
    (before after : AgentState ψ) : Prop :=
  after.path =
      .some after.label.val (if after.bit then 1 else 0) ∨
    after.path = before.path

theorem genPathFrom_refl {ψ : Nat} (u : AgentState ψ) :
    genPathFrom u u := by
  exact Or.inr rfl

theorem genPathFrom_trans {ψ : Nat} {u v w : AgentState ψ}
    (hlabel : w.label = v.label) (hbit : w.bit = v.bit)
    (huv : genPathFrom u v) (hvw : genPathFrom v w) :
    genPathFrom u w := by
  rcases hvw with hNew | hSame
  · exact Or.inl hNew
  · rcases huv with hNew | hOld
    · apply Or.inl
      calc
        w.path = v.path := hSame
        _ = .some v.label.val (if v.bit then 1 else 0) := hNew
        _ = .some w.label.val (if w.bit then 1 else 0) := by
          rw [hlabel, hbit]
    · exact Or.inr (hSame.trans hOld)

theorem wait_genSigPath {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    genPathFrom l (wait hψ κ l r).1 ∧
      genPathFrom r (wait hψ κ l r).2 := by
  have h := ZZWaitStaged.wait_path hψ κ l r
  exact ⟨Or.inr h.1, Or.inr h.2⟩

theorem genSigStart_path {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    genPathFrom l (genSigStart hψ l r).1 ∧
      genPathFrom r (genSigStart hψ l r).2 := by
  simp only [genSigStart]
  split
  · exact ⟨Or.inr rfl, Or.inr rfl⟩
  · exact ⟨Or.inr rfl, Or.inr rfl⟩

theorem genSigPropagate_path {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    genPathFrom l (genSigPropagate hψ l r).1 ∧
      genPathFrom r (genSigPropagate hψ l r).2 := by
  simp only [genSigPropagate]
  split
  · exact ⟨Or.inr rfl, Or.inr rfl⟩
  · exact ⟨Or.inr rfl, Or.inr rfl⟩

theorem genSigEmitR_path {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    genPathFrom l (genSigEmitR hψ l r).1 ∧
      genPathFrom r (genSigEmitR hψ l r).2 := by
  simp only [genSigEmitR]
  split
  · exact ⟨Or.inr rfl, Or.inl rfl⟩
  · exact ⟨Or.inr rfl, Or.inr rfl⟩

theorem genSigEmitL_path {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    genPathFrom l (genSigEmitL hψ l r).1 ∧
      genPathFrom r (genSigEmitL hψ l r).2 := by
  simp only [genSigEmitL]
  split
  · exact ⟨Or.inl rfl, Or.inr rfl⟩
  · exact ⟨Or.inr rfl, Or.inr rfl⟩

theorem genSigFinish_path {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    genPathFrom l (genSigFinish hψ l r).1 ∧
      genPathFrom r (genSigFinish hψ l r).2 := by
  simp only [genSigFinish]
  split
  · exact ⟨Or.inr rfl, Or.inr rfl⟩
  · exact ⟨Or.inr rfl, Or.inr rfl⟩

/-- Each final path is either the old path or the host's own label/bit payload. -/
theorem genSig_path {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    let q := genSig hψ κ l r
    (q.1.path =
        .some q.1.label.val (if q.1.bit then 1 else 0) ∨
      q.1.path = l.path) ∧
    (q.2.path =
        .some q.2.label.val (if q.2.bit then 1 else 0) ∨
      q.2.path = r.path) := by
  dsimp only
  rw [genSig_eq_staged]
  let q0 := wait hψ κ l r
  let q1 := genSigStart hψ q0.1 q0.2
  let q2 := genSigPropagate hψ q1.1 q1.2
  let q3 := genSigEmitR hψ q2.1 q2.2
  let q4 := genSigEmitL hψ q3.1 q3.2
  let q5 := genSigFinish hψ q4.1 q4.2
  have hp0 := wait_genSigPath hψ κ l r
  have hp1 := genSigStart_path hψ q0.1 q0.2
  have hp2 := genSigPropagate_path hψ q1.1 q1.2
  have hp3 := genSigEmitR_path hψ q2.1 q2.2
  have hp4 := genSigEmitL_path hψ q3.1 q3.2
  have hp5 := genSigFinish_path hψ q4.1 q4.2
  have hf1 := genSigStart_frame hψ q0.1 q0.2
  have hf2 := genSigPropagate_frame hψ q1.1 q1.2
  have hf3 := genSigEmitR_frame hψ q2.1 q2.2
  have hf4 := genSigEmitL_frame hψ q3.1 q3.2
  have hf5 := genSigFinish_frame hψ q4.1 q4.2
  have hl1 := genPathFrom_trans
    (congrArg (fun z => z.1.2.1) hf1)
    (congrArg (fun z => z.1.2.2.1) hf1) hp0.1 hp1.1
  have hr1 := genPathFrom_trans
    (congrArg (fun z => z.2.2.1) hf1)
    (congrArg (fun z => z.2.2.2.1) hf1) hp0.2 hp1.2
  have hl2 := genPathFrom_trans
    (congrArg (fun z => z.1.2.1) hf2)
    (congrArg (fun z => z.1.2.2.1) hf2) hl1 hp2.1
  have hr2 := genPathFrom_trans
    (congrArg (fun z => z.2.2.1) hf2)
    (congrArg (fun z => z.2.2.2.1) hf2) hr1 hp2.2
  have hl3 := genPathFrom_trans
    (congrArg (fun z => z.1.2.1) hf3)
    (congrArg (fun z => z.1.2.2.1) hf3) hl2 hp3.1
  have hr3 := genPathFrom_trans
    (congrArg (fun z => z.2.2.1) hf3)
    (congrArg (fun z => z.2.2.2.1) hf3) hr2 hp3.2
  have hl4 := genPathFrom_trans
    (congrArg (fun z => z.1.2.1) hf4)
    (congrArg (fun z => z.1.2.2.1) hf4) hl3 hp4.1
  have hr4 := genPathFrom_trans
    (congrArg (fun z => z.2.2.1) hf4)
    (congrArg (fun z => z.2.2.2.1) hf4) hr3 hp4.2
  have hl5 := genPathFrom_trans
    (congrArg (fun z => z.1.2.1) hf5)
    (congrArg (fun z => z.1.2.2.1) hf5) hl4 hp5.1
  have hr5 := genPathFrom_trans
    (congrArg (fun z => z.2.2.1) hf5)
    (congrArg (fun z => z.2.2.2.1) hf5) hr4 hp5.2
  change genPathFrom l q5.1 ∧ genPathFrom r q5.2
  exact ⟨hl5, hr5⟩

/-- A path described by `genPathFrom` is inherited or payload-consistent. -/
theorem genPathFrom_payload_or_old {ψ : Nat}
    {before after : AgentState ψ} (h : genPathFrom before after) :
    ∀ pLabel pBit,
      after.path = .some pLabel pBit →
      after.path = before.path ∨
        (after.label.val = pLabel ∧
          (if after.bit then 1 else 0) = pBit) := by
  intro pLabel pBit hPath
  rcases h with hNew | hOld
  · apply Or.inr
    have hSome :
        PathInfo.some pLabel pBit =
          PathInfo.some after.label.val
            (if after.bit then 1 else 0) :=
      hPath.symm.trans hNew
    have hArgs := PathInfo.some.inj hSome
    exact ⟨hArgs.1.symm, hArgs.2.symm⟩
  · exact Or.inl hOld

/-- Globally, every final payload is either inherited or host-consistent. -/
theorem genSig_path_payload_or_old {ψ : Nat}
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    let q := genSig hψ κ l r
    (∀ pLabel pBit,
      q.1.path = .some pLabel pBit →
      q.1.path = l.path ∨
        (q.1.label.val = pLabel ∧
          (if q.1.bit then 1 else 0) = pBit)) ∧
    (∀ pLabel pBit,
      q.2.path = .some pLabel pBit →
      q.2.path = r.path ∨
        (q.2.label.val = pLabel ∧
          (if q.2.bit then 1 else 0) = pBit)) := by
  let q := genSig hψ κ l r
  have hPath : genPathFrom l q.1 ∧ genPathFrom r q.2 := by
    exact genSig_path hψ κ l r
  change
    (∀ pLabel pBit,
      q.1.path = .some pLabel pBit →
      q.1.path = l.path ∨
        (q.1.label.val = pLabel ∧
          (if q.1.bit then 1 else 0) = pBit)) ∧
    (∀ pLabel pBit,
      q.2.path = .some pLabel pBit →
      q.2.path = r.path ∨
        (q.2.label.val = pLabel ∧
          (if q.2.bit then 1 else 0) = pBit))
  exact ⟨genPathFrom_payload_or_old hPath.1,
    genPathFrom_payload_or_old hPath.2⟩

/-- If GENSIG changed a path value, the resulting payload matches its host. -/
theorem genSig_written_path_self_consistent {ψ : Nat}
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    let q := genSig hψ κ l r
    (∀ pLabel pBit,
      q.1.path = .some pLabel pBit → q.1.path ≠ l.path →
      q.1.label.val = pLabel ∧
        (if q.1.bit then 1 else 0) = pBit) ∧
    (∀ pLabel pBit,
      q.2.path = .some pLabel pBit → q.2.path ≠ r.path →
      q.2.label.val = pLabel ∧
        (if q.2.bit then 1 else 0) = pBit) := by
  let q := genSig hψ κ l r
  have hPayload := genSig_path_payload_or_old hψ κ l r
  change
    (∀ pLabel pBit,
      q.1.path = .some pLabel pBit → q.1.path ≠ l.path →
      q.1.label.val = pLabel ∧
        (if q.1.bit then 1 else 0) = pBit) ∧
    (∀ pLabel pBit,
      q.2.path = .some pLabel pBit → q.2.path ≠ r.path →
      q.2.label.val = pLabel ∧
        (if q.2.bit then 1 else 0) = pBit)
  constructor
  · intro pLabel pBit hPath hChanged
    rcases hPayload.1 pLabel pBit hPath with hOld | hConsistent
    · exact (hChanged hOld).elim
    · exact hConsistent
  · intro pLabel pBit hPath hChanged
    rcases hPayload.2 pLabel pBit hPath with hOld | hConsistent
    · exact (hChanged hOld).elim
    · exact hConsistent

end ZZT1GenSig

#print axioms ZZT1GenSig.genSig_eq_staged
#print axioms ZZT1GenSig.genSigStart_proj
#print axioms ZZT1GenSig.genSigPropagate_proj
#print axioms ZZT1GenSig.genSigEmitR_proj
#print axioms ZZT1GenSig.genSigEmitL_proj
#print axioms ZZT1GenSig.genSigFinish_proj
#print axioms ZZT1GenSig.wait_genSigFrame
#print axioms ZZT1GenSig.genSigStart_frame
#print axioms ZZT1GenSig.genSigPropagate_frame
#print axioms ZZT1GenSig.genSigEmitR_frame
#print axioms ZZT1GenSig.genSigEmitL_frame
#print axioms ZZT1GenSig.genSigFinish_frame
#print axioms ZZT1GenSig.genSig_frame
#print axioms ZZT1GenSig.genSig_leader
#print axioms ZZT1GenSig.genSig_label
#print axioms ZZT1GenSig.genSig_bit
#print axioms ZZT1GenSig.genSig_path2
#print axioms ZZT1GenSig.genSig_path3
#print axioms ZZT1GenSig.genSig_write
#print axioms ZZT1GenSig.genStateFrom_refl
#print axioms ZZT1GenSig.genStateFrom_trans
#print axioms ZZT1GenSig.wait_genSigState
#print axioms ZZT1GenSig.genSigStart_state
#print axioms ZZT1GenSig.genSigPropagate_state
#print axioms ZZT1GenSig.genSigEmitR_state
#print axioms ZZT1GenSig.genSigEmitL_state
#print axioms ZZT1GenSig.genSigFinish_state
#print axioms ZZT1GenSig.genSig_state
#print axioms ZZT1GenSig.genPathFrom_refl
#print axioms ZZT1GenSig.genPathFrom_trans
#print axioms ZZT1GenSig.wait_genSigPath
#print axioms ZZT1GenSig.genSigStart_path
#print axioms ZZT1GenSig.genSigPropagate_path
#print axioms ZZT1GenSig.genSigEmitR_path
#print axioms ZZT1GenSig.genSigEmitL_path
#print axioms ZZT1GenSig.genSigFinish_path
#print axioms ZZT1GenSig.genSig_path
#print axioms ZZT1GenSig.genPathFrom_payload_or_old
#print axioms ZZT1GenSig.genSig_path_payload_or_old
#print axioms ZZT1GenSig.genSig_written_path_self_consistent
