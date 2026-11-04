import Leader.Wu.Safety.Counterexamples
import Leader.Wu.Scheduler.BoundedToRepairedLift

set_option autoImplicit false
set_option Elab.async false

namespace ZZSafeN4ReversedCleanGPT

open PPLL

def hpsi2 : 0 < 2 := by decide

/-- Exactly the protected non-path fields that CLEAN must frame.
The omitted protocol fields remain completely arbitrary. -/
structure CleanProtectedView where
  state : MainState
  leader : Bool
  label : Fin 2
  probe : Bool
  phase : Bool
  path2 : Option Path2Info
  p : Bool
  p_carry : Bool
  signal_B : Fin 2
  bullet : Fin 3
  shield : Bool
  deriving DecidableEq

namespace CleanProtectedView

def ofState (u : AgentState 2) : CleanProtectedView :=
  { state := u.state
    leader := u.leader
    label := u.label
    probe := u.probe
    phase := u.phase
    path2 := u.path2
    p := u.p
    p_carry := u.p_carry
    signal_B := u.signal_B
    bullet := u.bullet
    shield := u.shield }

end CleanProtectedView

def cleanProtectedPair (q : AgentState 2 × AgentState 2) :
    CleanProtectedView × CleanProtectedView :=
  (CleanProtectedView.ofState q.1, CleanProtectedView.ofState q.2)

/-! ## Generic CLEAN protected-field frame

These lemmas use only the literal CLEAN helpers from Leader/Wu/Protocol/Algorithm.lean.
They make no assumptions on bit, wait, reset, carry, count, h_field, path3,
reset_cmd, echo, write_state, write, last, last_set, last_unset, b_carry,
gen_ws, ws_echo, or signal_ws.
-/

private theorem cleanSigGenConnect_protected (u : AgentState 2) :
    CleanProtectedView.ofState (PPLL.cleanSigGenConnect u) =
      CleanProtectedView.ofState u := by
  unfold PPLL.cleanSigGenConnect CleanProtectedView.ofState
  try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigCleanApply_protected (u : AgentState 2) :
    CleanProtectedView.ofState (PPLL.cleanSigCleanApply u) =
      CleanProtectedView.ofState u := by
  unfold PPLL.cleanSigCleanApply CleanProtectedView.ofState
  try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigGenConnect_pair_protected
    (l r : AgentState 2) :
    cleanProtectedPair
        (PPLL.cleanSigGenConnect l, PPLL.cleanSigGenConnect r) =
      cleanProtectedPair (l, r) := by
  apply Prod.ext
  · exact cleanSigGenConnect_protected l
  · exact cleanSigGenConnect_protected r

private theorem cleanSigCleanApply_pair_protected
    (l r : AgentState 2) :
    cleanProtectedPair
        (PPLL.cleanSigCleanApply l, PPLL.cleanSigCleanApply r) =
      cleanProtectedPair (l, r) := by
  apply Prod.ext
  · exact cleanSigCleanApply_protected l
  · exact cleanSigCleanApply_protected r

private theorem cleanSigStep3_protected (l r : AgentState 2) :
    cleanProtectedPair (PPLL.cleanSigStep3 l r) =
      cleanProtectedPair (l, r) := by
  unfold PPLL.cleanSigStep3 cleanProtectedPair
    CleanProtectedView.ofState
  try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep4_protected (l r : AgentState 2) :
    cleanProtectedPair (PPLL.cleanSigStep4 l r) =
      cleanProtectedPair (l, r) := by
  unfold PPLL.cleanSigStep4 cleanProtectedPair
    CleanProtectedView.ofState
  try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep5_protected (l r : AgentState 2) :
    cleanProtectedPair (PPLL.cleanSigStep5 hpsi2 l r) =
      cleanProtectedPair (l, r) := by
  unfold PPLL.cleanSigStep5 cleanProtectedPair
    CleanProtectedView.ofState
  try dsimp only []
  repeat (first | rfl | split)

private theorem cleanSigStep6_protected (l r : AgentState 2) :
    cleanProtectedPair (PPLL.cleanSigStep6 hpsi2 l r) =
      cleanProtectedPair (l, r) := by
  unfold PPLL.cleanSigStep6 cleanProtectedPair
    CleanProtectedView.ofState
  try dsimp only []
  repeat (first | rfl | split)

private theorem clean_protected_pair (l r : AgentState 2) :
    cleanProtectedPair (PPLL.cleanSig hpsi2 l r) =
      cleanProtectedPair (l, r) := by
  let q0 : AgentState 2 × AgentState 2 :=
    (PPLL.cleanSigGenConnect l, PPLL.cleanSigGenConnect r)
  let q1 := PPLL.cleanSigStep3 q0.1 q0.2
  let q2 := PPLL.cleanSigStep4 q1.1 q1.2
  let q3 := PPLL.cleanSigStep5 hpsi2 q2.1 q2.2
  let q4 := PPLL.cleanSigStep6 hpsi2 q3.1 q3.2
  have hdef :
      PPLL.cleanSig hpsi2 l r =
        (PPLL.cleanSigCleanApply q4.1,
         PPLL.cleanSigCleanApply q4.2) := by
    rfl
  rw [hdef]
  exact
    (cleanSigCleanApply_pair_protected q4.1 q4.2).trans
      ((cleanSigStep6_protected q3.1 q3.2).trans
        ((cleanSigStep5_protected q2.1 q2.2).trans
          ((cleanSigStep4_protected q1.1 q1.2).trans
            ((cleanSigStep3_protected q0.1 q0.2).trans
              (cleanSigGenConnect_pair_protected l r)))))

private theorem clean_protected_frame (l r : AgentState 2) :
    let q := PPLL.cleanSig hpsi2 l r
    CleanProtectedView.ofState q.1 = CleanProtectedView.ofState l ∧
      CleanProtectedView.ofState q.2 = CleanProtectedView.ofState r := by
  dsimp only
  have h := clean_protected_pair l r
  constructor
  · simpa [cleanProtectedPair] using congrArg Prod.fst h
  · simpa [cleanProtectedPair] using congrArg Prod.snd h

/-! ## Exact AB connector calculation -/

private theorem clean_AB_shape
    (l r : AgentState 2)
    (hlLabel : l.label = 0)
    (hrLabel : r.label = 1)
    (hlPath : l.path = .some 1 0)
    (hrPath : r.path = .some 0 0)
    (hlPath4 :
      l.path4 = none ∨
        l.path4 = some ((1 : Int), (1 : Nat)))
    (hlPath5 : l.path5 = none)
    (hrPath4 : r.path4 = none)
    (hrPath5 :
      r.path5 = none ∨
        r.path5 = some ((0 : Int), (1 : Nat))) :
    let q := PPLL.cleanSig hpsi2 l r
    q.1.path = .some 1 0 ∧
      q.2.path = .some 0 0 ∧
      q.1.path4 = some ((1 : Int), (1 : Nat)) ∧
      q.1.path5 = none ∧
      q.2.path4 = none ∧
      q.2.path5 = some ((0 : Int), (1 : Nat)) := by
  rcases hlPath4 with hL4 | hL4 <;>
    rcases hrPath5 with hR5 | hR5 <;>
      simp [PPLL.cleanSig, PPLL.cleanSigGenConnect,
        PPLL.cleanSigStep3, PPLL.cleanSigStep4,
        PPLL.cleanSigStep5, PPLL.cleanSigStep6,
        PPLL.cleanSigCleanApply,
        hlLabel, hrLabel, hlPath, hrPath,
        hL4, hlPath5, hrPath4, hR5]

/-- CLEAN on the A-to-B orientation.

A has label 0 and reversed main path some 1 0.
B has label 1 and reversed main path some 0 0.
The incoming connectors are exactly the ReversedCore connector options.
CLEAN preserves both main paths, frames every protected non-path field,
and normalizes the connectors to the generated A/B pair. -/
theorem clean_AB
    (l r : AgentState 2)
    (hlLabel : l.label = 0)
    (hrLabel : r.label = 1)
    (hlPath : l.path = .some 1 0)
    (hrPath : r.path = .some 0 0)
    (hlPath4 :
      l.path4 = none ∨
        l.path4 = some ((1 : Int), (1 : Nat)))
    (hlPath5 : l.path5 = none)
    (hrPath4 : r.path4 = none)
    (hrPath5 :
      r.path5 = none ∨
        r.path5 = some ((0 : Int), (1 : Nat))) :
    let q := PPLL.cleanSig hpsi2 l r
    q.1.path = .some 1 0 ∧
      q.2.path = .some 0 0 ∧
      CleanProtectedView.ofState q.1 = CleanProtectedView.ofState l ∧
      CleanProtectedView.ofState q.2 = CleanProtectedView.ofState r ∧
      q.1.path4 = some ((1 : Int), (1 : Nat)) ∧
      q.1.path5 = none ∧
      q.2.path4 = none ∧
      q.2.path5 = some ((0 : Int), (1 : Nat)) := by
  have hs := clean_AB_shape l r
    hlLabel hrLabel hlPath hrPath
    hlPath4 hlPath5 hrPath4 hrPath5
  have hf := clean_protected_frame l r
  dsimp only at hs hf ⊢
  rcases hs with ⟨hpL, hpR, h4L, h5L, h4R, h5R⟩
  rcases hf with ⟨hfL, hfR⟩
  exact ⟨hpL, hpR, hfL, hfR, h4L, h5L, h4R, h5R⟩

/-! ## Exact BA connector calculation -/

private theorem clean_BA_shape
    (l r : AgentState 2)
    (hlLabel : l.label = 1)
    (hrLabel : r.label = 0)
    (hlPath : l.path = .some 0 0)
    (hrPath : r.path = .some 1 0)
    (hlPath4 : l.path4 = none)
    (hlPath5 :
      l.path5 = none ∨
        l.path5 = some ((0 : Int), (1 : Nat)))
    (hrPath4 :
      r.path4 = none ∨
        r.path4 = some ((1 : Int), (1 : Nat)))
    (hrPath5 : r.path5 = none) :
    let q := PPLL.cleanSig hpsi2 l r
    q.1.path = .some 0 0 ∧
      q.2.path = .some 1 0 ∧
      q.1.path4 = none ∧
      q.1.path5 = none ∧
      q.2.path4 = none ∧
      q.2.path5 = none := by
  rcases hlPath5 with hL5 | hL5 <;>
    rcases hrPath4 with hR4 | hR4 <;>
      simp [PPLL.cleanSig, PPLL.cleanSigGenConnect,
        PPLL.cleanSigStep3, PPLL.cleanSigStep4,
        PPLL.cleanSigStep5, PPLL.cleanSigStep6,
        PPLL.cleanSigCleanApply,
        hlLabel, hrLabel, hlPath, hrPath,
        hlPath4, hL5, hR4, hrPath5]

/-- CLEAN on the B-to-A orientation.

The generated matching connectors are consumed by Step3/Step4.
Both reversed main paths survive, all protected non-path fields are framed,
and both endpoints leave CLEAN with path4 = path5 = none. -/
theorem clean_BA
    (l r : AgentState 2)
    (hlLabel : l.label = 1)
    (hrLabel : r.label = 0)
    (hlPath : l.path = .some 0 0)
    (hrPath : r.path = .some 1 0)
    (hlPath4 : l.path4 = none)
    (hlPath5 :
      l.path5 = none ∨
        l.path5 = some ((0 : Int), (1 : Nat)))
    (hrPath4 :
      r.path4 = none ∨
        r.path4 = some ((1 : Int), (1 : Nat)))
    (hrPath5 : r.path5 = none) :
    let q := PPLL.cleanSig hpsi2 l r
    q.1.path = .some 0 0 ∧
      q.2.path = .some 1 0 ∧
      CleanProtectedView.ofState q.1 = CleanProtectedView.ofState l ∧
      CleanProtectedView.ofState q.2 = CleanProtectedView.ofState r ∧
      q.1.path4 = none ∧
      q.1.path5 = none ∧
      q.2.path4 = none ∧
      q.2.path5 = none := by
  have hs := clean_BA_shape l r
    hlLabel hrLabel hlPath hrPath
    hlPath4 hlPath5 hrPath4 hrPath5
  have hf := clean_protected_frame l r
  dsimp only at hs hf ⊢
  rcases hs with ⟨hpL, hpR, h4L, h5L, h4R, h5R⟩
  rcases hf with ⟨hfL, hfR⟩
  exact ⟨hpL, hpR, hfL, hfR, h4L, h5L, h4R, h5R⟩

end ZZSafeN4ReversedCleanGPT

#print axioms ZZSafeN4ReversedCleanGPT.clean_AB
#print axioms ZZSafeN4ReversedCleanGPT.clean_BA
