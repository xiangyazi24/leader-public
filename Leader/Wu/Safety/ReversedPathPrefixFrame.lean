import Leader.Wu.Safety.Counterexamples
import Leader.Wu.Scheduler.BoundedToRepairedLift

set_option autoImplicit false
set_option Elab.async false

namespace ZZSafeN4ReversedPrefixGPT

open PPLL PPLLRepair

def hpsi2 : 0 < 2 := by decide

def ring4 : DirectedRing 4 := PPLLCounterexample.ring4

/-- The exact n=4 invariant supplied by the downstream proof. -/
def ReversedCore (C : Fin 4 → AgentState 2) : Prop :=
  let a0 := C 0
  let a1 := C 1
  let a2 := C 2
  let a3 := C 3
  a0.leader = true ∧ a1.leader = false ∧
  a2.leader = false ∧ a3.leader = false ∧
  a0.label = 0 ∧ a1.label = 1 ∧ a2.label = 0 ∧ a3.label = 1 ∧
  a0.probe = false ∧ a1.probe = false ∧
  a2.probe = false ∧ a3.probe = false ∧
  a0.phase = false ∧ a1.phase = false ∧
  a2.phase = false ∧ a3.phase = false ∧
  a0.path = .some 1 0 ∧ a1.path = .some 0 0 ∧
  a2.path = .some 1 0 ∧ a3.path = .some 0 0 ∧
  a0.path2 = none ∧ a1.path2 = none ∧
  a2.path2 = none ∧ a3.path2 = none ∧
  a0.p = false ∧ a1.p = false ∧ a2.p = false ∧ a3.p = false ∧
  a0.p_carry = false ∧ a1.p_carry = false ∧
  a2.p_carry = false ∧ a3.p_carry = false ∧
  (a0.state = .congest ∨ a0.state = .lock) ∧
  a1.state = .congest ∧
  (a2.state = .congest ∨ a2.state = .lock) ∧
  a3.state = .congest ∧
  a0.signal_B = 0 ∧ a1.signal_B = 0 ∧
  a2.signal_B = 0 ∧ a3.signal_B = 0 ∧
  a0.bullet = 0 ∧ a1.bullet = 2 ∧
  a2.bullet = 0 ∧ a3.bullet = 0 ∧
  a0.shield = true ∧ a1.shield = true ∧
  a2.shield = true ∧ a3.shield = true ∧
  (a0.path4 = none ∨ a0.path4 = some ((1 : Int), 1)) ∧
  a0.path5 = none ∧
  a1.path4 = none ∧
  (a1.path5 = none ∨ a1.path5 = some ((0 : Int), 1)) ∧
  (a2.path4 = none ∨ a2.path4 = some ((1 : Int), 1)) ∧
  a2.path5 = none ∧
  a3.path4 = none ∧
  (a3.path5 = none ∨ a3.path5 = some ((0 : Int), 1))

/-!
The prefix view contains every ReversedCore field that pPsi/WAIT/GENSIG
must frame.  path4/path5 are included as a handoff to the CLEAN module:
this file proves that they reach CLEAN unchanged, but makes no claim about
what CLEAN itself does.

The deliberately omitted fields are exactly the universally unrestricted
ones from the task: bit, wait, reset, carry, count, h_field, path3,
reset_cmd, echo, write_state, write, last, last_set, last_unset, b_carry,
gen_ws, ws_echo, signal_ws.
-/
structure PrefixCellView where
  leader : Bool
  label : Fin 2
  probe : Bool
  phase : Bool
  path : PathInfo
  path2 : Option Path2Info
  p : Bool
  p_carry : Bool
  state : MainState
  signal_B : Fin 2
  bullet : Fin 3
  shield : Bool
  path4 : Option (Int × Nat)
  path5 : Option (Int × Nat)
  deriving DecidableEq, Repr

def prefixCellView (u : AgentState 2) : PrefixCellView :=
  { leader := u.leader
    label := u.label
    probe := u.probe
    phase := u.phase
    path := u.path
    path2 := u.path2
    p := u.p
    p_carry := u.p_carry
    state := u.state
    signal_B := u.signal_B
    bullet := u.bullet
    shield := u.shield
    path4 := u.path4
    path5 := u.path5 }

def prefixPairView
    (q : AgentState 2 × AgentState 2) :
    PrefixCellView × PrefixCellView :=
  (prefixCellView q.1, prefixCellView q.2)

/-- The local AB shape needed to block pPsi and GENSIG.
All omitted AgentState fields remain arbitrary. -/
structure ABPrefixRole (l r : AgentState 2) : Prop where
  leftLabel : l.label = 0
  rightLabel : r.label = 1
  leftProbe : l.probe = false
  rightProbe : r.probe = false
  leftPhase : l.phase = false
  rightPhase : r.phase = false
  leftPath : l.path = .some 1 0
  rightPath : r.path = .some 0 0
  leftState : l.state = .congest ∨ l.state = .lock
  rightState : r.state = .congest

/-- The local BA shape needed to block pPsi and GENSIG.
All omitted AgentState fields remain arbitrary. -/
structure BAPrefixRole (l r : AgentState 2) : Prop where
  leftLabel : l.label = 1
  rightLabel : r.label = 0
  leftProbe : l.probe = false
  rightProbe : r.probe = false
  leftPhase : l.phase = false
  rightPhase : r.phase = false
  leftPath : l.path = .some 0 0
  rightPath : r.path = .some 1 0
  leftState : l.state = .congest
  rightState : r.state = .congest ∨ r.state = .lock

def afterPPsi (l r : AgentState 2) : AgentState 2 × AgentState 2 :=
  PPLL.pPsi hpsi2 l r

def afterGenSig (l r : AgentState 2) : AgentState 2 × AgentState 2 :=
  let q := afterPPsi l r
  PPLLRepair.genSigSaturated hpsi2 10 q.1 q.2

/-! ## P'_psi: aligned, probe-free responder is exact identity -/

private theorem aligned_AB
    (l r : AgentState 2)
    (hl : l.label = 0)
    (hr : r.label = 1) :
    r.label =
      ⟨(l.label.val + 1) % 2, Nat.mod_lt _ hpsi2⟩ := by
  apply Fin.ext
  have hlv : l.label.val = 0 := by
    simpa using congrArg (fun x : Fin 2 => x.val) hl
  have hrv : r.label.val = 1 := by
    simpa using congrArg (fun x : Fin 2 => x.val) hr
  simp [hlv, hrv]

private theorem aligned_BA
    (l r : AgentState 2)
    (hl : l.label = 1)
    (hr : r.label = 0) :
    r.label =
      ⟨(l.label.val + 1) % 2, Nat.mod_lt _ hpsi2⟩ := by
  apply Fin.ext
  have hlv : l.label.val = 1 := by
    simpa using congrArg (fun x : Fin 2 => x.val) hl
  have hrv : r.label.val = 0 := by
    simpa using congrArg (fun x : Fin 2 => x.val) hr
  simp [hlv, hrv]

/-- Stronger than the requested four-field frame: on an aligned pair with
probe-free responder, actual pPsi is the exact identity pair. -/
theorem pPsi_aligned_noProbe_eq
    (l r : AgentState 2)
    (halign :
      r.label =
        ⟨(l.label.val + 1) % 2, Nat.mod_lt _ hpsi2⟩)
    (hrProbe : r.probe = false) :
    PPLL.pPsi hpsi2 l r = (l, r) := by
  simp [PPLL.pPsi, halign, hrProbe]

theorem afterPPsi_AB_eq
    (l r : AgentState 2) (h : ABPrefixRole l r) :
    afterPPsi l r = (l, r) := by
  unfold afterPPsi
  exact pPsi_aligned_noProbe_eq l r
    (aligned_AB l r h.leftLabel h.rightLabel) h.rightProbe

theorem afterPPsi_BA_eq
    (l r : AgentState 2) (h : BAPrefixRole l r) :
    afterPPsi l r = (l, r) := by
  unfold afterPPsi
  exact pPsi_aligned_noProbe_eq l r
    (aligned_BA l r h.leftLabel h.rightLabel) h.rightProbe

/-! ## Saturating WAIT frames every protected prefix field -/

private theorem waitPrepare_prefix_frame
    (l r : AgentState 2) :
    prefixPairView
      (PPLLRepair.waitSaturatedPrepare hpsi2 l r) =
      prefixPairView (l, r) := by
  unfold prefixPairView prefixCellView PPLLRepair.waitSaturatedPrepare
  dsimp only
  repeat (first | rfl | split)

private theorem waitCarry_prefix_frame
    (l r : AgentState 2) :
    prefixPairView
      (PPLLRepair.waitSaturatedCarry hpsi2 10 l r) =
      prefixPairView (l, r) := by
  unfold prefixPairView prefixCellView PPLLRepair.waitSaturatedCarry
  dsimp only
  repeat (first | rfl | split)

private theorem waitReset_prefix_frame
    (l r : AgentState 2) :
    prefixPairView
      (PPLLRepair.waitSaturatedReset hpsi2 l r) =
      prefixPairView (l, r) := by
  unfold prefixPairView prefixCellView PPLLRepair.waitSaturatedReset
  dsimp only
  repeat (first | rfl | split)

private theorem waitFinish_prefix_frame
    (l r : AgentState 2) :
    prefixPairView
      (PPLLRepair.waitSaturatedFinish hpsi2 10 l r) =
      prefixPairView (l, r) := by
  unfold prefixPairView prefixCellView PPLLRepair.waitSaturatedFinish
  dsimp only
  repeat (first | rfl | split)

/-- WAIT may arbitrarily change its counter/control fields, but it frames
all fields fixed by ReversedCore. -/
theorem waitSaturated_prefix_frame
    (l r : AgentState 2) :
    prefixPairView
      (PPLLRepair.waitSaturated hpsi2 10 l r) =
      prefixPairView (l, r) := by
  let q0 := PPLLRepair.waitSaturatedPrepare hpsi2 l r
  let q1 := PPLLRepair.waitSaturatedCarry hpsi2 10 q0.1 q0.2
  let q2 := PPLLRepair.waitSaturatedReset hpsi2 q1.1 q1.2
  change
    prefixPairView
      (PPLLRepair.waitSaturatedFinish hpsi2 10 q2.1 q2.2) =
      prefixPairView (l, r)
  exact
    (waitFinish_prefix_frame q2.1 q2.2).trans
      ((waitReset_prefix_frame q1.1 q1.2).trans
        ((waitCarry_prefix_frame q0.1 q0.2).trans
          (waitPrepare_prefix_frame l r)))

private theorem waitSaturated_path_state
    (l r : AgentState 2) :
    let q := PPLLRepair.waitSaturated hpsi2 10 l r
    q.1.path = l.path ∧
    q.2.path = r.path ∧
    q.1.state = l.state ∧
    q.2.state = r.state := by
  let q := PPLLRepair.waitSaturated hpsi2 10 l r
  have hframe := waitSaturated_prefix_frame l r
  change prefixPairView q = prefixPairView (l, r) at hframe

  have hlPath :=
    congrArg
      (fun z : PrefixCellView × PrefixCellView => z.1.path) hframe
  have hrPath :=
    congrArg
      (fun z : PrefixCellView × PrefixCellView => z.2.path) hframe
  have hlState :=
    congrArg
      (fun z : PrefixCellView × PrefixCellView => z.1.state) hframe
  have hrState :=
    congrArg
      (fun z : PrefixCellView × PrefixCellView => z.2.state) hframe

  change q.1.path = l.path at hlPath
  change q.2.path = r.path at hrPath
  change q.1.state = l.state at hlState
  change q.2.state = r.state at hrState

  exact ⟨hlPath, hrPath, hlState, hrState⟩

/-! ## GENSIG tail: non-bottom reversed paths block every main write -/

private theorem genStart_eq_of_nonbottom
    (l r : AgentState 2)
    (hlPath : l.path ≠ .bot)
    (hrPath : r.path ≠ .bot) :
    PPLLRepair.genSigSaturatedStart hpsi2 l r = (l, r) := by
  simp [PPLLRepair.genSigSaturatedStart, hlPath, hrPath]

private theorem genEmit_eq_of_right_not_produce
    (l r : AgentState 2)
    (hrProduce : r.state ≠ .produce) :
    PPLLRepair.genSigSaturatedEmit hpsi2 l r = (l, r) := by
  simp [PPLLRepair.genSigSaturatedEmit, hrProduce]

private theorem genPropagate_eq_of_left_not_produce
    (l r : AgentState 2)
    (hlProduce : l.state ≠ .produce) :
    PPLLRepair.genSigSaturatedPropagate hpsi2 l r = (l, r) := by
  simp [PPLLRepair.genSigSaturatedPropagate, hlProduce]

private theorem genFinish_eq_of_left_not_done
    (l r : AgentState 2)
    (hlDone : l.state ≠ .done) :
    PPLLRepair.genSigSaturatedFinish hpsi2 l r = (l, r) := by
  simp [PPLLRepair.genSigSaturatedFinish, hlDone]

private theorem genAfterWait_eq_of_blocked
    (l r : AgentState 2)
    (hlPath : l.path ≠ .bot)
    (hrPath : r.path ≠ .bot)
    (hlProduce : l.state ≠ .produce)
    (hlDone : l.state ≠ .done)
    (hrProduce : r.state ≠ .produce) :
    PPLLRepair.genSigSaturatedAfterWait hpsi2 l r = (l, r) := by
  let q0 := PPLLRepair.genSigSaturatedStart hpsi2 l r
  have h0 : q0 = (l, r) :=
    genStart_eq_of_nonbottom l r hlPath hrPath

  let q1 := PPLLRepair.genSigSaturatedEmit hpsi2 q0.1 q0.2
  have h1 : q1 = (l, r) := by
    change
      PPLLRepair.genSigSaturatedEmit hpsi2 q0.1 q0.2 = (l, r)
    rw [h0]
    exact genEmit_eq_of_right_not_produce l r hrProduce

  let q2 := PPLLRepair.genSigSaturatedPropagate hpsi2 q1.1 q1.2
  have h2 : q2 = (l, r) := by
    change
      PPLLRepair.genSigSaturatedPropagate hpsi2 q1.1 q1.2 = (l, r)
    rw [h1]
    exact genPropagate_eq_of_left_not_produce l r hlProduce

  let q3 := PPLLRepair.genSigSaturatedFinish hpsi2 q2.1 q2.2
  have h3 : q3 = (l, r) := by
    change
      PPLLRepair.genSigSaturatedFinish hpsi2 q2.1 q2.2 = (l, r)
    rw [h2]
    exact genFinish_eq_of_left_not_done l r hlDone

  change q3 = (l, r)
  exact h3

/-- Under the reversed-path blocker, the post-WAIT GENSIG tail is literally
the identity.  Thus genSigSaturated differs from input only in unrestricted
WAIT fields. -/
theorem genSigSaturated_eq_wait_of_blocked
    (l r : AgentState 2)
    (hlPath : l.path ≠ .bot)
    (hrPath : r.path ≠ .bot)
    (hlProduce : l.state ≠ .produce)
    (hlDone : l.state ≠ .done)
    (hrProduce : r.state ≠ .produce) :
    PPLLRepair.genSigSaturated hpsi2 10 l r =
      PPLLRepair.waitSaturated hpsi2 10 l r := by
  let w := PPLLRepair.waitSaturated hpsi2 10 l r

  have hw :
      w.1.path = l.path ∧
      w.2.path = r.path ∧
      w.1.state = l.state ∧
      w.2.state = r.state := by
    simpa [w] using (waitSaturated_path_state l r)

  have hwlPath : w.1.path ≠ .bot := by
    rw [hw.1]
    exact hlPath
  have hwrPath : w.2.path ≠ .bot := by
    rw [hw.2.1]
    exact hrPath
  have hwlProduce : w.1.state ≠ .produce := by
    rw [hw.2.2.1]
    exact hlProduce
  have hwlDone : w.1.state ≠ .done := by
    rw [hw.2.2.1]
    exact hlDone
  have hwrProduce : w.2.state ≠ .produce := by
    rw [hw.2.2.2]
    exact hrProduce

  change
    PPLLRepair.genSigSaturatedAfterWait hpsi2 w.1 w.2 = w
  have htail :=
    genAfterWait_eq_of_blocked w.1 w.2
      hwlPath hwrPath hwlProduce hwlDone hwrProduce
  exact htail.trans (by cases w <;> rfl)

/-- Protected-prefix frame for arbitrary WAIT fields. -/
theorem genSigSaturated_prefix_frame_of_blocked
    (l r : AgentState 2)
    (hlPath : l.path ≠ .bot)
    (hrPath : r.path ≠ .bot)
    (hlProduce : l.state ≠ .produce)
    (hlDone : l.state ≠ .done)
    (hrProduce : r.state ≠ .produce) :
    prefixPairView
      (PPLLRepair.genSigSaturated hpsi2 10 l r) =
      prefixPairView (l, r) := by
  rw [genSigSaturated_eq_wait_of_blocked l r
    hlPath hrPath hlProduce hlDone hrProduce]
  exact waitSaturated_prefix_frame l r

private theorem AB_blockers
    (l r : AgentState 2) (h : ABPrefixRole l r) :
    l.path ≠ .bot ∧
    r.path ≠ .bot ∧
    l.state ≠ .produce ∧
    l.state ≠ .done ∧
    r.state ≠ .produce := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [h.leftPath]
  · simp [h.rightPath]
  · rcases h.leftState with hs | hs
    · simp [hs]
    · simp [hs]
  · rcases h.leftState with hs | hs
    · simp [hs]
    · simp [hs]
  · simp [h.rightState]

private theorem BA_blockers
    (l r : AgentState 2) (h : BAPrefixRole l r) :
    l.path ≠ .bot ∧
    r.path ≠ .bot ∧
    l.state ≠ .produce ∧
    l.state ≠ .done ∧
    r.state ≠ .produce := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [h.leftPath]
  · simp [h.rightPath]
  · simp [h.leftState]
  · simp [h.leftState]
  · rcases h.rightState with hs | hs
    · simp [hs]
    · simp [hs]

/-- AB headline: arbitrary omitted fields are allowed.  The complete
ReversedCore protected prefix, including path4/path5 as CLEAN input,
is unchanged through actual pPsi + saturated GENSIG. -/
theorem afterGenSig_AB_frame
    (l r : AgentState 2) (h : ABPrefixRole l r) :
    prefixPairView (afterGenSig l r) =
      prefixPairView (l, r) := by
  rcases AB_blockers l r h with
    ⟨hlPath, hrPath, hlProduce, hlDone, hrProduce⟩
  change
    prefixPairView
      (PPLLRepair.genSigSaturated hpsi2 10
        (afterPPsi l r).1 (afterPPsi l r).2) =
      prefixPairView (l, r)
  rw [afterPPsi_AB_eq l r h]
  exact
    genSigSaturated_prefix_frame_of_blocked
      l r hlPath hrPath hlProduce hlDone hrProduce

/-- BA headline: arbitrary omitted fields are allowed.  The complete
ReversedCore protected prefix, including path4/path5 as CLEAN input,
is unchanged through actual pPsi + saturated GENSIG. -/
theorem afterGenSig_BA_frame
    (l r : AgentState 2) (h : BAPrefixRole l r) :
    prefixPairView (afterGenSig l r) =
      prefixPairView (l, r) := by
  rcases BA_blockers l r h with
    ⟨hlPath, hrPath, hlProduce, hlDone, hrProduce⟩
  change
    prefixPairView
      (PPLLRepair.genSigSaturated hpsi2 10
        (afterPPsi l r).1 (afterPPsi l r).2) =
      prefixPairView (l, r)
  rw [afterPPsi_BA_eq l r h]
  exact
    genSigSaturated_prefix_frame_of_blocked
      l r hlPath hrPath hlProduce hlDone hrProduce

/-! ## Exact handoff to the separate CLEAN module -/

/-- The exact remainder of ppllSaturatedBeforeCheck after the post-GENSIG
boundary.  This definition contains CLEAN, ELIMINATE_SIG, and SIGMOVE only. -/
def postGenToBeforeCheck
    (q : AgentState 2 × AgentState 2) :
    AgentState 2 × AgentState 2 :=
  let q := PPLL.cleanSig hpsi2 q.1 q.2
  let q := PPLL.eliminateSig hpsi2 q.1 q.2
  PPLL.sigMove hpsi2 q.1 q.2

/-- Definitional audit of the exact repaired prefix.  No CLEAN behavior is
claimed here. -/
theorem ppllSaturatedBeforeCheck_factor
    (l r : AgentState 2) :
    PPLLRepair.ppllSaturatedBeforeCheck hpsi2 10 l r =
      postGenToBeforeCheck (afterGenSig l r) := by
  rfl

/-- Exact AB composition interface for the next module.
The only missing premise is the post-GENSIG CLEAN/ELIMINATE_SIG/SIGMOVE frame. -/
theorem ppllSaturatedBeforeCheck_AB_frame_of_tail
    (l r : AgentState 2)
    (h : ABPrefixRole l r)
    (htail :
      prefixPairView
          (postGenToBeforeCheck (afterGenSig l r)) =
        prefixPairView (afterGenSig l r)) :
    prefixPairView
        (PPLLRepair.ppllSaturatedBeforeCheck hpsi2 10 l r) =
      prefixPairView (l, r) := by
  calc
    prefixPairView
        (PPLLRepair.ppllSaturatedBeforeCheck hpsi2 10 l r) =
      prefixPairView
        (postGenToBeforeCheck (afterGenSig l r)) :=
      congrArg prefixPairView
        (ppllSaturatedBeforeCheck_factor l r)
    _ = prefixPairView (afterGenSig l r) := htail
    _ = prefixPairView (l, r) := afterGenSig_AB_frame l r h

/-- Exact BA composition interface for the next module.
The only missing premise is the post-GENSIG CLEAN/ELIMINATE_SIG/SIGMOVE frame. -/
theorem ppllSaturatedBeforeCheck_BA_frame_of_tail
    (l r : AgentState 2)
    (h : BAPrefixRole l r)
    (htail :
      prefixPairView
          (postGenToBeforeCheck (afterGenSig l r)) =
        prefixPairView (afterGenSig l r)) :
    prefixPairView
        (PPLLRepair.ppllSaturatedBeforeCheck hpsi2 10 l r) =
      prefixPairView (l, r) := by
  calc
    prefixPairView
        (PPLLRepair.ppllSaturatedBeforeCheck hpsi2 10 l r) =
      prefixPairView
        (postGenToBeforeCheck (afterGenSig l r)) :=
      congrArg prefixPairView
        (ppllSaturatedBeforeCheck_factor l r)
    _ = prefixPairView (afterGenSig l r) := htail
    _ = prefixPairView (l, r) := afterGenSig_BA_frame l r h

end ZZSafeN4ReversedPrefixGPT

#print axioms ZZSafeN4ReversedPrefixGPT.pPsi_aligned_noProbe_eq
#print axioms ZZSafeN4ReversedPrefixGPT.afterPPsi_AB_eq
#print axioms ZZSafeN4ReversedPrefixGPT.afterPPsi_BA_eq
#print axioms ZZSafeN4ReversedPrefixGPT.waitSaturated_prefix_frame
#print axioms ZZSafeN4ReversedPrefixGPT.genSigSaturated_eq_wait_of_blocked
#print axioms ZZSafeN4ReversedPrefixGPT.genSigSaturated_prefix_frame_of_blocked
#print axioms ZZSafeN4ReversedPrefixGPT.afterGenSig_AB_frame
#print axioms ZZSafeN4ReversedPrefixGPT.afterGenSig_BA_frame
#print axioms ZZSafeN4ReversedPrefixGPT.ppllSaturatedBeforeCheck_factor
#print axioms ZZSafeN4ReversedPrefixGPT.ppllSaturatedBeforeCheck_AB_frame_of_tail
#print axioms ZZSafeN4ReversedPrefixGPT.ppllSaturatedBeforeCheck_BA_frame_of_tail
