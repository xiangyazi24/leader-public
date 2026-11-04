import Leader.Wu.Safety.Counterexamples
import Leader.Wu.Scheduler.BoundedToRepairedLift


set_option autoImplicit false
set_option Elab.async false


namespace ZZSafeN4ReversedMiddleGPT


open PPLL PPLLRepair


theorem hpsi2 : 0 < 2 := by
  decide


theorem ring4 : DirectedRing 4 :=
  PPLLCounterexample.ring4


/-- The downstream invariant, copied exactly.  Fields not mentioned here are
universally unrestricted. -/
def ReversedCore (C : Fin 4 -> AgentState 2) : Prop :=
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
  (a0.path4 = none ∨ a0.path4 = some (1, 1)) ∧
  a0.path5 = none ∧
  a1.path4 = none ∧
  (a1.path5 = none ∨ a1.path5 = some (0, 1)) ∧
  (a2.path4 = none ∨ a2.path4 = some (1, 1)) ∧
  a2.path5 = none ∧
  a3.path4 = none ∧
  (a3.path5 = none ∨ a3.path5 = some (0, 1))


/-- The fields actually needed to make an A-role cell silent through
ELIMINATE_SIG, SIGMOVE, CHECK, and DISAPPEAR.  No omitted field is constrained. -/
def AQuiet (u : AgentState 2) : Prop :=
  u.label = 0 ∧
  u.path = .some 1 0 ∧
  u.path2 = none ∧
  u.p = false ∧
  u.p_carry = false ∧
  (u.state = .congest ∨ u.state = .lock)


/-- The fields actually needed to make a B-role cell silent through the same
middle chain.  No omitted field is constrained. -/
def BQuiet (u : AgentState 2) : Prop :=
  u.label = 1 ∧
  u.path = .some 0 0 ∧
  u.path2 = none ∧
  u.p = false ∧
  u.p_carry = false ∧
  u.state = .congest


/-- Full protected A-role frame from ReversedCore, parameterized only by the
site's leader bit. -/
def AProtected (leaderBit : Bool) (u : AgentState 2) : Prop :=
  AQuiet u ∧
  u.leader = leaderBit ∧
  u.probe = false ∧
  u.phase = false ∧
  u.signal_B = 0 ∧
  u.bullet = 0 ∧
  u.shield = true ∧
  (u.path4 = none ∨ u.path4 = some (1, 1)) ∧
  u.path5 = none


/-- Full protected B-role frame from ReversedCore, parameterized by the site's
bullet value (2 at B1, 0 at B3). -/
def BProtected (bulletVal : Fin 3) (u : AgentState 2) : Prop :=
  BQuiet u ∧
  u.leader = false ∧
  u.probe = false ∧
  u.phase = false ∧
  u.signal_B = 0 ∧
  u.bullet = bulletVal ∧
  u.shield = true ∧
  u.path4 = none ∧
  (u.path5 = none ∨ u.path5 = some (0, 1))


/-- Exactly the requested middle chain: after CLEAN and before COMPARE. -/
def middleBeforeCompare
    (l r : AgentState 2) : AgentState 2 × AgentState 2 :=
  let q0 := eliminateSig hpsi2 l r
  let q1 := sigMove hpsi2 q0.1 q0.2
  let q2 := checkSig hpsi2 q1.1 q1.2
  disappear hpsi2 q2.1 q2.2


/-! ## ELIMINATE_SIG -/


/-- ELIMINATE_SIG cannot fire when the responder is one of the protected
comparison states. -/
theorem eliminateSig_quiet
    (l r : AgentState 2)
    (hrState : r.state = .congest ∨ r.state = .lock) :
    eliminateSig hpsi2 l r = (l, r) := by
  rcases hrState with hrState | hrState <;>
    simp [eliminateSig, hrState]


theorem eliminateSig_AB
    (l r : AgentState 2)
    (hl : AQuiet l) (hr : BQuiet r) :
    eliminateSig hpsi2 l r = (l, r) := by
  unfold BQuiet at hr
  rcases hr with
    ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  exact eliminateSig_quiet l r (Or.inl hrState)


theorem eliminateSig_BA
    (l r : AgentState 2)
    (hl : BQuiet l) (hr : AQuiet r) :
    eliminateSig hpsi2 l r = (l, r) := by
  unfold AQuiet at hr
  rcases hr with
    ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  exact eliminateSig_quiet l r hrState


/-! ## SIGMOVE -/


/-- With both main paths present and both path2 controls absent, all five
transport substages are inert.  The responder state assumption also disables
the final CHECK_ready/depart tail. -/
theorem sigMove_quiet
    (l r : AgentState 2)
    (a b c d : Nat)
    (hlPath : l.path = .some a b)
    (hrPath : r.path = .some c d)
    (hlPath2 : l.path2 = none)
    (hrPath2 : r.path2 = none)
    (hrState : r.state = .congest ∨ r.state = .lock) :
    sigMove hpsi2 l r = (l, r) := by
  rcases hrState with hrState | hrState <;>
    simp [sigMove, sigMoveStep1, sigMoveStep2, sigMoveStep3,
      sigMoveStep4, sigMoveStep5, sigMoveApplyControl,
      hlPath, hrPath, hlPath2, hrPath2, hrState]


theorem sigMove_AB
    (l r : AgentState 2)
    (hl : AQuiet l) (hr : BQuiet r) :
    sigMove hpsi2 l r = (l, r) := by
  unfold AQuiet at hl
  unfold BQuiet at hr
  rcases hl with
    ⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩
  rcases hr with
    ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  exact sigMove_quiet l r 1 0 0 0
    hlPath hrPath hlPath2 hrPath2 (Or.inl hrState)


theorem sigMove_BA
    (l r : AgentState 2)
    (hl : BQuiet l) (hr : AQuiet r) :
    sigMove hpsi2 l r = (l, r) := by
  unfold BQuiet at hl
  unfold AQuiet at hr
  rcases hl with
    ⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩
  rcases hr with
    ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  exact sigMove_quiet l r 0 0 1 0
    hlPath hrPath hlPath2 hrPath2 hrState


/-! ## CHECK -/


/-- A->B CHECK is completely inert.  The crucial ready guards fail because
physical label 0 carries path label 1 and physical label 1 carries path label
0.  No hypothesis on either bit is used. -/
theorem checkSig_AB
    (l r : AgentState 2)
    (hl : AQuiet l) (hr : BQuiet r) :
    checkSig hpsi2 l r = (l, r) := by
  unfold AQuiet at hl
  unfold BQuiet at hr
  rcases hl with
    ⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩
  rcases hr with
    ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  rcases hlState with hlState | hlState <;>
    simp [checkSig, checkSigSetReady, checkSigCheckL, checkSigCheckR,
      checkSigSetResult, hlLabel, hlPath, hrLabel, hrPath,
      hlState, hrState]


/-- B->A CHECK is also completely inert for the same host/payload mismatch.
Again the proof is independent of both bit fields. -/
theorem checkSig_BA
    (l r : AgentState 2)
    (hl : BQuiet l) (hr : AQuiet r) :
    checkSig hpsi2 l r = (l, r) := by
  unfold BQuiet at hl
  unfold AQuiet at hr
  rcases hl with
    ⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩
  rcases hr with
    ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  rcases hrState with hrState | hrState <;>
    simp [checkSig, checkSigSetReady, checkSigCheckL, checkSigCheckR,
      checkSigSetResult, hlLabel, hlPath, hrLabel, hrPath,
      hlState, hrState]


/-! ## DISAPPEAR -/


/-- DISAPPEAR is inert when neither endpoint is toss and the initiator has no
p-carry.  The p fields themselves remain arbitrary in this generic lemma. -/
theorem disappear_quiet
    (l r : AgentState 2)
    (hlState : l.state = .congest ∨ l.state = .lock)
    (hrState : r.state = .congest ∨ r.state = .lock)
    (hlPCarry : l.p_carry = false) :
    disappear hpsi2 l r = (l, r) := by
  rcases hlState with hlState | hlState <;>
    rcases hrState with hrState | hrState <;>
      simp [disappear, hlState, hrState, hlPCarry]


theorem disappear_AB
    (l r : AgentState 2)
    (hl : AQuiet l) (hr : BQuiet r) :
    disappear hpsi2 l r = (l, r) := by
  unfold AQuiet at hl
  unfold BQuiet at hr
  rcases hl with
    ⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩
  rcases hr with
    ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  exact disappear_quiet l r hlState (Or.inl hrState) hlPCarry


theorem disappear_BA
    (l r : AgentState 2)
    (hl : BQuiet l) (hr : AQuiet r) :
    disappear hpsi2 l r = (l, r) := by
  unfold BQuiet at hl
  unfold AQuiet at hr
  rcases hl with
    ⟨hlLabel, hlPath, hlPath2, hlP, hlPCarry, hlState⟩
  rcases hr with
    ⟨hrLabel, hrPath, hrPath2, hrP, hrPCarry, hrState⟩
  exact disappear_quiet l r (Or.inl hlState) hrState hlPCarry


/-! ## Four-stage composition -/


/-- Strongest A->B middle-chain frame: the whole pair is definitionally
unchanged after the four requested stages. -/
theorem middle_AB_eq
    (l r : AgentState 2)
    (hl : AQuiet l) (hr : BQuiet r) :
    middleBeforeCompare l r = (l, r) := by
  simp [middleBeforeCompare,
    eliminateSig_AB l r hl hr,
    sigMove_AB l r hl hr,
    checkSig_AB l r hl hr,
    disappear_AB l r hl hr]


/-- Strongest B->A middle-chain frame. -/
theorem middle_BA_eq
    (l r : AgentState 2)
    (hl : BQuiet l) (hr : AQuiet r) :
    middleBeforeCompare l r = (l, r) := by
  simp [middleBeforeCompare,
    eliminateSig_BA l r hl hr,
    sigMove_BA l r hl hr,
    checkSig_BA l r hl hr,
    disappear_BA l r hl hr]


/-- Full protected A->B frame, ready to feed COMPARE.  Because the result is
the exact input pair, this preserves every field, not only the fields named in
AProtected/BProtected. -/
theorem middle_AB_protected
    (leaderBit : Bool) (bulletVal : Fin 3)
    (l r : AgentState 2)
    (hl : AProtected leaderBit l)
    (hr : BProtected bulletVal r) :
    let q := middleBeforeCompare l r
    q = (l, r) ∧
      AProtected leaderBit q.1 ∧
      BProtected bulletVal q.2 := by
  have hlQuiet : AQuiet l := hl.1
  have hrQuiet : BQuiet r := hr.1
  have hq : middleBeforeCompare l r = (l, r) :=
    middle_AB_eq l r hlQuiet hrQuiet
  dsimp only
  rw [hq]
  exact ⟨rfl, hl, hr⟩


/-- Full protected B->A frame, ready to feed COMPARE. -/
theorem middle_BA_protected
    (leaderBit : Bool) (bulletVal : Fin 3)
    (l r : AgentState 2)
    (hl : BProtected bulletVal l)
    (hr : AProtected leaderBit r) :
    let q := middleBeforeCompare l r
    q = (l, r) ∧
      BProtected bulletVal q.1 ∧
      AProtected leaderBit q.2 := by
  have hlQuiet : BQuiet l := hl.1
  have hrQuiet : AQuiet r := hr.1
  have hq : middleBeforeCompare l r = (l, r) :=
    middle_BA_eq l r hlQuiet hrQuiet
  dsimp only
  rw [hq]
  exact ⟨rfl, hl, hr⟩


/-! Site-specialized protected headlines.  These are just the four physical
role combinations in ReversedCore; no omitted field is specialized. -/


theorem middle_A0_B1_protected
    (l r : AgentState 2)
    (hl : AProtected true l)
    (hr : BProtected (2 : Fin 3) r) :
    let q := middleBeforeCompare l r
    q = (l, r) ∧
      AProtected true q.1 ∧
      BProtected (2 : Fin 3) q.2 :=
  middle_AB_protected true (2 : Fin 3) l r hl hr


theorem middle_B1_A2_protected
    (l r : AgentState 2)
    (hl : BProtected (2 : Fin 3) l)
    (hr : AProtected false r) :
    let q := middleBeforeCompare l r
    q = (l, r) ∧
      BProtected (2 : Fin 3) q.1 ∧
      AProtected false q.2 :=
  middle_BA_protected false (2 : Fin 3) l r hl hr


theorem middle_A2_B3_protected
    (l r : AgentState 2)
    (hl : AProtected false l)
    (hr : BProtected (0 : Fin 3) r) :
    let q := middleBeforeCompare l r
    q = (l, r) ∧
      AProtected false q.1 ∧
      BProtected (0 : Fin 3) q.2 :=
  middle_AB_protected false (0 : Fin 3) l r hl hr


theorem middle_B3_A0_protected
    (l r : AgentState 2)
    (hl : BProtected (0 : Fin 3) l)
    (hr : AProtected true r) :
    let q := middleBeforeCompare l r
    q = (l, r) ∧
      BProtected (0 : Fin 3) q.1 ∧
      AProtected true q.2 :=
  middle_BA_protected true (0 : Fin 3) l r hl hr


end ZZSafeN4ReversedMiddleGPT


#print axioms ZZSafeN4ReversedMiddleGPT.eliminateSig_quiet
#print axioms ZZSafeN4ReversedMiddleGPT.sigMove_quiet
#print axioms ZZSafeN4ReversedMiddleGPT.checkSig_AB
#print axioms ZZSafeN4ReversedMiddleGPT.checkSig_BA
#print axioms ZZSafeN4ReversedMiddleGPT.disappear_quiet
#print axioms ZZSafeN4ReversedMiddleGPT.middle_AB_eq
#print axioms ZZSafeN4ReversedMiddleGPT.middle_BA_eq
#print axioms ZZSafeN4ReversedMiddleGPT.middle_AB_protected
#print axioms ZZSafeN4ReversedMiddleGPT.middle_BA_protected
#print axioms ZZSafeN4ReversedMiddleGPT.middle_A0_B1_protected
#print axioms ZZSafeN4ReversedMiddleGPT.middle_B1_A2_protected
#print axioms ZZSafeN4ReversedMiddleGPT.middle_A2_B3_protected
#print axioms ZZSafeN4ReversedMiddleGPT.middle_B3_A0_protected
