import Leader.Wu.Safety.Counterexamples
import Leader.Wu.Scheduler.BoundedToRepairedLift


set_option autoImplicit false
set_option Elab.async false


namespace ZZSafeN4ReversedCompareGPT


open PPLL


theorem hpsi2 : 0 < 2 := by
  decide


def ring4 : DirectedRing 4 :=
  PPLLCounterexample.ring4


abbrev Raw : PopulationProtocol :=
  PPLLRepair.protocol hpsi2 10


/-- Exactly the coordinates requested to be framed by the COMPARE slice.
The exact pair equalities below are stronger: they frame every non-state field. -/
def ProtectedFrame (before after : AgentState 2) : Prop :=
  after.leader = before.leader ∧
  after.label = before.label ∧
  after.probe = before.probe ∧
  after.phase = before.phase ∧
  after.p = before.p ∧
  after.p_carry = before.p_carry ∧
  after.signal_B = before.signal_B ∧
  after.bullet = before.bullet ∧
  after.shield = before.shield ∧
  after.path4 = before.path4 ∧
  after.path5 = before.path5


/-!
AB orientation:
  left  = label 0, path some 1 0, state congest or lock, path2 none
  right = label 1, path some 0 0, state congest,         path2 none


At label 0, cmpUpdate first writes the left state to congest.
For psi = 2 that left label is not terminal, so cmpUpdatePropagate reaches
the congest/lock propagation branch and writes right.state := congest.
cmpUpdateSetPath2 is inert because the left state is not compare2, and
compareSigDispatch is the identity because both path2 fields remain none.
-/
theorem compareSig_AB_exact
    (l r : AgentState 2)
    (hlLabel : l.label = 0)
    (hlPath : l.path = .some 1 0)
    (hlState : l.state = .congest ∨ l.state = .lock)
    (hlPath2 : l.path2 = none)
    (hrLabel : r.label = 1)
    (hrPath : r.path = .some 0 0)
    (hrState : r.state = .congest)
    (hrPath2 : r.path2 = none) :
    compareSig hpsi2 l r =
      ({ l with state := .congest },
       { r with state := .congest }) := by
  rcases hlState with hlState | hlState
  · simp [compareSig, compareSigInit, cmpUpdate, cmpUpdatePropagate,
      cmpUpdateSetPath2, compareSigDispatch,
      hlLabel, hlPath, hlState, hlPath2,
      hrLabel, hrPath, hrState, hrPath2]
  · simp [compareSig, compareSigInit, cmpUpdate, cmpUpdatePropagate,
      cmpUpdateSetPath2, compareSigDispatch,
      hlLabel, hlPath, hlState, hlPath2,
      hrLabel, hrPath, hrState, hrPath2]


/-!
BA orientation:
  left  = label 1, path some 0 0, state congest,         path2 none
  right = label 0, path some 1 0, state congest or lock, path2 none


For psi = 2, left label 1 is terminal. Because left.state = congest,
the first branch of cmpUpdatePropagate fires and writes right.state := lock.
The left endpoint is unchanged. cmpUpdateSetPath2 is inert, and dispatch is
again the identity because both path2 fields are none.
-/
theorem compareSig_BA_exact
    (l r : AgentState 2)
    (hlLabel : l.label = 1)
    (hlPath : l.path = .some 0 0)
    (hlState : l.state = .congest)
    (hlPath2 : l.path2 = none)
    (hrLabel : r.label = 0)
    (hrPath : r.path = .some 1 0)
    (hrState : r.state = .congest ∨ r.state = .lock)
    (hrPath2 : r.path2 = none) :
    compareSig hpsi2 l r =
      (l, { r with state := .lock }) := by
  rcases hrState with hrState | hrState
  · simp [compareSig, compareSigInit, cmpUpdate, cmpUpdatePropagate,
      cmpUpdateSetPath2, compareSigDispatch,
      hlLabel, hlPath, hlState, hlPath2,
      hrLabel, hrPath, hrState, hrPath2]
  · simp [compareSig, compareSigInit, cmpUpdate, cmpUpdatePropagate,
      cmpUpdateSetPath2, compareSigDispatch,
      hlLabel, hlPath, hlState, hlPath2,
      hrLabel, hrPath, hrState, hrPath2]


/-- Expanded AB consequence for direct invariant bookkeeping. -/
theorem compareSig_AB_protected
    (l r : AgentState 2)
    (hlLabel : l.label = 0)
    (hlPath : l.path = .some 1 0)
    (hlState : l.state = .congest ∨ l.state = .lock)
    (hlPath2 : l.path2 = none)
    (hrLabel : r.label = 1)
    (hrPath : r.path = .some 0 0)
    (hrState : r.state = .congest)
    (hrPath2 : r.path2 = none) :
    let q := compareSig hpsi2 l r
    q.1.state = .congest ∧
    q.2.state = .congest ∧
    q.1.path = .some 1 0 ∧
    q.2.path = .some 0 0 ∧
    q.1.path2 = none ∧
    q.2.path2 = none ∧
    ProtectedFrame l q.1 ∧
    ProtectedFrame r q.2 := by
  rw [compareSig_AB_exact l r
    hlLabel hlPath hlState hlPath2
    hrLabel hrPath hrState hrPath2]
  simp [ProtectedFrame, hlPath, hrPath, hlPath2, hrPath2]


/-- Expanded BA consequence for direct invariant bookkeeping. -/
theorem compareSig_BA_protected
    (l r : AgentState 2)
    (hlLabel : l.label = 1)
    (hlPath : l.path = .some 0 0)
    (hlState : l.state = .congest)
    (hlPath2 : l.path2 = none)
    (hrLabel : r.label = 0)
    (hrPath : r.path = .some 1 0)
    (hrState : r.state = .congest ∨ r.state = .lock)
    (hrPath2 : r.path2 = none) :
    let q := compareSig hpsi2 l r
    q.1.state = .congest ∧
    q.2.state = .lock ∧
    q.1.path = .some 0 0 ∧
    q.2.path = .some 1 0 ∧
    q.1.path2 = none ∧
    q.2.path2 = none ∧
    ProtectedFrame l q.1 ∧
    ProtectedFrame r q.2 := by
  rw [compareSig_BA_exact l r
    hlLabel hlPath hlState hlPath2
    hrLabel hrPath hrState hrPath2]
  simp [ProtectedFrame, hlState, hlPath, hrPath, hlPath2, hrPath2]


end ZZSafeN4ReversedCompareGPT


#print axioms ZZSafeN4ReversedCompareGPT.compareSig_AB_exact
#print axioms ZZSafeN4ReversedCompareGPT.compareSig_BA_exact
#print axioms ZZSafeN4ReversedCompareGPT.compareSig_AB_protected
#print axioms ZZSafeN4ReversedCompareGPT.compareSig_BA_protected
