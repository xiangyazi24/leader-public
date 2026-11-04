import Leader.Wu.Protocol.Algorithm
import Leader.Wu.Safety.ReversedPathWriterLeaders

set_option autoImplicit false

namespace ZZSafeN4WriterViewGPT

open PPLL

def hpsi2 : 0 < 2 := by decide

structure WriterProtectedView where
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

namespace WriterProtectedView

def ofState (u : AgentState 2) : WriterProtectedView :=
  ⟨u.label, u.probe, u.phase, u.path, u.path2, u.p, u.p_carry,
    u.state, u.signal_B, u.bullet, u.shield, u.path4, u.path5⟩

theorem ext (a b : WriterProtectedView)
    (h1 : a.label = b.label) (h2 : a.probe = b.probe)
    (h3 : a.phase = b.phase) (h4 : a.path = b.path)
    (h5 : a.path2 = b.path2) (h6 : a.p = b.p)
    (h7 : a.p_carry = b.p_carry) (h8 : a.state = b.state)
    (h9 : a.signal_B = b.signal_B) (h10 : a.bullet = b.bullet)
    (h11 : a.shield = b.shield) (h12 : a.path4 = b.path4)
    (h13 : a.path5 = b.path5) : a = b := by
  cases a
  cases b
  simp_all

end WriterProtectedView

def pairView (q : AgentState 2 × AgentState 2) :
    WriterProtectedView × WriterProtectedView :=
  (WriterProtectedView.ofState q.1, WriterProtectedView.ofState q.2)

private theorem groupInfoStart_view (l r : AgentState 2) :
    pairView (groupInfoStart hpsi2 l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState groupInfoStart
    try dsimp only
    repeat (first | rfl | split)

private theorem groupInfoSet_view (l r : AgentState 2) :
    pairView (groupInfoSet hpsi2 l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState groupInfoSet
    try dsimp only
    repeat (first | rfl | split)

private theorem groupInfoUnset_view (l r : AgentState 2) :
    pairView (groupInfoUnset l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState groupInfoUnset
    try dsimp only
    repeat (first | rfl | split)

theorem groupInfo_view (l r : AgentState 2) :
    pairView (groupInfo hpsi2 l r) = pairView (l, r) := by
  rw [groupInfo_eq_staged hpsi2 l r]
  let q0 := groupInfoStart hpsi2 l r
  let q1 := groupInfoSet hpsi2 q0.1 q0.2
  change pairView (groupInfoUnset q1.1 q1.2) = pairView (l, r)
  exact (groupInfoUnset_view q1.1 q1.2).trans
    ((groupInfoSet_view q0.1 q0.2).trans (groupInfoStart_view l r))

private theorem gensigStart_view (l r : AgentState 2) :
    pairView (gensigWriteseqStart hpsi2 l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState gensigWriteseqStart
    try dsimp only
    repeat (first | rfl | split)

private theorem gensigEmit_view (l r : AgentState 2) :
    pairView (gensigWriteseqEmit hpsi2 l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState gensigWriteseqEmit
    try dsimp only
    repeat (first | rfl | split)

private theorem gensigPropagate_view (l r : AgentState 2) :
    pairView (gensigWriteseqPropagate hpsi2 l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState gensigWriteseqPropagate
    try dsimp only
    repeat (first | rfl | split)

private theorem gensigFinish_view (l r : AgentState 2) :
    pairView (gensigWriteseqFinish hpsi2 l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState gensigWriteseqFinish
    try dsimp only
    repeat (first | rfl | split)

theorem gensigWriteseq_view (l r : AgentState 2) :
    pairView (gensigWriteseq hpsi2 l r) = pairView (l, r) := by
  rw [gensigWriteseq_eq_staged hpsi2 l r]
  let q0 := gensigWriteseqStart hpsi2 l r
  let q1 := gensigWriteseqEmit hpsi2 q0.1 q0.2
  let q2 := gensigWriteseqPropagate hpsi2 q1.1 q1.2
  change pairView (gensigWriteseqFinish hpsi2 q2.1 q2.2) =
    pairView (l, r)
  exact (gensigFinish_view q2.1 q2.2).trans
    ((gensigPropagate_view q1.1 q1.2).trans
      ((gensigEmit_view q0.1 q0.2).trans (gensigStart_view l r)))

theorem writeSeqLeaderMove_view (l r : AgentState 2) :
    pairView (writeSeqLeaderMove hpsi2 l r) = pairView (l, r) := by
  apply Prod.ext <;> apply WriterProtectedView.ext
  all_goals
    unfold pairView WriterProtectedView.ofState writeSeqLeaderMove
    try dsimp only
    repeat (first | rfl | split)

end ZZSafeN4WriterViewGPT

#print axioms ZZSafeN4WriterViewGPT.groupInfo_view
#print axioms ZZSafeN4WriterViewGPT.gensigWriteseq_view
#print axioms ZZSafeN4WriterViewGPT.writeSeqLeaderMove_view
