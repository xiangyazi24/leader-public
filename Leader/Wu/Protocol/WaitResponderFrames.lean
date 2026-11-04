import Leader.Wu.Protocol.WaitStaged

set_option autoImplicit false
set_option Elab.async false

namespace ZZStep3

open PPLL

/-!
# C5 step 3: the WAIT responder frames

Three earlier rounds attacked these directly and left the same residual every
time.  The cause was not the statements, which a kernel sweep over every
guard-relevant configuration at psi = 2 confirmed
(`Leader.ZZWaitProbe2.wait_frames_hold_psi2`).  The cause was that `wait`
contains three `let (l, r) := if c then (a, b) else (l, r)` bindings, and such a
binding desugars to a `match` whose auxiliary matcher sits *outside* its own
`if`.  `split` therefore targets the matcher, generalises the discriminant into
a fresh pair and strands every usable fact in an unused equation.

`Leader/Wu/Protocol/WaitStaged.lean` removes the obstruction at the source by splitting
`wait` into six stages that each return a pair directly, bridging with
`wait_eq_staged := by rfl`, and carrying the eight tracked fields through a
single projection tuple.  This file is now a thin consumer of that work.
-/

theorem wait_right_label
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).2.label = r.label :=
  (ZZWaitStaged.wait_label hψ κ l r).2

theorem wait_right_state
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).2.state = r.state :=
  (ZZWaitStaged.wait_state hψ κ l r).2

theorem wait_right_path
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).2.path = r.path :=
  (ZZWaitStaged.wait_path hψ κ l r).2

/-- The left endpoint is framed too, which step 3 also needs. -/
theorem wait_left_label
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).1.label = l.label :=
  (ZZWaitStaged.wait_label hψ κ l r).1

theorem wait_left_state
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).1.state = l.state :=
  (ZZWaitStaged.wait_state hψ κ l r).1

theorem wait_left_path
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).1.path = l.path :=
  (ZZWaitStaged.wait_path hψ κ l r).1

#print axioms wait_right_label
#print axioms wait_right_state
#print axioms wait_right_path
#print axioms wait_left_label
#print axioms wait_left_state
#print axioms wait_left_path

end ZZStep3
