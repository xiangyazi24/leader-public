/-!
# Positive-gap componentwise-projection obstruction

A pairwise interaction changes only its two physical endpoints.  Consequently,
if an abstract role is read componentwise from one agent's local state, an
interaction at the remote end of a positive-length carrier corridor cannot
change the source's abstract role.

This does not rule out a history-free *global* projection.  In particular, a
completed corridor certificate may make the remote source abstractly visible
as `S` even while its physical root state is unchanged.  It only rules out the
stronger componentwise refinement used by the first positive-gap sketches.
-/

namespace PositiveGapLocalProjectionNoGo

/-- One physical pairwise step, with the standard frame property away from the
two interacting agents. -/
structure PairStep (Node State : Type) where
  before : Node → State
  after : Node → State
  left : Node
  right : Node
  outside_eq : ∀ x, x ≠ left → x ≠ right → after x = before x

/-- A componentwise abstraction reads the abstract role of an agent from that
agent's current local state only. -/
def localView {Node State Role : Type}
    (project : State → Role) (config : Node → State) (x : Node) : Role :=
  project (config x)

/-- A physical pairwise step preserves every componentwise abstract role away
from the two scheduled endpoints. -/
theorem localView_eq_of_outside
    {Node State Role : Type}
    (project : State → Role) (step : PairStep Node State) (source : Node)
    (hleft : source ≠ step.left) (hright : source ≠ step.right) :
    localView project step.after source =
      localView project step.before source := by
  unfold localView
  rw [step.outside_eq source hleft hright]

/-- If the source is outside a target-boundary interaction, that interaction
cannot be the atomic `U -> S` event of a componentwise refinement. -/
theorem targetBoundary_cannot_change_remote_source
    {Node State Role : Type}
    (project : State → Role) (step : PairStep Node State)
    (source : Node) (U S : Role)
    (hleft : source ≠ step.left) (hright : source ≠ step.right)
    (hbefore : localView project step.before source = U)
    (hafter : localView project step.after source = S)
    (hne : U ≠ S) : False := by
  apply hne
  calc
    U = localView project step.before source := hbefore.symm
    _ = localView project step.after source :=
      (localView_eq_of_outside project step source hleft hright).symm
    _ = S := hafter

/-- The same obstruction specialized to a named target-boundary edge.  The
only geometric facts needed are that a positive gap separates the source from
both endpoints of that physical edge. -/
theorem positiveGap_targetCommit_no_componentwise_linearization
    {Node State Role : Type}
    (project : State → Role) (step : PairStep Node State)
    (source carrier target : Node) (U S : Role)
    (hleft : step.left = carrier) (hright : step.right = target)
    (hsourceCarrier : source ≠ carrier)
    (hsourceTarget : source ≠ target)
    (hbefore : localView project step.before source = U)
    (hafter : localView project step.after source = S)
    (hne : U ≠ S) : False := by
  apply targetBoundary_cannot_change_remote_source
      project step source U S
  · simpa [hleft] using hsourceCarrier
  · simpa [hright] using hsourceTarget
  · exact hbefore
  · exact hafter
  · exact hne

/-- The specialization used by the current five-pass candidate: an Ack2 turn
at the source boundary cannot simultaneously change the remote target from
`U` to `T` under a componentwise projection. -/
theorem positiveGap_sourceAck_no_componentwise_linearization
    {Node State Role : Type}
    (project : State → Role) (step : PairStep Node State)
    (source carrier target : Node) (U T : Role)
    (hleft : step.left = source) (hright : step.right = carrier)
    (htargetSource : target ≠ source)
    (htargetCarrier : target ≠ carrier)
    (hbefore : localView project step.before target = U)
    (hafter : localView project step.after target = T)
    (hne : U ≠ T) : False := by
  apply targetBoundary_cannot_change_remote_source
      project step target U T
  · simpa [hleft] using htargetSource
  · simpa [hright] using htargetCarrier
  · exact hbefore
  · exact hafter
  · exact hne

#print axioms localView_eq_of_outside
#print axioms positiveGap_targetCommit_no_componentwise_linearization
#print axioms positiveGap_sourceAck_no_componentwise_linearization

end PositiveGapLocalProjectionNoGo
