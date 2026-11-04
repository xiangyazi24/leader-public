import Std.Tactic

/-!
# Work-conserving serializer for a shared root mover

One leader root is simultaneously the actor endpoint of its counterclockwise
gap and the owner of its clockwise gap.  Those two producers share one physical
mover.  Each producer has a one-entry stop-and-wait inbox; `turn` selects the
preferred inbox when both are occupied and falls through when it is empty.

`dispatch` models only an instant at which the mover is home.  It removes the
selected pending message and flips preference.  The theorems below show that
an initially pending side is selected within two home dispatches, and that two
dispatches drain all initially pending work if neither producer enqueues a new
message.  Long-range mover return, malformed residue cleanup, and interaction-
level nonmasking remain separate physical obligations.
-/

namespace TwoInboxSerializer

inductive Side where
  | actor
  | gapOwner
  deriving DecidableEq, Repr

structure State where
  actorPending : Bool
  gapPending : Bool
  turn : Side
  deriving DecidableEq, Repr

/-- Select one pending producer, preferring `turn` but never idling while the
other producer is pending. -/
def choose (state : State) : Option Side :=
  match state.turn with
  | .actor =>
      if state.actorPending then some .actor
      else if state.gapPending then some .gapOwner else none
  | .gapOwner =>
      if state.gapPending then some .gapOwner
      else if state.actorPending then some .actor else none

/-- One home dispatch deposits the selected message into the shared mover and
gives the other producer first preference when the mover next returns. -/
def dispatch (state : State) : State :=
  match choose state with
  | none => state
  | some .actor =>
      { state with actorPending := false, turn := .gapOwner }
  | some .gapOwner =>
      { state with gapPending := false, turn := .actor }

def pendingCount (state : State) : Nat :=
  (if state.actorPending then 1 else 0) +
    (if state.gapPending then 1 else 0)

theorem choose_eq_none_iff (state : State) :
    choose state = none <->
      state.actorPending = false /\ state.gapPending = false := by
  rcases state with ⟨actorPending, gapPending, turn⟩
  cases actorPending <;> cases gapPending <;> cases turn <;>
    simp [choose]

/-- A home dispatch consumes exactly one pending inbox whenever work exists. -/
theorem pendingCount_dispatch
    (state : State) (work : choose state ≠ none) :
    pendingCount (dispatch state) + 1 = pendingCount state := by
  rcases state with ⟨actorPending, gapPending, turn⟩
  cases actorPending <;> cases gapPending <;> cases turn <;>
    simp [choose, dispatch, pendingCount] at work ⊢

/-- Actor-side traffic cannot be masked by a continuously preferred gap-owner
message: it is selected now or immediately after that one message. -/
theorem actor_selected_within_two
    (state : State) (pending : state.actorPending = true) :
    choose state = some .actor \/
      (choose state = some .gapOwner /\
        choose (dispatch state) = some .actor) := by
  rcases state with ⟨actorPending, gapPending, turn⟩
  cases actorPending <;> cases gapPending <;> cases turn <;>
    simp [choose, dispatch] at pending ⊢

/-- Symmetric nonmasking for gap-owner traffic. -/
theorem gapOwner_selected_within_two
    (state : State) (pending : state.gapPending = true) :
    choose state = some .gapOwner \/
      (choose state = some .actor /\
        choose (dispatch state) = some .gapOwner) := by
  rcases state with ⟨actorPending, gapPending, turn⟩
  cases actorPending <;> cases gapPending <;> cases turn <;>
    simp [choose, dispatch] at pending ⊢

/-- With stop-and-wait producers and no intervening enqueue, two returns of the
shared mover drain both initially occupied inboxes. -/
theorem dispatch_twice_clears (state : State) :
    (dispatch (dispatch state)).actorPending = false /\
      (dispatch (dispatch state)).gapPending = false := by
  rcases state with ⟨actorPending, gapPending, turn⟩
  cases actorPending <;> cases gapPending <;> cases turn <;>
    simp [choose, dispatch]

end TwoInboxSerializer

#print axioms TwoInboxSerializer.choose_eq_none_iff
#print axioms TwoInboxSerializer.pendingCount_dispatch
#print axioms TwoInboxSerializer.actor_selected_within_two
#print axioms TwoInboxSerializer.gapOwner_selected_within_two
#print axioms TwoInboxSerializer.dispatch_twice_clears
