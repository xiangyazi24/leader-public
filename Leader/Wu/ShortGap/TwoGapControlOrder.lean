import Leader.Wu.ShortGap.BoundaryLeaseArbitration
import Std.Tactic

/-!
# Acyclic control order for one two-gap attempt

This file isolates the control dependency which prevents the provisional
two-gap protocol from becoming a dining-philosophers lock cycle.

On the losing side, the first deposited denial changes the actor root
irreversibly to `ABORTING`.  That root-visible decision has two independent
successors:

* return a retirement witness to the gap on which the actor lost; and
* clean any provisional grant on the actor's other gap.

Only the first successor is a prerequisite of the winning gap's `FINAL`.
Finalization never waits for the loser's other-gap cleanup.  On the winning
side, two provisional deposits are joined before either `WIN` is sent.  The
two branches meet at `gapFinal`; final delivery then permits `HOLD`.

This is a finite semantic control quotient, not the literal carrier.  It
proves that the intended prerequisite graph has no wait SCC and records the
guard that the later four-block refinement must preserve.
-/

namespace TwoGapControlOrder

open BoundaryLeaseArbitration

/-- Persistent semantic services for one side of a fixed arbitration attempt.
`abortOtherGrant` and `freeClean` are deliberately a side branch rather than
predecessors of `gapFinal`. -/
inductive Service where
  | denialDeposit
  | enterAborting
  | retirementDeposit
  | abortOtherGrant
  | freeClean
  | twoProvisionalDeposits
  | enterWinning
  | winDeposit
  | gapFinal
  | finalDeposit
  | hold
  deriving DecidableEq, Repr

/-- `Before a b` means that service `a` is an immediate semantic prerequisite
of service `b`. -/
inductive Before : Service -> Service -> Prop where
  | denial_decides : Before .denialDeposit .enterAborting
  | abort_publishes_retirement : Before .enterAborting .retirementDeposit
  | abort_starts_other_cleanup : Before .enterAborting .abortOtherGrant
  | other_cleanup_finishes : Before .abortOtherGrant .freeClean
  | provisional_join_decides :
      Before .twoProvisionalDeposits .enterWinning
  | winner_sends_win : Before .enterWinning .winDeposit
  | win_allows_final : Before .winDeposit .gapFinal
  | retirement_allows_final : Before .retirementDeposit .gapFinal
  | final_returns : Before .gapFinal .finalDeposit
  | two_returned_finals_allow_hold : Before .finalDeposit .hold

/-- A rank certificate for the prerequisite DAG.  Equal ranks are allowed on
independent branches; every declared edge is strictly increasing. -/
def rank : Service -> Nat
  | .denialDeposit => 0
  | .twoProvisionalDeposits => 0
  | .enterAborting => 1
  | .enterWinning => 1
  | .retirementDeposit => 2
  | .abortOtherGrant => 2
  | .winDeposit => 2
  | .freeClean => 3
  | .gapFinal => 3
  | .finalDeposit => 4
  | .hold => 5

theorem before_rank_lt {a b : Service} (edge : Before a b) :
    rank a < rank b := by
  cases edge <;> decide

/-- Nonempty transitive closure, kept local so its rank proof has no library
orientation ambiguity. -/
inductive BeforePlus : Service -> Service -> Prop where
  | single {a b : Service} : Before a b -> BeforePlus a b
  | tail {a b c : Service} : Before a b -> BeforePlus b c -> BeforePlus a c

theorem beforePlus_rank_lt {a b : Service} (path : BeforePlus a b) :
    rank a < rank b := by
  induction path with
  | single edge => exact before_rank_lt edge
  | tail edge _ ih => exact Nat.lt_trans (before_rank_lt edge) ih

/-- The semantic wait graph contains no directed cycle. -/
theorem beforePlus_irrefl (service : Service) :
    ¬ BeforePlus service service := by
  intro cycle
  exact (Nat.lt_irrefl (rank service)) (beforePlus_rank_lt cycle)

/-- `FINAL` consumes exactly the winner's `WIN` and the loser's root-visible
retirement witness.  Completion of the loser's other-gap cleanup is not a
guard. -/
theorem immediate_before_gapFinal {service : Service}
    (edge : Before service .gapFinal) :
    service = .winDeposit ∨ service = .retirementDeposit := by
  cases edge with
  | win_allows_final => exact Or.inl rfl
  | retirement_allows_final => exact Or.inr rfl

theorem abortOtherGrant_not_before_gapFinal :
    ¬ Before .abortOtherGrant .gapFinal := by
  intro edge
  cases edge

theorem freeClean_not_before_gapFinal :
    ¬ Before .freeClean .gapFinal := by
  intro edge
  cases edge

/-- The two control facts used at a winning actor: both adjacent contenders
have an immediately available abort decision, and neither decision depends on
the contender's exterior gap orientation. -/
theorem winner_opens_both_retirement_branches
    (outerLeft leftGap rightGap outerRight : GrantRight)
    (winner : MaySendWin leftGap rightGap) :
    MustAbort outerLeft leftGap /\ MustAbort rightGap outerRight :=
  winner_has_local_retirement_frontier
    outerLeft leftGap rightGap outerRight winner

/-! ## Root-last two-side cleanup -/

inductive GapSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Constant two-bit obligation mask stored by an aborting or releasing actor
root.  A side remains pending until its gap accepts retirement/release or a
touching committed transition consumes that exact gap phase. -/
structure SideObligations where
  leftPending : Bool
  rightPending : Bool
  deriving DecidableEq, Repr

def SideObligations.discharge
    (obligations : SideObligations) (side : GapSide) : SideObligations :=
  match side with
  | .left => { obligations with leftPending := false }
  | .right => { obligations with rightPending := false }

def SideObligations.rootMayErase (obligations : SideObligations) : Prop :=
  obligations.leftPending = false /\ obligations.rightPending = false

/-- Completing or consuming the left gap never masks a pending right-side
retirement. -/
theorem discharge_left_preserves_right
    (obligations : SideObligations) :
    (obligations.discharge .left).rightPending =
      obligations.rightPending := rfl

theorem discharge_right_preserves_left
    (obligations : SideObligations) :
    (obligations.discharge .right).leftPending =
      obligations.leftPending := rfl

theorem root_cannot_erase_with_left_pending
    (obligations : SideObligations)
    (pending : obligations.leftPending = true) :
    ¬ obligations.rootMayErase := by
  intro erasable
  simp [SideObligations.rootMayErase, pending] at erasable

theorem root_cannot_erase_with_right_pending
    (obligations : SideObligations)
    (pending : obligations.rightPending = true) :
    ¬ obligations.rootMayErase := by
  intro erasable
  simp [SideObligations.rootMayErase, pending] at erasable

/-- After both side-specific acknowledgments, root-last cleanup is enabled in
either discharge order. -/
theorem discharge_both_rootMayErase (obligations : SideObligations) :
    ((obligations.discharge .left).discharge .right).rootMayErase /\
      ((obligations.discharge .right).discharge .left).rootMayErase := by
  cases obligations
  simp [SideObligations.discharge, SideObligations.rootMayErase]

end TwoGapControlOrder

#print axioms TwoGapControlOrder.before_rank_lt
#print axioms TwoGapControlOrder.beforePlus_irrefl
#print axioms TwoGapControlOrder.immediate_before_gapFinal
#print axioms TwoGapControlOrder.winner_opens_both_retirement_branches
#print axioms TwoGapControlOrder.discharge_left_preserves_right
#print axioms TwoGapControlOrder.root_cannot_erase_with_right_pending
#print axioms TwoGapControlOrder.discharge_both_rootMayErase
