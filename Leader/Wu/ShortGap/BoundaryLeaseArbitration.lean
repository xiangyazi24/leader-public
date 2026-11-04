import Std.Tactic

/-!
# Boundary-lease arbitration for local-minimum deletion

Every eligible leader requests the leases on its two incident live gaps.  A
gap with requests from both endpoints grants exactly one endpoint.  We encode
`true` as a grant to the clockwise/right endpoint and `false` as a grant to
the counterclockwise/left endpoint.  A leader therefore wins precisely at a
`true, false` transition in the gap-orientation word.

This tiny combinatorial layer gives the physical transaction two facts which
do not depend on priority ties:

* adjacent leaders cannot both win, because their shared gap cannot grant in
  both directions; and
* every path component of eligible leaders has a winner, because its two
  uncontested exterior gaps point inward.

For a cyclic component, the same argument applies after any nonconstant
orientation is cut at a change.  The only no-winner words are the two uniform
orientations; the protocol retries those locally after every candidate has
received one grant and one denial.
-/

namespace BoundaryLeaseArbitration

/-- `true` grants the gap to its right endpoint; `false` grants it left. -/
abbrev GrantRight := Bool

/-- The middle leader owns both incident gap leases. -/
def Wins (leftGap rightGap : GrantRight) : Prop :=
  leftGap = true /\ rightGap = false

/-- Two adjacent leaders cannot both own their shared gap. -/
theorem adjacent_winners_false
    {leftGap sharedGap rightGap : GrantRight}
    (leftWins : Wins leftGap sharedGap)
    (rightWins : Wins sharedGap rightGap) : False := by
  simp only [Wins] at leftWins rightWins
  have impossible : true = false := rightWins.1.symm.trans leftWins.2
  cases impossible

/-- A linear orientation word contains a winning `true,false` transition. -/
inductive HasWinner : List GrantRight -> Prop
  | here (tail : List GrantRight) : HasWinner (true :: false :: tail)
  | there {a b : GrantRight} {tail : List GrantRight}
      (later : HasWinner (b :: tail)) : HasWinner (a :: b :: tail)

/-- Prepending an exterior orientation cannot destroy an existing winner. -/
theorem HasWinner.prepend {word : List GrantRight}
    (winner : HasWinner word) (head : GrantRight) :
    HasWinner (head :: word) := by
  cases winner with
  | here tail =>
      exact HasWinner.there (HasWinner.here tail)
  | @there a b tail later =>
      exact HasWinner.there (HasWinner.there later)

/-- A path of contenders has uncontested exterior leases pointing inward,
so every possible collection of internal grants leaves at least one winner. -/
theorem inward_path_has_winner (internal : List GrantRight) :
    HasWinner (true :: internal ++ [false]) := by
  induction internal with
  | nil =>
      exact HasWinner.here []
  | cons direction rest ih =>
      cases direction with
      | false =>
          exact HasWinner.here (rest ++ [false])
      | true =>
          exact HasWinner.prepend ih true

/-- No clockwise-to-counterclockwise transition occurs in a linear word. -/
def NoLinearWinner : List GrantRight -> Prop
  | [] => True
  | [_] => True
  | a :: b :: tail => ¬ Wins a b ∧ NoLinearWinner (b :: tail)

theorem noLinearWinner_of_not_hasWinner :
    ∀ word : List GrantRight, ¬ HasWinner word -> NoLinearWinner word := by
  intro word
  induction word with
  | nil =>
      simp [NoLinearWinner]
  | cons a tail ih =>
      cases tail with
      | nil =>
          simp [NoLinearWinner]
      | cons b rest =>
          intro noWinner
          constructor
          · intro wins
            rcases wins with ⟨rfl, rfl⟩
            exact noWinner (HasWinner.here rest)
          · exact ih fun later => noWinner (HasWinner.there later)

def AllTrue : List GrantRight -> Prop
  | [] => True
  | value :: tail => value = true ∧ AllTrue tail

theorem allTrue_of_noLinearWinner_true :
    ∀ tail : List GrantRight,
      NoLinearWinner (true :: tail) -> AllTrue tail := by
  intro tail
  induction tail with
  | nil =>
      simp [AllTrue]
  | cons value rest ih =>
      cases value with
      | false =>
          simp [NoLinearWinner, Wins]
      | true =>
          intro noLinear
          exact ⟨rfl, ih noLinear.2⟩

theorem replicate_true_of_allTrue :
    ∀ word : List GrantRight, AllTrue word ->
      ∃ count, word = List.replicate count true := by
  intro word
  induction word with
  | nil =>
      intro _
      exact ⟨0, rfl⟩
  | cons value tail ih =>
      intro allTrue
      rcases allTrue with ⟨rfl, tailTrue⟩
      rcases ih tailTrue with ⟨count, rfl⟩
      exact ⟨count + 1, by simp [List.replicate_succ]⟩

/-- A linear word without a winner consists of a false prefix followed by a
true suffix. -/
theorem noLinearWinner_normalForm :
    ∀ word : List GrantRight, NoLinearWinner word ->
      ∃ falseCount trueCount,
        word = List.replicate falseCount false ++
          List.replicate trueCount true := by
  intro word
  induction word with
  | nil =>
      intro _
      exact ⟨0, 0, rfl⟩
  | cons value tail ih =>
      intro noLinear
      cases value with
      | false =>
          have tailNoLinear : NoLinearWinner tail := by
            cases tail with
            | nil => simp [NoLinearWinner]
            | cons next rest => exact noLinear.2
          rcases ih tailNoLinear with ⟨falseCount, trueCount, rfl⟩
          exact ⟨falseCount + 1, trueCount, by
            simp [List.replicate_succ]⟩
      | true =>
          have tailTrue := allTrue_of_noLinearWinner_true tail noLinear
          rcases replicate_true_of_allTrue tail tailTrue with ⟨trueCount, rfl⟩
          exact ⟨0, trueCount + 1, by simp [List.replicate_succ]⟩

/-- The second disjunct exposes a cyclic winner across the last/first cut. -/
def WrapWinner (word : List GrantRight) : Prop :=
  ∃ falseCount trueCount,
    word = List.replicate (falseCount + 1) false ++
      List.replicate (trueCount + 1) true

def CyclicWinner (word : List GrantRight) : Prop :=
  HasWinner word ∨ WrapWinner word

def Uniform (word : List GrantRight) : Prop :=
  (∃ count, word = List.replicate count false) ∨
    (∃ count, word = List.replicate count true)

/-- Every finite cyclic grant word either has a winner or is uniform. -/
theorem cyclicWinner_or_uniform (word : List GrantRight) :
    CyclicWinner word ∨ Uniform word := by
  by_cases winner : HasWinner word
  · exact Or.inl (Or.inl winner)
  · rcases noLinearWinner_normalForm word
      (noLinearWinner_of_not_hasWinner word winner) with
      ⟨falseCount, trueCount, normal⟩
    cases falseCount with
    | zero =>
        exact Or.inr (Or.inr ⟨trueCount, by simpa using normal⟩)
    | succ falseCount =>
        cases trueCount with
        | zero =>
            exact Or.inr (Or.inl ⟨falseCount + 1, by simpa using normal⟩)
        | succ trueCount =>
            exact Or.inl (Or.inr ⟨falseCount, trueCount, by simpa using normal⟩)

theorem uniform_of_no_cyclicWinner {word : List GrantRight}
    (noWinner : ¬ CyclicWinner word) : Uniform word :=
  (cyclicWinner_or_uniform word).resolve_left noWinner

/-! ## Provisional-receipt join -/

inductive EndpointResult where
  | provisional
  | denied
  deriving DecidableEq, Repr

/-- Result seen by the right endpoint of its left incident gap. -/
def leftResult (leftGap : GrantRight) : EndpointResult :=
  if leftGap then .provisional else .denied

/-- Result seen by the left endpoint of its right incident gap. -/
def rightResult (rightGap : GrantRight) : EndpointResult :=
  if rightGap then .denied else .provisional

def MaySendWin (leftGap rightGap : GrantRight) : Prop :=
  leftResult leftGap = .provisional /\
    rightResult rightGap = .provisional

def MustAbort (leftGap rightGap : GrantRight) : Prop :=
  leftResult leftGap = .denied \/
    rightResult rightGap = .denied

/-- The actor may join two provisional receipts exactly when it owns both
incident gap orientations. -/
theorem maySendWin_iff_wins (leftGap rightGap : GrantRight) :
    MaySendWin leftGap rightGap <-> Wins leftGap rightGap := by
  cases leftGap <;> cases rightGap <;>
    simp [MaySendWin, Wins, leftResult, rightResult]

/-- After both results arrive there is no third half-lock decision: the actor
either owns both provisional receipts or must enter abort. -/
theorem receipt_join_total (leftGap rightGap : GrantRight) :
    MaySendWin leftGap rightGap \/ MustAbort leftGap rightGap := by
  cases leftGap <;> cases rightGap <;>
    simp [MaySendWin, MustAbort, leftResult, rightResult]

theorem receipt_join_exclusive (leftGap rightGap : GrantRight) :
    ¬ (MaySendWin leftGap rightGap /\ MustAbort leftGap rightGap) := by
  cases leftGap <;> cases rightGap <;>
    simp [MaySendWin, MustAbort, leftResult, rightResult]

/-- Both uniform cyclic orientations force every actor into abort rather than
exposing a final one-gap lease. -/
theorem uniform_receipts_force_abort (direction : GrantRight) :
    MustAbort direction direction := by
  cases direction <;> simp [MustAbort, leftResult, rightResult]

/-- Naming the same physical gap through both actor ports cannot manufacture
two provisional grants.  This is the singleton-live-leader safety core: its
clockwise and counterclockwise incident roles denote one cyclic gap. -/
theorem same_gap_cannot_join (direction : GrantRight) :
    ¬ MaySendWin direction direction := by
  cases direction <;> simp [MaySendWin, leftResult, rightResult]

/-- Adjacent actors cannot both pass the provisional-receipt join. -/
theorem adjacent_maySendWin_false
    {leftGap sharedGap rightGap : GrantRight}
    (leftMayWin : MaySendWin leftGap sharedGap)
    (rightMayWin : MaySendWin sharedGap rightGap) : False := by
  apply adjacent_winners_false
  · exact (maySendWin_iff_wins _ _).mp leftMayWin
  · exact (maySendWin_iff_wins _ _).mp rightMayWin

/-- A winner's counterclockwise neighbouring contender sees a denial on their
shared gap, independently of the neighbour's other gap.  Entering abort on
this first denial must therefore not wait for the other result. -/
theorem winner_forces_left_neighbor_abort
    (outerLeft leftGap rightGap : GrantRight)
    (winner : MaySendWin leftGap rightGap) :
    MustAbort outerLeft leftGap := by
  have won := (maySendWin_iff_wins _ _).mp winner
  rcases won with ⟨rfl, _⟩
  exact Or.inr (by simp [rightResult])

/-- Symmetrically, the clockwise neighbouring contender sees a denial on the
shared gap without waiting for its other result. -/
theorem winner_forces_right_neighbor_abort
    (leftGap rightGap outerRight : GrantRight)
    (winner : MaySendWin leftGap rightGap) :
    MustAbort rightGap outerRight := by
  have won := (maySendWin_iff_wins _ _).mp winner
  rcases won with ⟨_, rfl⟩
  exact Or.inl (by simp [leftResult])

/-- Both retirement decisions needed by a winner's two gaps are consequences
of the two shared denials.  Cleanup of either loser's other provisional grant
is deliberately absent from this interface. -/
theorem winner_has_local_retirement_frontier
    (outerLeft leftGap rightGap outerRight : GrantRight)
    (winner : MaySendWin leftGap rightGap) :
    MustAbort outerLeft leftGap /\ MustAbort rightGap outerRight :=
  ⟨winner_forces_left_neighbor_abort outerLeft leftGap rightGap winner,
   winner_forces_right_neighbor_abort leftGap rightGap outerRight winner⟩

/-! ## Weighted one-round drift numerators -/

def winnerCharge (weight : Nat) (leftGap rightGap : GrantRight) : Nat :=
  if leftGap && !rightGap then weight else 0

/-- Across the four equiprobable orientations of two independently contested
incident gaps, an interior actor contributes its full weight exactly once.
After division by four this is the local `weight/4` drift used by aggregate
contention accounting. -/
theorem winnerCharge_four_cases (weight : Nat) :
    winnerCharge weight false false +
      winnerCharge weight false true +
      winnerCharge weight true false +
      winnerCharge weight true true = weight := by
  simp [winnerCharge]

/-- A left endpoint of a proper eligible component has its exterior gap forced
inward and wins in one of the two orientations of its internal gap. -/
theorem leftEndpointCharge_two_cases (weight : Nat) :
    winnerCharge weight true false + winnerCharge weight true true = weight := by
  simp [winnerCharge]

/-- Symmetric right-endpoint numerator. -/
theorem rightEndpointCharge_two_cases (weight : Nat) :
    winnerCharge weight false false + winnerCharge weight true false = weight := by
  simp [winnerCharge]

/-- A uniform cyclic orientation has no local winner.  These are the two
retry cases left after cutting every nonuniform cyclic word at a change. -/
theorem uniform_gap_not_won (direction : GrantRight) :
    ¬ Wins direction direction := by
  cases direction <;> simp [Wins]

/-- Winning the leases is only arbitration.  Eligibility remains the primary
geometric-priority local-minimum predicate used by the heap theorem. -/
def Eligible (left self right : Nat) : Prop :=
  self <= left /\ self <= right

/-- Adjacent eligible leaders have equal primary priorities.  Hence if every
leader in a nonempty cycle is eligible, the whole priority word is constant. -/
theorem adjacent_eligible_priorities_equal
    {outerLeft left right outerRight : Nat}
    (leftEligible : Eligible outerLeft left right)
    (rightEligible : Eligible left right outerRight) :
    left = right :=
  Nat.le_antisymm leftEligible.2 rightEligible.1

/-- If two adjacent leaders are eligible and the left one is deleted, the
right one remains eligible after seeing the deleted leader's outer neighbour.
This is the local persistence fact needed by aggregate contention analysis. -/
theorem right_remains_eligible_after_left_deleted
    {outerLeft left right outerRight : Nat}
    (leftEligible : Eligible outerLeft left right)
    (rightEligible : Eligible left right outerRight) :
    Eligible outerLeft right outerRight :=
  ⟨Nat.le_trans rightEligible.1 leftEligible.1, rightEligible.2⟩

/-- Symmetric persistence when the right eligible neighbour is deleted. -/
theorem left_remains_eligible_after_right_deleted
    {outerLeft left right outerRight : Nat}
    (leftEligible : Eligible outerLeft left right)
    (rightEligible : Eligible left right outerRight) :
    Eligible outerLeft left outerRight :=
  ⟨leftEligible.1, Nat.le_trans leftEligible.2 rightEligible.2⟩

theorem winning_certificate_is_local_minimum
    {left self right : Nat} {leftGap rightGap : GrantRight}
    (eligible : Eligible left self right)
    (_won : Wins leftGap rightGap) :
    self <= left /\ self <= right :=
  eligible

end BoundaryLeaseArbitration

#print axioms BoundaryLeaseArbitration.adjacent_winners_false
#print axioms BoundaryLeaseArbitration.inward_path_has_winner
#print axioms BoundaryLeaseArbitration.cyclicWinner_or_uniform
#print axioms BoundaryLeaseArbitration.uniform_of_no_cyclicWinner
#print axioms BoundaryLeaseArbitration.maySendWin_iff_wins
#print axioms BoundaryLeaseArbitration.receipt_join_total
#print axioms BoundaryLeaseArbitration.receipt_join_exclusive
#print axioms BoundaryLeaseArbitration.uniform_receipts_force_abort
#print axioms BoundaryLeaseArbitration.same_gap_cannot_join
#print axioms BoundaryLeaseArbitration.adjacent_maySendWin_false
#print axioms BoundaryLeaseArbitration.winnerCharge_four_cases
#print axioms BoundaryLeaseArbitration.leftEndpointCharge_two_cases
#print axioms BoundaryLeaseArbitration.rightEndpointCharge_two_cases
#print axioms BoundaryLeaseArbitration.uniform_gap_not_won
#print axioms BoundaryLeaseArbitration.adjacent_eligible_priorities_equal
#print axioms BoundaryLeaseArbitration.right_remains_eligible_after_left_deleted
#print axioms BoundaryLeaseArbitration.left_remains_eligible_after_right_deleted
#print axioms BoundaryLeaseArbitration.winning_certificate_is_local_minimum
