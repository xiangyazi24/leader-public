import Leader.Wu.ShortGap.SpliceCommit

open ShortGapSpliceCommit
open ShortGapLiteralGapRows
open ShortGapCaptureReservation

namespace ShortGapSpliceCommit

set_option autoImplicit false

/-! ## Corrected adoption view -/

/--
A snapshot is live exactly when it still records one physical carrier that has
not returned to its owner.

There are two such encodings in `SnapPhase`:

* `cw = waiting`: the old selection declaration/reply carrier is in flight;
* `out = proposal`: the old capture PROPOSAL/FINAL carrier is in flight.

The direction of a capture carrier is not stored in `SnapPhase`: both its
outbound PROPOSAL and returning FINAL phases keep `out = proposal` at the
source.  By contrast, `toSend` is unlaunched, `heldDenial` and
`heldCandidate` are settled selection verdicts, and `finalReady` means that
the capture FINAL has already been delivered.  Those settled cases are not
live merely because a verdict is present.
-/
def SnapPhase.isLive : SnapPhase -> Bool
  | ⟨.toSend, .home⟩ => false
  | ⟨.toSend, .proposal⟩ => true
  | ⟨.toSend, .finalReady⟩ => false
  | ⟨.waiting, .home⟩ => true
  | ⟨.waiting, .proposal⟩ => true
  | ⟨.waiting, .finalReady⟩ => true
  | ⟨.heldDenial, .home⟩ => false
  | ⟨.heldDenial, .proposal⟩ => true
  | ⟨.heldDenial, .finalReady⟩ => false
  | ⟨.heldCandidate, .home⟩ => false
  | ⟨.heldCandidate, .proposal⟩ => true
  | ⟨.heldCandidate, .finalReady⟩ => false

/--
Corrected adoption of B's old outgoing phase.  Adoption waits only for a
snapshot that still carries a live token.  An unlaunched phase or a settled
old verdict is reset to `toSend`; no verdict is copied to A.
-/
def adoptCwCorrected : SnapPhase -> CwPort
  | ⟨.toSend, .home⟩ => .toSend
  | ⟨.toSend, .proposal⟩ => .waiting
  | ⟨.toSend, .finalReady⟩ => .toSend
  | ⟨.waiting, .home⟩ => .waiting
  | ⟨.waiting, .proposal⟩ => .waiting
  | ⟨.waiting, .finalReady⟩ => .waiting
  | ⟨.heldDenial, .home⟩ => .toSend
  | ⟨.heldDenial, .proposal⟩ => .waiting
  | ⟨.heldDenial, .finalReady⟩ => .toSend
  | ⟨.heldCandidate, .home⟩ => .toSend
  | ⟨.heldCandidate, .proposal⟩ => .waiting
  | ⟨.heldCandidate, .finalReady⟩ => .toSend

theorem adoptCorrected_waiting_iff (s : SnapPhase) :
    adoptCwCorrected s = CwPort.waiting <-> SnapPhase.isLive s = true := by
  rcases s with ⟨cw, out⟩
  cases cw <;> cases out <;> simp [adoptCwCorrected, SnapPhase.isLive]

theorem adoptCorrected_ne_candidate (s : SnapPhase) :
    adoptCwCorrected s ≠ CwPort.heldCandidate := by
  rcases s with ⟨cw, out⟩
  cases cw <;> cases out <;> simp [adoptCwCorrected]

theorem adoptCorrected_ne_denial (s : SnapPhase) :
    adoptCwCorrected s ≠ CwPort.heldDenial := by
  rcases s with ⟨cw, out⟩
  cases cw <;> cases out <;> simp [adoptCwCorrected]

/-! ## Single-flight transport accounting -/

/--
A proof-level one-token transport state.  `none` means that no token is live.
For `some (outbound, r)`, `r` is the remaining number of transport hops;
`outbound = true` is the declaration/proposal direction and
`outbound = false` is the returning receipt direction.
-/
structure TxState where
  phase : Option (Bool × Nat)

/-- Interaction-scaled remaining transport work. -/
def txPot (n : Nat) : TxState -> Nat
  | ⟨none⟩ => 0
  | ⟨some (_, remaining)⟩ => n * remaining

/--
Move the owner x hops to the left.  An already-returning token has x extra
hops to its new owner.  An outbound token keeps its present remaining suffix;
the extra return distance is charged only when that same single token turns.
-/
def adoptTx (x : Nat) : TxState -> TxState
  | ⟨none⟩ => ⟨none⟩
  | ⟨some (true, remaining)⟩ => ⟨some (true, remaining)⟩
  | ⟨some (false, remaining)⟩ => ⟨some (false, remaining + x)⟩

private theorem nat_le_add_self (a b : Nat) : a ≤ a + b := by
  omega

private theorem nat_mul_le_mul_succ (n x : Nat) :
    n * x ≤ n * (x + 1) := by
  rw [Nat.mul_add, Nat.mul_one]
  exact nat_le_add_self _ _

/-- There is one carrier, so adoption can add at most one copy of x. -/
theorem single_flight_no_2x (n x : Nat) (s : TxState) :
    txPot n (adoptTx x s) ≤ txPot n s + n * x := by
  rcases s with ⟨phase⟩
  cases phase with
  | none =>
      simp [adoptTx, txPot]
  | some p =>
      rcases p with ⟨outbound, remaining⟩
      cases outbound with
      | false =>
          simp [adoptTx, txPot, Nat.mul_add]
      | true =>
          simpa [adoptTx, txPot] using
            nat_le_add_self (n * remaining) (n * x)

/--
The coarser splice budget used by the lifecycle accounting.  Since the exact
single-flight increase is at most `n*x`, it is certainly covered by the
`n*(x+1)` splice tail plus the one additional local service.
-/
theorem txPot_adopt_le (n x : Nat) (s : TxState) :
    txPot n (adoptTx x s) ≤
      txPot n s + n * (x + 1) + n := by
  calc
    txPot n (adoptTx x s) ≤ txPot n s + n * x :=
      single_flight_no_2x n x s
    _ ≤ txPot n s + n * (x + 1) :=
      Nat.add_le_add_left (nat_mul_le_mul_succ n x) (txPot n s)
    _ ≤ txPot n s + n * (x + 1) + n :=
      nat_le_add_self _ _

/-! ## Capture release pays the splice tail -/

/--
The pending target-cleanup bit `u` is at most one.  The inequality is in fact
an equality after commuting the two summands; the hypothesis records the
concrete lifecycle invariant used at the commit/splice boundary.
-/
theorem cap_splice_release (n x u : Nat) (hu : u ≤ 1) :
    n * u + n * (x + 1) ≤ n * ((x + 1) + u) := by
  have hEq : n * u + n * (x + 1) = n * ((x + 1) + u) := by
    calc
      n * u + n * (x + 1) = n * (x + 1) + n * u :=
        Nat.add_comm _ _
      _ = n * ((x + 1) + u) :=
        (Nat.mul_add n (x + 1) u).symm
  rw [hEq]
  exact Nat.le_refl _

private theorem le_of_add_same_right {a b c : Nat}
    (h : a + c ≤ b + c) : a ≤ b := by
  omega

/--
Concrete cancellation form of the commit/splice potential inequality.

`hcommit` is the same arithmetic interface as the imported
`commit_splice_potential_le`: the after-potential is charged with the fused
post-commit tail `n*((x+1)+u)`, while the before-potential still exposes the
same work as the two separate charges `n*u` and `n*(x+1)`.  The supplied
excerpt does not expose the imported theorem's argument list, so this theorem
states that interface explicitly rather than depending on its binder order.
`cap_splice_release` then cancels the complete fused tail.
-/
theorem commit_splice_potential_le_concrete
    (n x u before after : Nat) (hu : u ≤ 1)
    (hcommit :
      after + n * ((x + 1) + u) ≤
        before + (n * u + n * (x + 1))) :
    after ≤ before := by
  have hrelease :
      n * u + n * (x + 1) ≤ n * ((x + 1) + u) :=
    cap_splice_release n x u hu
  have hbound :
      after + n * ((x + 1) + u) ≤
        before + n * ((x + 1) + u) := by
    calc
      after + n * ((x + 1) + u) ≤
          before + (n * u + n * (x + 1)) := hcommit
      _ ≤ before + n * ((x + 1) + u) :=
        Nat.add_le_add_left hrelease before
  exact le_of_add_same_right hbound

#print axioms adoptCorrected_waiting_iff
#print axioms adoptCorrected_ne_candidate
#print axioms adoptCorrected_ne_denial
#print axioms single_flight_no_2x
#print axioms txPot_adopt_le
#print axioms cap_splice_release
#print axioms commit_splice_potential_le_concrete

end ShortGapSpliceCommit
