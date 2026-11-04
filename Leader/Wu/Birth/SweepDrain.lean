import Leader.Wu.Birth.ReacquireReentryMass
import Leader.Wu.Birth.LeaderlessResetFree

set_option autoImplicit false

namespace BirthB1SweepDrain

open BirthPhaseWait2BlockProgress

variable {n psi kappa tau : Nat}

/-- k-fold movement to the right. -/
def iterRight (ring : DirectedRing n) (a : Fin n) : Nat -> Fin n
  | 0 => a
  | k + 1 => ring.rightNeighbor (iterRight ring a k)

/-- One full sweep.  Range form avoids depending on List.ofFn lemmas. -/
def sweepWord (ring : DirectedRing n) (anchor : Fin n) : List (Fin n) :=
  (List.range n).map (iterRight ring anchor)

def clockDist (ring : DirectedRing n) (anchor i : Fin n) : Nat :=
  ((List.range n).find? (fun d => iterRight ring anchor d = i)).getD n

def BitsAtOrAfter
    (ring : DirectedRing n) (anchor : Fin n)
    (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau)
    (front : Nat) : Prop :=
  forall i : Fin n,
    (BirthB1ResetFreeControlled.rawAt C i).reset_cmd = true ->
      front <= clockDist ring anchor i

structure SweepFrame
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (anchor : Fin n) : Prop where
  frontier_advances :
    forall (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau)
      (d : Nat), d < n ->
      BirthB1LeaderlessResetFree.Leaderless C ->
      BitsAtOrAfter ring anchor C d ->
      BitsAtOrAfter ring anchor
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C
          (iterRight ring anchor d)) (d + 1)
  leaderless_kept :
    forall (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau)
      (e : Fin n),
      BirthB1LeaderlessResetFree.Leaderless C ->
      BirthB1LeaderlessResetFree.Leaderless
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e)
  clockDist_lt : forall i : Fin n, clockDist ring anchor i < n

/-! The frontier induction (`sweep_frontier`: after the ring-order sweep every live
reset bit is at clockwise distance >= n, hence `resetFree_after_sweep`) is an OPEN
Lean obligation as of 2026-09-12; the SweepFrame record above is
the deliverable. -/

end BirthB1SweepDrain
