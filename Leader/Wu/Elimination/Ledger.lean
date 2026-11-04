/-!
# Elimination ledger

Self-contained, core-only abstract ledger for the global elimination proof.
There are no repository imports.

Local mirrors of real definitions:
* `StopNode` mirrors `FiniteUniformStoppingTree.StopNode`.
* `treeWeight` mirrors `FiniteUniformStoppingTree.treeWeight`.
* `successCount` mirrors `FiniteUniformStoppingTree.successCount`.
* `truncatedActiveCostNumerator` mirrors
  `FiniteUniformStoppingTree.truncatedActiveCostNumerator`.

Abstract compiled-piece interfaces:
* A: `OneGapCleanupSpec`.
* B: `AttemptCostSpec`.
* C: `EntranceHalfSpec`.
* D: `RaceSixteenthSpec`.
* E: `TwoGapDeletionSpec`.
* F: hypothesis `hF` in `elimination_cost_from_residuals`.
* G: hypothesis `hG` in `elimination_cost_from_residuals`.
* H: hypothesis `hH` in `elimination_cost_from_residuals`.

The only structure fields are the six residuals R1--R6.
-/

set_option autoImplicit false

namespace EliminationLedger

/-! ## Tiny finite stopping-tree mirror -/

inductive StopNode (S : Type) where
  | active : S → StopNode S
  | success : StopNode S
  | failure : StopNode S


def stepNode {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) : StopNode S → Fin n → StopNode S
  | .active s, e => step s e
  | .success, _ => .success
  | .failure, _ => .failure


def treeWeight {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (weight : StopNode S → Nat) :
    StopNode S → Nat → Nat
  | x, 0 => weight x
  | x, T + 1 =>
      (List.ofFn (fun e : Fin n =>
        treeWeight step weight (stepNode step x e) T)).sum


def successWeight {S : Type} : StopNode S → Nat
  | .active _ => 0
  | .success => 1
  | .failure => 0


def successCount {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (T : Nat) : Nat :=
  treeWeight step successWeight x T


def truncatedActiveCostNumerator {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) : StopNode S → Nat → Nat
  | _, 0 => 0
  | .success, _ + 1 => 0
  | .failure, _ + 1 => 0
  | .active s, T + 1 =>
      n ^ (T + 1) +
        (List.ofFn (fun e : Fin n =>
          truncatedActiveCostNumerator step (step s e) T)).sum

/-! ## Visible constants -/

/-- Exact physical two-gap deletion potential from piece E.

For `s = a+b`, this is
`2048 * n * s + 256 * n` after elementary normalization.
-/
def episodePhi (n s : Nat) : Nat :=
  2 * 32 * (32 * n * s + 4 * n)

/-- One normalized telescope round. This is the normal form of
`(C*n)*(2*n)` from `telescoping_quadratic`. -/
def roundPhi (n C : Nat) : Nat :=
  (2 * C) * (n ^ 2)

/-- `k` halving rounds. -/
def eliminationPhi (n C k : Nat) : Nat :=
  (2 * C) * (n ^ 2) * k

/-! ## Abstract analogues of A--E -/

/-- A. Abstract one-gap cleanup: the supplied one-gap potential is at most
`2*n*d`. -/
def OneGapCleanupSpec {Gap : Type}
    (n : Nat) (distance gapPotential : Gap → Nat) : Prop :=
  ∀ g, gapPotential g ≤ 2 * n * distance g

/-- B. Abstract two-gap attempt cost. -/
def AttemptCostSpec {S Frame : Type} {n : Nat}
    (attemptStep : Frame → S → Fin n → StopNode S)
    (span : Frame → Nat) (F : Frame) : Prop :=
  ∀ x T,
    truncatedActiveCostNumerator (attemptStep F) (.active x) T ≤
      n ^ T * (n * 16 * span F)

/-- C. Abstract entrance half-mass certificate at horizon `32*n*(a+b)`.
`entranceStart` is deliberately a parameter so the ledger does not invent the
real entrance-domain predicate. -/
def EntranceHalfSpec {S Frame : Type} {n : Nat}
    (entranceStep : Frame → S → Fin n → StopNode S)
    (entranceStart : S → Frame → Prop)
    (span : Frame → Nat) (F : Frame) : Prop :=
  ∀ x, entranceStart x F →
    n ^ (32 * n * span F) ≤
      2 * successCount (entranceStep F) (.active x) (32 * n * span F)

/-- D. Abstract kernel-free serial-race sixteenth-mass certificate at horizon
`4*n`. -/
def RaceSixteenthSpec {S Frame : Type} {n : Nat}
    (raceStep : Frame → S → Fin n → StopNode S)
    (raceStart : S → Frame → Prop) (F : Frame) : Prop :=
  ∀ x, raceStart x F →
    n ^ (4 * n) ≤
      16 * successCount (raceStep F) (.active x) (4 * n)

/-- E. Abstract real-state two-gap deletion theorem, with the exact compiled
potential `episodePhi n (a+b)`. -/
def TwoGapDeletionSpec {S Frame : Type} {n : Nat}
    (blockStep : Frame → S → Fin n → StopNode S)
    (span : Frame → Nat) (F : Frame) : Prop :=
  ∀ x T,
    truncatedActiveCostNumerator (blockStep F) (.active x) T ≤
      n ^ T * episodePhi n (span F)

/-! ## Exactly the six open residuals -/

/-- The proof ledger. There are exactly six fields, corresponding to R1--R6.

`rankOK`, `simulationOK`, `restartOK`, and `signalOK` stand for the real
frame-indexed residual propositions. `candidate` is the pigeonhole-selected
triple relation, while `applicable` means that the physical episode theorem is
legally instantiable on that proof-selected frame.
-/
structure EliminationResidual
    {S Gap Frame EState : Type} {n C : Nat}
    (distance gapPotential : Gap → Nat)
    (blockStep : Frame → S → Fin n → StopNode S)
    (span : Frame → Nat)
    (rankOK simulationOK restartOK signalOK : Frame → Prop)
    (next : EState → EState → Prop)
    (episodeBound : EState → EState → Nat)
    (w phase : EState → Nat)
    (candidate applicable : EState → Frame → Prop) : Prop where

  /-- R1. Reachable entrance states satisfy the rank laws needed by C/E. -/
  reachableEntranceRank : ∀ F, rankOK F

  /-- R2. Same-edge virtual/physical simulation needed by E. -/
  simulation : ∀ F, simulationOK F

  /-- R3. Every physical active restart has a related virtual entrance. -/
  restart : ∀ F, restartOK F

  /-- R4. Clean-pre/nonclean-post boundary implies the required signal/bullet
  ordering fact. -/
  signal : ∀ F, signalOK F

  /-- R5. The physical one-gap and two-gap episode theorems induce the exact
  `telescoping_quadratic` step inequality with coefficient `C`.

  This is intentionally where the still-unknown numerical value of `C` lives.
  In particular, the ledger does not pretend that the distance-anchored
  `sum gapWC` is merge-stable.
  -/
  episodeToTelescope :
    OneGapCleanupSpec n distance gapPotential →
    (∀ F, TwoGapDeletionSpec blockStep span F) →
    ∀ {x y}, next x y →
      w y ≤ w x ∧
      phase y < phase x ∧
      episodeBound x y ≤ (C * n) * ((w x - w y) + 1)

  /-- R6. Any triple selected by the proof is a legal frame for the episode
  theorem. -/
  tripleChoice :
    ∀ {x F}, candidate x F → applicable x F

/-! ## Capstone ledger theorem -/

/-- The end-to-end elimination bound from exactly R1--R6 plus abstract
analogues of compiled pieces A--H.

Piece I (`entranceReach_invariant'`) is folded into `hC`: concretely, the real
wiring may use R4 to obtain the corrected entrance invariant and then discharge
C. It is not an additional residual field.

`hF` is the normalized abstract form of `telescoping_quadratic`: its conclusion
`roundPhi n C = (2*C)*n^2` is algebraically the same as `(C*n)*(2*n)`.

`hG` is the abstract round-composition/batching seam. Its second premise is
formed below by composing H's pigeonhole choice
`m * (a+b) ≤ 2*n` with R6's applicability bridge. Its third premise is the
real batching/round-count certificate obtained from the round machinery,
including the excess-shrink theorem.
-/
theorem elimination_cost_from_residuals
    {S Gap Frame EState : Type} {n C k : Nat}
    (step : S → Fin n → StopNode S)
    (attemptStep entranceStep raceStep blockStep :
      Frame → S → Fin n → StopNode S)
    (entranceStart raceStart : S → Frame → Prop)
    (distance gapPotential : Gap → Nat)
    (span : Frame → Nat)
    (rankOK simulationOK restartOK signalOK : Frame → Prop)
    (next : EState → EState → Prop)
    (episodeBound : EState → EState → Nat)
    (w phase leaders : EState → Nat)
    (candidate applicable : EState → Frame → Prop)
    (Trace : EState → Nat → EState → Prop)
    (RoundCertificate : Nat → Prop)
    (R : EliminationResidual (C := C) distance gapPotential blockStep span
      rankOK simulationOK restartOK signalOK
      next episodeBound w phase candidate applicable)

    -- A
    (hA : OneGapCleanupSpec n distance gapPotential)

    -- B
    (hB : ∀ F, AttemptCostSpec attemptStep span F)

    -- C; the corrected entrance-invariant theorem is wired inside this seam.
    (hC : ∀ F, rankOK F → signalOK F →
      EntranceHalfSpec entranceStep entranceStart span F)

    -- D
    (hD : ∀ F, RaceSixteenthSpec raceStep raceStart F)

    -- E
    (hE : ∀ F,
      AttemptCostSpec attemptStep span F →
      EntranceHalfSpec entranceStep entranceStart span F →
      RaceSixteenthSpec raceStep raceStart F →
      rankOK F → simulationOK F → restartOK F →
      TwoGapDeletionSpec blockStep span F)

    -- F
    (hF :
      (∀ {x y}, next x y →
        w y ≤ w x ∧
        phase y < phase x ∧
        episodeBound x y ≤ (C * n) * ((w x - w y) + 1)) →
      ∀ {start total finish}, Trace start total finish →
        w start ≤ n → phase start ≤ n →
        total ≤ roundPhi n C)

    -- G
    (hG :
      (∀ {start total finish}, Trace start total finish →
        w start ≤ n → phase start ≤ n →
        total ≤ roundPhi n C) →
      (∀ e : EState, 1 < leaders e →
        ∃ F, candidate e F ∧ applicable e F ∧
          leaders e * span F ≤ 2 * n) →
      RoundCertificate k →
      ∀ x : S, ∀ T,
        truncatedActiveCostNumerator step (.active x) T ≤
          n ^ T * eliminationPhi n C k)

    -- H
    (hH : ∀ e : EState, 1 < leaders e →
      ∃ F, candidate e F ∧ leaders e * span F ≤ 2 * n)

    (hBatch : RoundCertificate k)
    (x : S) (T : Nat) :
    truncatedActiveCostNumerator step (.active x) T ≤
      n ^ T * eliminationPhi n C k := by
  have hTwoGap : ∀ F, TwoGapDeletionSpec blockStep span F := by
    intro F
    have hRank : rankOK F := R.reachableEntranceRank F
    have hSignal : signalOK F := R.signal F
    have hEntrance : EntranceHalfSpec entranceStep entranceStart span F :=
      hC F hRank hSignal
    exact hE F (hB F) hEntrance (hD F) hRank
      (R.simulation F) (R.restart F)

  have hStep :
      ∀ {u v}, next u v →
        w v ≤ w u ∧
        phase v < phase u ∧
        episodeBound u v ≤ (C * n) * ((w u - w v) + 1) :=
    R.episodeToTelescope hA hTwoGap

  have hRound :
      ∀ {start total finish}, Trace start total finish →
        w start ≤ n → phase start ≤ n →
        total ≤ roundPhi n C :=
    hF hStep

  have hChoice :
      ∀ e : EState, 1 < leaders e →
        ∃ F, candidate e F ∧ applicable e F ∧
          leaders e * span F ≤ 2 * n := by
    intro e he
    obtain ⟨F, hCandidate, hCharge⟩ := hH e he
    exact ⟨F, hCandidate, R.tripleChoice hCandidate, hCharge⟩

  exact hG hRound hChoice hBatch x T

/-- Batching specialization.

With a real batching certificate for `k` rounds,
`Phi = (2*C) * n^2 * k`; thus the explicit constant is `2*C`.

Using `afterTripleBatch_excess_shrink` plus the round-count certificate, `k`
may be taken to be the number of halvings needed to reduce the initial excess
to zero; equivalently a safe conventional choice is the least `k` with
`n ≤ 2^k` (up to the trivial `n = 0,1` conventions). Hence `k = O(log n)` and
the elimination cost is `O(C*n^2*log n)`. Once R5 supplies an absolute `C`,
this is `O(n^2 log n)`, which is inside the project's actual
`O(n^2 log n log log n)` interactions-whp budget.
-/
theorem eliminationPhi_le_square_times_rounds
    {RoundCertificate : Nat → Prop}
    (n C k : Nat) (_hBatch : RoundCertificate k) :
    eliminationPhi n C k ≤ (2 * C) * (n ^ 2) * k := by
  exact Nat.le_refl _

/-- Bellman-form restatement of the same specialization. -/
theorem elimination_cost_square_times_rounds
    {S : Type} {n C k : Nat}
    (step : S → Fin n → StopNode S)
    (RoundCertificate : Nat → Prop)
    (_hBatch : RoundCertificate k)
    (x : S) (T : Nat)
    (h : truncatedActiveCostNumerator step (.active x) T ≤
      n ^ T * eliminationPhi n C k) :
    truncatedActiveCostNumerator step (.active x) T ≤
      n ^ T * ((2 * C) * (n ^ 2) * k) := by
  exact h

end EliminationLedger

#print axioms EliminationLedger.elimination_cost_from_residuals
#print axioms EliminationLedger.eliminationPhi_le_square_times_rounds
#print axioms EliminationLedger.elimination_cost_square_times_rounds
