import Leader.PPL.Elim.AttemptCostLong

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-!
# LD(736): concrete long-stage live Bellman certificate

The raw LongAttemptState datatype contains the deliberately unreachable
LongStage.stuck self-loop, so the certificate is built on a semantic live
domain.  The potential is measured first in predictable-service units and is
then multiplied by the scheduler size n.

The suffix reserves are the paper charges, read from the end of an attempt:

  recovery                  2b - 2
  retained trial        2b + 2b - 2
  incident wait       1 + 2b + 2b - 2
  target race      2b-1 + 1 + 2b + 2b - 2
  advance       a-1-2b + 2b-1 + 1 + 2b + 2b - 2
  live launch 2a + the advance suffix
  attacker CR 3a + the live-launch suffix
  target CR   3b + the attacker-CR suffix.

Thus the initial reserve is definitionally the eight-term
longAttemptPaperBudgetLong, up to Nat arithmetic.

The local pieces mirror the already proved stage potentials:
* crRank is the cleanReady_cost_proved / crRankStep_proved rank;
* longLaunchPhaseUnits is the sealed Ready/dummy/return launch clock;
* longAdvancePhaseUnits is the retained live-bullet distance to 2b;
* phaseDebt F.b is the predictable target-race / recovery service debt;
* longRetainedPhaseUnits is retainedPotential / n, whose Bellman row is
  retainedTrial_cost_nr via controlRowSpec_proved;
* the incident stage reserves one service unit for the two predictable
  incident edges.

All malformed stage witnesses, in particular stuck, are excluded by
longStageLegit.  Because longStart hides private choice functions, longLiveGood
also contains the literal good start states as an entry clause.  The single
remaining bounded-round residual below is therefore only the one-interaction
fact saying that this exact domain is closed and this exact potential obeys
the Bellman row.
-/

/-! ## Paper suffix reserves in service units -/

def longRecoveryReserveUnits
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  2 * F.b - 2

def longRetainedReserveUnits
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  2 * F.b + longRecoveryReserveUnits F

def longIncidentReserveUnits
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  1 + longRetainedReserveUnits F

def longRaceReserveUnits
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  (2 * F.b - 1) + longIncidentReserveUnits F

def longAdvanceReserveUnits
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  (F.a - 1 - 2 * F.b) + longRaceReserveUnits F

def longLaunchReserveUnits
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  2 * F.a + longAdvanceReserveUnits F

def longAttackerCRReserveUnits
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  3 * F.a + longLaunchReserveUnits F

def longTargetCRReserveUnits
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Nat :=
  3 * F.b + longAttackerCRReserveUnits F

theorem longTargetCRReserveUnits_eq_paper
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    longTargetCRReserveUnits F =
      longAttemptPaperBudgetLong F := by
  unfold longTargetCRReserveUnits
    longAttackerCRReserveUnits
    longLaunchReserveUnits
    longAdvanceReserveUnits
    longRaceReserveUnits
    longIncidentReserveUnits
    longRetainedReserveUnits
    longRecoveryReserveUnits
    longAttemptPaperBudgetLong
  omega

/-! ## Local stage ranks -/

/-- The 2a clean-live launch recurrence from a sealed attacker sector.

Ready has reserve 2a.  An incoming firing enters Dummy(0), whose
2a-1 return debt is added to the same 2a retry reserve.  A surviving outgoing
firing leaves liveWait immediately, so live phases carry no launch debt here.
-/
def longLaunchPhaseUnits (a : Nat) : SectorPhase → Nat
  | .ready => 2 * a
  | .dummy p => phaseDebt a (.dummy p) + 2 * a
  | .live _ => 0
  | .ret q => q + 2 * a

/-- Number of attacker services still required before the retained live bullet
has at most 2b hops left. -/
def longAdvancePhaseUnits
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : SectorPhase → Nat
  | .live p => (F.a - 2 * F.b) - p
  | _ => 0

/-- Retained-bullet vulnerable potential with the common scheduler factor
removed. -/
def longRetainedPhaseUnits
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : SectorPhase → Nat
  | .live p => F.a - p
  | _ => 0

/-- Concrete service-unit potential for every long monitor stage.

The suffix reserve is included in the current stage, so a stage crossing can
spend the current local rank and hand the remaining reserve to its child.
-/
def longStageUnits
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : LongStage → Nat
  | .targetCR mode =>
      crRank F.B mode + longAttackerCRReserveUnits F
  | .attackerCR _ mode =>
      crRank F.A mode + longLaunchReserveUnits F
  | .liveWait _ attackPhase =>
      longLaunchPhaseUnits F.a attackPhase +
        longAdvanceReserveUnits F
  | .advance _ attackPhase =>
      longAdvancePhaseUnits F attackPhase +
        longRaceReserveUnits F
  | .race targetPhase _ =>
      phaseDebt F.b targetPhase +
        longIncidentReserveUnits F
  | .incident _ =>
      longIncidentReserveUnits F
  | .retained _ attackPhase =>
      longRetainedPhaseUnits F attackPhase +
        longRecoveryReserveUnits F
  | .recovery targetPhase _ =>
      phaseDebt F.b targetPhase
  | .stuck => 0

/-! ## Semantic live domain -/

/-- Legitimate stage witnesses.  These are exactly the facts needed by the
corresponding already-proved row.

The recovery clause records the sharper 2b-2 post-failure debt.  The retained
clause records target unshieldedness, which is the extra hypothesis of the
controlled vulnerable monitor.
-/
def longStageLegit
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (C : Config n) :
    LongStage → Prop
  | .targetCR mode =>
      CRModeHolds F.B C mode
  | .attackerCR targetPhase mode =>
      PhaseHolds F.B C targetPhase ∧
        CRModeHolds F.A C mode
  | .liveWait targetPhase attackPhase =>
      PhaseHolds F.B C targetPhase ∧
        PhaseHolds F.A C attackPhase ∧
        (match attackPhase with
         | .live _ => False
         | _ => True)
  | .advance targetPhase attackPhase =>
      PhaseHolds F.B C targetPhase ∧
        PhaseHolds F.A C attackPhase ∧
        ∃ p,
          attackPhase = .live p ∧
          0 < p ∧
          p < F.a - 2 * F.b
  | .race targetPhase attackPhase =>
      PhaseHolds F.B C targetPhase ∧
        PhaseHolds F.A C attackPhase ∧
        ∃ p,
          attackPhase = .live p ∧
          F.a - p ≤ 2 * F.b
  | .incident attackPhase =>
      PhaseHolds F.B C .ready ∧
        PhaseHolds F.A C attackPhase ∧
        ∃ p,
          attackPhase = .live p ∧
          F.a - p ≤ 2 * F.b
  | .retained targetPhase attackPhase =>
      PhaseHolds F.B C targetPhase ∧
        PhaseHolds F.A C attackPhase ∧
        (∃ p,
          attackPhase = .live p ∧
          F.a - p ≤ 2 * F.b) ∧
        (C F.j).shield = false
  | .recovery targetPhase _ =>
      PhaseHolds F.B C targetPhase ∧
        targetPhase ≠ .ready ∧
        phaseDebt F.b targetPhase ≤
          longRecoveryReserveUnits F
  | .stuck => False

theorem longStageLegit_not_stuck
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (C : Config n) :
    ¬ longStageLegit F C .stuck := by
  simp [longStageLegit]

/-- Good active states.

The left disjunct names literal good starts.  This avoids reopening the private
Classical.choose implementation of longInitialStage merely to prove the entry
lemma.  Every later semantic state is described by longStageLegit.  The single
one-step residual below proves that a good start immediately enters, and then
stays inside, this semantic domain.
-/
def longLiveGood
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F) : Prop :=
  (∃ s : Config n,
      AttemptGood ring F s ∧
        a = (longAttemptKernel ring F).start s) ∨
    match a with
    | .junk _ => False
    | .live C _ stage => longStageLegit F C stage

theorem longLiveGood_start
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s) :
    longLiveGood ring F
      ((longAttemptKernel ring F).start s) := by
  exact Or.inl ⟨s, hs, rfl⟩

/-- Scheduler-scaled concrete potential.

The min is only an entry cap.  On semantic stage witnesses the intended
single-step proof shows that the raw stage reserve is within the paper
envelope.  Keeping the cap here makes the entry inequality independent of the
private initial-stage choice while still assigning zero to malformed stuck.
-/
def longLivePhi
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F → Nat
  | .junk _ => 0
  | .live _ _ stage =>
      n * Nat.min
        (longStageUnits F stage)
        (longAttemptPaperBudgetLong F)

theorem longLivePhi_le_entry_budget
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F) :
    longLivePhi ring F a ≤
      n * longAttemptPaperBudgetLong F := by
  cases a with
  | junk C =>
      simp [longLivePhi]
  | live C hgood stage =>
      exact
        Nat.mul_le_mul_left n
          (Nat.min_le_right _ _)

/-!
## One remaining single-interaction splice

This is deliberately not another cost theorem.  It contains only the two
one-letter facts required by attemptCostNumerator_reachableBellman_Long for
the concrete Good and Phi above.

A direct stage split discharges it from current main as follows.

* targetCR / attackerCR: crRankStep_proved; the Good witness supplies
  CRModeHolds, PB and CRInteriorFollowers.
* liveWait / advance / recovery: sealedStepSpec and the deterministic
  nextSectorPhase service debts.
* race / incident: the two distinct predictable edges used by
  PredictableTwoTargetFiniteTree; for cost, their ordinary one/two-exception
  Bellman rows suffice.
* retained: controlRowSpec_proved together with retainedTrial_cost_nr; the raw
  Ready-time R_j branch enters recovery, while Q redirects that same port, so
  the recovery suffix is the only stage-crossing reserve to check.

Thus this Prop is the exact bounded-round seam: no horizon, expectation,
restart, or global reachability statement occurs in it.
-/
def LongStageSingleInteractionSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 ≤ F.b →
      2 * F.b + 1 ≤ F.a →
      (∀ a,
        longLiveGood ring F a →
        ∀ e a',
          (longAttemptKernel ring F).step a e = .active a' →
          longLiveGood ring F a') ∧
      (∀ a,
        longLiveGood ring F a →
        n +
            (List.ofFn (fun e : Fin n =>
              attemptNodePotLong
                (longLivePhi ring F)
                ((longAttemptKernel ring F).step a e))).sum ≤
          n * longLivePhi ring F a)

/-! ## Assembly -/

/-- Concrete LongStageBellmanCostSpec from the sole remaining literal
single-interaction splice. -/
theorem longStageBellmanCost
    (hOne : LongStageSingleInteractionSpec) :
    LongStageBellmanCostSpec := by
  unfold LongStageBellmanCostSpec
  intro hSealed n ring C0 F hb hab
  have hsingle :=
    hOne hSealed ring F hb hab
  refine
    ⟨longLiveGood ring F,
      longLivePhi ring F,
      ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact longLiveGood_start ring F s hs
  · exact hsingle.1
  · exact hsingle.2
  · intro s _hs
    exact
      longLivePhi_le_entry_budget
        ring F
        ((longAttemptKernel ring F).start s)

/-- Once the literal one-step splice is closed, the requested one-attempt
cost theorem is exactly the already-proved generic reduction. -/
theorem longAttemptCostSpec_proved
    (hOne : LongStageSingleInteractionSpec) :
    LongAttemptCostSpec :=
  longAttemptCostSpec_of_stageBellman_Long
    (longStageBellmanCost hOne)

end PPL.Convergence.LDLocal

