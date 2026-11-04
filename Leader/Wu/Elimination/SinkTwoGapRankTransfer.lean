import Leader.Wu.Elimination.SinkTwoGapReachInvariant

set_option autoImplicit false

open FiniteUniformStoppingTree PredictableRenewalOverlap LDTwoGapFrame
open LDSinkGapCleanup PPLLRepair LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptCells
open LDSinkTwoGapEntrance LDSinkTwoGapDeletion LDSinkTwoGapDeletionWired
open LDSinkTwoGapReachInvariant Classical

namespace LDSinkTwoGapRankTransfer

variable {n psi : Nat}

/-- The exact two one-step inequalities carried by the old R1, but for one raw
state rather than for a reachability domain. -/
def RawEntranceRankLaw
    (hpsi : psi > 0) (F : TwoGapFrame n) (x : AState n psi) : Prop :=
  (forall e : Fin n,
    rawStoppedR F (entranceStep hpsi F x e) <= R F x) ∧
  exists e : Fin n,
    rawStoppedR F (entranceStep hpsi F x e) < R F x

/-- R1' exactly as a statement over the corrected tagged invariant. -/
def CorrectedReachableEntranceRank
    (hpsi : psi > 0) (F : TwoGapFrame n) : Prop :=
  forall z : TaggedState n psi,
    TaggedReach hpsi F z ->
    AInvariant' hpsi F z ->
    RawEntranceRankLaw hpsi F z.raw

/--
The corrected theorem transfers to the old raw-state residual by erasing only
the proof tag.  No success-count theorem is required: both sides are literally
one-step rank statements on `z.raw`, and `entranceReach_invariant'` supplies
`z.raw = x`.
-/
theorem reachableRankResidual_of_corrected
    {hpsi : psi > 0} {F : TwoGapFrame n}
    (hBoundary : CleanBoundarySignalResidual hpsi F)
    (hcorrected : CorrectedReachableEntranceRank hpsi F) :
    ReachableEntranceRankResidual hpsi F := by
  refine ⟨?_, ?_⟩
  · intro x hx _ e
    obtain ⟨z, hzraw, hzreach, hzinv⟩ :=
      entranceReach_invariant' hpsi F hBoundary x hx
    have he := (hcorrected z hzreach hzinv).1 e
    rw [hzraw] at he
    exact he
  · intro x hx _
    obtain ⟨z, hzraw, hzreach, hzinv⟩ :=
      entranceReach_invariant' hpsi F hBoundary x hx
    obtain ⟨e, he⟩ := (hcorrected z hzreach hzinv).2
    refine ⟨e, ?_⟩
    rw [hzraw] at he
    exact he

/--
The tracking half has no tag-specific rank content.  `trackingLaw` is the
interface that the existing checked attempt law is supposed to instantiate.
I keep it as a parameter here because the exact type of that existing theorem
is not present in the connector-visible source and was not included in the
question.
-/
theorem tracking_rankLaw
    {hpsi : psi > 0} {F : TwoGapFrame n}
    (trackingLaw :
      forall x : AState n psi,
        AInvariant hpsi F x -> RawEntranceRankLaw hpsi F x)
    (z : TaggedState n psi)
    (_hz : TaggedReach hpsi F z)
    (_hi : AInvariant' hpsi F z)
    (hold : AInvariant hpsi F z.raw) :
    RawEntranceRankLaw hpsi F z.raw := by
  exact trackingLaw z.raw hold

/--
A corrected-state theorem splits cleanly into the old-invariant tracking case
and the corrected exceptional case.  No assertion about the concrete tag-mode
representation is needed for this split.
-/
theorem corrected_of_tracking_and_exceptional
    {hpsi : psi > 0} {F : TwoGapFrame n}
    (trackingLaw :
      forall x : AState n psi,
        AInvariant hpsi F x -> RawEntranceRankLaw hpsi F x)
    (exceptionalLaw :
      forall z : TaggedState n psi,
        TaggedReach hpsi F z ->
        AInvariant' hpsi F z ->
        ¬ AInvariant hpsi F z.raw ->
        RawEntranceRankLaw hpsi F z.raw) :
    CorrectedReachableEntranceRank hpsi F := by
  intro z hz hi
  rcases Classical.em (AInvariant hpsi F z.raw) with hold | hold
  · exact trackingLaw z.raw hold
  · exact exceptionalLaw z hz hi hold

/--
If an exceptional corrected state is a genuine one-step rank plateau, the
strict half of R1' is false there.  This elementary lemma records the logical
reason that a bounded seeking stretch cannot be squeezed back into a one-step
strict-drop statement without changing the potential or the theorem.
-/
theorem no_strictDrop_of_plateau
    (hpsi : psi > 0) (F : TwoGapFrame n) (x : AState n psi)
    (hPlateau :
      forall e : Fin n,
        rawStoppedR F (entranceStep hpsi F x e) = R F x) :
    ¬ (exists e : Fin n,
      rawStoppedR F (entranceStep hpsi F x e) < R F x) := by
  intro h
  obtain ⟨e, he⟩ := h
  rw [hPlateau e] at he
  exact (Nat.lt_irrefl (R F x)) he

/--
Honest replacement seam for the corrected exceptional domain when one-step
strict decrease is unavailable.  `ExitWithin z k` is intentionally a parameter:
the current question does not expose the tagged service iterator or the exact
predicate for leaving `seeking`.  An instance must interpret it as "after at
most k charged services the tagged execution has left the exceptional seeking
stretch (or has stopped)".

There is only one proof field.  `B` is also a parameter rather than a guessed
constant.
-/
structure SeekingStretchResidual
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (ExitWithin : TaggedState n psi -> Nat -> Prop)
    (B : Nat) : Prop where
  boundedExit :
    forall z : TaggedState n psi,
      TaggedReach hpsi F z ->
      AInvariant' hpsi F z ->
      ¬ AInvariant hpsi F z.raw ->
      exists k : Nat, k <= B ∧ ExitWithin z k

end LDSinkTwoGapRankTransfer

#print axioms LDSinkTwoGapRankTransfer.reachableRankResidual_of_corrected
#print axioms LDSinkTwoGapRankTransfer.tracking_rankLaw
#print axioms LDSinkTwoGapRankTransfer.corrected_of_tracking_and_exceptional
#print axioms LDSinkTwoGapRankTransfer.no_strictDrop_of_plateau
