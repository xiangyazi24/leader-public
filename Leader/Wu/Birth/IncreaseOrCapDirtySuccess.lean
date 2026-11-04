import Leader.Wu.Birth.WidthTwoWaitBlockProgress
import Leader.Wu.Birth.ShortWaitProjection

set_option autoImplicit false
set_option pp.structureInstances false

namespace BirthPhaseB3DirtySuccess

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWaitProjection
open BirthWaitClockMass.Line
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Rotation

variable {n psi kappa tau : Nat}

/-- An actual current-consumer configuration together with exactly the B4
carrier premise.  The proof field is not protocol state. -/
abbrev CarrierState
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n) :=
  { C : BirthPhaseWait2BlockProgress.FC n psi kappa tau //
      BirthPhaseWait2BlockProgress.Carrier
        hpsi h2 hn ring anchor C }

/-- Canonical width-two raw seed attached to an actual local carrier.

The canonical raw sites 0 and 1 are the real projected anchor and successor.
Other raw-ring sites are filled by the projected root cell only to totalize the
`Fin n -> AgentState 2` argument expected by `DirtyMass`; no claim is made that
this filler is a global physical projection.  The later B3 bridge must use
`RowProjection2` for actual pre-cap rows. -/
def projectedSeed
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (x : CarrierState (kappa := kappa) (tau := tau)
      hpsi h2 hn ring anchor) :
    Fin n -> AgentState 2 :=
  let hlocal : BirthPhaseWait2Transfer.LocalWait2Carrier
      hpsi h2 hn ring anchor x.1 := by
    have hx := x.2
    unfold BirthPhaseWait2BlockProgress.Carrier at hx
    unfold BirthPhaseWait2BlockProgress.LocalCarrier at hx
    exact hx.1
  let h0 : (raw (x.1 anchor)).label.val < 2 := by
    have h := hlocal
    unfold BirthPhaseWait2Transfer.LocalWait2Carrier at h
    rw [h.lab0]
    omega
  let h1 :
      (raw (x.1 (ring.rightNeighbor anchor))).label.val < 2 := by
    have h := hlocal
    unfold BirthPhaseWait2Transfer.LocalWait2Carrier at h
    rw [h.lab1]
    omega
  fun i =>
    if i = p1 hn then
      waitPrefixProject (width := 2)
        (raw (x.1 (ring.rightNeighbor anchor))) h1
    else
      waitPrefixProject (width := 2) (raw (x.1 anchor)) h0

/-- Raw width-two dirty first-increase, pulled back to the same original
physical scheduler word.  `unrotateWord` is only a coordinate permutation; it
does not filter or reweight scheduler letters. -/
noncomputable def dirtySuccessBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (x : CarrierState (kappa := kappa) (tau := tau)
      hpsi h2 hn ring anchor)
    (u : List (Fin n)) : Bool := by
  classical
  exact if
    BirthWaitClockMass.DirtyMass.DirtyIncreaseWithin
      (w := 2) (n := n)
      (by decide : 2 <= 2) (by omega : 2 < n) kappa
      (projectedSeed hpsi h2 hn ring anchor x)
      (unrotateWord ring anchor u)
    then true else false

/-- The relation to pass to the B3/B4 bridge once a `CarrierState` has been
extracted from the B4 `Allowed` state. -/
def DirtySuccess
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (x : CarrierState (kappa := kappa) (tau := tau)
      hpsi h2 hn ring anchor)
    (u : List (Fin n)) : Prop :=
  dirtySuccessBit hpsi h2 hn ring anchor x u = true

/-- Fact 1: the pulled-back success relation is decidable because its public
interface is equality of a Boolean with `true`. -/
noncomputable instance dirtySuccess_decidable
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (x : CarrierState (kappa := kappa) (tau := tau)
      hpsi h2 hn ring anchor)
    (u : List (Fin n)) :
    Decidable (DirtySuccess hpsi h2 hn ring anchor x u) := by
  unfold DirtySuccess
  infer_instance

/-- Fact 2: exact scheduler-word pullback.  The first conjunct is equality of
numerators, not merely a lower bound.  The second conjunct is the width-two
`1/128` mass after rewriting
`2^(DirtyMass.requestedLength 2 + 1) = 128`. -/
theorem dirtySuccess_wordSum_eq_raw_and_mass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (x : CarrierState (kappa := kappa) (tau := tau)
      hpsi h2 hn ring anchor) :
    let T := BirthWaitClockMass.DirtyMass.horizon n 2
    let W := FixedSpanRenewalPayload.wordSum n T
      (fun u => if DirtySuccess hpsi h2 hn ring anchor x u then 1 else 0)
    W = BirthWaitClockMass.DirtyMass.dirtyNumerator
        (by decide : 2 <= 2) (by omega : 2 < n) kappa
        (projectedSeed hpsi h2 hn ring anchor x) T /\
      n ^ T <= 128 * W := by
  classical
  dsimp only
  have hlocal : BirthPhaseWait2Transfer.LocalWait2Carrier
      hpsi h2 hn ring anchor x.1 := by
    have hx := x.2
    unfold BirthPhaseWait2BlockProgress.Carrier at hx
    unfold BirthPhaseWait2BlockProgress.LocalCarrier at hx
    exact hx.1
  have hline := hlocal
  unfold BirthPhaseWait2Transfer.LocalWait2Carrier at hline

  have hlabels : forall i : Fin 2,
      (projectedSeed hpsi h2 hn ring anchor x
        (BirthWaitClockMass.RawRing.site
          (by omega : 2 < n) i)).label = i := by
    intro i
    have hi : i.val = 0 \/ i.val = 1 := by omega
    rcases hi with hi | hi
    · have hne :
          BirthWaitClockMass.RawRing.site (by omega : 2 < n) i ≠
            p1 hn := by
        intro hbad
        have hv := congrArg Fin.val hbad
        change i.val = 1 at hv
        omega
      apply Fin.ext
      simp only [projectedSeed, hne, if_neg,
        waitPrefixProject_label_val]
      exact hline.lab0.trans hi.symm
    · have heq :
          BirthWaitClockMass.RawRing.site (by omega : 2 < n) i =
            p1 hn := by
        apply Fin.ext
        exact hi
      apply Fin.ext
      simp only [projectedSeed, heq, if_pos,
        waitPrefixProject_label_val]
      exact hline.lab1.trans hi.symm

  have hsite :
      BirthWaitClockMass.RawRing.site (by omega : 2 < n)
          (BirthWaitClockMass.Line.last (by decide : 2 <= 2)) = p1 hn := by
    apply Fin.ext
    rfl
  have hcount :
      (projectedSeed hpsi h2 hn ring anchor x
        (BirthWaitClockMass.RawRing.site (by omega : 2 < n)
          (BirthWaitClockMass.Line.last (by decide : 2 <= 2)))).count =
        BirthPhaseWait2BlockProgress.shortCountAt ring anchor x.1 := by
    rw [hsite]
    simp [projectedSeed,
      BirthPhaseWait2BlockProgress.shortCountAt,
      BirthWaitPassive.raw, BoundedAgentState.erase]
  have hbelow :
      (projectedSeed hpsi h2 hn ring anchor x
        (BirthWaitClockMass.RawRing.site (by omega : 2 < n)
          (BirthWaitClockMass.Line.last (by decide : 2 <= 2)))).count < kappa := by
    rw [hcount]
    have hx := x.2
    unfold BirthPhaseWait2BlockProgress.Carrier at hx
    exact hx.2

  have hindicator (u : List (Fin n)) :
      (if DirtySuccess hpsi h2 hn ring anchor x u then 1 else 0) =
        BirthWaitClockMass.DirtyMass.dirtyBit
          (by decide : 2 <= 2) (by omega : 2 < n) kappa
          (projectedSeed hpsi h2 hn ring anchor x)
          (unrotateWord ring anchor u) := by
    by_cases h : BirthWaitClockMass.DirtyMass.DirtyIncreaseWithin
        (w := 2) (n := n)
        (by decide : 2 <= 2) (by omega : 2 < n) kappa
        (projectedSeed hpsi h2 hn ring anchor x)
        (unrotateWord ring anchor u)
    · simp [DirtySuccess, dirtySuccessBit,
        BirthWaitClockMass.DirtyMass.dirtyBit, h]
    · simp [DirtySuccess, dirtySuccessBit,
        BirthWaitClockMass.DirtyMass.dirtyBit, h]

  have hfun :
      (fun u : List (Fin n) =>
        if DirtySuccess hpsi h2 hn ring anchor x u then 1 else 0) =
      (fun u => BirthWaitClockMass.DirtyMass.dirtyBit
        (by decide : 2 <= 2) (by omega : 2 < n) kappa
        (projectedSeed hpsi h2 hn ring anchor x)
        (unrotateWord ring anchor u)) := by
    funext u
    exact hindicator u

  have hreindex :
      FixedSpanRenewalPayload.wordSum n
          (BirthWaitClockMass.DirtyMass.horizon n 2)
          (fun u => BirthWaitClockMass.DirtyMass.dirtyBit
            (by decide : 2 <= 2) (by omega : 2 < n) kappa
            (projectedSeed hpsi h2 hn ring anchor x)
            (unrotateWord ring anchor u)) =
        FixedSpanRenewalPayload.wordSum n
          (BirthWaitClockMass.DirtyMass.horizon n 2)
          (BirthWaitClockMass.DirtyMass.dirtyBit
            (by decide : 2 <= 2) (by omega : 2 < n) kappa
            (projectedSeed hpsi h2 hn ring anchor x)) := by
    simpa only [unrotateWord] using
      (BirthShortDoneTerminalPassiveLocal3Rotation.wordSum_reindex
        (forward := unrotateIndex ring anchor)
        (backward := rotateIndex ring anchor)
        (hleft := rotateIndex_unrotateIndex ring anchor)
        (hright := unrotateIndex_rotateIndex ring anchor)
        (BirthWaitClockMass.DirtyMass.horizon n 2)
        (BirthWaitClockMass.DirtyMass.dirtyBit
          (by decide : 2 <= 2) (by omega : 2 < n) kappa
          (projectedSeed hpsi h2 hn ring anchor x)))

  have heq :
      FixedSpanRenewalPayload.wordSum n
          (BirthWaitClockMass.DirtyMass.horizon n 2)
          (fun u =>
            if DirtySuccess hpsi h2 hn ring anchor x u then 1 else 0) =
        BirthWaitClockMass.DirtyMass.dirtyNumerator
          (by decide : 2 <= 2) (by omega : 2 < n) kappa
          (projectedSeed hpsi h2 hn ring anchor x)
          (BirthWaitClockMass.DirtyMass.horizon n 2) := by
    rw [hfun]
    unfold BirthWaitClockMass.DirtyMass.dirtyNumerator
    exact hreindex

  have hraw := BirthWaitClockMass.DirtyMass.raw_dirty_firstIncrease_mass
    (w := 2) (n := n)
    (by decide : 2 <= 2) (by omega : 2 < n) kappa
    (projectedSeed hpsi h2 hn ring anchor x) hlabels hbelow
  rw [BirthPhaseWait2BlockProgress.dirty_factor_eq_Q] at hraw
  have hmass :
      n ^ BirthWaitClockMass.DirtyMass.horizon n 2 <=
        128 * BirthWaitClockMass.DirtyMass.dirtyNumerator
          (by decide : 2 <= 2) (by omega : 2 < n) kappa
          (projectedSeed hpsi h2 hn ring anchor x)
          (BirthWaitClockMass.DirtyMass.horizon n 2) := by
    simpa [BirthPhaseWait2BlockProgress.Q] using hraw
  rw [<- heq] at hmass
  exact ⟨heq, hmass⟩

/-- The literal state, now packaged with the B4 carrier's sub-cap rank
premise. -/
def boundaryCarrier :
    CarrierState (n := 4) (psi := 2) (kappa := 2) (tau := 3)
      (by decide : 0 < 2) (by decide : 2 <= 2) (by decide : 4 <= 4)
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4 :=
  ⟨BirthPhaseWait2Transfer.boundaryConfig4, by
    unfold BirthPhaseWait2BlockProgress.Carrier
    constructor
    · unfold BirthPhaseWait2BlockProgress.LocalCarrier
      exact
        BirthPhaseWait2Transfer.boundary_outgoing_preCap_destroys_carrier.1
    · decide
  ⟩

/-- Fact 3: the destroying edge is not in the dirty first-increase
event.  It is a pre-cap boundary stop, and the tracked endpoint count does not
increase. -/
theorem boundary_word_classification :
    dirtySuccessBit
        (by decide : 0 < 2) (by decide : 2 <= 2) (by decide : 4 <= 4)
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4 boundaryCarrier
        [BirthPhaseWait2Transfer.boundaryEdge4] = false /\
      (¬ BirthShortDoneTerminalPassiveR4.RowCap2
        (by decide : 0 < 2) (by decide : 2 <= 2) 2
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryConfig4
        BirthPhaseWait2Transfer.boundaryEdge4) /\
      BirthPhaseWait2Transfer.LocalWait2BoundaryNow
        (by decide : 4 <= 4)
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4
        BirthPhaseWait2Transfer.boundaryEdge4 /\
      BirthPhaseWait2BlockProgress.shortCountAt
          BirthPhaseWait2Transfer.boundaryRing4
          BirthPhaseWait2Transfer.boundaryAnchor4
          BirthPhaseWait2Transfer.boundaryConfig4 =
        BirthPhaseWait2BlockProgress.shortCountAt
          BirthPhaseWait2Transfer.boundaryRing4
          BirthPhaseWait2Transfer.boundaryAnchor4
          (BirthPhaseWait2BlockProgress.currentStep2
            (by decide : 0 < 2) (by decide : 2 <= 2)
            BirthPhaseWait2Transfer.boundaryRing4
            BirthPhaseWait2Transfer.boundaryConfig4
            BirthPhaseWait2Transfer.boundaryEdge4) := by
  classical
  let C2 : Fin 4 -> AgentState 2 :=
    projectedSeed
      (by decide : 0 < 2) (by decide : 2 <= 2) (by decide : 4 <= 4)
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4 boundaryCarrier
  let t : Fin 4 := BirthWaitClockMass.RawRing.site
    (by decide : 2 < 4)
    (BirthWaitClockMass.Line.last (by decide : 2 <= 2))

  have hunrotate :
      unrotateWord BirthPhaseWait2Transfer.boundaryRing4
          BirthPhaseWait2Transfer.boundaryAnchor4
          [BirthPhaseWait2Transfer.boundaryEdge4] =
        [BirthPhaseWait2Transfer.boundaryEdge4] := by
    decide

  have hrawFrame :
      (BirthWaitClockMass.RawRing.rawRun
        (by decide : 2 < 4) (by decide : 2 <= 2) 2 C2
        [BirthPhaseWait2Transfer.boundaryEdge4] t).count =
      (C2 t).count := by
    change
      (BirthWaitClockMass.RawRing.rawStep
        (by decide : 2 < 4) (by decide : 2 <= 2) 2 C2
        BirthPhaseWait2Transfer.boundaryEdge4 t).count =
      (C2 t).count
    have hte : t ≠ BirthPhaseWait2Transfer.boundaryEdge4 := by decide
    have htr : t ≠
        (BirthWaitClockMass.RawRing.ring
          (by decide : 2 < 4)).rightNeighbor
            BirthPhaseWait2Transfer.boundaryEdge4 := by decide
    unfold BirthWaitClockMass.RawRing.rawStep
    rw [updatePair_other C2 BirthPhaseWait2Transfer.boundaryEdge4
      ((BirthWaitClockMass.RawRing.ring
        (by decide : 2 < 4)).rightNeighbor
          BirthPhaseWait2Transfer.boundaryEdge4) t _ hte htr]

  have hnotDirty :
      ¬ BirthWaitClockMass.DirtyMass.DirtyIncreaseWithin
        (w := 2) (n := 4)
        (by decide : 2 <= 2) (by decide : 2 < 4) 2 C2
        [BirthPhaseWait2Transfer.boundaryEdge4] := by
    intro h
    rcases h with ⟨pre, post, heq, hinc⟩
    have hlen := congrArg List.length heq
    simp only [List.length_singleton, List.length_append] at hlen
    cases pre with
    | nil =>
        simpa [BirthWaitClockMass.RawRing.rawRun] using hinc
    | cons a rest =>
        cases rest with
        | nil =>
            cases post with
            | nil =>
                simp at heq
                subst a
                change (C2 t).count <
                  (BirthWaitClockMass.RawRing.rawRun
                    (by decide : 2 < 4) (by decide : 2 <= 2) 2 C2
                    [BirthPhaseWait2Transfer.boundaryEdge4] t).count at hinc
                rw [hrawFrame] at hinc
                exact Nat.lt_irrefl _ hinc
            | cons b bs =>
                simp only [List.length_cons, List.length_nil] at hlen
                omega
        | cons b rest =>
            simp only [List.length_cons] at hlen
            omega

  have hfalse :
      dirtySuccessBit
          (by decide : 0 < 2) (by decide : 2 <= 2) (by decide : 4 <= 4)
          BirthPhaseWait2Transfer.boundaryRing4
          BirthPhaseWait2Transfer.boundaryAnchor4 boundaryCarrier
          [BirthPhaseWait2Transfer.boundaryEdge4] = false := by
    unfold dirtySuccessBit
    rw [hunrotate]
    change (if BirthWaitClockMass.DirtyMass.DirtyIncreaseWithin
      (by decide : 2 <= 2) (by decide : 2 < 4) 2 C2
      [BirthPhaseWait2Transfer.boundaryEdge4] then true else false) = false
    simp [hnotDirty]

  have hb :=
    BirthPhaseWait2Transfer.boundary_outgoing_preCap_destroys_carrier
  have hnocap :
      ¬ BirthShortDoneTerminalPassiveR4.RowCap2
        (by decide : 0 < 2) (by decide : 2 <= 2) 2
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryConfig4
        BirthPhaseWait2Transfer.boundaryEdge4 := by
    simpa only [BirthShortDoneTerminalPassiveR4.RowPreCap2] using hb.2.1
  have hboundary : BirthPhaseWait2Transfer.LocalWait2BoundaryNow
      (by decide : 4 <= 4)
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4
      BirthPhaseWait2Transfer.boundaryEdge4 := by
    unfold BirthPhaseWait2Transfer.LocalWait2BoundaryNow
    exact hb.2.2.1

  let i := BirthPhaseWait2Transfer.boundaryRing4.rightNeighbor
    BirthPhaseWait2Transfer.boundaryAnchor4
  have hhost :
      BirthShortDoneTerminalPassiveR4.hostStep
          (by decide : 0 < 2) (by decide : 2 <= 2)
          BirthPhaseWait2Transfer.boundaryRing4
          BirthPhaseWait2Transfer.boundaryConfig4
          BirthPhaseWait2Transfer.boundaryEdge4 i =
        BirthPhaseWait2Transfer.boundaryConfig4 i := by
    apply BirthShortDoneTerminalPassiveR4.hostStep_other
    · decide
    · decide
  have hstepEq := BirthPhaseWait2BlockProgress.hostStep_eq_currentStep2
    (kappa := 2) (tau := 3)
    (by decide : 0 < 2) (by decide : 2 <= 2)
    BirthPhaseWait2Transfer.boundaryRing4
    BirthPhaseWait2Transfer.boundaryConfig4
    BirthPhaseWait2Transfer.boundaryEdge4
  have hcur :
      BirthPhaseWait2BlockProgress.currentStep2
          (by decide : 0 < 2) (by decide : 2 <= 2)
          BirthPhaseWait2Transfer.boundaryRing4
          BirthPhaseWait2Transfer.boundaryConfig4
          BirthPhaseWait2Transfer.boundaryEdge4 i =
        BirthPhaseWait2Transfer.boundaryConfig4 i :=
    (congrArg (fun D => D i) hstepEq).symm.trans hhost
  have hcountEq := congrArg
    (fun z : ExpiringAgentState 2 2 3 => z.core.core.count.val) hcur
  have hend :
      BirthPhaseWait2BlockProgress.shortCountAt
          BirthPhaseWait2Transfer.boundaryRing4
          BirthPhaseWait2Transfer.boundaryAnchor4
          BirthPhaseWait2Transfer.boundaryConfig4 =
        BirthPhaseWait2BlockProgress.shortCountAt
          BirthPhaseWait2Transfer.boundaryRing4
          BirthPhaseWait2Transfer.boundaryAnchor4
          (BirthPhaseWait2BlockProgress.currentStep2
            (by decide : 0 < 2) (by decide : 2 <= 2)
            BirthPhaseWait2Transfer.boundaryRing4
            BirthPhaseWait2Transfer.boundaryConfig4
            BirthPhaseWait2Transfer.boundaryEdge4) := by
    simpa [BirthPhaseWait2BlockProgress.shortCountAt, i] using hcountEq.symm
  exact ⟨hfalse, hnocap, hboundary, hend⟩

#print axioms BirthPhaseB3DirtySuccess.dirtySuccess_decidable
#print axioms BirthPhaseB3DirtySuccess.dirtySuccess_wordSum_eq_raw_and_mass
#print axioms BirthPhaseB3DirtySuccess.boundary_word_classification

end BirthPhaseB3DirtySuccess
