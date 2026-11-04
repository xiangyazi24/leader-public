import Leader.Wu.Birth.IncreaseOrCapNoBoundarySurvival

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthPhaseB3CoverageFour

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Rotation

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

private theorem right_anchor_is_safe
    (hn : 4 <= n) (ring : DirectedRing n) (anchor : Fin n) :
    SafeLine3EdgeAt hn ring anchor (ring.rightNeighbor anchor) := by
  unfold SafeLine3EdgeAt SafeLine3Edge
  have h := congrArg (unrotateIndex ring anchor)
    (rotateIndex_p1 hn ring anchor)
  have hp :
      unrotateIndex ring anchor (ring.rightNeighbor anchor) = p1 hn := by
    simpa only [unrotateIndex_rotateIndex] using h.symm
  rw [hp]
  constructor
  · intro he
    have hv := congrArg Fin.val he
    change 1 = 2 at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    change 1 = n - 1 at hv
    omega

/-- A Local3 crossing never touches the tracked p1 site. -/
theorem crossing_shortCount_frame
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n)
    (hb : BirthPhaseWait2Transfer.LocalWait2BoundaryNow hn ring anchor e) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C =
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) := by
  have hboundary := hb
  unfold BirthPhaseWait2Transfer.LocalWait2BoundaryNow at hboundary
  have he0 : e ≠ anchor := by
    intro he
    subst e
    exact hboundary
      (BirthPhaseB3BridgeStageA.anchor_is_safe hn ring anchor)
  have he1 : e ≠ ring.rightNeighbor anchor := by
    intro he
    subst e
    exact hboundary (right_anchor_is_safe hn ring anchor)
  have hf := BirthPhaseB3NoBoundarySurvival.other_edge_count_frame
    (kappa := kappa) (tau := tau)
    hpsi h2 ring anchor e C he0 he1
  rw [BirthPhaseWait2BlockProgress.hostStep_eq_currentStep2
    hpsi h2 ring C e] at hf
  exact hf

/-- The fourth row case: execute a pre-cap crossing, reseed at the successor
Carrier, and record that the B4 rank did not move. -/
def SurvivingCrossingRow
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  let D := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e
  BirthPhaseWait2BlockProgress.Carrier hpsi h2 hn ring anchor C /\
    RowPreCap2 hpsi h2 kappa ring C e /\
    BirthPhaseWait2Transfer.LocalWait2BoundaryNow hn ring anchor e /\
    BirthPhaseWait2BlockProgress.Carrier hpsi h2 hn ring anchor D /\
    BirthPhaseWait2BlockProgress.rank kappa ring anchor D =
      BirthPhaseWait2BlockProgress.rank kappa ring anchor C

def SurvivingCrossingWithin
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  exists pre e post,
    u = pre ++ (e :: post) /\
      SurvivingCrossingRow hpsi h2 hn kappa tau ring anchor
        (pre.foldl
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C) e

/-- Replacement for Stage A's old three-way carrier coverage. -/
def CarrierDirtyCaseCoverage4
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor) : Prop :=
  forall u : List (Fin n),
    u.length = BirthPhaseWait2BlockProgress.L n ->
    BirthPhaseB3DirtySuccess.DirtySuccess hpsi h2 hn ring anchor x u ->
      BirthPhaseWait2BlockProgress.FirstCapWithin
          hpsi h2 kappa ring x.1 u \/
      BirthPhaseWait2BlockProgress.rank kappa ring anchor
          (BirthPhaseGenericRenewal.rawEndpoint
            (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) x.1 u) <
        BirthPhaseWait2BlockProgress.rank kappa ring anchor x.1 \/
      BirthPhaseB3BridgeStageA.BoundaryCaseWithin
          hpsi h2 hn kappa tau ring anchor x.1 u \/
      SurvivingCrossingWithin
          hpsi h2 hn kappa tau ring anchor x.1 u

/-- The upstream suffix scan stops at its first crossing.  The prefix is a
literal no-stop run and its endpoint is still a B4 Carrier. -/
def FirstCrossingWithin
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  exists pre e post,
    u = pre ++ (e :: post) /\
    BirthPhaseWait2Transfer.LocalWait2RunSource
      hpsi h2 hn kappa tau ring anchor C pre /\
    BirthPhaseWait2BlockProgress.Carrier hpsi h2 hn ring anchor
      (pre.foldl (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C) /\
    RowPreCap2 hpsi h2 kappa ring
      (pre.foldl (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C) e /\
    BirthPhaseWait2Transfer.LocalWait2BoundaryNow hn ring anchor e

def SuffixStopTrichotomy
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  BirthPhaseWait2BlockProgress.FirstCapWithin hpsi h2 kappa ring C u \/
  FirstCrossingWithin hpsi h2 hn kappa tau ring anchor C u \/
  BirthPhaseWait2Transfer.LocalWait2RunSource
    hpsi h2 hn kappa tau ring anchor C u

def SuffixFourWay
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  BirthPhaseWait2BlockProgress.FirstCapWithin hpsi h2 kappa ring C u \/
  BirthPhaseB3BridgeStageA.BoundaryCaseWithin
    hpsi h2 hn kappa tau ring anchor C u \/
  SurvivingCrossingWithin hpsi h2 hn kappa tau ring anchor C u \/
  BirthPhaseWait2Transfer.LocalWait2RunSource
    hpsi h2 hn kappa tau ring anchor C u

/-- Split the first crossing into break/restart.  Count framing keeps the
successor sub-cap, and in the restart arm also gives exact rank equality. -/
theorem suffix_trichotomy_to_four_way
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n))
    (h : SuffixStopTrichotomy
      hpsi h2 hn kappa tau ring anchor C u) :
    SuffixFourWay hpsi h2 hn kappa tau ring anchor C u := by
  rcases h with hcap | hcross | hnone
  · exact Or.inl hcap
  · rcases hcross with
      ⟨pre, e, post, hword, _hrun, hCpre, hpre, hb⟩
    let Cpre := pre.foldl
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C
    let D := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring Cpre e
    have hf := crossing_shortCount_frame
      hpsi h2 hn ring anchor Cpre e hb
    have hsub : BirthPhaseWait2BlockProgress.shortCountAt ring anchor D < kappa := by
      dsimp only [D]
      rw [← hf]
      exact hCpre.2
    by_cases hlocal : BirthPhaseWait2BlockProgress.LocalCarrier
        hpsi h2 hn ring anchor D
    · have hD : BirthPhaseWait2BlockProgress.Carrier
          hpsi h2 hn ring anchor D := ⟨hlocal, hsub⟩
      have hrank : BirthPhaseWait2BlockProgress.rank kappa ring anchor D =
          BirthPhaseWait2BlockProgress.rank kappa ring anchor Cpre := by
        dsimp only [D]
        unfold BirthPhaseWait2BlockProgress.rank
        rw [← hf]
      refine Or.inr (Or.inr (Or.inl ?_))
      refine ⟨pre, e, post, hword, ?_⟩
      simpa [Cpre, D, SurvivingCrossingRow] using
        And.intro hCpre (And.intro hpre
          (And.intro hb (And.intro hD hrank)))
    · refine Or.inr (Or.inl ?_)
      refine ⟨pre, e, post, hword, ?_⟩
      have hbreak : BirthPhaseB3BridgeStageA.BoundaryBreakRow
          hpsi h2 hn kappa tau ring anchor Cpre e := by
        refine ⟨hCpre, hpre, hb, ?_, ?_⟩
        · simpa [D] using hlocal
        · simpa [D] using hsub
      simpa [Cpre] using hbreak
  · exact Or.inr (Or.inr (Or.inr hnone))

/-- Sufficient mass contract if restart words are charged as failed blocks.
This is exactly the old Q=128 bound after filtering surviving crossings. -/
noncomputable def restartFreeDirtyBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor)
    (u : List (Fin n)) : Nat := by
  classical
  exact if BirthPhaseB3DirtySuccess.DirtySuccess
      hpsi h2 hn ring anchor x u /\
      ¬ SurvivingCrossingWithin
        hpsi h2 hn kappa tau ring anchor x.1 u
    then 1 else 0

def RestartFreeDirtyMass128
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor,
    n ^ BirthPhaseWait2BlockProgress.L n <=
      BirthPhaseWait2BlockProgress.Q *
        FixedSpanRenewalPayload.wordSum n
          (BirthPhaseWait2BlockProgress.L n)
          (restartFreeDirtyBit hpsi h2 hn kappa tau ring anchor x)

/-- The no-stop arm: micro 3b supplies `hprefix` and the strict physical fire;
micro 4a then carries that strict gain through the remaining no-stop suffix. -/
theorem none_case_from_micro_4a_3b
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C Cpre fired : FC n psi kappa tau)
    (hprefix : BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <=
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor Cpre)
    (hfire : BirthPhaseWait2BlockProgress.shortCountAt ring anchor Cpre <
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor fired)
    (hfired : BirthPhaseWait2Transfer.LocalWait2Carrier
      hpsi h2 hn ring anchor fired)
    (post : List (Fin n))
    (hrun : BirthPhaseWait2Transfer.LocalWait2RunSource
      hpsi h2 hn kappa tau ring anchor fired post) :
    BirthPhaseWait2BlockProgress.rank kappa ring anchor
        (BirthPhaseGenericRenewal.rawEndpoint
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) fired post) <
      BirthPhaseWait2BlockProgress.rank kappa ring anchor C := by
  exact BirthPhaseB3NoBoundarySurvival.noBoundaryNoCap_suffix_strict_rank_drop
    hpsi h2 hn kappa tau ring anchor C fired
      (Nat.lt_of_le_of_lt hprefix hfire) hfired post hrun

#print axioms BirthPhaseB3CoverageFour.crossing_shortCount_frame
#print axioms BirthPhaseB3CoverageFour.suffix_trichotomy_to_four_way
#print axioms BirthPhaseB3CoverageFour.none_case_from_micro_4a_3b

end BirthPhaseB3CoverageFour
