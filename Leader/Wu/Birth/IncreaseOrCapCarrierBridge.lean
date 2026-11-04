import Leader.Wu.Birth.IncreaseOrCapDirtySuccess
import Leader.Wu.Birth.FirstLeaderComposition


set_option autoImplicit false
set_option pp.structureInstances false


namespace BirthPhaseB3BridgeStageA


open PPLL PPLLRepair PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWaitProjection
open BirthWaitClockMass.Line
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Rotation


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau


/-! ## The exact mass adapter -/


/-- The raw theorem already gives the entire source inequality on a genuine
B4 carrier.  This is the Carrier half of `hmass_of_source.hsource`. -/
theorem carrier_hsource
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor) :
    n ^ BirthPhaseWait2BlockProgress.L n <=
      BirthPhaseWait2BlockProgress.Q *
        FixedSpanRenewalPayload.wordSum n
          (BirthPhaseWait2BlockProgress.L n)
          (fun u =>
            if BirthPhaseB3DirtySuccess.DirtySuccess
                hpsi h2 hn ring anchor x u
            then 1 else 0) := by
  have hm :=
    (BirthPhaseB3DirtySuccess.dirtySuccess_wordSum_eq_raw_and_mass
      hpsi h2 hn ring anchor x).2
  simpa [BirthPhaseWait2BlockProgress.Q] using hm


/-- A full B4 dirty relation agrees with the certified raw pullback whenever
its starting state is a genuine Carrier.  Nothing is asserted here on the
Reacquire side. -/
def CarrierDirtyAgreement
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau) : Prop :=
  forall (C : FC n psi kappa tau)
      (hC : BirthPhaseWait2BlockProgress.Carrier
        hpsi h2 hn ring anchor C)
      (u : List (Fin n)),
    DirtySuccess C u <->
      BirthPhaseB3DirtySuccess.DirtySuccess
        hpsi h2 hn ring anchor
        (⟨C, hC⟩ : BirthPhaseB3DirtySuccess.CarrierState
          (kappa := kappa) (tau := tau)
          hpsi h2 hn ring anchor) u


/-- Carrier specialization of `hsource` for any full relation that agrees
with the raw pullback there. -/
theorem carrier_hsource_of_agreement
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau)
    [hdec : forall C u, Decidable (DirtySuccess C u)]
    (hagrees : CarrierDirtyAgreement
      hpsi h2 hn kappa tau ring anchor DirtySuccess)
    (C : FC n psi kappa tau)
    (hC : BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor C) :
    n ^ BirthPhaseWait2BlockProgress.L n <=
      BirthPhaseWait2BlockProgress.Q *
        FixedSpanRenewalPayload.wordSum n
          (BirthPhaseWait2BlockProgress.L n)
          (fun u => if DirtySuccess C u then 1 else 0) := by
  let x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor :=
    ⟨C, hC⟩
  have hm := carrier_hsource hpsi h2 hn ring anchor x
  have hfun :
      (fun u : List (Fin n) => if DirtySuccess C u then 1 else 0) =
      (fun u : List (Fin n) =>
        if BirthPhaseB3DirtySuccess.DirtySuccess
            hpsi h2 hn ring anchor x u
        then 1 else 0) := by
    funext u
    have hiff :
        DirtySuccess C u <->
          BirthPhaseB3DirtySuccess.DirtySuccess
            hpsi h2 hn ring anchor x u := by
      simpa [x] using hagrees C hC u
    by_cases hd : DirtySuccess C u
    · have hr := hiff.mp hd
      simp [hd, hr]
    · have hr :
          ¬ BirthPhaseB3DirtySuccess.DirtySuccess
            hpsi h2 hn ring anchor x u := by
        intro hs
        exact hd (hiff.mpr hs)
      simp [hd, hr]
  rw [hfun]
  exact hm


/-- The genuinely missing half of `hmass_of_source.hsource`: B1 must provide
an event of the same `1/Q` mass when the active renewal state is Reacquire. -/
def ReacquireSourceMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau)
    [hdec : forall C u, Decidable (DirtySuccess C u)] : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
      n ^ BirthPhaseWait2BlockProgress.L n <=
        BirthPhaseWait2BlockProgress.Q *
          FixedSpanRenewalPayload.wordSum n
            (BirthPhaseWait2BlockProgress.L n)
            (fun u => if DirtySuccess C u then 1 else 0)


/-- Exact `hsource` requested by `hmass_of_source`, split along
`Allowed = Carrier ∨ Reacquire`. -/
theorem hsource_of_carrier_and_reacquire
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau)
    [hdec : forall C u, Decidable (DirtySuccess C u)]
    (hagrees : CarrierDirtyAgreement
      hpsi h2 hn kappa tau ring anchor DirtySuccess)
    (hreacquire : ReacquireSourceMass
      hpsi h2 hn kappa tau ring anchor DirtySuccess) :
    forall C : FC n psi kappa tau,
      BirthPhaseWait2BlockProgress.Allowed
          hpsi h2 hn kappa tau ring anchor C ->
        n ^ BirthPhaseWait2BlockProgress.L n <=
          BirthPhaseWait2BlockProgress.Q *
            FixedSpanRenewalPayload.wordSum n
              (BirthPhaseWait2BlockProgress.L n)
              (fun u => if DirtySuccess C u then 1 else 0) := by
  intro C hAllowed
  change
    BirthPhaseWait2BlockProgress.Carrier
        hpsi h2 hn ring anchor C \/
      BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C at hAllowed
  rcases hAllowed with hC | hR
  · exact carrier_hsource_of_agreement
      hpsi h2 hn kappa tau ring anchor
      DirtySuccess hagrees C hC
  · exact hreacquire C hR


/-- Once the missing Reacquire source is supplied, the existing B4 adapter
closes `HMass` with no further probability argument. -/
theorem hmass_of_carrier_and_reacquire
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau)
    [hdec : forall C u, Decidable (DirtySuccess C u)]
    (hagrees : CarrierDirtyAgreement
      hpsi h2 hn kappa tau ring anchor DirtySuccess)
    (hreacquire : ReacquireSourceMass
      hpsi h2 hn kappa tau ring anchor DirtySuccess) :
    BirthPhaseWait2BlockProgress.HMass
      hpsi h2 hn kappa tau ring anchor DirtySuccess := by
  apply BirthPhaseWait2BlockProgress.hmass_of_source
    hpsi h2 hn kappa tau ring anchor DirtySuccess
  exact hsource_of_carrier_and_reacquire
    hpsi h2 hn kappa tau ring anchor
    DirtySuccess hagrees hreacquire


/-! ## Width-two raw geometry -/


/-- At width two there is one internal raw service port, canonical edge p0. -/
theorem raw_width_two_service_edge_eq_p0
    (hn : 4 <= n) :
    BirthWaitClockMass.RawRing.port
        (w := 2) (n := n) (by omega : 2 < n) (0 : Fin 1) =
      p0 hn := by
  apply Fin.ext
  rfl


/-- The tracked width-two raw terminal is canonical site p1. -/
theorem raw_width_two_terminal_site_eq_p1
    (hn : 4 <= n) :
    BirthWaitClockMass.RawRing.site
        (w := 2) (n := n) (by omega : 2 < n)
        (BirthWaitClockMass.Line.last (by decide : 2 <= 2)) =
      p1 hn := by
  apply Fin.ext
  rfl


/-- The unique raw service edge rotates to the actual physical anchor. -/
theorem raw_width_two_service_rotates_to_anchor
    (hn : 4 <= n) (ring : DirectedRing n) (anchor : Fin n) :
    rotateIndex ring anchor
        (BirthWaitClockMass.RawRing.port
          (w := 2) (n := n) (by omega : 2 < n) (0 : Fin 1)) =
      anchor := by
  rw [raw_width_two_service_edge_eq_p0 (n := n) hn]
  exact rotateIndex_p0 hn ring anchor


/-- The raw terminal p1 rotates to the physical count site used by
`shortCountAt`. -/
theorem raw_width_two_terminal_rotates_to_shortCount_site
    (hn : 4 <= n) (ring : DirectedRing n) (anchor : Fin n) :
    rotateIndex ring anchor
        (BirthWaitClockMass.RawRing.site
          (w := 2) (n := n) (by omega : 2 < n)
          (BirthWaitClockMass.Line.last (by decide : 2 <= 2))) =
      ring.rightNeighbor anchor := by
  rw [raw_width_two_terminal_site_eq_p1 (n := n) hn]
  exact rotateIndex_p1 hn ring anchor


/-- In inverse coordinates the physical anchor is canonical p0. -/
theorem unrotate_anchor_eq_p0
    (hn : 4 <= n) (ring : DirectedRing n) (anchor : Fin n) :
    unrotateIndex ring anchor anchor = p0 hn := by
  have h := congrArg (unrotateIndex ring anchor)
    (rotateIndex_p0 hn ring anchor)
  simpa only [unrotateIndex_rotateIndex] using h.symm


/-- Therefore the physical anchor row is one of the two internal Local3 rows. -/
theorem anchor_is_internal
    (hn : 4 <= n) (ring : DirectedRing n) (anchor : Fin n) :
    InternalLine3EdgeAt hn ring anchor anchor := by
  unfold InternalLine3EdgeAt InternalLine3Edge
  rw [unrotate_anchor_eq_p0 hn ring anchor]
  exact Or.inl rfl


/-- The physical anchor row is not either Local3 crossing edge. -/
theorem anchor_is_safe
    (hn : 4 <= n) (ring : DirectedRing n) (anchor : Fin n) :
    SafeLine3EdgeAt hn ring anchor anchor := by
  unfold SafeLine3EdgeAt SafeLine3Edge
  rw [unrotate_anchor_eq_p0 hn ring anchor]
  constructor
  · intro h
    have hv := congrArg Fin.val h
    change 0 = 2 at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change 0 = n - 1 at hv
    omega


/-- In particular, the dirty firing row itself is never the B2 boundary stop. -/
theorem anchor_is_not_boundary
    (hn : 4 <= n) (ring : DirectedRing n) (anchor : Fin n) :
    ¬ BirthPhaseWait2Transfer.LocalWait2BoundaryNow
      hn ring anchor anchor := by
  intro hboundary
  unfold BirthPhaseWait2Transfer.LocalWait2BoundaryNow at hboundary
  exact hboundary (anchor_is_safe hn ring anchor)


/-! ## Raw first-strict-step extraction: named Stage B gap -/


/-- A single strict raw firing row.  The source event `DirtyIncreaseWithin`
only gives a prefix net increase; Stage B should choose the first strict step
of that prefix.  At width two that step must be p0 -> p1. -/
def RawWidthTwoServiceFire
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor)
    (u : List (Fin n)) : Prop :=
  exists pre post,
    unrotateWord ring anchor u = pre ++ (p0 hn :: post) /\
      (let S := BirthWaitClockMass.RawRing.rawRun
          (w := 2) (n := n) (by omega : 2 < n)
          (by decide : 2 <= 2) kappa
          (BirthPhaseB3DirtySuccess.projectedSeed
            hpsi h2 hn ring anchor x) pre
       (S (p1 hn)).count <
         (BirthWaitClockMass.RawRing.rawStep
           (w := 2) (n := n) (by omega : 2 < n)
           (by decide : 2 <= 2) kappa S (p0 hn) (p1 hn)).count)


/-- Missing extraction lemma.  It is deliberately a proposition, not a
placeholder theorem: prove it in Stage B from `DirtyIncreaseWithin` by taking
the first strict terminal-count step. -/
def DirtySuccessRawFireExtraction
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor) : Prop :=
  forall u : List (Fin n),
    BirthPhaseB3DirtySuccess.DirtySuccess
        hpsi h2 hn ring anchor x u ->
      RawWidthTwoServiceFire hpsi h2 hn ring anchor x u


/-- Once a raw p0 firing witness has been extracted, its scheduler letter in
the original physical word is literally the anchor. -/
theorem raw_service_fire_has_physical_anchor_decomposition
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor)
    (u : List (Fin n))
    (hfire : RawWidthTwoServiceFire hpsi h2 hn ring anchor x u) :
    exists pre post, u = pre ++ (anchor :: post) := by
  rcases hfire with ⟨rpre, rpost, hword, _hinc⟩
  refine ⟨rotateWord ring anchor rpre,
    rotateWord ring anchor rpost, ?_⟩
  calc
    u = rotateWord ring anchor (unrotateWord ring anchor u) :=
      (rotateWord_unrotateWord ring anchor u).symm
    _ = rotateWord ring anchor (rpre ++ (p0 hn :: rpost)) := by
      rw [hword]
    _ = rotateWord ring anchor rpre ++
        (anchor :: rotateWord ring anchor rpost) := by
      simp [rotateWord]


/-! ## The three physical cases -/


/-- A cap exposed at a physical decomposition is already the exact B4 target. -/
theorem rowCap_in_word_gives_target
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (u pre post : List (Fin n))
    (hword : u = pre ++ (anchor :: post))
    (hcap : BirthShortDoneTerminalPassiveR4.RowCap2
      hpsi h2 kappa ring
      (pre.foldl
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C)
      anchor) :
    BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C u = true := by
  apply (BirthPhaseWait2BlockProgress.target_true_iff
    hpsi h2 kappa ring C u).2
  exact ⟨pre, anchor, post, hword, hcap⟩


/-- On the non-cap branch the physical firing row is safe and internal, hence
the existing B2 one-edge theorem preserves Local3 and supplies RowProjection2. -/
theorem anchor_preCap_preserves_carrier_and_projects
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (hC : BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor C)
    (hpre : BirthShortDoneTerminalPassiveR4.RowPreCap2
      hpsi h2 kappa ring C anchor) :
    BirthPhaseWait2BlockProgress.LocalCarrier
        hpsi h2 hn ring anchor
        (BirthPhaseWait2BlockProgress.currentStep2
          hpsi h2 ring C anchor) /\
      BirthShortDoneTerminalPassiveR4.RowProjection2
        hpsi h2 kappa tau ring C anchor := by
  have hlocal : BirthPhaseWait2Transfer.LocalWait2Carrier
      hpsi h2 hn ring anchor C := by
    exact hC.1
  have hs := BirthPhaseWait2Transfer.local_wait2_one_edge
    hpsi h2 hn kappa tau ring anchor C hlocal anchor
    (anchor_is_safe hn ring anchor) (fun _ => hpre)
  have hstep := BirthPhaseWait2BlockProgress.hostStep_eq_currentStep2
    hpsi h2 ring C anchor
  rw [hstep] at hs
  exact ⟨hs.1, hs.2 (anchor_is_internal hn ring anchor)⟩


/-- Endpoint count progress is exactly the strict rank drop used after
`hgood_of_dirty_bridge`. -/
theorem endpoint_increase_is_strict_rank_drop
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C D : FC n psi kappa tau)
    (hinc : BirthPhaseWait2BlockProgress.shortCountAt
        ring anchor C <
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor D) :
    BirthPhaseWait2BlockProgress.rank kappa ring anchor D <
      BirthPhaseWait2BlockProgress.rank kappa ring anchor C := by
  exact (BirthPhaseWait2BlockProgress.rank_lt_iff_shortCount_lt
    kappa ring anchor C D).2 hinc


/-- Exact pre-cap boundary row which leaves the Local3 carrier but stays below
cap. -/
def BoundaryBreakRow
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor C /\
    BirthShortDoneTerminalPassiveR4.RowPreCap2
      hpsi h2 kappa ring C e /\
    BirthPhaseWait2Transfer.LocalWait2BoundaryNow hn ring anchor e /\
    (¬ BirthPhaseWait2BlockProgress.LocalCarrier
      hpsi h2 hn ring anchor
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e)) /\
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) <
      kappa


/-- This case is immediate from the public B4 side-state constructor. -/
theorem boundary_break_row_gives_reacquire
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n)
    (h : BoundaryBreakRow
      hpsi h2 hn kappa tau ring anchor C e) :
    BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) := by
  rcases h with ⟨hC, hpre, hboundary, hbreak, hsub⟩
  exact BirthPhaseWait2BlockProgress.boundary_step_is_reacquire
    hpsi h2 hn kappa tau ring anchor e C
    hC hpre hboundary hbreak hsub


/-- A boundary occurrence somewhere in the literal block. -/
def BoundaryCaseWithin
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  exists pre e post,
    u = pre ++ (e :: post) /\
      BoundaryBreakRow hpsi h2 hn kappa tau ring anchor
        (pre.foldl
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C) e


/-- The boundary case really does expose an immediate Reacquire state at its
witnessed row. -/
theorem boundary_case_gives_reacquire_witness
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n))
    (h : BoundaryCaseWithin
      hpsi h2 hn kappa tau ring anchor C u) :
    exists pre e post,
      u = pre ++ (e :: post) /\
        BirthPhaseWait2BlockProgress.Reacquire
          hpsi h2 hn kappa tau ring anchor
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring
            (pre.foldl
              (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C)
            e) := by
  rcases h with ⟨pre, e, post, hword, hrow⟩
  refine ⟨pre, e, post, hword, ?_⟩
  exact boundary_break_row_gives_reacquire
    hpsi h2 hn kappa tau ring anchor
    (pre.foldl
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C)
    e hrow


/-! ## Remaining Stage B propositions -/


/-- The Carrier-start three-way census.  The first two disjuncts are exactly
the final B3 outcomes; the third records the intermediate B1 side-state. -/
def CarrierDirtyCaseCoverage
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (x : BirthPhaseB3DirtySuccess.CarrierState
      (kappa := kappa) (tau := tau) hpsi h2 hn ring anchor) : Prop :=
  forall u : List (Fin n),
    u.length = BirthPhaseWait2BlockProgress.L n ->
    BirthPhaseB3DirtySuccess.DirtySuccess
        hpsi h2 hn ring anchor x u ->
      BirthPhaseWait2BlockProgress.FirstCapWithin
          hpsi h2 kappa ring x.1 u \/
        BirthPhaseWait2BlockProgress.shortCountAt ring anchor x.1 <
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor
            (BirthPhaseGenericRenewal.rawEndpoint
              (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
              x.1 u) \/
        BoundaryCaseWithin
          hpsi h2 hn kappa tau ring anchor x.1 u


/-- The exact missing suffix statement for the third census case.  Since
`B3DirtySuccessBridge` has no Reacquire disjunct, the remaining literal suffix
must turn the boundary/reacquire case into cap or endpoint progress. -/
def BoundaryCaseResolvesBridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  forall u : List (Fin n),
    u.length = BirthPhaseWait2BlockProgress.L n ->
    BoundaryCaseWithin
        hpsi h2 hn kappa tau ring anchor C u ->
      BirthPhaseWait2BlockProgress.target
          hpsi h2 kappa ring C u = true \/
        BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor
            (BirthPhaseGenericRenewal.rawEndpoint
              (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
              C u)


/-- Starting from an already-active Reacquire state is a separate B1-side
pointwise obligation required because `B3DirtySuccessBridge` quantifies over
all `Allowed` states. -/
def ReacquireStartBridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall u : List (Fin n),
      u.length = BirthPhaseWait2BlockProgress.L n ->
      DirtySuccess C u ->
        BirthPhaseWait2BlockProgress.target
            hpsi h2 kappa ring C u = true \/
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
            BirthPhaseWait2BlockProgress.shortCountAt ring anchor
              (BirthPhaseGenericRenewal.rawEndpoint
                (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
                C u)


/-! ## The concrete boundary side-state is real -/


/-- Reacquire is disjoint from Carrier for the exact current definitions. -/
theorem reacquire_not_carrier
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (hR : BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor C) :
    ¬ BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor C := by
  intro hC
  exact hR.2.1 hC.1


/-- The public fixture actually lands in the B4 Reacquire side-state.
This also certifies that the missing Reacquire source/bridge branches are not
vacuous artifacts of the definitions. -/
theorem boundary_fixture_successor_is_reacquire :
    BirthPhaseWait2BlockProgress.Reacquire
      (by decide : 0 < 2) (by decide : 2 <= 2) (by decide : 4 <= 4)
      2 3
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4
      (BirthPhaseWait2BlockProgress.currentStep2
        (by decide : 0 < 2) (by decide : 2 <= 2)
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryConfig4
        BirthPhaseWait2Transfer.boundaryEdge4) := by
  have hC := BirthPhaseB3DirtySuccess.boundaryCarrier.2
  have hpre :=
    BirthPhaseWait2Transfer.boundary_outgoing_preCap_destroys_carrier.2.1
  have hboundary :=
    BirthPhaseB3DirtySuccess.boundary_word_classification.2.2.1
  have hdestroy :=
    BirthPhaseWait2Transfer.boundary_outgoing_preCap_destroys_carrier.2.2.2
  have hstep := BirthPhaseWait2BlockProgress.hostStep_eq_currentStep2
    (by decide : 0 < 2) (by decide : 2 <= 2)
    BirthPhaseWait2Transfer.boundaryRing4
    BirthPhaseWait2Transfer.boundaryConfig4
    BirthPhaseWait2Transfer.boundaryEdge4
  rw [hstep] at hdestroy
  have hbreak :
      ¬ BirthPhaseWait2BlockProgress.LocalCarrier
        (by decide : 0 < 2) (by decide : 2 <= 2) (by decide : 4 <= 4)
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4
        (BirthPhaseWait2BlockProgress.currentStep2
          (by decide : 0 < 2) (by decide : 2 <= 2)
          BirthPhaseWait2Transfer.boundaryRing4
          BirthPhaseWait2Transfer.boundaryConfig4
          BirthPhaseWait2Transfer.boundaryEdge4) := by
    exact hdestroy
  have hcount :=
    BirthPhaseB3DirtySuccess.boundary_word_classification.2.2.2
  have hsub0 := BirthPhaseB3DirtySuccess.boundaryCarrier.2.2
  have hsub :
      BirthPhaseWait2BlockProgress.shortCountAt
          BirthPhaseWait2Transfer.boundaryRing4
          BirthPhaseWait2Transfer.boundaryAnchor4
          (BirthPhaseWait2BlockProgress.currentStep2
            (by decide : 0 < 2) (by decide : 2 <= 2)
            BirthPhaseWait2Transfer.boundaryRing4
            BirthPhaseWait2Transfer.boundaryConfig4
            BirthPhaseWait2Transfer.boundaryEdge4) < 2 := by
    rw [<- hcount]
    exact hsub0
  exact BirthPhaseWait2BlockProgress.boundary_step_is_reacquire
    (by decide : 0 < 2) (by decide : 2 <= 2) (by decide : 4 <= 4)
    2 3
    BirthPhaseWait2Transfer.boundaryRing4
    BirthPhaseWait2Transfer.boundaryAnchor4
    BirthPhaseWait2Transfer.boundaryEdge4
    BirthPhaseWait2Transfer.boundaryConfig4
    hC hpre hboundary hbreak hsub


#print axioms BirthPhaseB3BridgeStageA.carrier_hsource
#print axioms BirthPhaseB3BridgeStageA.carrier_hsource_of_agreement
#print axioms BirthPhaseB3BridgeStageA.hsource_of_carrier_and_reacquire
#print axioms BirthPhaseB3BridgeStageA.hmass_of_carrier_and_reacquire
#print axioms BirthPhaseB3BridgeStageA.raw_width_two_service_edge_eq_p0
#print axioms BirthPhaseB3BridgeStageA.raw_width_two_terminal_site_eq_p1
#print axioms BirthPhaseB3BridgeStageA.raw_width_two_service_rotates_to_anchor
#print axioms BirthPhaseB3BridgeStageA.raw_width_two_terminal_rotates_to_shortCount_site
#print axioms BirthPhaseB3BridgeStageA.unrotate_anchor_eq_p0
#print axioms BirthPhaseB3BridgeStageA.anchor_is_internal
#print axioms BirthPhaseB3BridgeStageA.anchor_is_safe
#print axioms BirthPhaseB3BridgeStageA.anchor_is_not_boundary
#print axioms BirthPhaseB3BridgeStageA.raw_service_fire_has_physical_anchor_decomposition
#print axioms BirthPhaseB3BridgeStageA.rowCap_in_word_gives_target
#print axioms BirthPhaseB3BridgeStageA.anchor_preCap_preserves_carrier_and_projects
#print axioms BirthPhaseB3BridgeStageA.endpoint_increase_is_strict_rank_drop
#print axioms BirthPhaseB3BridgeStageA.boundary_break_row_gives_reacquire
#print axioms BirthPhaseB3BridgeStageA.boundary_case_gives_reacquire_witness
#print axioms BirthPhaseB3BridgeStageA.reacquire_not_carrier
#print axioms BirthPhaseB3BridgeStageA.boundary_fixture_successor_is_reacquire


end BirthPhaseB3BridgeStageA
