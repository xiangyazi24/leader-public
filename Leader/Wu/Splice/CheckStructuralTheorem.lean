import Leader.Wu.Splice.CheckStructuralCensus
import Leader.Wu.Splice.PeakSafeEqualTargetBlock


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9CheckStructuralTheorem


open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
  BirthShortDoneTerminalEntryCut
open BirthPhaseCohortDesign
open BirthShortDoneTerminalCheckInputSources
open PPLLComparisonHistory
open B9CheckStructuralCensus


variable {n psi kappa tau : Nat}


/-! ## Literal list/physical-group glue -/


/-- `leaderSegmentWord` contains exactly the advertised number of complete
positive groups. -/
private theorem leaderSegmentWord_length
    (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (leader : Fin n) (groups : Nat) :
    (leaderSegmentWord ring C leader groups).length = groups := by
  simp [leaderSegmentWord]


/-- Entry `k` of the certified physical word is exactly current group `k+1`.
This is the index glue needed to feed the generic PeakSafe contradiction. -/
private theorem leaderSegmentWord_get_current
    (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (leader : Fin n) (groups k : Nat)
    (hk : k < (leaderSegmentWord ring C leader groups).length) :
    (leaderSegmentWord ring C leader groups).get ⟨k, hk⟩ =
      groupID ring.hn
        (fun i => BirthPhaseCohortDesign.rawAt C i)
        (stableGroupStart ring leader psi (k + 1)) := by
  simp [leaderSegmentWord, List.get_eq_getElem, stableGroupStart, groupOffset]


/-! ## Boundary branch -/


/-- A comparison-neutral responder cannot satisfy either the stale-equality or
live-path branch of the exact CHECK follower-birth input predicate. -/
private theorem not_checkFollowerBirthInput_of_neutral_right
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hr : ComparisonNeutral r) :
    ¬ CheckFollowerBirthInput hpsi l r := by
  intro h
  rcases h with ⟨_, _, hsource⟩
  rcases hsource with hstale |
      ⟨pathLabel, pathBit, hpath, _⟩
  · rw [hr.1] at hstale
    cases hstale
  · rw [hr.2.1] at hpath
    cases hpath


/-! ## CHECK-side structural theorem -/


/-- Peak-safe leader-delimited geometry, authenticated current comparison
lineage, live crossed-ID survival, and leader-boundary clearing together block
the exact current CHECK birth input on every edge. -/
theorem checkBlockedAt_of_structural_certificate
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (hPeak : leader_delimited_peak_safe hpsi ring C)
    (hRoute : comparison_route_certified hpsi h2 ring C)
    (hCross : crossed_id_survival_bound hpsi h2 ring C)
    (hBoundary : leader_boundary_clearing hpsi h2 ring C) :
    ∀ e, BirthPhaseCohortDesign.CheckBlockedAt hpsi h2 ring C e := by
  intro e
  change ¬ ActualCheckBirthInput hpsi
    (currentCheckInputAt hpsi h2 ring C e)
  intro hInput


  -- Step 1: the current target is the input predicate.  Its exact sufficiency
  -- theorem first recovers `ActualCheckBirth`; then the raw CHECK theorem
  -- forces terminal label plus `.equal` at the newly-born responder.
  have hActual :
      ActualCheckBirth hpsi (currentCheckInputAt hpsi h2 ring C e) :=
    BirthShortDoneTerminalCheckInputSufficiency.actualCheckBirth_of_input
      hpsi _ hInput
  rcases hInput with ⟨_, _, _, _, _, _, hKernel⟩


  -- Step 6 (handled first): an edge incident to a prepared leader reaches the
  -- exact CHECK input with a neutral responder, contradicting the CHECK kernel.
  by_cases hIncident :
      (preparedPairAt hpsi ring C e).1.core.leader = true ∨
        (preparedPairAt hpsi ring C e).2.core.leader = true
  · have hBoundaryAt := hBoundary e
    dsimp only at hBoundaryAt
    have hClear := hBoundaryAt hIncident
    exact not_checkFollowerBirthInput_of_neutral_right
      hpsi
      (currentCheckInputAt hpsi h2 ring C e).1.core
      (currentCheckInputAt hpsi h2 ring C e).2.core
      hClear.2 hKernel


  · rcases hActual with ⟨_, _, _, _, _, _, hFollower, hNewLeader⟩
    change
      (checkSig hpsi
        (currentCheckInputAt hpsi h2 ring C e).1.core
        (currentCheckInputAt hpsi h2 ring C e).2.core).2.leader = true
      at hNewLeader


    have hTerminalEqual :=
      PPLLVerify.checkSig_new_responder_leader_requires_terminal_equal
        hpsi
        (currentCheckInputAt hpsi h2 ring C e).1.core
        (currentCheckInputAt hpsi h2 ring C e).2.core
        hNewLeader hFollower


    have hOutputLabel := hTerminalEqual.1
    change
      (currentCheckOutputAt hpsi h2 ring C e).2.core.label =
        ⟨psi - 1, by omega⟩
      at hOutputLabel


    have hOutputEqual := hTerminalEqual.2
    change
      (currentCheckOutputAt hpsi h2 ring C e).2.core.state = .equal
      at hOutputEqual


    -- Step 2: the route certificate supplies the authenticated equal-prefix
    -- carrier for this actual equal responder output.
    have hRouteAt := hRoute.2 e
    dsimp only at hRouteAt
    have hLineage := hRouteAt.2 hOutputEqual
    rcases hLineage with
      ⟨referenceC, leader, sourceSite, history, carrier, hWitness⟩
    have hWitnessForCross := hWitness
    rcases hWitness with
      ⟨_, _, _, hStrict, hUpto, _, groups,
        hSegment, hTargetGroups, hAgree⟩


    -- The certified physical segment is non-wrapping and nontrivial, so the
    -- touched CHECK endpoints are distinct.  This lets the whole-config cut
    -- select the responder branch literally.
    have hFit : (groups + 1) * psi < n := by
      exact hSegment.2.2.1
    have hPsiLeProduct : psi ≤ (groups + 1) * psi := by
      calc
        psi = 1 * psi := by simp
        _ ≤ (groups + 1) * psi :=
          Nat.mul_le_mul_right psi (by omega)
    have hn : 1 < n := by
      exact Nat.lt_trans (by omega : 1 < psi)
        (Nat.lt_of_le_of_lt hPsiLeProduct hFit)
    have hNe : ring.rightNeighbor e ≠ e :=
      rightNeighbor_ne_self_of_one_lt ring hn e


    have hRightRaw :
        currentCheckOutputRawConfig hpsi h2 ring C e
            (ring.rightNeighbor e) =
          (currentCheckOutputAt hpsi h2 ring C e).2.core := by
      simp [currentCheckOutputRawConfig, hNe]


    -- Step 1, completed at the carrier cut: the actual terminal CHECK label is
    -- exactly the carrier's terminal prefix index.
    have hTerminal : carrier.upto = psi - 1 := by
      calc
        carrier.upto =
            (currentCheckOutputRawConfig hpsi h2 ring C e
              (ring.rightNeighbor e)).label.val := hUpto
        _ = (currentCheckOutputAt hpsi h2 ring C e).2.core.label.val := by
          rw [hRightRaw]
        _ = psi - 1 := congrArg (fun z => z.val) hOutputLabel


    -- Steps 3-4: terminal source authentication and terminal target matching
    -- identify the same CHECK payload with both reference endpoint group IDs.
    have hReferenceEq :
        groupID ring.hn referenceC
            (stableGroupStart ring leader psi carrier.route.source) =
          groupID ring.hn referenceC
            (stableGroupStart ring leader psi carrier.route.target) := by
      have hSourceSignal :=
        comparisonSignalID_eq_groupID_of_bits_match_between
          ring
          (currentCheckOutputRawConfig hpsi h2 ring C e)
          referenceC
          (stableGroupStart ring leader psi carrier.route.target)
          (stableGroupStart ring leader psi carrier.route.source)
          (carrier.toSourceTaggedComplete hTerminal).components
      have hTargetSignal :=
        comparisonSignalID_eq_groupID_of_bits_match_config
          ring
          (currentCheckOutputRawConfig hpsi h2 ring C e)
          referenceC
          (stableGroupStart ring leader psi carrier.route.target)
          (carrier.terminal_bits_match_target hTerminal)
      exact hSourceSignal.symm.trans hTargetSignal


    -- `RouteEndpointsAgree` transports that frozen/reference equality back to
    -- the two current physical endpoint IDs used by the PeakSafe word.
    have hCurrentEq :
        groupID ring.hn
            (fun i => BirthPhaseCohortDesign.rawAt C i)
            (stableGroupStart ring leader psi carrier.route.source) =
          groupID ring.hn
            (fun i => BirthPhaseCohortDesign.rawAt C i)
            (stableGroupStart ring leader psi carrier.route.target) :=
      hAgree.1.symm.trans (hReferenceEq.trans hAgree.2)


    have hPayloadCurrent :
        carrier.route.payload =
          groupID ring.hn
            (fun i => BirthPhaseCohortDesign.rawAt C i)
            (stableGroupStart ring leader psi carrier.route.source) :=
      carrier.route.payload_from_source.trans hAgree.1


    -- Step 5: map route group numbers to zero-based list indices.
    have hLength := leaderSegmentWord_length ring C leader groups
    have hSourcePos : 0 < carrier.route.source := carrier.route.source_pos
    have hSourceGroups : carrier.route.source ≤ groups := by
      omega
    have hTargetPos : 0 < carrier.route.target := by
      omega


    have hSourceIndex :
        carrier.route.source - 1 <
          (leaderSegmentWord ring C leader groups).length := by
      rw [hLength]
      omega
    have hTargetIndex :
        carrier.route.target - 1 <
          (leaderSegmentWord ring C leader groups).length := by
      rw [hLength]
      omega
    have hIndexLt :
        carrier.route.source - 1 < carrier.route.target - 1 := by
      omega


    have hMapSource :=
      leaderSegmentWord_get_current ring C leader groups
        (carrier.route.source - 1) hSourceIndex
    have hSourcePredSucc :
        carrier.route.source - 1 + 1 = carrier.route.source := by
      omega
    rw [hSourcePredSucc] at hMapSource


    have hMapTarget :=
      leaderSegmentWord_get_current ring C leader groups
        (carrier.route.target - 1) hTargetIndex
    have hTargetPredSucc :
        carrier.route.target - 1 + 1 = carrier.route.target := by
      omega
    rw [hTargetPredSucc] at hMapTarget


    have hWordEqual :
        (leaderSegmentWord ring C leader groups).get
            ⟨carrier.route.source - 1, hSourceIndex⟩ =
          (leaderSegmentWord ring C leader groups).get
            ⟨carrier.route.target - 1, hTargetIndex⟩ :=
      hMapSource.trans (hCurrentEq.trans hMapTarget.symm)


    have hRepeatPeak :=
      leader_segment_repeat_peak_safe
        hpsi ring C hPeak leader groups hSegment


    -- Every strict interior list position is physical group `k+1`.  The
    -- crossed-ID hypothesis bounds it by the route payload, and source
    -- authentication identifies that payload with the source word entry.
    have hSurvive :
        ∀ (k : Nat)
          (hk : k < (leaderSegmentWord ring C leader groups).length),
          carrier.route.source - 1 < k →
          k < carrier.route.target - 1 →
          (leaderSegmentWord ring C leader groups).get ⟨k, hk⟩ ≤
            (leaderSegmentWord ring C leader groups).get
              ⟨carrier.route.source - 1, hSourceIndex⟩ := by
      intro k hk hSourceK hKTarget
      have hRouteSourceK : carrier.route.source < k + 1 := by
        omega
      have hRouteKTarget : k + 1 < carrier.route.target := by
        omega
      have hCrossK :=
        hCross e (ring.rightNeighbor e) referenceC leader sourceSite
          history carrier hWitnessForCross (k + 1)
          hRouteSourceK hRouteKTarget
      have hMapK :=
        leaderSegmentWord_get_current ring C leader groups k hk
      calc
        (leaderSegmentWord ring C leader groups).get ⟨k, hk⟩ =
            groupID ring.hn
              (fun i => BirthPhaseCohortDesign.rawAt C i)
              (stableGroupStart ring leader psi (k + 1)) := hMapK
        _ ≤ carrier.route.payload := hCrossK
        _ = groupID ring.hn
              (fun i => BirthPhaseCohortDesign.rawAt C i)
              (stableGroupStart ring leader psi carrier.route.source) :=
            hPayloadCurrent
        _ = (leaderSegmentWord ring C leader groups).get
              ⟨carrier.route.source - 1, hSourceIndex⟩ := hMapSource.symm


    exact
      Q11588PeakSafeCensus.repeatPeakSafe_blocks_equal_after_bounded_crossing
        hRepeatPeak hSourceIndex hTargetIndex hIndexLt hWordEqual hSurvive


end B9CheckStructuralTheorem


#print axioms B9CheckStructuralTheorem.checkBlockedAt_of_structural_certificate
