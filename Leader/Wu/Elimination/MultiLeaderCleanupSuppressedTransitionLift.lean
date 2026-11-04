import Leader.Wu.Elimination.MultiLeaderCleanupPhysicalBridge
import Leader.Wu.Comparison.TerminalEqualSupportRepair
import Leader.Wu.WallSweep.NormalResetContract
import Leader.Wu.Safety.Counterexamples

/-!
# Full-transition lift of the Algorithm-14 reset suppressor candidate

This is a separately named repair candidate.  Wu's printed Algorithm 14 does
not clear comparison material and does not assign `wait`, `h_field`, or
`carry` in this way.

The candidate reuses the current physical `suppressSigResetKill` wrapper.  A
small Boolean mask records whether each endpoint carries reset at either of
Algorithm 14's two deletion catchpoints (after reset generation and after reset
movement).  The already-proved physical suppressor executes once; only then do
we set the three WAIT controls on endpoints selected by that mask.

`CleanupPhysicalView` is exactly the five-field quotient
`leader`/`label`/`shield`/`bullet`/`signal_B`.  It therefore forgets every
comparison carrier and every WAIT control written by this candidate, just as
`PeaceView` does.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLRepair PPLLResearchFormulation PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWriteIncrementGate PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair
  PPLLWallSweepNormalResetContract PPLLWallSweepEchoDrain
  PPLLPpsiLeaderCreationRepair PPLLWallSweepClockwiseAttempt
  PPLLNoCheckBirthConditionTwoPhysical

open PhysicalBridge

set_option autoImplicit false

variable {psi kappa tau : Nat}

/-! ## Exact five-field physical quotient -/

private def cleanupPhysicalViewOfPeaceViewLift
    (w : PeaceView psi) : CleanupPhysicalView psi where
  leader := w.leader
  label := w.label
  shield := w.shield
  bullet := w.bullet
  signal_B := w.signal_B

private theorem cleanupPhysicalViewOfState_eq_lift
    (u : AgentState psi) :
    cleanupPhysicalViewOfState u =
      cleanupPhysicalViewOfPeaceViewLift (PeaceView.ofState u) := by
  rfl

/-- `CleanupPhysicalView` contains exactly the five fields also exposed by
`PeaceView`: `leader`, `label`, `shield`, `bullet`, and `signal_B`.
Consequently equality of `PeaceView`s implies equality of cleanup physical
views without inspecting any comparison, reset, path, WAIT, or writer field. -/
theorem cleanupPhysicalViewOfState_eq_of_peaceView
    {u v : AgentState psi}
    (h : PeaceView.ofState u = PeaceView.ofState v) :
    cleanupPhysicalViewOfState u = cleanupPhysicalViewOfState v := by
  calc
    cleanupPhysicalViewOfState u =
        cleanupPhysicalViewOfPeaceViewLift (PeaceView.ofState u) :=
      cleanupPhysicalViewOfState_eq_lift u
    _ = cleanupPhysicalViewOfPeaceViewLift (PeaceView.ofState v) :=
      congrArg cleanupPhysicalViewOfPeaceViewLift h
    _ = cleanupPhysicalViewOfState v :=
      (cleanupPhysicalViewOfState_eq_lift v).symm

/-! ## Proof quotient for the three added WAIT assignments -/

/-- Forget exactly the three WAIT controls written by this candidate. -/
def eraseAlgorithm14WaitControls
    (u : AgentState psi) : AgentState psi :=
  { u with
    wait := false
    h_field := false
    carry := false }

/-- Pairwise form of `eraseAlgorithm14WaitControls`. -/
def eraseAlgorithm14WaitControlPair
    (q : AgentState psi × AgentState psi) :
    AgentState psi × AgentState psi :=
  (eraseAlgorithm14WaitControls q.1,
    eraseAlgorithm14WaitControls q.2)

/-- The quotient changes no field constrained by `inProtocolDomain`. -/
theorem eraseAlgorithm14WaitControls_inProtocolDomain_iff
    (u : AgentState psi) :
    (eraseAlgorithm14WaitControls u).inProtocolDomain kappa ↔
      u.inProtocolDomain kappa := by
  rfl

/-- Apply the candidate WAIT assignments iff this endpoint was touched by a
reset at one of the two Algorithm-14 catchpoints. -/
def algorithm14WaitSuppress
    (active : Bool) (u : AgentState psi) : AgentState psi :=
  if active then
    { u with wait := true, h_field := false, carry := false }
  else u

@[simp]
theorem eraseAlgorithm14WaitControls_algorithm14WaitSuppress
    (active : Bool) (u : AgentState psi) :
    eraseAlgorithm14WaitControls (algorithm14WaitSuppress active u) =
      eraseAlgorithm14WaitControls u := by
  cases active <;> rfl

@[simp]
theorem algorithm14WaitSuppress_peaceView
    (active : Bool) (u : AgentState psi) :
    PeaceView.ofState (algorithm14WaitSuppress active u) =
      PeaceView.ofState u := by
  cases active <;> rfl

@[simp]
theorem algorithm14WaitSuppress_cleanupPhysicalView
    (active : Bool) (u : AgentState psi) :
    cleanupPhysicalViewOfState (algorithm14WaitSuppress active u) =
      cleanupPhysicalViewOfState u := by
  exact cleanupPhysicalViewOfState_eq_of_peaceView
    (algorithm14WaitSuppress_peaceView active u)

@[simp]
theorem algorithm14WaitSuppress_inProtocolDomain_iff
    (active : Bool) (u : AgentState psi) :
    (algorithm14WaitSuppress active u).inProtocolDomain kappa ↔
      u.inProtocolDomain kappa := by
  cases active <;> rfl

/-! ## One endpoint -/

/-- Endpoint primitive: use the current physical reset deletion and then write
only the candidate WAIT controls. -/
def algorithm14ResetSuppressorRepairCandidateEndpoint
    (u : AgentState psi) : AgentState psi :=
  algorithm14WaitSuppress u.reset_cmd (resetKillComparison u)

/-- On a reset-bearing endpoint, the candidate has the exact intended output. -/
theorem algorithm14ResetSuppressorRepairCandidateEndpoint_exact
    (u : AgentState psi) (hreset : u.reset_cmd = true) :
    let v := algorithm14ResetSuppressorRepairCandidateEndpoint u
    ComparisonNeutral v ∧
      v.wait = true ∧
      v.h_field = false ∧
      v.carry = false ∧
      v.reset_cmd = true := by
  simp [algorithm14ResetSuppressorRepairCandidateEndpoint,
    algorithm14WaitSuppress, resetKillComparison, clearComparisonSignal,
    ComparisonNeutral, hreset]

/-- After forgetting the three added controls, the endpoint is exactly the
current `resetKillComparison` endpoint. -/
theorem
    eraseAlgorithm14WaitControls_algorithm14ResetSuppressorRepairCandidateEndpoint
    (u : AgentState psi) :
    eraseAlgorithm14WaitControls
        (algorithm14ResetSuppressorRepairCandidateEndpoint u) =
      eraseAlgorithm14WaitControls (resetKillComparison u) := by
  exact eraseAlgorithm14WaitControls_algorithm14WaitSuppress
    u.reset_cmd (resetKillComparison u)

/-- The candidate endpoint preserves the five-field physical `PeaceView`. -/
theorem
    algorithm14ResetSuppressorRepairCandidateEndpoint_peaceView
    (u : AgentState psi) :
    PeaceView.ofState
        (algorithm14ResetSuppressorRepairCandidateEndpoint u) =
      PeaceView.ofState u := by
  calc
    PeaceView.ofState
        (algorithm14ResetSuppressorRepairCandidateEndpoint u) =
        PeaceView.ofState (resetKillComparison u) :=
      algorithm14WaitSuppress_peaceView
        u.reset_cmd (resetKillComparison u)
    _ = PeaceView.ofState u := by
      cases hreset : u.reset_cmd <;>
        simp [resetKillComparison, clearComparisonSignal,
          PeaceView.ofState, hreset]

/-- The same source computation gives the exact cleanup physical frame. -/
theorem
    algorithm14ResetSuppressorRepairCandidateEndpoint_cleanupPhysicalView
    (u : AgentState psi) :
    cleanupPhysicalViewOfState
        (algorithm14ResetSuppressorRepairCandidateEndpoint u) =
      cleanupPhysicalViewOfState u := by
  exact cleanupPhysicalViewOfState_eq_of_peaceView
    (algorithm14ResetSuppressorRepairCandidateEndpoint_peaceView u)

/-- Numeric-domain closure follows from the current deletion primitive. -/
theorem
    algorithm14ResetSuppressorRepairCandidateEndpoint_inProtocolDomain
    (u : AgentState psi) (hu : u.inProtocolDomain kappa) :
    (algorithm14ResetSuppressorRepairCandidateEndpoint u).inProtocolDomain
      kappa := by
  apply
    (algorithm14WaitSuppress_inProtocolDomain_iff
      u.reset_cmd (resetKillComparison u)).2
  exact resetKillComparison_inProtocolDomain u hu

/-! ## Compact full Algorithm 14 -/

/-- Whether each endpoint carries reset at either physical comparison-deletion
catchpoint of the current `suppressSigResetKill` implementation. -/
def algorithm14ResetCatchpoints
    (l r : AgentState psi) : Bool × Bool :=
  let q0 := suppressSigStart l r
  let q0k :=
    (resetKillComparison q0.1, resetKillComparison q0.2)
  let q1 := suppressSigMoveReset q0k.1 q0k.2
  (q0.1.reset_cmd || q1.1.reset_cmd,
    q0.2.reset_cmd || q1.2.reset_cmd)

/-- Candidate Algorithm 14.  The current physical suppressor runs once; the
three added WAIT assignments are a postprocessing layer selected by the exact
catchpoint mask. -/
def suppressSigAlgorithm14ResetSuppressorRepairCandidate
    (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let touched := algorithm14ResetCatchpoints l r
  let q := suppressSigResetKill hpsi l r
  (algorithm14WaitSuppress touched.1 q.1,
    algorithm14WaitSuppress touched.2 q.2)

/-- Whole-stage WAIT erasure is two endpoint rewrites; no Algorithm-14 branch
tree is re-expanded here. -/
theorem
    suppressSigAlgorithm14ResetSuppressorRepairCandidate_erasure
    (hpsi : psi > 0) (l r : AgentState psi) :
    eraseAlgorithm14WaitControlPair
        (suppressSigAlgorithm14ResetSuppressorRepairCandidate hpsi l r) =
      eraseAlgorithm14WaitControlPair
        (suppressSigResetKill hpsi l r) := by
  let touched := algorithm14ResetCatchpoints l r
  let q := suppressSigResetKill hpsi l r
  change
    (eraseAlgorithm14WaitControls
        (algorithm14WaitSuppress touched.1 q.1),
      eraseAlgorithm14WaitControls
        (algorithm14WaitSuppress touched.2 q.2)) =
      (eraseAlgorithm14WaitControls q.1,
        eraseAlgorithm14WaitControls q.2)
  exact Prod.ext
    (eraseAlgorithm14WaitControls_algorithm14WaitSuppress touched.1 q.1)
    (eraseAlgorithm14WaitControls_algorithm14WaitSuppress touched.2 q.2)

/-- Reuse the current public `suppressSigResetKill_peaceViewPair` theorem. -/
theorem
    suppressSigAlgorithm14ResetSuppressorRepairCandidate_peaceViewPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    peaceViewPair
        (suppressSigAlgorithm14ResetSuppressorRepairCandidate hpsi l r) =
      peaceViewPair (l, r) := by
  let touched := algorithm14ResetCatchpoints l r
  let q := suppressSigResetKill hpsi l r
  change
    (PeaceView.ofState (algorithm14WaitSuppress touched.1 q.1),
      PeaceView.ofState (algorithm14WaitSuppress touched.2 q.2)) =
      peaceViewPair (l, r)
  calc
    _ = (PeaceView.ofState q.1, PeaceView.ofState q.2) :=
      Prod.ext
        (algorithm14WaitSuppress_peaceView touched.1 q.1)
        (algorithm14WaitSuppress_peaceView touched.2 q.2)
    _ = peaceViewPair (l, r) :=
      suppressSigResetKill_peaceViewPair hpsi l r

/-- Pair form of the exact cleanup physical projection. -/
def candidateCleanupPhysicalViewPair
    (q : AgentState psi × AgentState psi) :=
  (cleanupPhysicalViewOfState q.1,
    cleanupPhysicalViewOfState q.2)

/-- The complete candidate SUPPRESS stage preserves the cleanup physical view
exactly.  Comparison clearing and all three WAIT writes are outside this
five-field quotient. -/
theorem
    suppressSigAlgorithm14ResetSuppressorRepairCandidate_cleanupPhysicalViewPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    candidateCleanupPhysicalViewPair
        (suppressSigAlgorithm14ResetSuppressorRepairCandidate hpsi l r) =
      candidateCleanupPhysicalViewPair (l, r) := by
  have hpeace :=
    suppressSigAlgorithm14ResetSuppressorRepairCandidate_peaceViewPair
      hpsi l r
  have hleft :
      PeaceView.ofState
          (suppressSigAlgorithm14ResetSuppressorRepairCandidate
            hpsi l r).1 =
        PeaceView.ofState l := by
    exact congrArg Prod.fst hpeace
  have hright :
      PeaceView.ofState
          (suppressSigAlgorithm14ResetSuppressorRepairCandidate
            hpsi l r).2 =
        PeaceView.ofState r := by
    exact congrArg Prod.snd hpeace
  change
    (cleanupPhysicalViewOfState
        (suppressSigAlgorithm14ResetSuppressorRepairCandidate
          hpsi l r).1,
      cleanupPhysicalViewOfState
        (suppressSigAlgorithm14ResetSuppressorRepairCandidate
          hpsi l r).2) =
      (cleanupPhysicalViewOfState l,
        cleanupPhysicalViewOfState r)
  exact Prod.ext
    (cleanupPhysicalViewOfState_eq_of_peaceView hleft)
    (cleanupPhysicalViewOfState_eq_of_peaceView hright)

/-- Domain closure is inherited endpointwise from the current physical
suppressor and the domain-transparent WAIT postprocessing. -/
theorem
    suppressSigAlgorithm14ResetSuppressorRepairCandidate_inProtocolDomain
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := suppressSigAlgorithm14ResetSuppressorRepairCandidate hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  let touched := algorithm14ResetCatchpoints l r
  let q := suppressSigResetKill hpsi l r
  have hq : q.1.inProtocolDomain kappa ∧
      q.2.inProtocolDomain kappa := by
    simpa [q] using
      suppressSigResetKill_inProtocolDomain hpsi l r hl hr
  change
    (algorithm14WaitSuppress touched.1 q.1).inProtocolDomain kappa ∧
      (algorithm14WaitSuppress touched.2 q.2).inProtocolDomain kappa
  exact
    ⟨(algorithm14WaitSuppress_inProtocolDomain_iff touched.1 q.1).2 hq.1,
      (algorithm14WaitSuppress_inProtocolDomain_iff touched.2 q.2).2 hq.2⟩

/-! ## Authorized stage adapter -/

/-- `PeaceView` ignores authorization and therefore reduces to the raw theorem. -/
theorem
    authorizedReconcile_suppressSigAlgorithm14ResetSuppressorRepairCandidate_peaceViewPair
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair
        (authorizedReconcile
          (suppressSigAlgorithm14ResetSuppressorRepairCandidate hpsi)
          l r) =
      authorizedPeaceViewPair (l, r) := by
  change
    peaceViewPair
        (suppressSigAlgorithm14ResetSuppressorRepairCandidate
          hpsi l.core r.core) =
      peaceViewPair (l.core, r.core)
  exact
    suppressSigAlgorithm14ResetSuppressorRepairCandidate_peaceViewPair
      hpsi l.core r.core

/-- Authorized cleanup-view projection used by the exact frame and finite
transport theorems. -/
def candidateAuthorizedCleanupPhysicalViewPair
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :=
  candidateCleanupPhysicalViewPair (q.1.core, q.2.core)

/-- Authorization reconciliation also preserves the exact cleanup physical
frame. -/
theorem
    authorizedReconcile_algorithm14ResetSuppressorRepairCandidate_cleanupPhysicalViewPair
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    candidateAuthorizedCleanupPhysicalViewPair
        (authorizedReconcile
          (suppressSigAlgorithm14ResetSuppressorRepairCandidate hpsi)
          l r) =
      candidateAuthorizedCleanupPhysicalViewPair (l, r) := by
  change candidateCleanupPhysicalViewPair
      (suppressSigAlgorithm14ResetSuppressorRepairCandidate
        hpsi l.core r.core) =
    candidateCleanupPhysicalViewPair (l.core, r.core)
  exact
    suppressSigAlgorithm14ResetSuppressorRepairCandidate_cleanupPhysicalViewPair
      hpsi l.core r.core

/-! ## Suffix factoring: only SUPPRESS varies -/

/-- Current multi-leader suffix parameterized by the one raw SUPPRESS stage. -/
def multiLeaderAfterCheckSuffixUsingSuppress
    (hpsi : psi > 0)
    (suppressStage :
      AgentState psi → AgentState psi →
        AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile suppressStage q1.1 q1.2
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  authorizedReconcile (writeSeqIncrementGate hpsi) q3.1 q3.2

/-- The existing suffix is the reset-kill instance. -/
theorem multiLeaderAfterCheckSuffixUsingSuppress_resetKill
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    multiLeaderAfterCheckSuffixUsingSuppress hpsi
        (suppressSigResetKill hpsi) l r =
      multiLeaderAfterCheckSuffix hpsi l r := by
  rfl

/-- Multi-leader suffix with only SUPPRESS replaced by the candidate. -/
def multiLeaderAfterCheckAlgorithm14ResetSuppressorRepairCandidate
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  multiLeaderAfterCheckSuffixUsingSuppress hpsi
    (suppressSigAlgorithm14ResetSuppressorRepairCandidate hpsi) l r

/-- Generic suffix-domain theorem.  Keeping the SUPPRESS stage abstract prevents
elaboration from expanding the complete candidate suffix. -/
theorem multiLeaderAfterCheckSuffixUsingSuppress_inProtocolDomain
    (hpsi : psi > 0)
    (suppressStage :
      AgentState psi → AgentState psi →
        AgentState psi × AgentState psi)
    (hsuppress : ∀ a b,
      a.inProtocolDomain kappa →
      b.inProtocolDomain kappa →
      let q := suppressStage a b
      q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := multiLeaderAfterCheckSuffixUsingSuppress
      hpsi suppressStage l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  let q0 := authorizedDisappear hpsi l r
  have h0 : q0.1.core.inProtocolDomain kappa ∧
      q0.2.core.inProtocolDomain kappa :=
    authorizedReconcile_inProtocolDomain (disappear hpsi) l r
      (disappear_inProtocolDomain hpsi l.core r.core hl hr)
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  have h1 : q1.1.core.inProtocolDomain kappa ∧
      q1.2.core.inProtocolDomain kappa :=
    authorizedCompareSigActionOne_inProtocolDomain
      hpsi q0.1 q0.2 h0.1 h0.2
  let q2 := authorizedReconcile suppressStage q1.1 q1.2
  have h2 : q2.1.core.inProtocolDomain kappa ∧
      q2.2.core.inProtocolDomain kappa :=
    authorizedReconcile_inProtocolDomain suppressStage q1.1 q1.2
      (hsuppress q1.1.core q1.2.core h1.1 h1.2)
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  have h3 : q3.1.core.inProtocolDomain kappa ∧
      q3.2.core.inProtocolDomain kappa :=
    authorizedReconcile_inProtocolDomain
      (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
      (eliminateLeadersNoCollisionEgressSink_inProtocolDomain
        hpsi q2.1.core q2.2.core h2.1 h2.2)
  exact authorizedReconcile_inProtocolDomain
    (writeSeqIncrementGate hpsi) q3.1 q3.2
    (writeSeqIncrementGate_inProtocolDomain
      hpsi q3.1.core q3.2.core h3.1 h3.2)

/-- Candidate suffix domain closure, by one instantiation of the generic proof. -/
theorem
    multiLeaderAfterCheckAlgorithm14ResetSuppressorRepairCandidate_inProtocolDomain
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q :=
      multiLeaderAfterCheckAlgorithm14ResetSuppressorRepairCandidate
        hpsi l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  exact multiLeaderAfterCheckSuffixUsingSuppress_inProtocolDomain
    (kappa := kappa) hpsi
    (suppressSigAlgorithm14ResetSuppressorRepairCandidate hpsi)
    (fun a b ha hb =>
      suppressSigAlgorithm14ResetSuppressorRepairCandidate_inProtocolDomain
        hpsi a b ha hb)
    l r hl hr

/-! ## Closed reset-host sanitizer regression -/

private def algorithm14ResetHostSanitizerInput :
    AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .equal with
      reset_cmd := true }, true⟩

private def algorithm14ResetHostSanitizerPeer :
    AuthorizedAgentState 2 :=
  ⟨PPLLCounterexample.state2 0, false⟩

/-- A pathless terminal reset host is demoted before CHECK, its one-shot
authorization is consumed, its reset token is retained, and the peer is
unchanged.  This is a closed computation over the actual pair sanitizer used by
the dispatcher. -/
theorem sanitizeAuthorizedPair_resetHost_regression :
    let q := sanitizeAuthorizedPair (by omega : 2 > 0)
      (algorithm14ResetHostSanitizerInput,
        algorithm14ResetHostSanitizerPeer)
    q =
        (⟨{ algorithm14ResetHostSanitizerInput.core with
              state := .none }, false⟩,
          algorithm14ResetHostSanitizerPeer) ∧
      q.1.core.reset_cmd = true := by
  decide

/-! ## Named normalized inputs and open dispatcher branch -/

/-- The two deletion-normalized dispatcher inputs. -/
def multiLeaderCleanupNormalizedInputs
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  (normalizeDeletion l, normalizeDeletion r)

/-- The non-priority branch after both deletion checks have failed.  It contains
only the reset-aware pre-CHECK pipeline, CHECK, birth marking, and the supplied
post-CHECK suffix. -/
def multiLeaderCleanupOpenBranchUsingAfterCheckSuffix
    (hpsi : psi > 0) (kappa : Nat)
    (afterCheckSuffix :
      AuthorizedAgentState psi → AuthorizedAgentState psi →
        AuthorizedAgentState psi × AuthorizedAgentState psi)
    (l0 r0 : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q0 := wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l0 r0
  let qR := preCheckResetWall q0.1 q0.2
  let beforeCheck := sanitizeAuthorizedPair hpsi qR
  let afterCheck :=
    authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born :=
    leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  markLeaderBirth born
    (afterCheckSuffix afterCheck.1 afterCheck.2)

/-- The current multi-leader dispatcher parameterized by its post-CHECK suffix.
Only the two deletion-priority decisions remain at this level. -/
def multiLeaderCleanupAuthorizedUsingAfterCheckSuffix
    (hpsi : psi > 0) (kappa : Nat)
    (afterCheckSuffix :
      AuthorizedAgentState psi → AuthorizedAgentState psi →
        AuthorizedAgentState psi × AuthorizedAgentState psi)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let normalized := multiLeaderCleanupNormalizedInputs l r
  if deletionActive normalized.2 then
    authorizedEliminateSig hpsi normalized.1 normalized.2
  else if deletionActive normalized.1 then
    normalized
  else
    multiLeaderCleanupOpenBranchUsingAfterCheckSuffix
      hpsi kappa afterCheckSuffix normalized.1 normalized.2

/-- Reinstating the current suffix recovers the current authorized transition.
The explicit unfold is confined to this definitional compatibility lemma. -/
theorem multiLeaderCleanupAuthorizedUsingAfterCheckSuffix_current
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    multiLeaderCleanupAuthorizedUsingAfterCheckSuffix
        hpsi kappa (multiLeaderAfterCheckSuffix hpsi) l r =
      multiLeaderCleanupAuthorizedTransition hpsi kappa l r := by
  unfold multiLeaderCleanupAuthorizedUsingAfterCheckSuffix
    multiLeaderCleanupNormalizedInputs
    multiLeaderCleanupOpenBranchUsingAfterCheckSuffix
  rfl

/-- Full authorized candidate: only the post-CHECK SUPPRESS slot differs. -/
def
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateAuthorizedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  multiLeaderCleanupAuthorizedUsingAfterCheckSuffix
    hpsi kappa
    (multiLeaderAfterCheckAlgorithm14ResetSuppressorRepairCandidate hpsi)
    l r

/-! ## Dispatcher branch equations -/

/-- Responder deletion has first priority. -/
theorem
    multiLeaderCleanupAuthorizedUsingAfterCheckSuffix_of_responderDeletion
    (hpsi : psi > 0) (kappa : Nat)
    (afterCheckSuffix :
      AuthorizedAgentState psi → AuthorizedAgentState psi →
        AuthorizedAgentState psi × AuthorizedAgentState psi)
    (l r : AuthorizedAgentState psi)
    (hResponder :
      deletionActive (multiLeaderCleanupNormalizedInputs l r).2 = true) :
    multiLeaderCleanupAuthorizedUsingAfterCheckSuffix
        hpsi kappa afterCheckSuffix l r =
      authorizedEliminateSig hpsi
        (multiLeaderCleanupNormalizedInputs l r).1
        (multiLeaderCleanupNormalizedInputs l r).2 := by
  simp [multiLeaderCleanupAuthorizedUsingAfterCheckSuffix, hResponder]

/-- If responder deletion is inactive and initiator deletion is active, the
normalized pair is returned. -/
theorem
    multiLeaderCleanupAuthorizedUsingAfterCheckSuffix_of_initiatorDeletion
    (hpsi : psi > 0) (kappa : Nat)
    (afterCheckSuffix :
      AuthorizedAgentState psi → AuthorizedAgentState psi →
        AuthorizedAgentState psi × AuthorizedAgentState psi)
    (l r : AuthorizedAgentState psi)
    (hResponder :
      deletionActive (multiLeaderCleanupNormalizedInputs l r).2 = false)
    (hInitiator :
      deletionActive (multiLeaderCleanupNormalizedInputs l r).1 = true) :
    multiLeaderCleanupAuthorizedUsingAfterCheckSuffix
        hpsi kappa afterCheckSuffix l r =
      multiLeaderCleanupNormalizedInputs l r := by
  simp [multiLeaderCleanupAuthorizedUsingAfterCheckSuffix,
    hResponder, hInitiator]

/-- If neither priority deletion is active, the dispatcher is exactly the named
open branch. -/
theorem multiLeaderCleanupAuthorizedUsingAfterCheckSuffix_of_open
    (hpsi : psi > 0) (kappa : Nat)
    (afterCheckSuffix :
      AuthorizedAgentState psi → AuthorizedAgentState psi →
        AuthorizedAgentState psi × AuthorizedAgentState psi)
    (l r : AuthorizedAgentState psi)
    (hResponder :
      deletionActive (multiLeaderCleanupNormalizedInputs l r).2 = false)
    (hInitiator :
      deletionActive (multiLeaderCleanupNormalizedInputs l r).1 = false) :
    multiLeaderCleanupAuthorizedUsingAfterCheckSuffix
        hpsi kappa afterCheckSuffix l r =
      multiLeaderCleanupOpenBranchUsingAfterCheckSuffix
        hpsi kappa afterCheckSuffix
        (multiLeaderCleanupNormalizedInputs l r).1
        (multiLeaderCleanupNormalizedInputs l r).2 := by
  simp [multiLeaderCleanupAuthorizedUsingAfterCheckSuffix,
    hResponder, hInitiator]

/-! ## Factored dispatcher domain closure -/

/-- Both named normalized inputs remain inside the numeric domain. -/
theorem multiLeaderCleanupNormalizedInputs_inProtocolDomain
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := multiLeaderCleanupNormalizedInputs l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  change
    (normalizeDeletion l).core.inProtocolDomain kappa ∧
      (normalizeDeletion r).core.inProtocolDomain kappa
  exact
    ⟨(cleanup_helpers_inProtocolDomain l hl).1,
      (cleanup_helpers_inProtocolDomain r hr).1⟩

/-- Domain closure of the named linear open branch.  There is no priority
conditional in this theorem. -/
theorem
    multiLeaderCleanupOpenBranchUsingAfterCheckSuffix_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat)
    (afterCheckSuffix :
      AuthorizedAgentState psi → AuthorizedAgentState psi →
        AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hafter : ∀ a b,
      a.core.inProtocolDomain kappa →
      b.core.inProtocolDomain kappa →
      let q := afterCheckSuffix a b
      q.1.core.inProtocolDomain kappa ∧
        q.2.core.inProtocolDomain kappa)
    (l0 r0 : AuthorizedAgentState psi)
    (hl0 : l0.core.inProtocolDomain kappa)
    (hr0 : r0.core.inProtocolDomain kappa) :
    let q := multiLeaderCleanupOpenBranchUsingAfterCheckSuffix
      hpsi kappa afterCheckSuffix l0 r0
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  let q0 :=
    wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l0 r0
  have h0 :=
    wallSweepResetProbeAuthorizedBeforeCheck_inProtocolDomain
      hpsi kappa l0 r0 hl0 hr0
  let qR := preCheckResetWall q0.1 q0.2
  have hR := preCheckResetWall_inProtocolDomain
    q0.1 q0.2 h0.1 h0.2
  let beforeCheck := sanitizeAuthorizedPair hpsi qR
  have hBefore : beforeCheck.1.core.inProtocolDomain kappa ∧
      beforeCheck.2.core.inProtocolDomain kappa :=
    ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain
        hpsi qR.1 hR.1,
      sanitizeAuthorizedTerminalEqual_inProtocolDomain
        hpsi qR.2 hR.2⟩
  let afterCheck :=
    authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  have hAfter := authorizedReconcile_inProtocolDomain
      (checkSig hpsi) beforeCheck.1 beforeCheck.2
      (checkSig_inProtocolDomain hpsi
        beforeCheck.1.core beforeCheck.2.core
        hBefore.1 hBefore.2)
  let born :=
    leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := afterCheckSuffix afterCheck.1 afterCheck.2
  have htail := hafter afterCheck.1 afterCheck.2 hAfter.1 hAfter.2
  change
    (markLeaderBirth born tail).1.core.inProtocolDomain kappa ∧
      (markLeaderBirth born tail).2.core.inProtocolDomain kappa
  exact markLeaderBirth_inProtocolDomain born tail htail

/-- Generic dispatcher-domain theorem.  It rewrites by one of the three named
branch equations and never unfolds the generic full transition. -/
theorem
    multiLeaderCleanupAuthorizedUsingAfterCheckSuffix_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat)
    (afterCheckSuffix :
      AuthorizedAgentState psi → AuthorizedAgentState psi →
        AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hafter : ∀ a b,
      a.core.inProtocolDomain kappa →
      b.core.inProtocolDomain kappa →
      let q := afterCheckSuffix a b
      q.1.core.inProtocolDomain kappa ∧
        q.2.core.inProtocolDomain kappa)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := multiLeaderCleanupAuthorizedUsingAfterCheckSuffix
      hpsi kappa afterCheckSuffix l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  have hnormalized :
      (multiLeaderCleanupNormalizedInputs l r).1.core.inProtocolDomain
          kappa ∧
        (multiLeaderCleanupNormalizedInputs l r).2.core.inProtocolDomain
          kappa := by
    simpa using
      (multiLeaderCleanupNormalizedInputs_inProtocolDomain
        (kappa := kappa) l r hl hr)
  change
    (multiLeaderCleanupAuthorizedUsingAfterCheckSuffix
      hpsi kappa afterCheckSuffix l r).1.core.inProtocolDomain kappa ∧
      (multiLeaderCleanupAuthorizedUsingAfterCheckSuffix
        hpsi kappa afterCheckSuffix l r).2.core.inProtocolDomain kappa
  cases hResponder :
      deletionActive (multiLeaderCleanupNormalizedInputs l r).2 with
  | false =>
      cases hInitiator :
          deletionActive (multiLeaderCleanupNormalizedInputs l r).1 with
      | false =>
          rw [multiLeaderCleanupAuthorizedUsingAfterCheckSuffix_of_open
            (hpsi := hpsi) (kappa := kappa)
            (afterCheckSuffix := afterCheckSuffix)
            (l := l) (r := r)
            (hResponder := hResponder)
            (hInitiator := hInitiator)]
          exact
            multiLeaderCleanupOpenBranchUsingAfterCheckSuffix_inProtocolDomain
              hpsi kappa afterCheckSuffix hafter
              (multiLeaderCleanupNormalizedInputs l r).1
              (multiLeaderCleanupNormalizedInputs l r).2
              hnormalized.1 hnormalized.2
      | true =>
          rw [multiLeaderCleanupAuthorizedUsingAfterCheckSuffix_of_initiatorDeletion
            (hpsi := hpsi) (kappa := kappa)
            (afterCheckSuffix := afterCheckSuffix)
            (l := l) (r := r)
            (hResponder := hResponder)
            (hInitiator := hInitiator)]
          exact hnormalized
  | true =>
      rw [multiLeaderCleanupAuthorizedUsingAfterCheckSuffix_of_responderDeletion
        (hpsi := hpsi) (kappa := kappa)
        (afterCheckSuffix := afterCheckSuffix)
        (l := l) (r := r)
        (hResponder := hResponder)]
      exact authorizedReconcile_inProtocolDomain
        (eliminateSig hpsi)
        (multiLeaderCleanupNormalizedInputs l r).1
        (multiLeaderCleanupNormalizedInputs l r).2
        (eliminateSig_inProtocolDomain hpsi
          (multiLeaderCleanupNormalizedInputs l r).1.core
          (multiLeaderCleanupNormalizedInputs l r).2.core
          hnormalized.1 hnormalized.2)

/-- Concrete authorized candidate domain closure, by one instantiation of the
factored dispatcher theorem. -/
theorem
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q :=
      multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateAuthorizedTransition
        hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  exact
    multiLeaderCleanupAuthorizedUsingAfterCheckSuffix_inProtocolDomain
      hpsi kappa
      (multiLeaderAfterCheckAlgorithm14ResetSuppressorRepairCandidate hpsi)
      (fun a b ha hb =>
        multiLeaderAfterCheckAlgorithm14ResetSuppressorRepairCandidate_inProtocolDomain
          (kappa := kappa) hpsi a b ha hb)
      l r hl hr

/-! ## Existing finite carrier and exact erasure -/

/-- Bounded execution on the unchanged authorized carrier. -/
def
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBoundedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa :=
  let q :=
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateAuthorizedTransition
      hpsi kappa l.erase r.erase
  let hq :=
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateAuthorizedTransition_inProtocolDomain
      hpsi kappa l.erase r.erase
      l.core.erase_inProtocolDomain
      r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1,
      q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2,
      q.2.path0Crossed⟩)

/-- Exact bounded erasure to the separately named authorized candidate. -/
theorem
    erase_multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBoundedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q :=
      multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBoundedTransition
        hpsi kappa l r
    (q.1.erase, q.2.erase) =
      multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateAuthorizedTransition
        hpsi kappa l.erase r.erase := by
  let q :=
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateAuthorizedTransition
      hpsi kappa l.erase r.erase
  let hq :=
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateAuthorizedTransition_inProtocolDomain
      hpsi kappa l.erase r.erase
      l.core.erase_inProtocolDomain
      r.core.erase_inProtocolDomain
  change
    (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
        q.1.path0Crossed⟩,
      ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
        q.2.path0Crossed⟩) = q
  rw [BoundedAgentState.erase_ofDomain,
    BoundedAgentState.erase_ofDomain]

/-- Exact `PeaceView` transport through finite reification. -/
theorem
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBounded_peaceView
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let bounded :=
      multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBoundedTransition
        hpsi kappa l r
    authorizedPeaceViewPair
        (bounded.1.erase, bounded.2.erase) =
      authorizedPeaceViewPair
        (multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateAuthorizedTransition
          hpsi kappa l.erase r.erase) := by
  exact congrArg authorizedPeaceViewPair
    (erase_multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBoundedTransition
      hpsi kappa l r)

/-- Exact `CleanupPhysicalView` transport through finite reification. -/
theorem
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBounded_cleanupPhysicalView
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let bounded :=
      multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBoundedTransition
        hpsi kappa l r
    candidateAuthorizedCleanupPhysicalViewPair
        (bounded.1.erase, bounded.2.erase) =
      candidateAuthorizedCleanupPhysicalViewPair
        (multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateAuthorizedTransition
          hpsi kappa l.erase r.erase) := by
  exact congrArg candidateAuthorizedCleanupPhysicalViewPair
    (erase_multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBoundedTransition
      hpsi kappa l r)

/-! ## Existing expiration carrier -/

/-- Expiring execution, using the same deletion-priority/path-stall endpoint
policy as the current multi-leader cleanup transition. -/
def multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateTransition
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  let q :=
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBoundedTransition
      hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau :=
    ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau :=
    ⟨q.2, r.stall⟩
  (deletionPriorityExpireOne tau l lOut,
    deletionPriorityExpireOne tau r rOut)

/-- Every expiring output erases to an audit core inside the declared numeric
domain; this follows from the bounded carrier independently of the timer
branch. -/
theorem
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    let out :=
      multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateTransition
        hpsi kappa tau l r
    out.1.core.erase.core.inProtocolDomain kappa ∧
      out.2.core.erase.core.inProtocolDomain kappa := by
  let out :=
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateTransition
      hpsi kappa tau l r
  change
    out.1.core.core.erase.inProtocolDomain kappa ∧
      out.2.core.core.erase.inProtocolDomain kappa
  exact
    ⟨out.1.core.core.erase_inProtocolDomain,
      out.2.core.core.erase_inProtocolDomain⟩

/-- Outer expiration is transparent on `PeaceView`. -/
theorem
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateTransition_peaceView
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    let bounded :=
      multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBoundedTransition
        hpsi kappa l.core r.core
    let out :=
      multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateTransition
        hpsi kappa tau l r
    (PeaceView.ofState out.1.core.erase.core,
      PeaceView.ofState out.2.core.erase.core) =
      (PeaceView.ofState bounded.1.erase.core,
        PeaceView.ofState bounded.2.erase.core) := by
  let bounded :=
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBoundedTransition
      hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau :=
    ⟨bounded.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau :=
    ⟨bounded.2, r.stall⟩
  change
    (PeaceView.ofState
        (deletionPriorityExpireOne tau l lOut).core.erase.core,
      PeaceView.ofState
        (deletionPriorityExpireOne tau r rOut).core.erase.core) =
      (PeaceView.ofState bounded.1.erase.core,
        PeaceView.ofState bounded.2.erase.core)
  apply Prod.ext
  · exact deletionPriorityExpireOne_peaceView_frame l lOut
  · exact deletionPriorityExpireOne_peaceView_frame r rOut

/-- Complete expiring-to-authorized `PeaceView` bridge. -/
theorem
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateTransition_peaceView_eq_authorized
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    let out :=
      multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateTransition
        hpsi kappa tau l r
    (PeaceView.ofState out.1.core.erase.core,
      PeaceView.ofState out.2.core.erase.core) =
      authorizedPeaceViewPair
        (multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateAuthorizedTransition
          hpsi kappa l.core.erase r.core.erase) := by
  let bounded :=
    multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBoundedTransition
      hpsi kappa l.core r.core
  calc
    (PeaceView.ofState
        (multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateTransition
          hpsi kappa tau l r).1.core.erase.core,
      PeaceView.ofState
        (multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateTransition
          hpsi kappa tau l r).2.core.erase.core) =
        (PeaceView.ofState bounded.1.erase.core,
          PeaceView.ofState bounded.2.erase.core) := by
      simpa [bounded] using
        (multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateTransition_peaceView
          hpsi kappa tau l r)
    _ = authorizedPeaceViewPair
        (bounded.1.erase, bounded.2.erase) := by
      rfl
    _ = authorizedPeaceViewPair
        (multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateAuthorizedTransition
          hpsi kappa l.core.erase r.core.erase) := by
      simpa [bounded] using
        (multiLeaderCleanupAlgorithm14ResetSuppressorRepairCandidateBounded_peaceView
          hpsi kappa l.core r.core)

/-! ## Local mixed-label/reset regression -/

/-- The candidate removes the WAIT/GENSIG hidden-control obstruction on the
specified follower/reset edge without changing either leader output. -/
theorem
    suppressSigAlgorithm14ResetSuppressorRepairCandidate_mixedFollowerResetEdge
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlFollower : l.leader = false)
    (hrFollower : r.leader = false)
    (hlReset : l.reset_cmd = true)
    (hrReset : r.reset_cmd = false)
    (hrEcho : r.echo = false) :
    let out :=
      suppressSigAlgorithm14ResetSuppressorRepairCandidate hpsi l r
    ComparisonNeutral out.1 ∧
      ComparisonNeutral out.2 ∧
      out.1.leader = false ∧
      out.2.leader = false ∧
      out.1.reset_cmd = false ∧
      out.2.reset_cmd = true ∧
      out.1.wait = true ∧
      out.2.wait = true ∧
      out.1.h_field = false ∧
      out.2.h_field = false ∧
      out.1.carry = false ∧
      out.2.carry = false := by
  let q := suppressSigResetKill hpsi l r
  have hbase :
      ComparisonNeutral q.1 ∧
        ComparisonNeutral q.2 ∧
        q.1.reset_cmd = false ∧
        q.2.reset_cmd = true := by
    simpa [q] using
      suppressSigResetKill_handoff hpsi l r hlReset hrEcho
  have hleaders :
      q.1.leader = l.leader ∧ q.2.leader = r.leader := by
    simpa [q] using
      PPLLWallSweepEchoDrain.suppressSigResetKill_leaders_eq
        hpsi l r
  have hcore :
      ComparisonNeutral q.1 ∧
        ComparisonNeutral q.2 ∧
        q.1.leader = false ∧
        q.2.leader = false ∧
        q.1.reset_cmd = false ∧
        q.2.reset_cmd = true := by
    exact
      ⟨hbase.1, hbase.2.1,
        hleaders.1.trans hlFollower,
        hleaders.2.trans hrFollower,
        hbase.2.2.1, hbase.2.2.2⟩
  have htouched :
      algorithm14ResetCatchpoints l r = (true, true) := by
    simp [algorithm14ResetCatchpoints, suppressSigStart,
      suppressSigMoveReset, resetKillComparison,
      clearComparisonSignal, hlFollower, hrFollower,
      hlReset, hrReset]
  have hout :
      suppressSigAlgorithm14ResetSuppressorRepairCandidate hpsi l r =
        (algorithm14WaitSuppress true q.1,
          algorithm14WaitSuppress true q.2) := by
    simpa [suppressSigAlgorithm14ResetSuppressorRepairCandidate,
      htouched, q]
  rw [hout]
  simpa [algorithm14WaitSuppress, ComparisonNeutral] using hcore

end PPLLCompleteMultiLeaderCleanup
