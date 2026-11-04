import Leader.Wu.Coherence.CheckSurvivalCheckCut
import Leader.Wu.Coherence.NewEqualCheckInput

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace R2CheckSurvivalSuppress

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
open BirthShortWait BirthShortDoneCuts BirthSigMoveDisposalRepair
open R2CoherenceBranches R2NewEqualLocal

variable {n ψ κ τ width : Nat}

inductive SuppressEndpoint where
  | left
  | right
  deriving DecidableEq

def suppressStateAt (side : SuppressEndpoint)
    (l r : AgentState ψ) : MainState :=
  match side with
  | .left => l.state
  | .right => r.state

def suppressResetAt (side : SuppressEndpoint)
    (l r : AgentState ψ) : Bool :=
  match side with
  | .left => l.reset_cmd
  | .right => r.reset_cmd

private def firstCatch (l r : AgentState ψ) := suppressSigStart l r
private def afterFirstKill (l r : AgentState ψ) :=
  let q := firstCatch l r
  (resetKillComparison q.1, resetKillComparison q.2)
private def secondCatch (l r : AgentState ψ) :=
  let q := afterFirstKill l r
  suppressSigMoveReset q.1 q.2
private def afterSecondKill (l r : AgentState ψ) :=
  let q := secondCatch l r
  (resetKillComparison q.1, resetKillComparison q.2)

def SuppressKillsEqualAt (side : SuppressEndpoint)
    (l r : AgentState ψ) : Prop :=
  let q0 := firstCatch l r
  let q1 := secondCatch l r
  (suppressStateAt side q0.1 q0.2 = .equal ∧
      suppressResetAt side q0.1 q0.2 = true) ∨
    (suppressStateAt side q1.1 q1.2 = .equal ∧
      suppressResetAt side q1.1 q1.2 = true)

instance suppressKillsEqualAt_decidable
    (side : SuppressEndpoint) (l r : AgentState ψ) :
    Decidable (SuppressKillsEqualAt side l r) := by
  unfold SuppressKillsEqualAt
  cases side <;> infer_instance

private theorem start_state_at (side : SuppressEndpoint)
    (l r : AgentState ψ) :
    suppressStateAt side (firstCatch l r).1 (firstCatch l r).2 =
      suppressStateAt side l r := by
  cases side with
  | left =>
      unfold firstCatch suppressStateAt suppressSigStart
      by_cases h : l.leader = true
      · simp only [if_pos h]
      · simp only [if_neg h]
  | right =>
      unfold firstCatch suppressStateAt suppressSigStart
      by_cases h : l.leader = true
      · simp only [if_pos h]
      · simp only [if_neg h]

private theorem move_state_at (side : SuppressEndpoint)
    (l r : AgentState ψ) :
    suppressStateAt side (suppressSigMoveReset l r).1
        (suppressSigMoveReset l r).2 = suppressStateAt side l r := by
  cases side with
  | left =>
      unfold suppressStateAt suppressSigMoveReset
      by_cases h : l.reset_cmd = true
      · simp only [if_pos h]
      · simp only [if_neg h]
  | right =>
      unfold suppressStateAt suppressSigMoveReset
      by_cases h : l.reset_cmd = true
      · simp only [if_pos h]
      · simp only [if_neg h]

private theorem short_state_at (side : SuppressEndpoint)
    (hw : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    suppressStateAt side (shortCountReset hw hle l r).1
        (shortCountReset hw hle l r).2 = suppressStateAt side l r := by
  cases side with
  | left =>
      unfold suppressStateAt shortCountReset
      by_cases h : r.label = widthTerminal hw hle ∧ r.reset_cmd = true
      · simp only [if_pos h]
      · simp only [if_neg h]
  | right =>
      unfold suppressStateAt shortCountReset
      by_cases h : r.label = widthTerminal hw hle ∧ r.reset_cmd = true
      · simp only [if_pos h]
      · simp only [if_neg h]

private theorem terminal_state_at (side : SuppressEndpoint)
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    suppressStateAt side (suppressSigTerminal hψ l r).1
        (suppressSigTerminal hψ l r).2 = suppressStateAt side l r := by
  cases side with
  | left =>
      unfold suppressStateAt suppressSigTerminal
      by_cases h : r.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧ r.reset_cmd = true
      · simp only [if_pos h]
      · simp only [if_neg h]
  | right =>
      unfold suppressStateAt suppressSigTerminal
      by_cases h : r.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧ r.reset_cmd = true
      · simp only [if_pos h]
      · simp only [if_neg h]

private theorem echo_state_at (side : SuppressEndpoint)
    (l r : AgentState ψ) :
    suppressStateAt side (suppressSigEcho l r).1
        (suppressSigEcho l r).2 = suppressStateAt side l r := by
  cases side with
  | left =>
      unfold suppressStateAt suppressSigEcho
      by_cases he : r.echo = true
      · simp only [if_pos he]
        by_cases hr : r.reset_cmd = true
        · simp only [if_pos hr]
        · simp only [if_neg hr]
      · simp only [if_neg he]
  | right =>
      unfold suppressStateAt suppressSigEcho
      by_cases he : r.echo = true
      · simp only [if_pos he]
        by_cases hr : r.reset_cmd = true
        · simp only [if_pos hr]
        · simp only [if_neg hr]
      · simp only [if_neg he]

private theorem finish_state_at (side : SuppressEndpoint)
    (l r : AgentState ψ) :
    suppressStateAt side (suppressSigFinish l r).1
        (suppressSigFinish l r).2 = suppressStateAt side l r := by
  cases side with
  | left =>
      unfold suppressStateAt suppressSigFinish
      by_cases h : l.leader = true
      · simp only [if_pos h]
      · simp only [if_neg h]
  | right =>
      unfold suppressStateAt suppressSigFinish
      by_cases h : l.leader = true
      · simp only [if_pos h]
      · simp only [if_neg h]

private def killPair (q : AgentState ψ × AgentState ψ) :=
  (resetKillComparison q.1, resetKillComparison q.2)

private theorem killPair_state_of_reset_false
    (side : SuppressEndpoint) (q : AgentState ψ × AgentState ψ)
    (h : suppressResetAt side q.1 q.2 = false) :
    suppressStateAt side (killPair q).1 (killPair q).2 =
      suppressStateAt side q.1 q.2 := by
  cases side with
  | left =>
      change (resetKillComparison q.1).state = q.1.state
      change q.1.reset_cmd = false at h
      simp [resetKillComparison, h]
  | right =>
      change (resetKillComparison q.2).state = q.2.state
      change q.2.reset_cmd = false at h
      simp [resetKillComparison, h]

private theorem killPair_state_none_of_reset_true
    (side : SuppressEndpoint) (q : AgentState ψ × AgentState ψ)
    (h : suppressResetAt side q.1 q.2 = true) :
    suppressStateAt side (killPair q).1 (killPair q).2 = .none := by
  cases side with
  | left =>
      change (resetKillComparison q.1).state = .none
      change q.1.reset_cmd = true at h
      exact (R2NewEqualProvenance.resetKill_main_path_erasure q.1 h).1
  | right =>
      change (resetKillComparison q.2).state = .none
      change q.2.reset_cmd = true at h
      exact (R2NewEqualProvenance.resetKill_main_path_erasure q.2 h).1

private theorem killPair_state_none_of_state_none
    (side : SuppressEndpoint) (q : AgentState ψ × AgentState ψ)
    (h : suppressStateAt side q.1 q.2 = .none) :
    suppressStateAt side (killPair q).1 (killPair q).2 = .none := by
  cases side with
  | left =>
      change q.1.state = .none at h
      change (resetKillComparison q.1).state = .none
      cases hr : q.1.reset_cmd <;>
        simp [resetKillComparison, hr, clearComparisonSignal, h]
  | right =>
      change q.2.state = .none at h
      change (resetKillComparison q.2).state = .none
      cases hr : q.2.reset_cmd <;>
        simp [resetKillComparison, hr, clearComparisonSignal, h]

private def suppressTailWidth
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (q : AgentState ψ × AgentState ψ) :=
  let q1 := shortCountReset hw hle q.1 q.2
  let q2 := suppressSigTerminal hψ q1.1 q1.2
  let q3 := suppressSigEcho q2.1 q2.2
  suppressSigFinish q3.1 q3.2

private theorem suppress_width_eq_tail
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    suppressSigResetKillWidth hψ hw hle l r =
      suppressTailWidth hψ hw hle (afterSecondKill l r) := by
  rfl

private theorem tail_state_at (side : SuppressEndpoint)
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (q : AgentState ψ × AgentState ψ) :
    suppressStateAt side (suppressTailWidth hψ hw hle q).1
        (suppressTailWidth hψ hw hle q).2 =
      suppressStateAt side q.1 q.2 := by
  let q1 := shortCountReset hw hle q.1 q.2
  let q2 := suppressSigTerminal hψ q1.1 q1.2
  let q3 := suppressSigEcho q2.1 q2.2
  change suppressStateAt side (suppressSigFinish q3.1 q3.2).1
      (suppressSigFinish q3.1 q3.2).2 = suppressStateAt side q.1 q.2
  exact (finish_state_at side q3.1 q3.2).trans
    ((echo_state_at side q2.1 q2.2).trans
      ((terminal_state_at side hψ q1.1 q1.2).trans
        (short_state_at side hw hle q.1 q.2)))

private theorem suppress_width_state_after_second
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (side : SuppressEndpoint) (l r : AgentState ψ) :
    suppressStateAt side (suppressSigResetKillWidth hψ hw hle l r).1
        (suppressSigResetKillWidth hψ hw hle l r).2 =
      suppressStateAt side (afterSecondKill l r).1 (afterSecondKill l r).2 := by
  rw [suppress_width_eq_tail hψ hw hle l r]
  exact tail_state_at side hψ hw hle (afterSecondKill l r)

private theorem reset_false_of_not_kill
    (side : SuppressEndpoint) (q : AgentState ψ × AgentState ψ)
    (heq : suppressStateAt side q.1 q.2 = .equal)
    (hn : ¬ (suppressStateAt side q.1 q.2 = .equal ∧
      suppressResetAt side q.1 q.2 = true)) :
    suppressResetAt side q.1 q.2 = false := by
  cases h : suppressResetAt side q.1 q.2 with
  | false => rfl
  | true => exact (hn ⟨heq, h⟩).elim

private theorem raw_equal_survives_of_not_killed
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (side : SuppressEndpoint) (l r : AgentState ψ)
    (hin : suppressStateAt side l r = .equal)
    (hn : ¬ SuppressKillsEqualAt side l r) :
    suppressStateAt side (suppressSigResetKillWidth hψ hw hle l r).1
        (suppressSigResetKillWidth hψ hw hle l r).2 = .equal := by
  let q0 := firstCatch l r
  let k0 := afterFirstKill l r
  let q1 := secondCatch l r
  let k1 := afterSecondKill l r
  change ¬ ((suppressStateAt side q0.1 q0.2 = .equal ∧
      suppressResetAt side q0.1 q0.2 = true) ∨
    (suppressStateAt side q1.1 q1.2 = .equal ∧
      suppressResetAt side q1.1 q1.2 = true)) at hn
  have hn0 := fun h => hn (Or.inl h)
  have hn1 := fun h => hn (Or.inr h)
  have hq0 : suppressStateAt side q0.1 q0.2 = .equal := by
    exact (start_state_at side l r).trans hin
  have hr0 := reset_false_of_not_kill side q0 hq0 hn0
  have hk0 : suppressStateAt side k0.1 k0.2 = .equal := by
    have h := killPair_state_of_reset_false side q0 hr0
    change suppressStateAt side k0.1 k0.2 = suppressStateAt side q0.1 q0.2 at h
    exact h.trans hq0
  have hq1 : suppressStateAt side q1.1 q1.2 = .equal := by
    have h := move_state_at side k0.1 k0.2
    change suppressStateAt side q1.1 q1.2 = suppressStateAt side k0.1 k0.2 at h
    exact h.trans hk0
  have hr1 := reset_false_of_not_kill side q1 hq1 hn1
  have hk1 : suppressStateAt side k1.1 k1.2 = .equal := by
    have h := killPair_state_of_reset_false side q1 hr1
    change suppressStateAt side k1.1 k1.2 = suppressStateAt side q1.1 q1.2 at h
    exact h.trans hq1
  exact (suppress_width_state_after_second hψ hw hle side l r).trans hk1

private theorem raw_state_none_of_killed
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (side : SuppressEndpoint) (l r : AgentState ψ)
    (hk : SuppressKillsEqualAt side l r) :
    suppressStateAt side (suppressSigResetKillWidth hψ hw hle l r).1
        (suppressSigResetKillWidth hψ hw hle l r).2 = .none := by
  let q0 := firstCatch l r
  let k0 := afterFirstKill l r
  let q1 := secondCatch l r
  let k1 := afterSecondKill l r
  change ((suppressStateAt side q0.1 q0.2 = .equal ∧
      suppressResetAt side q0.1 q0.2 = true) ∨
    (suppressStateAt side q1.1 q1.2 = .equal ∧
      suppressResetAt side q1.1 q1.2 = true)) at hk
  rcases hk with hk0 | hk1
  · have h0 := killPair_state_none_of_reset_true side q0 hk0.2
    change suppressStateAt side k0.1 k0.2 = .none at h0
    have hm := move_state_at side k0.1 k0.2
    change suppressStateAt side q1.1 q1.2 = suppressStateAt side k0.1 k0.2 at hm
    have h1 := killPair_state_none_of_state_none side q1 (hm.trans h0)
    change suppressStateAt side k1.1 k1.2 = .none at h1
    exact (suppress_width_state_after_second hψ hw hle side l r).trans h1
  · have h1 := killPair_state_none_of_reset_true side q1 hk1.2
    change suppressStateAt side k1.1 k1.2 = .none at h1
    exact (suppress_width_state_after_second hψ hw hle side l r).trans h1

 theorem authorizedSuppressWidth_equal_survives_of_not_killed
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (side : SuppressEndpoint) (l r : AuthorizedAgentState ψ)
    (hin : suppressStateAt side l.core r.core = .equal)
    (hn : ¬ SuppressKillsEqualAt side l.core r.core) :
    let q := authorizedSuppressWidth hψ hw hle l r
    suppressStateAt side q.1.core q.2.core = .equal := by
  change suppressStateAt side
      (suppressSigResetKillWidth hψ hw hle l.core r.core).1
      (suppressSigResetKillWidth hψ hw hle l.core r.core).2 = .equal
  exact raw_equal_survives_of_not_killed hψ hw hle side l.core r.core hin hn

theorem authorizedSuppressWidth_state_none_of_killed
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (side : SuppressEndpoint) (l r : AuthorizedAgentState ψ)
    (hk : SuppressKillsEqualAt side l.core r.core) :
    let q := authorizedSuppressWidth hψ hw hle l r
    suppressStateAt side q.1.core q.2.core = .none := by
  change suppressStateAt side
      (suppressSigResetKillWidth hψ hw hle l.core r.core).1
      (suppressSigResetKillWidth hψ hw hle l.core r.core).2 = .none
  exact raw_state_none_of_killed hψ hw hle side l.core r.core hk

theorem authorizedSuppressWidth_equal_iff_not_killed
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (side : SuppressEndpoint) (l r : AuthorizedAgentState ψ) :
    let q := authorizedSuppressWidth hψ hw hle l r
    suppressStateAt side q.1.core q.2.core = .equal ↔
      suppressStateAt side l.core r.core = .equal ∧
        ¬ SuppressKillsEqualAt side l.core r.core := by
  dsimp only
  constructor
  · intro hout
    have hp := R2NewEqualChainOrigin2.authorizedSuppressWidth_equal_preimage
      hψ hw hle l r
    dsimp only at hp
    have hin : suppressStateAt side l.core r.core = .equal := by
      cases side with
      | left => exact (hp.1 hout).1
      | right => exact (hp.2 hout).1
    refine ⟨hin, ?_⟩
    intro hk
    have hnone := authorizedSuppressWidth_state_none_of_killed
      hψ hw hle side l r hk
    have hbad : (MainState.none : MainState) = .equal := hnone.symm.trans hout
    cases hbad
  · intro h
    exact authorizedSuppressWidth_equal_survives_of_not_killed
      hψ hw hle side l r h.1 h.2

def beforeWriterSuppressInput (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let d := authorizedDisappear hψ l r
  PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ d.1 d.2

theorem beforeWriteWidth_equal_survives_of_no_suppress_kill
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (side : SuppressEndpoint) (l r : AuthorizedAgentState ψ) :
    let s := beforeWriterSuppressInput hψ l r
    suppressStateAt side s.1.core s.2.core = .equal →
    ¬ SuppressKillsEqualAt side s.1.core s.2.core →
    let q := beforeWriteWidth hψ hw hle l r
    suppressStateAt side q.1.core q.2.core = .equal := by
  unfold beforeWriterSuppressInput beforeWriteWidth
  dsimp only
  intro hin hn
  exact authorizedSuppressWidth_equal_survives_of_not_killed
    hψ hw hle side _ _ hin hn

theorem beforeWriterEqualSurvivalConditional_after_suppress_split
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) :
    R2CheckSurvivalCheckStage2.BeforeWriterEqualSurvivalConditional
      (κ := κ) hψ hw hle :=
  R2CheckSurvivalCheckStage2.beforeWriterEqualSurvivalConditional_holds
    (κ := κ) hψ hw hle

def SanitizedR2NewEqualFreshChainOriginCheckInputAlignmentRemaining
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  ∀ (l r : R2.Cell ψ κ τ),
    let sl := sanitizeReadyPhys l
    let sr := sanitizeReadyPhys r
    let pl := prepareExpiringDisposal hψ sl.base
    let pr := prepareExpiringDisposal hψ sr.base
    let al := normalizeDeletion pl.core.erase
    let ar := normalizeDeletion pr.core.erase
    let b := R2NewEqualProvenance.r2CheckInput (κ := κ) hψ hw hle al ar
    let q := R2.row hψ hw hle sl sr
    R2MainCarrierFrame l r q →
    deletionActive al = false → deletionActive ar = false →
    ReadyAlignedRaw b.1.core ∧ ReadyAlignedRaw b.2.core

end R2CheckSurvivalSuppress
