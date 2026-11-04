import Leader.Wu.Coherence.CheckEqualSurvival
import Leader.Wu.WriteSeq.WriterProducerRepair
import Leader.Wu.Entrance.CheckWriteStateFrame
import Leader.Wu.Coherence.NewEqualChainOriginSuppress

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace R2CheckSurvivalCheckStage2

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open BirthShortDoneTerminalEntryCut BirthShortDoneCuts
open BirthCheckPermitRepair
open WriterProducerRepair

variable {ψ κ τ width : Nat}

attribute [local irreducible]
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthCheckPermitRepair.permitFix
  BirthShortDoneCuts.beforeWriteWidth
  PPLLLeaderCreationCleanupRepair.markLeaderBirth
  WriterProducerRepair.stationaryProducerRow

private def boundedMainTriple
    (u : AuthorizedBoundedAgentState ψ κ) :
    MainState × PathInfo × Fin ψ :=
  (u.erase.core.state, u.erase.core.path, u.erase.core.label)

private def authMainTriple
    (u : AuthorizedAgentState ψ) : MainState × PathInfo × Fin ψ :=
  (u.core.state, u.core.path, u.core.label)

/-- Public spelling of the body hidden by the actual q13267 CHECK cut. -/
private def checkedPublic
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    doneThroughCheckEntryWidth hψ hw hle κ l.erase r.erase
  let hq := doneThroughCheckEntryWidth_domain
    (κ := κ) hψ hw hle l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (R2.ofAuth q.1 hq.1, R2.ofAuth q.2 hq.2)

private def permitPublic (u : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ :=
  let f : AuthorizedAgentState ψ := permitFix u.erase
  let hf : f.core.inProtocolDomain κ := by
    change (permitFix u.erase).core.inProtocolDomain κ
    rw [permitFix_core]
    exact u.core.erase_inProtocolDomain
  R2.ofAuth f hf

private def beforeWriterPublic
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    beforeWriteWidth hψ hw hle l.erase r.erase
  let hq := beforeWriteWidth_domain
    (κ := κ) hψ hw hle l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (R2.ofAuth q.1 hq.1, R2.ofAuth q.2 hq.2)

private def markPublic
    (oldL oldR outL outR : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let a : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    (outL.erase, outR.erase)
  let ha : a.1.core.inProtocolDomain κ ∧ a.2.core.inProtocolDomain κ :=
    ⟨outL.core.erase_inProtocolDomain, outR.core.erase_inProtocolDomain⟩
  let born : Bool := K2BirthDispatcher.authBirth oldL.erase oldR.erase a
  let m : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    markLeaderBirth born a
  let hm := markLeaderBirth_inProtocolDomain born a ha
  (R2.ofAuth m.1 hm.1, R2.ofAuth m.2 hm.2)

/-- Installed actual-cut frame: `Leader/Wu/WriteSeq/WriterProducerRepair.lean:240`.
Its raw CHECK source is `Leader/Wu/Entrance/CheckWriteStateFrame.lean:409-435`. -/
private theorem checkedPublic_writeState_frame
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let c := checkedPublic hψ hw hle l r
    c.1.core.write_state = l.core.write_state ∧
      c.2.core.write_state = r.core.write_state := by
  exact R2.q13267_checkedBounded_writeState (κ := κ) hψ hw hle l r

/-- Installed actual-cut frame: `Leader/Wu/WriteSeq/WriterProducerRepair.lean:255`. -/
private theorem checkedPublic_mainTriple_frame
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      doneThroughCheckEntryWidth hψ hw hle κ l.erase r.erase
    let c := checkedPublic hψ hw hle l r
    (c.1.erase.core.state, c.1.erase.core.path, c.1.erase.core.label) =
        (q.1.core.state, q.1.core.path, q.1.core.label) ∧
      (c.2.erase.core.state, c.2.erase.core.path, c.2.erase.core.label) =
        (q.2.core.state, q.2.core.path, q.2.core.label) := by
  exact R2.q13267_checkedBounded_mainTriple (κ := κ) hψ hw hle l r

/-- Installed actual-cut frame: `Leader/Wu/WriteSeq/WriterProducerRepair.lean:273`. -/
private theorem permitPublic_core_frame
    (u : AuthorizedBoundedAgentState ψ κ) :
    (permitPublic u).core = u.core := by
  exact R2.q13267_permitBounded_core (κ := κ) u

/-- Installed actual-cut frame: `Leader/Wu/WriteSeq/WriterProducerRepair.lean:290`. -/
private theorem beforeWriterPublic_core_frame
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      beforeWriteWidth hψ hw hle l.erase r.erase
    let p := beforeWriterPublic hψ hw hle l r
    p.1.erase.core = q.1.core ∧ p.2.erase.core = q.2.core := by
  exact R2.q13267_beforeWriterBounded_core (κ := κ) hψ hw hle l r

/-- Installed actual-cut frame: `Leader/Wu/WriteSeq/WriterProducerRepair.lean:305`. -/
private theorem markPublic_core_frame
    (oldL oldR outL outR : AuthorizedBoundedAgentState ψ κ) :
    let a : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      (outL.erase, outR.erase)
    let born : Bool := K2BirthDispatcher.authBirth oldL.erase oldR.erase a
    let m : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      markLeaderBirth born a
    let z := markPublic oldL oldR outL outR
    z.1.erase.core = m.1.core ∧ z.2.erase.core = m.2.core := by
  exact R2.q13267_markBounded_core (κ := κ) oldL oldR outL outR


/-- Projection-only replacement for the old whole-pair expansion.
Each conjunct is certified by one of the five installed frames whose hidden
left side is the actual private q13267 cut used by `R2.ordinary`. -/
theorem ordinary_public_cut_expansion
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : WCell ψ κ) :
    let checkRaw : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      doneThroughCheckEntryWidth hψ hw hle κ l.agent.erase r.agent.erase
    let c := checkedPublic hψ hw hle l.agent r.agent
    let f := permitPublic c.1
    let beforeRaw : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      beforeWriteWidth hψ hw hle f.erase c.2.erase
    let p := beforeWriterPublic hψ hw hle f c.2
    let z := stationaryProducerRow hψ
      ⟨p.1, l.fuel⟩ ⟨p.2, r.fuel⟩
    let a : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      (z.1.agent.erase, z.2.agent.erase)
    let born : Bool := K2BirthDispatcher.authBirth l.agent.erase r.agent.erase a
    let marked : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      markLeaderBirth born a
    let m := markPublic l.agent r.agent z.1.agent z.2.agent
    (c.1.core.write_state = l.agent.core.write_state ∧
      c.2.core.write_state = r.agent.core.write_state) ∧
    ((c.1.erase.core.state, c.1.erase.core.path, c.1.erase.core.label) =
        (checkRaw.1.core.state, checkRaw.1.core.path, checkRaw.1.core.label) ∧
      (c.2.erase.core.state, c.2.erase.core.path, c.2.erase.core.label) =
        (checkRaw.2.core.state, checkRaw.2.core.path, checkRaw.2.core.label)) ∧
    f.core = c.1.core ∧
    (p.1.erase.core = beforeRaw.1.core ∧
      p.2.erase.core = beforeRaw.2.core) ∧
    (m.1.erase.core = marked.1.core ∧
      m.2.erase.core = marked.2.core) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · exact checkedPublic_writeState_frame hψ hw hle l.agent r.agent
  · refine ⟨?_, ?_⟩
    · exact checkedPublic_mainTriple_frame hψ hw hle l.agent r.agent
    · refine ⟨?_, ?_⟩
      · exact permitPublic_core_frame _
      · refine ⟨?_, ?_⟩
        · exact beforeWriterPublic_core_frame hψ hw hle _ _
        · exact markPublic_core_frame _ _ _ _


/-- Paired `.equal` survival through the actual q13267 CHECK and permit cuts.
The CHECK triple bridge is `Leader/Wu/WriteSeq/WriterProducerRepair.lean:255`; the permit
core frame is `Leader/Wu/WriteSeq/WriterProducerRepair.lean:273`. -/
theorem actual_checked_permit_equal_frame
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      doneThroughCheckEntryWidth hψ hw hle κ l.erase r.erase
    q.1.core.state = .equal →
    q.2.core.state = .equal →
    let c := checkedPublic hψ hw hle l r
    let f := permitPublic c.1
    f.core.state = .equal ∧
      c.2.core.state = .equal ∧
      boundedMainTriple f = authMainTriple q.1 ∧
      boundedMainTriple c.2 = authMainTriple q.2 := by
  let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    doneThroughCheckEntryWidth hψ hw hle κ l.erase r.erase
  let c := checkedPublic hψ hw hle l r
  let f := permitPublic c.1
  change q.1.core.state = .equal → q.2.core.state = .equal →
    f.core.state = .equal ∧ c.2.core.state = .equal ∧
      boundedMainTriple f = authMainTriple q.1 ∧
      boundedMainTriple c.2 = authMainTriple q.2
  intro hL hR
  have hc := checkedPublic_mainTriple_frame hψ hw hle l r
  change boundedMainTriple c.1 = authMainTriple q.1 ∧
    boundedMainTriple c.2 = authMainTriple q.2 at hc
  have hfcore := permitPublic_core_frame c.1
  change f.core = c.1.core at hfcore
  have hfc : boundedMainTriple f = boundedMainTriple c.1 := by
    unfold boundedMainTriple
    exact congrArg
      (fun b : BoundedAgentState ψ κ =>
        let e := BoundedAgentState.erase b
        (e.state, e.path, e.label)) hfcore
  have hleft := hfc.trans hc.1
  have hsL := congrArg
    (fun t : MainState × PathInfo × Fin ψ => t.1) hleft
  have hsR := congrArg
    (fun t : MainState × PathInfo × Fin ψ => t.1) hc.2
  have hfEq : f.core.state = .equal := by
    change f.erase.core.state = .equal
    exact hsL.trans hL
  have hc2Eq : c.2.core.state = .equal := by
    change c.2.erase.core.state = .equal
    exact hsR.trans hR
  exact ⟨hfEq, hc2Eq, hleft, hc.2⟩

/-- The exact forward seam left by SUPPRESS reset-kill.
The installed bounded/raw bridge is `Leader/Wu/WriteSeq/WriterProducerRepair.lean:290`;
the backward composite is
`Leader/Wu/Coherence/NewEqualChainOriginSuppress.lean:261-321`.

An input `.equal` is not asserted to survive unconditionally.  The extra
premise `p.i.core.state = .equal` is precisely the forward survival fact still
needed at reset-kill.  Once supplied, label is fixed and path is either fixed
or genuinely cleared to `.bot`. -/
def BeforeWriterEqualSurvivalConditional
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  ∀ (l r : AuthorizedBoundedAgentState ψ κ),
    let p := beforeWriterPublic hψ hw hle l r
    (l.core.state = .equal →
      p.1.core.state = .equal →
      (boundedMainTriple p.1 = boundedMainTriple l ∨
        (p.1.erase.core.path = .bot ∧
          p.1.erase.core.path ≠ l.erase.core.path))) ∧
    (r.core.state = .equal →
      p.2.core.state = .equal →
      (boundedMainTriple p.2 = boundedMainTriple r ∨
        (p.2.erase.core.path = .bot ∧
          p.2.erase.core.path ≠ r.erase.core.path)))


private theorem boundedMainTriple_ext
    (a b : AuthorizedBoundedAgentState ψ κ)
    (hs : a.erase.core.state = b.erase.core.state)
    (hp : a.erase.core.path = b.erase.core.path)
    (hl : a.erase.core.label = b.erase.core.label) :
    boundedMainTriple a = boundedMainTriple b := by
  unfold boundedMainTriple
  apply Prod.ext
  · exact hs
  · apply Prod.ext
    · exact hp
    · exact hl

/-- `BeforeWriterEqualSurvivalConditional` follows from the actual q13267
bounded/raw frame (`Leader/Wu/WriteSeq/WriterProducerRepair.lean:290`) and the backward
preimage theorem (`Leader/Wu/Coherence/NewEqualChainOriginSuppress.lean:261-321`). -/
theorem beforeWriterEqualSurvivalConditional_holds
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) :
    BeforeWriterEqualSurvivalConditional (κ := κ) hψ hw hle := by
  unfold BeforeWriterEqualSurvivalConditional
  intro l r
  let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    beforeWriteWidth hψ hw hle l.erase r.erase
  let p := beforeWriterPublic hψ hw hle l r
  change
    (l.core.state = .equal → p.1.core.state = .equal →
      (boundedMainTriple p.1 = boundedMainTriple l ∨
        (p.1.erase.core.path = .bot ∧
          p.1.erase.core.path ≠ l.erase.core.path))) ∧
    (r.core.state = .equal → p.2.core.state = .equal →
      (boundedMainTriple p.2 = boundedMainTriple r ∨
        (p.2.erase.core.path = .bot ∧
          p.2.erase.core.path ≠ r.erase.core.path)))
  have hcore := beforeWriterPublic_core_frame hψ hw hle l r
  change p.1.erase.core = q.1.core ∧ p.2.erase.core = q.2.core at hcore
  have hpre :=
    R2NewEqualChainOrigin2.beforeWriteWidth_equal_preimage
      hψ hw hle l.erase r.erase
  change
    (q.1.core.state = .equal →
      l.erase.core.state = .equal ∧
        (q.1.core.path = l.erase.core.path ∨ q.1.core.path = .bot) ∧
        q.1.core.label = l.erase.core.label) ∧
    (q.2.core.state = .equal →
      r.erase.core.state = .equal ∧
        (q.2.core.path = r.erase.core.path ∨ q.2.core.path = .bot) ∧
        q.2.core.label = r.erase.core.label) at hpre
  constructor
  · intro hlin hpout
    change l.erase.core.state = .equal at hlin
    change p.1.erase.core.state = .equal at hpout
    have hs := congrArg (fun u : AgentState ψ => u.state) hcore.1
    have hp := congrArg (fun u : AgentState ψ => u.path) hcore.1
    have hl := congrArg (fun u : AgentState ψ => u.label) hcore.1
    have hqout : q.1.core.state = .equal := hs.symm.trans hpout
    rcases hpre.1 hqout with ⟨_, hpath, hlabelQ⟩
    have hstate : p.1.erase.core.state = l.erase.core.state :=
      hpout.trans hlin.symm
    have hlabel : p.1.erase.core.label = l.erase.core.label :=
      hl.trans hlabelQ
    rcases hpath with hsame | hbot
    · exact Or.inl
        (boundedMainTriple_ext p.1 l hstate (hp.trans hsame) hlabel)
    · have hpbot : p.1.erase.core.path = .bot := hp.trans hbot
      by_cases hlbot : l.erase.core.path = .bot
      · exact Or.inl
          (boundedMainTriple_ext p.1 l hstate
            (hpbot.trans hlbot.symm) hlabel)
      · exact Or.inr ⟨hpbot, by
          intro heq
          exact hlbot (heq.symm.trans hpbot)⟩
  · intro hrin hpout
    change r.erase.core.state = .equal at hrin
    change p.2.erase.core.state = .equal at hpout
    have hs := congrArg (fun u : AgentState ψ => u.state) hcore.2
    have hp := congrArg (fun u : AgentState ψ => u.path) hcore.2
    have hl := congrArg (fun u : AgentState ψ => u.label) hcore.2
    have hqout : q.2.core.state = .equal := hs.symm.trans hpout
    rcases hpre.2 hqout with ⟨_, hpath, hlabelQ⟩
    have hstate : p.2.erase.core.state = r.erase.core.state :=
      hpout.trans hrin.symm
    have hlabel : p.2.erase.core.label = r.erase.core.label :=
      hl.trans hlabelQ
    rcases hpath with hsame | hbot
    · exact Or.inl
        (boundedMainTriple_ext p.2 r hstate (hp.trans hsame) hlabel)
    · have hpbot : p.2.erase.core.path = .bot := hp.trans hbot
      by_cases hrbot : r.erase.core.path = .bot
      · exact Or.inl
          (boundedMainTriple_ext p.2 r hstate
            (hpbot.trans hrbot.symm) hlabel)
      · exact Or.inr ⟨hpbot, by
          intro heq
          exact hrbot (heq.symm.trans hpbot)⟩

/-- Exact mark-stage projection.  The bounded/raw frame is
`Leader/Wu/WriteSeq/WriterProducerRepair.lean:305`; `markLeaderBirth` itself is at
`Leader/Wu/Comparison/LeaderCreationCleanupRepair.lean:93-100` and may replace `.equal` by
`.eliminate_signal` when birth marking is active, so no unconditional equal
survival is asserted here. -/

theorem mark_stage_mainTriple_frame
    (oldL oldR outL outR : AuthorizedBoundedAgentState ψ κ) :
    let a : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      (outL.erase, outR.erase)
    let born : Bool := K2BirthDispatcher.authBirth oldL.erase oldR.erase a
    let marked : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
      markLeaderBirth born a
    let z := markPublic oldL oldR outL outR
    boundedMainTriple z.1 = authMainTriple marked.1 ∧
      boundedMainTriple z.2 = authMainTriple marked.2 := by
  let a : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    (outL.erase, outR.erase)
  let born : Bool := K2BirthDispatcher.authBirth oldL.erase oldR.erase a
  let marked : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    markLeaderBirth born a
  let z := markPublic oldL oldR outL outR
  have hcore := markPublic_core_frame oldL oldR outL outR
  change z.1.erase.core = marked.1.core ∧
    z.2.erase.core = marked.2.core at hcore
  change boundedMainTriple z.1 = authMainTriple marked.1 ∧
    boundedMainTriple z.2 = authMainTriple marked.2
  constructor
  · unfold boundedMainTriple authMainTriple
    exact congrArg
      (fun u : AgentState ψ => (u.state, u.path, u.label)) hcore.1
  · unfold boundedMainTriple authMainTriple
    exact congrArg
      (fun u : AgentState ψ => (u.state, u.path, u.label)) hcore.2

end R2CheckSurvivalCheckStage2
