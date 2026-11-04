import Leader.Wu.Coherence.NewEqualChainOriginFrames
import Leader.Wu.Coherence.NewEqualStatePathFrame
import Leader.Wu.Coherence.NewEqualComparePreimage


set_option autoImplicit false
set_option Elab.async false


namespace R2NewEqualChainOrigin2


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
open PPLLCompleteMultiLeaderCleanup
open BirthShortWait BirthShortDoneCuts BirthCheckPermitRepair
open K2BirthDispatcher K2BirthLeaderNormalize
open WriterProducerRepair
open R2NewEqualLocal R2NewEqualProvenance
open R2NewEqualPreimage R2NewEqualPreimage2 R2NewEqualChainOrigin


variable {ψ width κ τ : Nat}


/-!
Exact target seam, `Leader/Wu/Coherence/OpenNoHazardFromChainOrigin.lean:27-41`:


def SanitizedR2NewEqualFreshChainOriginNoMainMutation
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  ∀ (l r : R2.Cell ψ κ τ),
    let q := R2.row hψ hw hle
      (sanitizeReadyPhys l) (sanitizeReadyPhys r)
    R2MainCarrierFrame l r q →
      (q.1.base.core.core.state = .equal →
        l.base.core.core.state ≠ .equal →
        R2FreshAtOwnLabel q.1 ∧
          q.1.base.core.core.label.val = 0) ∧
      (q.2.base.core.core.state = .equal →
        r.base.core.core.state ≠ .equal →
        R2FreshAtOwnLabel q.2 ∧
          (q.2.base.core.core.label.val = 0 ∨
            q.1.base.core.core.state = .equal))


Stage decomposition of the ordinary R2 row:
* CHECK: `q13267_checkedBounded` / `doneThroughCheckEntryWidth`.
* permit: `q13267_permitBounded`, applying `permitFix` to the left CHECK
  endpoint.  Public `permitFix_core` makes this a literal core frame.
* pre-writer: `q13267_beforeWriterBounded` / `beforeWriteWidth`.
  At `Leader/Wu/Birth/ShortDoneCuts.lean:376-386` its exact order is
  `authorizedDisappear`, then
  `PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne`, then
  `authorizedSuppressWidth`.
* writer: `stationaryProducerRow`; the six state/path/label equalities are
  `R2NewEqualLocal.stationaryProducerMainComparisonFrame`
  (`Leader/Wu/Coherence/NewEqualLocal.lean:466-476`).
* mark: private `q13267_markBounded`, i.e. `markLeaderBirth`.
* outer `R2.row`: `deletionPriorityExpireOne` on each endpoint, then
  `normalizeLeader`, then `finalPhysical`.


`normalizeLeader_state_path_frame` and `finalPhysical_main_frame` are already
public in `R2NewEqualChainOrigin`; the remaining exposure problem is therefore
localized to CHECK provenance and the private q13267/mark/expiry transport.
-/


private def mainCmpView (u : AgentState ψ) :
    MainState × PathInfo × Fin ψ :=
  (u.state, u.path, u.label)


private def suppressMainTail
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q2 := suppressSigTerminal hψ l r
  let q3 := suppressSigEcho q2.1 q2.2
  suppressSigFinish q3.1 q3.2


private theorem shortCountReset_mainCmp_frame
    (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    let q := shortCountReset hw hle l r
    mainCmpView q.1 = mainCmpView l ∧
      mainCmpView q.2 = mainCmpView r := by
  unfold shortCountReset mainCmpView
  repeat (first | constructor | rfl | split)


private theorem suppressTerminal_mainCmp_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    let q := suppressSigTerminal hψ l r
    mainCmpView q.1 = mainCmpView l ∧
      mainCmpView q.2 = mainCmpView r := by
  unfold suppressSigTerminal mainCmpView
  repeat (first | constructor | rfl | split)


private theorem suppressEcho_mainCmp_frame
    (l r : AgentState ψ) :
    let q := suppressSigEcho l r
    mainCmpView q.1 = mainCmpView l ∧
      mainCmpView q.2 = mainCmpView r := by
  unfold suppressSigEcho mainCmpView
  repeat (first | constructor | rfl | split)


private theorem suppressFinish_mainCmp_frame
    (l r : AgentState ψ) :
    let q := suppressSigFinish l r
    mainCmpView q.1 = mainCmpView l ∧
      mainCmpView q.2 = mainCmpView r := by
  unfold suppressSigFinish mainCmpView
  repeat (first | constructor | rfl | split)


private theorem suppressMainTail_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    let q := suppressMainTail hψ l r
    mainCmpView q.1 = mainCmpView l ∧
      mainCmpView q.2 = mainCmpView r := by
  let q2 := suppressSigTerminal hψ l r
  let q3 := suppressSigEcho q2.1 q2.2
  let q4 := suppressSigFinish q3.1 q3.2
  have h2 := suppressTerminal_mainCmp_frame hψ l r
  change mainCmpView q2.1 = mainCmpView l ∧
    mainCmpView q2.2 = mainCmpView r at h2
  have h3 := suppressEcho_mainCmp_frame q2.1 q2.2
  change mainCmpView q3.1 = mainCmpView q2.1 ∧
    mainCmpView q3.2 = mainCmpView q2.2 at h3
  have h4 := suppressFinish_mainCmp_frame q3.1 q3.2
  change mainCmpView q4.1 = mainCmpView q3.1 ∧
    mainCmpView q4.2 = mainCmpView q3.2 at h4
  change mainCmpView q4.1 = mainCmpView l ∧
    mainCmpView q4.2 = mainCmpView r
  exact ⟨h4.1.trans (h3.1.trans h2.1),
    h4.2.trans (h3.2.trans h2.2)⟩


private theorem suppressWidth_mainCmp_eq_full
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    let q := suppressSigResetKillWidth hψ hw hle l r
    let old := suppressSigResetKill hψ l r
    mainCmpView q.1 = mainCmpView old.1 ∧
      mainCmpView q.2 = mainCmpView old.2 := by
  let p := suppressPrefix l r
  let c := shortCountReset hw hle p.1 p.2
  have hc := shortCountReset_mainCmp_frame hw hle p.1 p.2
  change mainCmpView c.1 = mainCmpView p.1 ∧
    mainCmpView c.2 = mainCmpView p.2 at hc
  have hn := suppressMainTail_frame hψ c.1 c.2
  have ho := suppressMainTail_frame hψ p.1 p.2
  have hnew :
      suppressSigResetKillWidth hψ hw hle l r =
        suppressMainTail hψ c.1 c.2 := by
    rfl
  have hold :
      suppressSigResetKill hψ l r =
        suppressMainTail hψ p.1 p.2 := by
    rfl
  rw [hnew, hold]
  exact ⟨hn.1.trans (hc.1.trans ho.1.symm),
    hn.2.trans (hc.2.trans ho.2.symm)⟩



/-- Width-SUPPRESS inherits the accepted full-SUPPRESS backward theorem.
The only extra operation is the count-only short reset, which the preceding
three-field bridge removes before applying `suppress_equal_preimage`. -/
theorem authorizedSuppressWidth_equal_preimage
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) :
    let q := authorizedSuppressWidth hψ hw hle l r
    (q.1.core.state = .equal →
      l.core.state = .equal ∧
        (q.1.core.path = l.core.path ∨ q.1.core.path = .bot) ∧
        q.1.core.label = l.core.label) ∧
    (q.2.core.state = .equal →
      r.core.state = .equal ∧
        (q.2.core.path = r.core.path ∨ q.2.core.path = .bot) ∧
        q.2.core.label = r.core.label) := by
  dsimp only
  have hv := suppressWidth_mainCmp_eq_full hψ hw hle l.core r.core
  dsimp only at hv
  have hvLs :
      (authorizedSuppressWidth hψ hw hle l r).1.core.state =
        (authorizedReconcile (suppressSigResetKill hψ) l r).1.core.state := by
    change (suppressSigResetKillWidth hψ hw hle l.core r.core).1.state =
      (suppressSigResetKill hψ l.core r.core).1.state
    simpa only [mainCmpView] using
      congrArg (fun x : MainState × PathInfo × Fin ψ => x.1) hv.1
  have hvLp :
      (authorizedSuppressWidth hψ hw hle l r).1.core.path =
        (authorizedReconcile (suppressSigResetKill hψ) l r).1.core.path := by
    change (suppressSigResetKillWidth hψ hw hle l.core r.core).1.path =
      (suppressSigResetKill hψ l.core r.core).1.path
    simpa only [mainCmpView] using
      congrArg (fun x : MainState × PathInfo × Fin ψ => x.2.1) hv.1
  have hvLl :
      (authorizedSuppressWidth hψ hw hle l r).1.core.label =
        (authorizedReconcile (suppressSigResetKill hψ) l r).1.core.label := by
    change (suppressSigResetKillWidth hψ hw hle l.core r.core).1.label =
      (suppressSigResetKill hψ l.core r.core).1.label
    simpa only [mainCmpView] using
      congrArg (fun x : MainState × PathInfo × Fin ψ => x.2.2) hv.1
  have hvRs :
      (authorizedSuppressWidth hψ hw hle l r).2.core.state =
        (authorizedReconcile (suppressSigResetKill hψ) l r).2.core.state := by
    change (suppressSigResetKillWidth hψ hw hle l.core r.core).2.state =
      (suppressSigResetKill hψ l.core r.core).2.state
    simpa only [mainCmpView] using
      congrArg (fun x : MainState × PathInfo × Fin ψ => x.1) hv.2
  have hvRp :
      (authorizedSuppressWidth hψ hw hle l r).2.core.path =
        (authorizedReconcile (suppressSigResetKill hψ) l r).2.core.path := by
    change (suppressSigResetKillWidth hψ hw hle l.core r.core).2.path =
      (suppressSigResetKill hψ l.core r.core).2.path
    simpa only [mainCmpView] using
      congrArg (fun x : MainState × PathInfo × Fin ψ => x.2.1) hv.2
  have hvRl :
      (authorizedSuppressWidth hψ hw hle l r).2.core.label =
        (authorizedReconcile (suppressSigResetKill hψ) l r).2.core.label := by
    change (suppressSigResetKillWidth hψ hw hle l.core r.core).2.label =
      (suppressSigResetKill hψ l.core r.core).2.label
    simpa only [mainCmpView] using
      congrArg (fun x : MainState × PathInfo × Fin ψ => x.2.2) hv.2
  have hs := R2NewEqualPreimage.suppress_equal_preimage hψ l r
  dsimp only at hs
  constructor
  · intro hout
    have hold :
        (authorizedReconcile (suppressSigResetKill hψ) l r).1.core.state =
          .equal := hvLs.symm.trans hout
    rcases hs.1 hold with ⟨hstate, hpath, hlabel⟩
    refine ⟨hstate, ?_, hvLl.trans hlabel⟩
    rcases hpath with hp | hp
    · exact Or.inl (hvLp.trans hp)
    · exact Or.inr (hvLp.trans hp)
  · intro hout
    have hold :
        (authorizedReconcile (suppressSigResetKill hψ) l r).2.core.state =
          .equal := hvRs.symm.trans hout
    rcases hs.2 hold with ⟨hstate, hpath, hlabel⟩
    refine ⟨hstate, ?_, hvRl.trans hlabel⟩
    rcases hpath with hp | hp
    · exact Or.inl (hvRp.trans hp)
    · exact Or.inr (hvRp.trans hp)



/-- Composite backward theorem for the exact public pre-writer cut.
`beforeWriteWidth` is, in source order, DISAPPEAR → action-one COMPARE →
width-SUPPRESS.  Thus any endpoint that is `.equal` at the writer input was
already `.equal` at the pre-writer input.  Labels are preserved; the main path
is preserved unless SUPPRESS cleared it to `.bot`. -/
theorem beforeWriteWidth_equal_preimage
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) :
    let q := beforeWriteWidth hψ hw hle l r
    (q.1.core.state = .equal →
      l.core.state = .equal ∧
        (q.1.core.path = l.core.path ∨ q.1.core.path = .bot) ∧
        q.1.core.label = l.core.label) ∧
    (q.2.core.state = .equal →
      r.core.state = .equal ∧
        (q.2.core.path = r.core.path ∨ q.2.core.path = .bot) ∧
        q.2.core.label = r.core.label) := by
  let q0 := authorizedDisappear hψ l r
  let q1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne
    hψ q0.1 q0.2
  have hd := R2NewEqualPreimage.authorizedDisappear_equal_preimage hψ l r
  dsimp only at hd
  have hc :=
    R2NewEqualPreimage2.compareActionOne_equal_preimage_holds hψ q0.1 q0.2
  unfold R2NewEqualPreimage.compareActionOne_equal_preimage at hc
  dsimp only at hc
  have hs := authorizedSuppressWidth_equal_preimage
    hψ hw hle q1.1 q1.2
  dsimp only at hs
  change
    ((authorizedSuppressWidth hψ hw hle q1.1 q1.2).1.core.state = .equal →
      l.core.state = .equal ∧
        ((authorizedSuppressWidth hψ hw hle q1.1 q1.2).1.core.path =
            l.core.path ∨
          (authorizedSuppressWidth hψ hw hle q1.1 q1.2).1.core.path = .bot) ∧
        (authorizedSuppressWidth hψ hw hle q1.1 q1.2).1.core.label =
          l.core.label) ∧
    ((authorizedSuppressWidth hψ hw hle q1.1 q1.2).2.core.state = .equal →
      r.core.state = .equal ∧
        ((authorizedSuppressWidth hψ hw hle q1.1 q1.2).2.core.path =
            r.core.path ∨
          (authorizedSuppressWidth hψ hw hle q1.1 q1.2).2.core.path = .bot) ∧
        (authorizedSuppressWidth hψ hw hle q1.1 q1.2).2.core.label =
          r.core.label)
  constructor
  · intro hout
    rcases hs.1 hout with ⟨hsState, hsPath, hsLabel⟩
    rcases hc.1 hsState with ⟨hcState, hcPath, hcLabel⟩
    rcases hd.1 hcState with ⟨hdState, hdPath, hdLabel⟩
    refine ⟨hdState, ?_, hsLabel.trans (hcLabel.symm.trans hdLabel.symm)⟩
    rcases hsPath with hp | hp
    · exact Or.inl (hp.trans (hcPath.symm.trans hdPath.symm))
    · exact Or.inr hp
  · intro hout
    rcases hs.2 hout with ⟨hsState, hsPath, hsLabel⟩
    rcases hc.2 hsState with ⟨hcState, hcPath, hcLabel⟩
    rcases hd.2 hcState with ⟨hdState, hdPath, hdLabel⟩
    refine ⟨hdState, ?_, hsLabel.trans (hcLabel.symm.trans hdLabel.symm)⟩
    rcases hsPath with hp | hp
    · exact Or.inl (hp.trans (hcPath.symm.trans hdPath.symm))
    · exact Or.inr hp


/-- What remains after `beforeWriteWidth_equal_preimage` and the public writer,
permit, normalize-state/path, and finalPhysical frames.


For the actual sanitized ordinary pair, CHECK still owes ready/source alignment
at its real input.  The private q13267/mark/expiry shell still owes a public
transport saying a final equal comes from the corresponding through-CHECK equal
(with its path/label carrier), plus the paired left-equal survival needed when
the responder equality is the non-root CHECK-R continuation. -/
def RemainingCheckAndPrivateCutsObligation
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  ∀ (l r : R2.Cell ψ κ τ),
    let sl := R2CoherenceBranches.sanitizeReadyPhys l
    let sr := R2CoherenceBranches.sanitizeReadyPhys r
    let pl := BirthSigMoveDisposalRepair.prepareExpiringDisposal hψ sl.base
    let pr := BirthSigMoveDisposalRepair.prepareExpiringDisposal hψ sr.base
    let al := PPLLLeaderCreationCleanupRepair.normalizeDeletion pl.core.erase
    let ar := PPLLLeaderCreationCleanupRepair.normalizeDeletion pr.core.erase
    let b := R2NewEqualProvenance.r2CheckInput (κ := κ) hψ hw hle al ar
    let c := R2NewEqualProvenance.r2ThroughCheck (κ := κ) hψ hw hle al ar
    let q := R2.row hψ hw hle sl sr
    let ql : AgentState ψ := q.1.base.core.erase.core
    let qr : AgentState ψ := q.2.base.core.erase.core
    PPLLLeaderCreationCleanupRepair.deletionActive al = false →
    PPLLLeaderCreationCleanupRepair.deletionActive ar = false →
    R2NewEqualLocal.R2MainCarrierFrame l r q →
    (R2CoherenceBranches.ReadyAlignedRaw b.1.core ∧
      R2CoherenceBranches.ReadyAlignedRaw b.2.core) ∧
    (ql.state = .equal →
      c.1.core.state = .equal ∧
        (ql.path = c.1.core.path ∨ ql.path = .bot) ∧
        ql.label = c.1.core.label) ∧
    (qr.state = .equal →
      c.2.core.state = .equal ∧
        (qr.path = c.2.core.path ∨ qr.path = .bot) ∧
        qr.label = c.2.core.label) ∧
    (qr.state = .equal → c.1.core.state = .equal → ql.state = .equal)


end R2NewEqualChainOrigin2
