import Leader.Wu.ShortGap.UnifiedSync

/-!
# Real traffic accessor audit for the unified short-gap node

This file instantiates the abstract Drop-4 traffic view with the repository's
actual legacy fields and shows that the unconditional classifiability law is
false on the checked commit-at-target row itself.

No runner, protocol edit, axiom, `sorry`, `admit`, or `native_decide` occurs.
-/

namespace ShortGapUnifiedRealTrafficAudit

open ShortGapLiteralGapRows
open ShortGapCaptureReservation
open ShortGapCaptureCommitRows
open ShortGapSpliceCommit
open ShortGapSpliceCommitCorrected
open ShortGapSpliceDemotion
open ShortGapUnifiedNode
open ShortGapUnifiedGuards
open ShortGapUnifiedDispatch
open ShortGapUnifiedSync

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

/-! ## The actual legacy accessors -/

/-- The existing optional clockwise selection-port accessor is
`Node.cwPort`, read through `CNode.raw`. -/
def selectionPortView (n : CNode) : Option CwPort :=
  n.raw.cwPort

/-- `CNode.carrier` uses the constructor `.none` internally; lift the two
physically occupied carrier values into the `Option` expected by `TrafficView`. -/
def captureCarrierView (n : CNode) : Option CommitCarrier :=
  match n.carrier with
  | .none => none
  | .commit => some .commit
  | .committedBack => some .committedBack

/-- `payload`, not `bridge`, is the moving splice snapshot.  `liftLeft` installs
and transports it with the returning committed receipt; `adoptDepositLCorrected`
then moves it into A and `directAdoptLCorrected` consumes it. -/
def splicePayloadView (n : UNode) : Option SnapPhase :=
  n.payload

/-- Repository-real instantiation of the abstract view. -/
def realTrafficView : TrafficView where
  hasSelection := selectionPortView
  hasCapture := captureCarrierView
  hasSplice := splicePayloadView

/-- Audit the three instantiated accessors against the actual stored fields. -/
theorem realTrafficView_accessors (a : UNode) :
    realTrafficView.hasSelection a.core = a.core.raw.cwPort ∧
      realTrafficView.hasCapture a.core = captureCarrierView a.core ∧
      realTrafficView.hasSplice a = a.payload := by
  constructor
  · rfl
  constructor <;> rfl

/-- The first `TrafficViewSpec` law is valid for the real splice accessor. -/
theorem realTrafficView_splice_traffic_irrelevant
    (a : UNode) (t : UTraffic) :
    realTrafficView.hasSplice (setTraffic a t) =
      realTrafficView.hasSplice a := by
  cases a
  rfl

/-! ## Checked commit-at-target counterexample to exclusive classifiability -/

/-- The exact snapshot stored by the concrete target below. -/
def witnessSnap : SnapPhase :=
  ⟨.toSend, .home⟩

/-- Empty interior commit slot.  All splice wrapper fields are neutral. -/
def witnessLeftS : SNode :=
  { core := slotNode .commit
    bridge := none
    payload := none
    splice := .inactive
    witness := .none
    flush := .none }

/-- Literal accepted live target for `commit_at_target`, again splice-neutral. -/
def witnessRightS : SNode :=
  { core := targetNode .toSend .home .capturing .reserved true
    bridge := none
    payload := none
    splice := .inactive
    witness := .none
    flush := .none }

private theorem witnessLeftNeutral : Neutral witnessLeftS := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem witnessRightNeutral : Neutral witnessRightS := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The core row is exactly the public checked `commit_at_target` equation. -/
private theorem witnessCommitRow :
    commitRow witnessLeftS.core witnessRightS.core =
      (slotNode .committedBack,
        targetNode .toSend .home .capturing .committed false) := by
  change
    commitRow (slotNode .commit)
        (targetNode .toSend .home .capturing .reserved true) = _
  exact commit_at_target .toSend .home .capturing

private theorem witnessV2CoreRow :
    spliceRowCorrected witnessLeftS witnessRightS =
      liftPair witnessLeftS witnessRightS
        (commitRow witnessLeftS.core witnessRightS.core) :=
  spliceRowCorrected_core witnessLeftS witnessRightS
    witnessLeftNeutral witnessRightNeutral

private theorem witnessNotDemotion :
    ¬ DemotionEnabled witnessLeftS witnessRightS := by
  intro h
  have hs : witnessRightS.splice = .drained := h.1.2.1
  have hbad : SpliceCtl.inactive = SpliceCtl.drained := by
    simpa [witnessRightS] using hs
  cases hbad

/-- The real WithDemotion output is a *coupled* returning receipt: the capture carrier
and splice payload coexist on the same interior slot. -/
private theorem witnessV3LeftFields :
    let x := (spliceRowWithDemotion witnessLeftS witnessRightS).1
    x.core.raw = emptyRaw ∧
      x.core.carrier = .committedBack ∧
      x.payload = some witnessSnap := by
  rw [spliceRowWithDemotion_eq_of_not_demotion
    witnessLeftS witnessRightS witnessNotDemotion]
  rw [witnessV2CoreRow, witnessCommitRow]
  simp [liftPair, liftLeft, committedNow,
    witnessLeftS, witnessRightS, witnessSnap,
    slotNode, targetNode, snapNode]

/-- Put the exact exclusive tags on the two pre-row legacy states. -/
def witnessLeftU : UNode :=
  setTraffic (ofSNode witnessLeftS) (.capture .commit)

/-- The target's actual `Node.cwPort` is `some .toSend`. -/
def witnessRightU : UNode :=
  setTraffic (ofSNode witnessRightS) (.selection .toSend)

private theorem witnessLeftU_toSNode :
    toSNode witnessLeftU = witnessLeftS := by
  unfold witnessLeftU
  rw [toSNode_setTraffic, toSNode_ofSNode]

private theorem witnessRightU_toSNode :
    toSNode witnessRightU = witnessRightS := by
  unfold witnessRightU
  rw [toSNode_setTraffic, toSNode_ofSNode]

private theorem witnessLeftUSync :
    USync realTrafficView witnessLeftU := by
  rfl

private theorem witnessRightUSync :
    USync realTrafficView witnessRightU := by
  rfl

/-- The exact legacy left output re-embedded with the old empty Drop-3 tag. -/
def witnessLeftOut : UNode :=
  ofSNode (spliceRowWithDemotion witnessLeftS witnessRightS).1

private theorem witnessLeftOut_selection_none :
    realTrafficView.hasSelection witnessLeftOut.core = none := by
  rcases witnessV3LeftFields with ⟨hraw, _hcarrier, _hpayload⟩
  change selectionPortView (spliceRowWithDemotion witnessLeftS witnessRightS).1.core = none
  unfold selectionPortView
  rw [hraw]
  rfl

private theorem witnessLeftOut_capture_back :
    realTrafficView.hasCapture witnessLeftOut.core =
      some CommitCarrier.committedBack := by
  rcases witnessV3LeftFields with ⟨_hraw, hcarrier, _hpayload⟩
  change captureCarrierView (spliceRowWithDemotion witnessLeftS witnessRightS).1.core =
    some CommitCarrier.committedBack
  unfold captureCarrierView
  rw [hcarrier]

private theorem witnessLeftOut_splice_some :
    realTrafficView.hasSplice witnessLeftOut = some witnessSnap := by
  rcases witnessV3LeftFields with ⟨_hraw, _hcarrier, hpayload⟩
  change (spliceRowWithDemotion witnessLeftS witnessRightS).1.payload = some witnessSnap
  exact hpayload

/-- This is the failed `TrafficViewSpec` clause in its smallest concrete form:
`trafficCode` rejects the simultaneously live committed-back carrier and splice
snapshot. -/
private theorem witnessLeftOut_code_none :
    trafficCode realTrafficView witnessLeftOut = none := by
  unfold trafficCode
  rw [witnessLeftOut_selection_none,
    witnessLeftOut_capture_back, witnessLeftOut_splice_some]

private theorem witnessLeftOut_not_shape :
    ¬ TrafficShape realTrafficView witnessLeftOut := by
  intro h
  rcases h with ⟨t, ht⟩
  rw [witnessLeftOut_code_none] at ht
  cases ht

/-- Minimal source-correct additional traffic shape forced by
`commit_at_target` + `liftLeft`: a returning committed carrier physically owns
a splice snapshot at the same interior slot. -/
def CoupledCommittedSnapshot (a : UNode) : Prop :=
  a.core.raw = emptyRaw ∧
    a.core.carrier = .committedBack ∧
    ∃ s : SnapPhase, a.payload = some s

private theorem witnessLeftOut_coupled :
    CoupledCommittedSnapshot witnessLeftOut := by
  rcases witnessV3LeftFields with ⟨hraw, hcarrier, hpayload⟩
  change
    (spliceRowWithDemotion witnessLeftS witnessRightS).1.core.raw = emptyRaw ∧
      (spliceRowWithDemotion witnessLeftS witnessRightS).1.core.carrier = .committedBack ∧
      ∃ s : SnapPhase,
        (spliceRowWithDemotion witnessLeftS witnessRightS).1.payload = some s
  exact ⟨hraw, hcarrier, ⟨witnessSnap, hpayload⟩⟩

/-- The synchronized-input restriction does not repair the false output law. -/
theorem commit_at_target_sync_exposes_coupled_shape :
    USync realTrafficView witnessLeftU ∧
      USync realTrafficView witnessRightU ∧
      ¬ TrafficShape realTrafficView witnessLeftOut ∧
      CoupledCommittedSnapshot witnessLeftOut :=
  ⟨witnessLeftUSync, witnessRightUSync,
    witnessLeftOut_not_shape, witnessLeftOut_coupled⟩

/-- Therefore the repository-real view cannot satisfy the abstract
`TrafficViewSpec`: its unconditional WithDemotion classifiability field is false. -/
theorem realTrafficView_not_spec :
    ¬ TrafficViewSpec realTrafficView := by
  intro H
  have hshape :=
    (H.v3_outputs_classifiable witnessLeftU witnessRightU).1
  rw [witnessLeftU_toSNode, witnessRightU_toSNode] at hshape
  exact witnessLeftOut_not_shape hshape

/-! ## The exact corrected classifier clause forced by the row -/

/-- Keep the old exclusive classifier except for the physically real
`committedBack + payload` return state, which is one splice-return traffic
object rather than two independent traffic objects. -/
def trafficCodeCoupled (a : UNode) : Option UTraffic :=
  match selectionPortView a.core, captureCarrierView a.core, splicePayloadView a with
  | none, some .committedBack, some s => some (.splice s)
  | _, _, _ => trafficCode realTrafficView a

/-- The concrete failing output is classified by the corrected coupled rule. -/
theorem witnessLeftOut_coupled_code :
    trafficCodeCoupled witnessLeftOut = some (.splice witnessSnap) := by
  unfold trafficCodeCoupled
  have hsel : selectionPortView witnessLeftOut.core = none := by
    exact witnessLeftOut_selection_none
  have hc : captureCarrierView witnessLeftOut.core =
      some CommitCarrier.committedBack := by
    exact witnessLeftOut_capture_back
  have hs : splicePayloadView witnessLeftOut = some witnessSnap := by
    exact witnessLeftOut_splice_some
  rw [hsel, hc, hs]

/-! ## Drop 3 really is not synchronization-preserving -/

private theorem witnessLegacyLeftNonempty :
    LegacyTrafficNonempty realTrafficView
      (spliceRowWithDemotion witnessLeftS witnessRightS).1 := by
  right
  left
  intro hnone
  have hc :
      realTrafficView.hasCapture
          (spliceRowWithDemotion witnessLeftS witnessRightS).1.core =
        some CommitCarrier.committedBack := by
    rcases witnessV3LeftFields with ⟨_hraw, hcarrier, _hpayload⟩
    change captureCarrierView
        (spliceRowWithDemotion witnessLeftS witnessRightS).1.core =
      some CommitCarrier.committedBack
    unfold captureCarrierView
    rw [hcarrier]
  rw [hc] at hnone
  cases hnone

private theorem witnessULegacyLeftNonempty :
    LegacyTrafficNonempty realTrafficView
      (spliceRowWithDemotion (toSNode witnessLeftU) (toSNode witnessRightU)).1 := by
  rw [witnessLeftU_toSNode, witnessRightU_toSNode]
  exact witnessLegacyLeftNonempty

/-- Concrete real-instance failure at the left endpoint of Drop 3. -/
theorem real_uRow_left_not_sync :
    ¬ USync realTrafficView
      (ShortGapUnifiedDispatch.uRow witnessLeftU witnessRightU).1 :=
  uRow_left_not_sync_of_nonempty
    realTrafficView witnessLeftU witnessRightU witnessULegacyLeftNonempty

/-- Discharges the abstract existence obligation with the concrete checked
commit-at-target pair above. -/
theorem real_uRow_not_sync_preserving :
    uRow_not_sync_preserving :=
  uRow_not_sync_preserving_of_witness
    realTrafficView witnessLeftU witnessRightU
    witnessLeftUSync witnessRightUSync witnessULegacyLeftNonempty

/-! ## Exact legacy non-interference seams that remain valid over `uRow4` -/

/-- Whatever happens to the derived traffic tag, Drop 4 changes no legacy
physical field beyond the checked WithDemotion row. -/
theorem real_uRow4_legacy_exact (a b : UNode) :
    (toSNode (uRow4 realTrafficView a b).1,
      toSNode (uRow4 realTrafficView a b).2) =
      spliceRowWithDemotion (toSNode a) (toSNode b) :=
  uRow4_toSNode realTrafficView a b

/-- Off demotion, every legacy field of Drop 4 is exactly the Corrected result.  This
is the sound seam for lifting the existing flush/fresh/capture/splice Corrected frame
lemmas; it makes no false `USync` claim. -/
theorem real_uRow4_v2_legacy_of_not_demotion
    (a b : UNode) (h : ¬ UDemotionEnabled a b) :
    (toSNode (uRow4 realTrafficView a b).1,
      toSNode (uRow4 realTrafficView a b).2) =
      spliceRowCorrected (toSNode a) (toSNode b) := by
  have hd : ¬ DemotionEnabled (toSNode a) (toSNode b) := by
    intro hD
    exact h ((uDemotionEnabled_iff_toSNode a b).2 hD)
  calc
    (toSNode (uRow4 realTrafficView a b).1,
        toSNode (uRow4 realTrafficView a b).2) =
        spliceRowWithDemotion (toSNode a) (toSNode b) :=
      uRow4_toSNode realTrafficView a b
    _ = spliceRowCorrected (toSNode a) (toSNode b) :=
      spliceRowWithDemotion_eq_of_not_demotion (toSNode a) (toSNode b) hd

/-- On demotion, Drop 4 projects to the exact WithDemotion demotion pair: the left
legacy node is framed completely and the right is exactly `demote`. -/
theorem real_uRow4_demotion_legacy
    (a b : UNode) (h : UDemotionEnabled a b) :
    toSNode (uRow4 realTrafficView a b).1 = toSNode a ∧
      toSNode (uRow4 realTrafficView a b).2 = demote (toSNode b) := by
  have hd : DemotionEnabled (toSNode a) (toSNode b) :=
    (uDemotionEnabled_iff_toSNode a b).1 h
  have hp := uRow4_toSNode realTrafficView a b
  rw [spliceRowWithDemotion_demotes (toSNode a) (toSNode b) hd] at hp
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

#print axioms ShortGapUnifiedRealTrafficAudit.realTrafficView_accessors
#print axioms ShortGapUnifiedRealTrafficAudit.realTrafficView_splice_traffic_irrelevant
#print axioms ShortGapUnifiedRealTrafficAudit.commit_at_target_sync_exposes_coupled_shape
#print axioms ShortGapUnifiedRealTrafficAudit.realTrafficView_not_spec
#print axioms ShortGapUnifiedRealTrafficAudit.witnessLeftOut_coupled_code
#print axioms ShortGapUnifiedRealTrafficAudit.real_uRow_left_not_sync
#print axioms ShortGapUnifiedRealTrafficAudit.real_uRow_not_sync_preserving
#print axioms ShortGapUnifiedRealTrafficAudit.real_uRow4_legacy_exact
#print axioms ShortGapUnifiedRealTrafficAudit.real_uRow4_v2_legacy_of_not_demotion
#print axioms ShortGapUnifiedRealTrafficAudit.real_uRow4_demotion_legacy

end ShortGapUnifiedRealTrafficAudit
