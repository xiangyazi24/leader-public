import Leader.Wu.ShortGap.UnifiedDispatch

set_option autoImplicit false

open ShortGapSpliceCommit
open ShortGapSpliceCommitCorrected
open ShortGapSpliceDemotion
open ShortGapUnifiedNode
open ShortGapUnifiedGuards
open ShortGapUnifiedDispatch
open ShortGapCaptureCommitRows
open ShortGapLiteralGapRows
open ShortGapSpliceCommit
open ShortGapUnifiedNode

namespace ShortGapUnifiedSync

/--
Abstract view of the three legacy traffic carriers.

Instantiate these with the repository's existing accessors for:
* the legacy selection port stored in `CNode`;
* the legacy capture carrier stored in `CNode`;
* the legacy splice snapshot stored in the non-traffic fields of `UNode`.

The last accessor is intentionally abstract rather than guessing whether the
repository's splice snapshot is read from `bridge`, `payload`, or a derived
combination of those fields.
-/
structure TrafficView where
  hasSelection : CNode -> Option CwPort
  hasCapture : CNode -> Option CommitCarrier
  hasSplice : UNode -> Option SnapPhase

/-- Replace only the derived unified traffic tag. -/
def setTraffic (a : UNode) (t : UTraffic) : UNode :=
  { a with traffic := t }

/-- The legacy core is unchanged when only the unified tag is replaced. -/
theorem setTraffic_core (a : UNode) (t : UTraffic) :
    (setTraffic a t).core = a.core := by
  cases a
  rfl

/-- Replacing the unified tag sets exactly that tag. -/
theorem setTraffic_traffic (a : UNode) (t : UTraffic) :
    (setTraffic a t).traffic = t := by
  cases a
  rfl

/-- Forgetting unified traffic is insensitive to `setTraffic`. -/
theorem toSNode_setTraffic (a : UNode) (t : UTraffic) :
    toSNode (setTraffic a t) = toSNode a := by
  cases a
  rfl

/-- Embedded legacy nodes preserve their legacy core. -/
theorem ofSNode_core (a : SNode) :
    (ofSNode a).core = a.core := by
  cases a
  rfl

/-- Embedded legacy nodes always start with empty unified traffic. -/
theorem ofSNode_traffic (a : SNode) :
    (ofSNode a).traffic = .empty := by
  cases a
  rfl

/--
Classify the legacy traffic fields when, and only when, they describe one of
exactly four physically admissible shapes: selection only, capture only,
splice only, or all empty.  Overlapping legacy traffic is rejected as `none`.
-/
def trafficCode (V : TrafficView) (a : UNode) : Option UTraffic :=
  match V.hasSelection a.core, V.hasCapture a.core, V.hasSplice a with
  | some c, none, none => some (.selection c)
  | none, some k, none => some (.capture k)
  | none, none, some s => some (.splice s)
  | none, none, none => some .empty
  | _, _, _ => none

/--
Synchronization means that the legacy fields are physically exclusive and
classify to exactly the unified tag stored in the node.
-/
def USync (V : TrafficView) (a : UNode) : Prop :=
  trafficCode V a = some a.traffic

/-- Exact characterization requested for the old embedding. -/
theorem sync_ofSNode_iff (V : TrafficView) (a : SNode) :
    USync V (ofSNode a) <->
      (V.hasSelection a.core = none /\
       V.hasCapture a.core = none /\
       V.hasSplice (ofSNode a) = none) := by
  unfold USync
  rw [ofSNode_traffic]
  cases hSel : V.hasSelection a.core <;>
  cases hCap : V.hasCapture a.core <;>
  cases hSpl : V.hasSplice (ofSNode a) <;>
  simp [trafficCode, ofSNode_core, hSel, hCap, hSpl]

/-- A legacy configuration is classifiable by the exclusive unified tag. -/
def TrafficShape (V : TrafficView) (a : UNode) : Prop :=
  Exists fun t : UTraffic => trafficCode V a = some t

/--
Changing only `traffic` leaves the classifier unchanged when the splice view
really is an accessor for legacy fields only.
-/
theorem trafficCode_setTraffic
    (V : TrafficView) (a : UNode) (t : UTraffic)
    (hSplice : V.hasSplice (setTraffic a t) = V.hasSplice a) :
    trafficCode V (setTraffic a t) = trafficCode V a := by
  unfold trafficCode
  simpa only [setTraffic_core, hSplice]

/-- Re-derive a unified tag from the legacy fields; overlap falls back to empty. -/
def resyncTraffic (V : TrafficView) (a : UNode) : UTraffic :=
  match trafficCode V a with
  | some t => t
  | none => .empty

/-- Re-derive only the unified traffic tag, preserving all legacy fields. -/
def resyncNode (V : TrafficView) (a : UNode) : UNode :=
  setTraffic a (resyncTraffic V a)

/-- Resynchronization never changes the legacy physical node. -/
theorem resyncNode_toSNode (V : TrafficView) (a : UNode) :
    toSNode (resyncNode V a) = toSNode a := by
  unfold resyncNode
  exact toSNode_setTraffic a (resyncTraffic V a)

/--
A classifiable legacy state resynchronizes successfully, provided the splice
accessor ignores the new traffic tag.
-/
theorem resyncNode_sync
    (V : TrafficView)
    (hStable : forall (x : UNode) (t : UTraffic),
      V.hasSplice (setTraffic x t) = V.hasSplice x)
    (a : UNode) (hShape : TrafficShape V a) :
    USync V (resyncNode V a) := by
  rcases hShape with ⟨t, ht⟩
  have hCode : trafficCode V (resyncNode V a) = some t := by
    calc
      trafficCode V (resyncNode V a) = trafficCode V a := by
        unfold resyncNode
        exact trafficCode_setTraffic V a (resyncTraffic V a)
          (hStable a (resyncTraffic V a))
      _ = some t := ht
  have hTraffic : (resyncNode V a).traffic = t := by
    simp [resyncNode, resyncTraffic, ht, setTraffic_traffic]
  unfold USync
  rw [hTraffic]
  exact hCode

/--
These are the two repository-specific facts needed for the unconditional
`uRow4_sync` requested below.

`splice_traffic_irrelevant` should be immediate once `hasSplice` is
instantiated by the real legacy splice accessor.

`v3_outputs_classifiable` is the substantive physical-exclusivity obligation:
every legacy WithDemotion row output must contain at most one of the three traffic kinds.
-/
structure TrafficViewSpec (V : TrafficView) where
  splice_traffic_irrelevant :
    forall (a : UNode) (t : UTraffic),
      V.hasSplice (setTraffic a t) = V.hasSplice a
  v3_outputs_classifiable :
    forall (a b : UNode),
      TrafficShape V
          (ofSNode (spliceRowWithDemotion (toSNode a) (toSNode b)).1) /\
      TrafficShape V
          (ofSNode (spliceRowWithDemotion (toSNode a) (toSNode b)).2)

/--
The real Drop-4 row: execute the checked legacy WithDemotion row, embed each physical
output, then derive its exclusive unified traffic tag.
-/
def uRow4 (V : TrafficView) (a b : UNode) : UNode × UNode :=
  let r := spliceRowWithDemotion (toSNode a) (toSNode b)
  (resyncNode V (ofSNode r.1), resyncNode V (ofSNode r.2))

/-- Every Drop-4 output is synchronized under the two explicit view laws. -/
theorem uRow4_sync
    (V : TrafficView) (H : TrafficViewSpec V) (a b : UNode) :
    USync V (uRow4 V a b).1 /\ USync V (uRow4 V a b).2 := by
  dsimp [uRow4]
  constructor
  · apply resyncNode_sync V H.splice_traffic_irrelevant
    exact (H.v3_outputs_classifiable a b).1
  · apply resyncNode_sync V H.splice_traffic_irrelevant
    exact (H.v3_outputs_classifiable a b).2

/-- Drop 4 changes no legacy physical field at either endpoint. -/
theorem uRow4_toSNode (V : TrafficView) (a b : UNode) :
    (toSNode (uRow4 V a b).1, toSNode (uRow4 V a b).2) =
      spliceRowWithDemotion (toSNode a) (toSNode b) := by
  simp [uRow4, resyncNode_toSNode, toSNode_ofSNode]

/-- At least one legacy traffic view is nonempty. -/
def LegacyTrafficNonempty (V : TrafficView) (a : SNode) : Prop :=
  V.hasSelection a.core ≠ none \/
  V.hasCapture a.core ≠ none \/
  V.hasSplice (ofSNode a) ≠ none

/-- Any embedded legacy node carrying traffic fails `USync`. -/
theorem not_sync_ofSNode_of_nonempty
    (V : TrafficView) (a : SNode) (h : LegacyTrafficNonempty V a) :
    ¬ USync V (ofSNode a) := by
  intro hSync
  have hZero := (sync_ofSNode_iff V a).mp hSync
  cases h with
  | inl hSel =>
      exact hSel hZero.1
  | inr hRest =>
      cases hRest with
      | inl hCap =>
          exact hCap hZero.2.1
      | inr hSpl =>
          exact hSpl hZero.2.2

/--
Drop 3's left output is not synchronized whenever its legacy WithDemotion result really
contains one of the three traffic payloads.
-/
theorem uRow_left_not_sync_of_nonempty
    (V : TrafficView) (a b : UNode)
    (h : LegacyTrafficNonempty V
      (spliceRowWithDemotion (toSNode a) (toSNode b)).1) :
    ¬ USync V (ShortGapUnifiedDispatch.uRow a b).1 := by
  simpa [ShortGapUnifiedDispatch.uRow] using
    (not_sync_ofSNode_of_nonempty V
      (spliceRowWithDemotion (toSNode a) (toSNode b)).1 h)

/--
Precise existence obligation for showing that the Drop-3 row is not a
`USync`-preserving transition relation.  A concrete repository witness is
needed; it cannot be obtained from the abstract accessor types alone.
-/
def uRow_not_sync_preserving : Prop :=
  Exists fun V : TrafficView =>
    Exists fun a : UNode =>
      Exists fun b : UNode =>
        USync V a /\ USync V b /\
          ¬ USync V (ShortGapUnifiedDispatch.uRow a b).1

/-- One synchronized input pair with a nonempty legacy left output is enough. -/
theorem uRow_not_sync_preserving_of_witness
    (V : TrafficView) (a b : UNode)
    (ha : USync V a) (hb : USync V b)
    (hOut : LegacyTrafficNonempty V
      (spliceRowWithDemotion (toSNode a) (toSNode b)).1) :
    uRow_not_sync_preserving := by
  exact ⟨V, a, b, ha, hb,
    uRow_left_not_sync_of_nonempty V a b hOut⟩

/--
List-based certificate for the eventual exact counting payoff.

`exact_ratio` uses the convention
  syncCount / legacyCount = ratioNum / ratioDen
encoded by cross multiplication, so no rational-number library is needed.

The four natural-number parameters are deliberately explicit: instantiate
them by numerals once the repository's concrete traffic accessors and state
enumeration lists are supplied.
-/
structure SyncEnumerationSpec
    (V : TrafficView)
    (syncCount legacyCount ratioNum ratioDen : Nat) where
  syncList : List UNode
  legacyList : List SNode
  sync_complete : forall a : UNode, USync V a -> List.Mem a syncList
  sync_sound : forall a : UNode, List.Mem a syncList -> USync V a
  sync_nodup : List.Nodup syncList
  legacy_complete : forall a : SNode, List.Mem a legacyList
  legacy_nodup : List.Nodup legacyList
  sync_length : syncList.length = syncCount
  legacy_length : legacyList.length = legacyCount
  strict_smaller : syncCount < legacyCount
  ratio_den_positive : 0 < ratioDen
  exact_ratio : syncCount * ratioDen = legacyCount * ratioNum

end ShortGapUnifiedSync

#print axioms ShortGapUnifiedSync.setTraffic_core
#print axioms ShortGapUnifiedSync.setTraffic_traffic
#print axioms ShortGapUnifiedSync.toSNode_setTraffic
#print axioms ShortGapUnifiedSync.ofSNode_core
#print axioms ShortGapUnifiedSync.ofSNode_traffic
#print axioms ShortGapUnifiedSync.sync_ofSNode_iff
#print axioms ShortGapUnifiedSync.trafficCode_setTraffic
#print axioms ShortGapUnifiedSync.resyncNode_toSNode
#print axioms ShortGapUnifiedSync.resyncNode_sync
#print axioms ShortGapUnifiedSync.uRow4_sync
#print axioms ShortGapUnifiedSync.uRow4_toSNode
#print axioms ShortGapUnifiedSync.not_sync_ofSNode_of_nonempty
#print axioms ShortGapUnifiedSync.uRow_left_not_sync_of_nonempty
#print axioms ShortGapUnifiedSync.uRow_not_sync_preserving_of_witness
