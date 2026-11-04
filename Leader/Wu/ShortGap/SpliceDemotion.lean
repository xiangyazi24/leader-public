import Leader.Wu.ShortGap.SpliceCommitCorrected
import Leader.Wu.ShortGap.SpliceFusedRow

namespace ShortGapSpliceDemotion

open ShortGapLiteralGapRows
open ShortGapCaptureReservation
open ShortGapCaptureCommitRows
open ShortGapSpliceCommit
open ShortGapSpliceCommitCorrected
open ShortGapSpliceFusedRow

set_option autoImplicit false

/-!
# Demotion of a spent splice bridge

A spent former-B bridge is already leaderless and drained, carries no commit
carrier, payload, or retirement witness, and has no pending fresh-lane flush.
Demotion erases only its raw bridge image and splice control, exposing the
ordinary empty slot used by the next fresh declaration.
-/

def SpentBridge (b : SNode) : Prop :=
  b.core.leader = false ∧
  b.splice = .drained ∧
  b.core.carrier = .none ∧
  b.payload = none ∧
  b.witness = .none ∧
  b.flush = .none

/-- Retire former B to the ordinary empty interior slot.  The leader bit and
all commit/splice metadata other than `splice` are framed. -/
def demote (b : SNode) : SNode :=
  { b with
    core := { b.core with raw := emptyRaw }
    splice := .inactive }

/-- A spent bridge becomes exactly an empty splice-lane endpoint. -/
theorem demote_empty {b : SNode} (h : SpentBridge b) :
    SEmpty (demote b) := by
  rcases h with ⟨_, _, hcarrier, _, _, _⟩
  exact ⟨rfl, hcarrier⟩

/-- After demoting former B, an already in-flight fresh declaration can move
into that now-empty right endpoint. -/
theorem fresh_lane_open_after_demotion
    (F : SFrameCorrected) (sp : SpliceCtl)
    (h : SpentBridge (bN F sp)) :
    FreshForward declNode (demote (bN F sp)) := by
  rcases h with ⟨_, _, hcarrier, _, _, hflush⟩
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact ⟨rfl, hcarrier⟩
  · exact hflush

/-- Length one: after demotion, the armed source can launch directly into the
now-empty former-B endpoint. -/
theorem fresh_launch_open_after_demotion
    (F : SFrameCorrected) (sp : SpliceCtl)
    (h : SpentBridge (bN F sp)) :
    FreshLaunch
      (sRootAt .toSend F.aCcw F.aInc F.aCtl F.aLease .armed .unflushed)
      (demote (bN F sp)) := by
  rcases h with ⟨_, _, hcarrier, _, _, hflush⟩
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact ⟨rfl, hcarrier⟩
  · exact hflush

/--
A spent right endpoint is constructor-disjoint from every old splice-tail row
that can read that endpoint.  The bridged rows contradict `splice = drained`;
the backward/deposit rows contradict the spent `witness = none`; adoption
contradicts `payload = none`.
-/
theorem demotion_disjoint_from_tail (a b : SNode) (h : SpentBridge b) :
    (¬ RetireLaunch a b) ∧
    (¬ RetireDeposit a b) ∧
    (¬ RetireBackward a b) ∧
    (¬ RetireFused a b) ∧
    (¬ AdoptDeposit a b) := by
  rcases h with ⟨_, hsplice, _, hpayload, hwitness, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hT
    have hb : b.splice = .bridged := hT.2.2.1
    have hbad : SpliceCtl.drained = SpliceCtl.bridged := hsplice.symm.trans hb
    cases hbad
  · intro hT
    have hb : b.witness = .token := hT.2.2
    have hbad : RetireWitness.none = RetireWitness.token := hwitness.symm.trans hb
    cases hbad
  · intro hT
    have hb : b.witness = .token := hT.2.2.2
    have hbad : RetireWitness.none = RetireWitness.token := hwitness.symm.trans hb
    cases hbad
  · intro hT
    have hb : b.splice = .bridged := hT.2.2.1
    have hbad : SpliceCtl.drained = SpliceCtl.bridged := hsplice.symm.trans hb
    cases hbad
  · intro hT
    exact hT.2.1 hpayload

/-- Demotion writes only `core.raw` and `splice`; all other stored fields are
framed.  The first two conjuncts record the two intentional writes. -/
theorem demote_frames (b : SNode) :
    (demote b).core.raw = emptyRaw ∧
    (demote b).splice = .inactive ∧
    (demote b).core.leader = b.core.leader ∧
    (demote b).core.carrier = b.core.carrier ∧
    (demote b).core.outgoing = b.core.outgoing ∧
    (demote b).core.incoming = b.core.incoming ∧
    (demote b).bridge = b.bridge ∧
    (demote b).payload = b.payload ∧
    (demote b).witness = b.witness ∧
    (demote b).flush = b.flush := by
  simp [demote]

#print axioms demote_empty
#print axioms fresh_lane_open_after_demotion
#print axioms fresh_launch_open_after_demotion
#print axioms demotion_disjoint_from_tail
#print axioms demote_frames

end ShortGapSpliceDemotion
