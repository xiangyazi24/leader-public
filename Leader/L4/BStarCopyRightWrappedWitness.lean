import Leader.L4.BStarCopyRightWrappedAttempt
import Leader.L4.BStarCopyRightActualWitness
import Leader.L4.BStarCopyRightAttemptAuthenticated
import Leader.L4.BStarAttemptSafety
import Leader.L4.BStarPostCutAttempt
import Leader.L4.BStarOwnedGrantLife
import Leader.L4.BStarAcquireAckWindow

namespace L4.BStarCopyRightWrappedWitness
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongTransport
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedTapeCuts BStarLongDoor BStarLongCommand
open BStarClearanceSource BStarOwnerLaunchOrigin BStarSeparatingRail BStarLongLayout
open BStarAcquireAckWindow BStarGrantBirth BStarGrantWriterHistory
open BStarNativeReceiptTape (Hit)
open BStarOwnedGrantLife BStarAttemptSafety BStarPostCutAttempt BStarLongGrant
open BStarAcquireLatch BStarAcquireReadout BStarWriterTransferWindow BStarCommitTailScan

set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

open BStarCopyRightActualWitness (selected_right_acquisition)
open BStarCommitOperands BStarCopyRightStrip
open BStarCopyRightRetained BStarClearanceDataChart BStarH6Ordinal BStarCustodyCuts
open BStarCopyRightFence BStarCopyRightFenceHold BStarCopyRightMixed BStarCopyRightReleaseCapture
open BStarCopyFenceSaturation BStarLongPackets

/-- Right retained readout from the *same* supplied witness of
actual_attempt. No acquisition, matching selector, post-ACK band,
or body write/read authority is supplied by this interface. -/
theorem packed_right_from_actual_witness {base global : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q global) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    {u v tail pre reset w flight : List (Fin n)}
    (facts : CutFacts hp base global u v)
    (door center : Fin n) (k : Nat) (K : k≤len)
    (loc : S.getD k fall=(center,1))
    (ownCenter : commandOwner (oldH6 B base) center 1=o.val)
    (ancestry : (u++v)++tail=(pre++reset)++w++door::flight)
    (below : u.length≤pre.length)
    (root a : Fin n) (seam last : Nat)
    (dest : Dest B base root r) (strip : BStarCopyRightWrappedGeometry.WrappedStrip B base a seam last)
    (join : addr a 0=addr root (r-1))
    (ownHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (width : last+1=seam+r) (rootAt : root=(S.getD len fall).1)
    (inside : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1) :
    let origin := run global (pre++reset)
    let slot := fun j=>S.getD j fall
    GeneratedOwner hp base slot len origin .idle w .idle →
    AttemptPrefix hp base origin slot len w →
    Launch (run origin w (slot 0).1).long (step (run origin w) door (slot 0).1).long →
    pc (run origin w) (slot 0).1=411 →
    BusyOnly hp base slot len commitOp (step (run origin w) door) (.out 0) flight (.out k) →
    ∃ (Ac : Acquisition hp origin [] w (endpoint (oldH6 B base) hh o 2).1 2)
      (before after : List (Fin n)),
      w=before++after ∧
      (∃ preAck e,before=preAck++[e] ∧ Hit hp base slot len (run origin preAck) e 11) ∧
     
      BStarCopySetupFinalCut.Floor hp (slot 0).1 (run origin before) after ∧
      pc (run origin before) (slot 0).1=12 ∧
      (∀ i sh,Region root a r seam last i sh →
        (readLane (Sheet.index sh) (run origin before i).long).mobile=.empty) ∧
      laneRead (rdRead (run origin before) root r) 0 r=
        (planOf (fun i=>i-seam) seam last).reverse.map
          (Digit9.data ∘ digitTable (run origin Ac.lead) (endpoint (oldH6 B base) hh o 2).1 a seam) := by
  intro origin slot G A launch op Busy
  have keep (x : X) (w : List (Fin n)) (J : Q x) : Q (run x w) := by
    induction w generalizing x with
    | nil => exact J
    | cons e w ih => exact ih _ (closed x e J)
  have originOK : Q origin := keep global (pre++reset) I
  obtain ⟨_,_,Ac,_,_,_⟩ := selected_right_acquisition hp C Q originOK fiber closed sep
    w flight door center k K loc ownCenter G A launch op Busy
  have W : (u++v)++tail=(pre++reset)++(w++door::flight) :=
    ancestry.trans (List.append_assoc _ _ _)
  obtain ⟨before,after,eq,hit,floor,pc12,mobile,read⟩ :=
    BStarCopyRightWrappedAttempt.packed_right_of_attempt_authenticated hp C sep Q originOK fiber closed A Ac ⟨w,rfl⟩
      facts rfl W below root a seam last dest strip join ownHead width rootAt inside notShort
  exact ⟨Ac,before,after,eq,hit,floor,pc12,mobile,read⟩

theorem packed_right_from_actual_chart {base global : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q global) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    {u v tail pre reset w flight : List (Fin n)}
    (facts : CutFacts hp base global u v)
    (door center : Fin n) (k : Nat) (K : k≤len)
    (loc : S.getD k fall=(center,1))
    (ownCenter : commandOwner (oldH6 B base) center 1=o.val)
    (ancestry : (u++v)++tail=(pre++reset)++w++door::flight)
    (below : u.length≤pre.length)
    (hr : 0<r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1) :
    let origin := run global (pre++reset)
    let slot := fun j=>S.getD j fall
    GeneratedOwner hp base slot len origin .idle w .idle →
    AttemptPrefix hp base origin slot len w →
    Launch (run origin w (slot 0).1).long (step (run origin w) door (slot 0).1).long →
    pc (run origin w) (slot 0).1=411 →
    BusyOnly hp base slot len commitOp (step (run origin w) door) (.out 0) flight (.out k) →
    let root := (S.getD len fall).1
    ∃ (a : Fin n) (seam last : Nat), Dest B base root r ∧
      BStarCopyRightWrappedGeometry.WrappedStrip B base a seam last ∧
      addr a 0=addr root (r-1) ∧ last+1=seam+r ∧
      ∃ (Ac : Acquisition hp origin [] w (endpoint (oldH6 B base) hh o 2).1 2)
      (before after : List (Fin n)),
      w=before++after ∧
      (∃ preAck e,before=preAck++[e] ∧ Hit hp base slot len (run origin preAck) e 11) ∧
     
      BStarCopySetupFinalCut.Floor hp (slot 0).1 (run origin before) after ∧
      pc (run origin before) (slot 0).1=12 ∧
      (∀ i sh,Region root a r seam last i sh →
        (readLane (Sheet.index sh) (run origin before i).long).mobile=.empty) ∧
      laneRead (rdRead (run origin before) root r) 0 r=
        (planOf (fun i=>i-seam) seam last).reverse.map
          (Digit9.data ∘ digitTable (run origin Ac.lead) (endpoint (oldH6 B base) hh o 2).1 a seam):= by
  intro origin slot G A launch op Busy
  obtain ⟨a,seam,last,D,U,join,width,own⟩ :=
    BStarCopyRightWrappedGeometry.wrapped_of_chart hp C hr flags notShort
  refine ⟨a,seam,last,D,U,join,width,?_⟩
  exact packed_right_from_actual_witness hp C sep Q I fiber closed facts door center k K loc ownCenter
    ancestry below _ a seam last D U join own width rfl (fun i => (flags i).1) notShort G A launch op Busy

#print axioms packed_right_from_actual_chart

#print axioms packed_right_from_actual_witness
end L4.BStarCopyRightWrappedWitness
