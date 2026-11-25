import Leader.L4.BStarCopyRightLinkedCapture
import Leader.L4.BStarCopyRightRecoveryFinish
import Leader.L4.BStarCopyRightRecoveryPostAck
import Leader.L4.BStarCopyLaunchEntry
import Leader.L4.BStarCopyRightGeometryWord

namespace L4.BStarCopyRightRecoveryCanonical
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongEvents BStarLongCommand BStarLongTransport BStarLongPrep
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarCopyRightStrip BStarCopyRightReleaseClass BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarSeparatingRail BStarAcquireHistoryReturn BStarOwnerControlHistory
open BStarClearanceCommandFrame
open BStarSeparatorControl BStarResetMarkAdapter

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

open BStarCopyRightReleaseCapture BStarCopyRightLoadToInject BStarCopyRightDeposit
open BStarClearanceDataChart BStarCommitOperands BStarLongPublication BStarLongDoor
open BStarLongFixedRouting BStarGeneratedBandScan BStarClearanceSource
open BStarCaptureDoorHistory BStarLongLayout

open BStarCopyRightReleaseCursor BStarCopyRightActiveFold BStarCopyRightMixed BStarCopyRightReleaseOrder
open BStarCopyRightRetained BStarCopyRightMark BStarCopyMarkedLedger BStarCopyFenceSaturation
open BStarCopyRightGeometryWord BStarCopyRightReturn BStarCopyLaunchEntry

open BStarCopyRightRecovered BStarCopyRightRecoveryFinish BStarCopyRightFenceHold BStarCopyRightFence
open BStarCopyRightRecoveryPostAck BStarCopyRightLinkedCapture
open BStarH6Ordinal BStarNativeReceiptTape BStarLongPackets

/-- Actual returned COPY bytes from one recovered original attempt.
All local byte, vacancy, and gate premises are derived. The supplied
evidence is an authenticated division of the literal owner tape. -/
theorem recovered_right_ack_canonical {base origin preOrigin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a : Fin n) (seam tail : Nat) (strip : Strip B base a seam tail)
    (ownHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (width : tail+1=seam+r)
    (w8 middle tour : List (Fin n))
    (M : OwnMiddle hp base preOrigin (fun t=>S.getD t fall) len w8 middle)
    (Ppre : BusyOnly hp base (fun t=>S.getD t fall) len 10
      (play preOrigin (w8++middle)) (.out 0) tour (.out len))
    (fiberPre : ∀ q z,((w8++middle)++tour)=q++z →
      ∀ i,Layout B base i=Layout B (play preOrigin q) i)
    (cut whole : List (Fin n))
    (A : Acquisition hp preOrigin cut whole (endpoint (oldH6 B base) hh o 2).1 2)
    (common : ∃ v,whole=cut++v)
    (sameWhole : ∃ suffix,whole=((w8++middle)++tour)++suffix)
    (ackLead : List (Fin n)) (ack : Fin n)
    (birthBeforeAck : ∃ t,ackLead=A.lead++A.mark::t)
    (ack2 : ((capturedSelector 2).read (ring (play preOrigin ackLead) ack (S.getD 0 fall).1).long).toNat=
      (readSel ((play preOrigin A.lead) (endpoint (oldH6 B base) hh o 2).1).long).val)
    (layout : ∀ w,oldH6 B (play preOrigin (cut++w))=oldH6 B base)
    (auth : ∀ w e z, BStarBodyStageProvenance.BodyAuthority hp (play preOrigin (cut++w)) e z
      (endpoint (oldH6 B base) hh o 2).1)
    (start : List (Fin n))
    (entry : origin=ring (play preOrigin ackLead) ack)
    (sameStart : w8++middle=(ackLead++[ack])++start)
    (w8post : List (Fin n))
    (loadCut : w8=(ackLead++[ack])++w8post)
    (initPrefix : ∃ q,start=w8post++q)
    (old5 : pc (play preOrigin ackLead) (S.getD 0 fall).1=5)
    (G8post : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w8post (.busy 8 (.back 0)))
    (G10 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle start (.busy 10 (.out 0)))
    (P10 : BusyOnly hp base (fun t=>S.getD t fall) len 10
      (play origin start) (.out 0) tour (.out len))
    (root : Fin n) (dest : Dest B base root r)
    (join : addr a 0=addr root (r-1))
    (lead10 : List (Fin n)) (issue10 : Fin n)
    (preIssue : start=lead10++[issue10])
    (idle10 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead10 .idle)
    (startPC : pc origin (S.getD 0 fall).1≤6)
    (oldPC : pc (play origin lead10) (S.getD 0 fall).1=10)
    (w9 gap : List (Fin n)) (ack9 : Fin n)
    (enableCut : start=w9++ack9::gap)
    (G9 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w9 (.busy 9 (.back 0)))
    (event9 : Event hp (fun j=>S.getD j fall) len (play origin w9) ack9 (.busy 9 (.back 0)) .idle)
    (accepted9 : pc (ring (play origin w9) ack9) (S.getD 0 fall).1=10)
    (full : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle ((start)++tour) (.busy 10 (.out len)))
    (f : Payload) (F : project (fun j=>S.getD j fall) (play (play origin (start)) tour) len=.forward f)
    (clear : f.fault=0) (op : f.opcode.toNat=10)
    (rootAt : root=(S.getD len fall).1)
    (inside : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (back fence : List (Fin n)) (turn ack10 ack11 : Fin n) :
    let lead := (start)++tour
    let x := play origin lead
    let y := play (ring x turn) back
    let z := ring y ack10
    let wholeTape := (((lead++[turn])++back)++[ack10])++(fence++[ack11])
    Event hp (fun j=>S.getD j fall) len x turn (.busy 10 (.out len)) (.busy 10 (.back len)) →
    BusyOnly hp base (fun j=>S.getD j fall) len 10 (ring x turn) (.back len) back (.back 0) →
    Event hp (fun j=>S.getD j fall) len y ack10 (.busy 10 (.back 0)) .idle →
    Current hp base (fun j=>S.getD j fall) len z .idle →
    pc z (S.getD 0 fall).1=11 →
    GeneratedOwner hp base (fun j=>S.getD j fall) len z .idle fence (.busy 11 (.back 0)) →
    Hit hp base (fun j=>S.getD j fall) len (play z fence) ack11 11 →
    pc (ring (play z fence) ack11) (S.getD 0 fall).1=12 →
    GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle wholeTape .idle →
    (∀ u v,wholeTape=u++v → (∀ i,Layout B base i=Layout B (play origin u) i) ∧
      Band (play origin u) (S.getD 0 fall).1) →
    let digits := digitTable (play preOrigin A.lead) (endpoint (oldH6 B base) hh o 2).1 a seam
    let plan := planOf (fun i=>i-seam) seam tail
    (∀ i sh,Region root a r seam tail i sh →
      (readLane (Sheet.index sh) (play origin wholeTape i).long).mobile=.empty) ∧
    laneRead (rdRead (play origin wholeTape) root r) 0 r=plan.reverse.map (Digit9.data ∘ digits) := by
  intro lead x y z wholeTape turnE ret ackE idle11 pc11 G11 H11 pc12 all valid
  dsimp only
  let digits := digitTable (play preOrigin A.lead) (endpoint (oldH6 B base) hh o 2).1 a seam
  let plan := planOf (fun i=>i-seam) seam tail
  have validOut (u v : List (Fin n)) (E : ((start)++tour)=u++v) :=
    valid u (v++turn::back++[ack10]++(fence++[ack11])) (by
      simp only [wholeTape,lead,E,List.append_assoc,List.cons_append,List.nil_append])
  have replayStart : play preOrigin (w8++middle)=play origin start := by
    rw [sameStart,BStarResetSchedule.run_append,entry,BStarResetSchedule.run_append]
    rfl
  have aft (before rest : List (Fin n)) (E : w8=((ackLead++[ack])++before)++rest) :
      ∃ m, GeneratedOwner hp base (fun j=>S.getD j fall) len (ring (play preOrigin ackLead) ack)
        .idle before m ∧
        (∀ p q,before=p++q →
          let y := play preOrigin ((ackLead++[ack])++p)
          Band y (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B y i)) := by
    have W : w8post=before++rest := by
      apply List.append_cancel_left (as:=ackLead++[ack])
      exact loadCut.symm.trans (E.trans (List.append_assoc _ _ _))
    obtain ⟨m,G,_⟩ := BStarGeneratedTapeCuts.split hp before rest (W ▸ G8post)
    refine ⟨m,entry ▸ G,?_⟩
    intro p q Q
    obtain ⟨u,U⟩ := initPrefix
    have A : ((start)++tour)=p++((q++rest++u)++tour) := by
      rw [U,W,Q]; simp only [List.append_assoc]
    have V := validOut p ((q++rest++u)++tour) A
    have replay : play preOrigin ((ackLead++[ack])++p)=play origin p := by
      rw [BStarResetSchedule.run_append,entry,BStarResetSchedule.run_append]; rfl
    dsimp only
    rw [replay]
    exact ⟨V.2,V.1⟩
  have cap := all_linked_release_bytes hp chart sep a seam tail strip ownHead width w8 middle tour M Ppre
    fiberPre cut whole A common sameWhole ackLead ack birthBeforeAck ack2
    ⟨w8post,loadCut.trans (by simp only [List.append_assoc,List.singleton_append])⟩ old5 aft layout auth
  rw [replayStart] at cap
  obtain ⟨t,lab,pend,ordered,old,mobile⟩ := post_ack_outward hp chart sep a seam tail strip ownHead width
    digits start tour G10 P10 cap root dest join lead10 issue10 preIssue idle10 startPC oldPC w9 gap ack9 enableCut
    G9 event9 accepted9 full validOut f F clear op
  have tape : lead=w9++ack9::(gap++tour) := by
    change (start)++tour=_
    rw [enableCut]
    simp only [List.append_assoc,List.cons_append]
  have newWhole : wholeTape=(w9++ack9::((gap++tour)++turn::back++[ack10]))++(fence++[ack11]) := by
    simp only [wholeTape,tape,List.append_assoc,List.cons_append,List.nil_append]
  have size : plan.length=r := by simp [planOf,plan]; omega
  have O : RetainedMatches digits x root r t := by
    rw [show x=play (play origin (start)) tour from BStarResetSchedule.run_append _ _ _ _]
    exact old
  have U : MobileMatches digits x a seam tail lab := by
    rw [show x=play (play origin (start)) tour from BStarResetSchedule.run_append _ _ _ _]
    exact mobile
  have res := finish_recovered hp digits chart sep root a r seam tail dest strip join ownHead rootAt inside notShort
    w9 (gap++tour) back fence ack9 turn ack10 ack11 G9 event9 accepted9
    (tape ▸ full) (tape ▸ turnE) (tape ▸ ret) (tape ▸ ackE) (tape ▸ idle11) (tape ▸ pc11)
    (tape ▸ G11) (tape ▸ H11) (tape ▸ pc12)
    (newWhole ▸ all) (fun u v E => valid u v (newWhole.trans E))
    plan t lab size pend ordered (tape ▸ O) (tape ▸ U)
  rw [newWhole]
  exact res

#print axioms recovered_right_ack_canonical
end L4.BStarCopyRightRecoveryCanonical
