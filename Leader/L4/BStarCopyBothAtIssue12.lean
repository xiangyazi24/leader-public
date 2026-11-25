import Leader.L4.BStarCopyRightWrappedWitness
import Leader.L4.BStarCopyRightPublication
import Leader.L4.BStarCopyLeftActualWitness
import Leader.L4.BStarCopyLastCut

namespace L4.BStarCopyBothAtIssue12
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarLongFixedRouting BStarCustodyCuts BStarPublicationBirth BStarGrantWriterHistory
open BStarPostCutAttempt BStarGeneratedBandScan BStarCommitOperands BStarLongPackets
open BStarCopyRightActualWitness BStarCopyRightChartGeometry BStarCopyRightStrip
open BStarCopyRightFence BStarCopyRightFenceHold BStarCopyRightMixed BStarCopyRightReleaseCapture
open BStarCopyFenceSaturation
open BStarNativeReceiptTape (Hit)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

open BStarCopyLeftActualWitness
open BStarCopyLeftFence (ldRead)
open BStarCopyLeftPending (pending)

/-- Both retained COPY inputs at one actual final ACK11 cut of the
same recovered publication attempt, including wrapped right geometry. -/
theorem before_publication {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (ring y e))
    (mark center : Fin n)
    (pub : ¬NoPublication hp (play initial ((u++v)++tail)) mark center)
    (hr : 0<r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1) :
    ∃ (o : Owners (oldH6 B base)) (S : List (Pos n)) (len : Nat) (fall : Pos n)
      (pre reset w before after rest : List (Fin n))
      (root a : Fin n) (leftSeam seam last : Nat),
      (u++v)++tail=(pre++reset)++(w++rest) ∧ w=before++after ∧
      Chart hp base hh o S len fall ∧
      let origin := play initial (pre++reset)
      let source := (S.getD 0 fall).1
      let y := play origin before
      (∃ preAck e,before=preAck++[e] ∧ Hit hp base (fun j=>S.getD j fall) len (play origin preAck) e 11) ∧
      pc y source=12 ∧
      ∃ (AcL : Acquisition hp origin [] w (endpoint (oldH6 B base) hh o 0).1 0)
        (AcR : Acquisition hp origin [] w (endpoint (oldH6 B base) hh o 2).1 2),
        laneRead (ldRead y (addr source leftSeam)) 0 r=
          (pending id r).reverse.map (Digit9.data ∘
            BStarCopyLeftReleaseCapture.digitTable (play origin AcL.lead) (endpoint (oldH6 B base) hh o 0).1 source) ∧
        laneRead (rdRead y root r) 0 r=
          (planOf (fun i=>i-seam) seam last).reverse.map (Digit9.data ∘
            BStarCopyRightReleaseCapture.digitTable (play origin AcR.lead) (endpoint (oldH6 B base) hh o 2).1 a seam) := by
  obtain ⟨o,S,len,fall,pre,reset,w,flight,door,k,_,_,W,below,_,_,own,C,K,loc,_,launch,op,_,_,_,G,A,F,_,_⟩ :=
    actual_attempt hp u v tail cuts hh sep Q I fiber closed mark center pub
  let root := (S.getD len fall).1
  have pc411 : pc (play (play initial (pre++reset)) w) (S.getD 0 fall).1=411 := op
  obtain ⟨AcL,leftSeam,bl,al,_,WL,⟨pl,el,EL,HL⟩,floorL,pc12,_,readL⟩ :=
    packed_left_from_actual_witness hp C sep Q I fiber closed cuts door center k K loc own W below
      hr flags notShort G A launch pc411 F
  obtain ⟨a,seam,last,_,_,_,_,AcR,br,ar,WR,⟨pr,er,ER,HR⟩,floorR,_,_,readR⟩ :=
    BStarCopyRightWrappedWitness.packed_right_from_actual_chart hp C sep Q I fiber closed cuts door center k K loc own W below
      hr flags notShort G A launch pc411 F
  have exactL : w=(pl++[el])++al := EL ▸ WL
  have exactR : w=(pr++[er])++ar := ER ▸ WR
  have fl := EL ▸ floorL
  have fr := ER ▸ floorR
  obtain ⟨same,edge,_⟩ := BStarCopyLastCut.unique hp (S.getD 0 fall).1 w pl pr al ar el er
    exactL exactR HL.2.2.1 HR.2.2.1 fl fr
  have one : br=bl := by rw [ER,EL,same,edge]
  rw [one] at readR
  exact ⟨o,S,len,fall,pre,reset,w,bl,al,door::flight,root,a,leftSeam,seam,last,
    W.trans (List.append_assoc _ _ _),WL,C,⟨pl,el,EL,HL⟩,pc12,AcL,AcR,readL,readR⟩

end L4.BStarCopyBothAtIssue12
