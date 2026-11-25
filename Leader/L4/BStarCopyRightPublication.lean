import Leader.L4.BStarCopyRightChartGeometry

namespace L4.BStarCopyRightPublication
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

/-- Final right COPY value for the same publication that selected the
recovery witness. The current physical strip is adequate when there
are two distinct H6 sites and the actual width is at least two. -/
theorem before_publication {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i, Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (ring y e))
    (mark center : Fin n)
    (pub : ¬NoPublication hp (play initial ((u++v)++tail)) mark center)
    (wide : 2≤r)
    (two : ∃ i j,i≠j ∧ oldH6 B base i=true ∧ oldH6 B base j=true)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1) :
    ∃ (o : Owners (oldH6 B base)) (pre reset w before after rest : List (Fin n))
      (root source a : Fin n) (seam last : Nat),
      (u++v)++tail=(pre++reset)++(w++rest) ∧ w=before++after ∧
      let origin := play initial (pre++reset)
      ∃ Ac : Acquisition hp origin [] w (endpoint (oldH6 B base) hh o 2).1 2,
        (∃ (S : List (Pos n)) (len : Nat) (fall : Pos n) (preAck : List (Fin n)) (e : Fin n),
          Chart hp base hh o S len fall ∧ source=(S.getD 0 fall).1 ∧ before=preAck++[e] ∧
          Hit hp base (fun j=>S.getD j fall) len (play origin preAck) e 11) ∧
        BStarCopySetupFinalCut.Floor hp source (play origin before) after ∧
        pc (play origin before) source=12 ∧
        (∀ i sh,Region root a r seam last i sh →
          (readLane (Sheet.index sh) (play origin before i).long).mobile=.empty) ∧
        laneRead (rdRead (play origin before) root r) 0 r=
          (planOf (fun i=>i-seam) seam last).reverse.map
            (Digit9.data ∘ digitTable (play origin Ac.lead) (endpoint (oldH6 B base) hh o 2).1 a seam) := by
  obtain ⟨o,S,len,fall,pre,reset,w,flight,door,k,_,_,W,below,_,_,own,C,K,loc,_,launch,op,_,_,_,G,A,F,_,_⟩ :=
    actual_attempt hp u v tail cuts hh sep Q I fiber closed mark center pub
  let root := (S.getD len fall).1
  have other : ∃ i,i≠root ∧ oldH6 B base i=true := by
    obtain ⟨i,j,ne,Hi,Hj⟩ := two
    by_cases E : i=root
    · exact ⟨j,fun K => ne (E.trans K.symm),Hj⟩
    · exact ⟨i,E,Hi⟩
  obtain ⟨a,seam,last,dest,strip,join,size,ownHead⟩ :=
    of_chart hp C wide flags notShort other
  have pc411 : pc (play (play initial (pre++reset)) w) (S.getD 0 fall).1=411 := op
  obtain ⟨Ac,before,after,P,hit,floor,pc12,mobile,read⟩ :=
    packed_right_from_actual_witness hp C sep Q I fiber closed cuts door center k K loc own W below
      root a seam last dest strip join ownHead size rfl (fun i=>(flags i).1) notShort
      G A launch pc411 F
  obtain ⟨preAck,e,eq,H⟩ := hit
  exact ⟨o,pre,reset,w,before,after,door::flight,root,(S.getD 0 fall).1,a,seam,last,
    W.trans (List.append_assoc _ _ _),P,Ac,⟨S,len,fall,preAck,e,C,rfl,eq,H⟩,floor,pc12,mobile,read⟩

end L4.BStarCopyRightPublication
