import Leader.L4.BStarCopyRightWrappedFenceHold
import Leader.L4.BStarCopyRightWrappedReturn
import Leader.L4.BStarCopyRightRecovered
import Leader.L4.BStarCopyRightFenceHold

namespace L4.BStarCopyRightWrappedFinish
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongToken BStarLongPackets BStarLongDoor BStarLongFixedRouting
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarH6Ordinal
open BStarGeneratedOwner BStarGeneratedBandScan BStarOwnerLaunchOrigin BStarSeparatingRail BStarNativeReceiptTape
open BStarCopyRightStrip BStarCopyRightMark BStarCopyRightRetained BStarCopyRightGeometryWord
open BStarCopyRightReturn BStarCopyRightFence BStarCopyRightFenceHold
open BStarCopyFenceSaturation BStarCopyMarkedLedger
open BStarClearanceDataChart

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

/-- Compose the terminal outward ledger with the actual return, FENCE
and ACK. The same accepted ENABLE9 supplies every gate needed here. -/
theorem finish_recovered {Tag : Type} (digits : Tag→BitVec 36)
    {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (root a : Fin n) (width seam tail : Nat)
    (dest : Dest B base root width) (strip : BStarCopyRightWrappedGeometry.WrappedStrip B base a seam tail)
    (join : addr a 0=addr root (width-1))
    (own : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (rootAt : root=(S.getD len fall).1)
    (inside : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    (w9 gap back w11 : List (Fin n)) (ack9 turn ack10 ack11 : Fin n)
    (G9 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w9 (.busy 9 (.back 0)))
    (event9 : Event hp (fun j=>S.getD j fall) len (play origin w9) ack9 (.busy 9 (.back 0)) .idle)
    (accepted9 : pc (ring (play origin w9) ack9) (S.getD 0 fall).1=10) :
    let lead := w9++ack9::gap
    let x := play origin lead
    let y := play (ring x turn) back
    let z := ring y ack10
    let bridge := gap++turn::back++[ack10]
    let whole := (w9++ack9::bridge)++(w11++[ack11])
    GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy 10 (.out len)) →
    Event hp (fun j=>S.getD j fall) len x turn (.busy 10 (.out len)) (.busy 10 (.back len)) →
    BusyOnly hp base (fun j=>S.getD j fall) len 10 (ring x turn) (.back len) back (.back 0) →
    Event hp (fun j=>S.getD j fall) len y ack10 (.busy 10 (.back 0)) .idle →
    Current hp base (fun j=>S.getD j fall) len z .idle →
    pc z (S.getD 0 fall).1=11 →
    GeneratedOwner hp base (fun j=>S.getD j fall) len z .idle w11 (.busy 11 (.back 0)) →
    Hit hp base (fun j=>S.getD j fall) len (play z w11) ack11 11 →
    pc (ring (play z w11) ack11) (S.getD 0 fall).1=12 →
    GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle whole .idle →
    (∀ u v,whole=u++v → (∀ i,Layout B base i=Layout B (play origin u) i) ∧ Band (play origin u) (S.getD 0 fall).1) →
    ∀ (plan : List Tag) (s : Ledger Tag) (labels : Nat→Option Tag),
      plan.length=width → s.release.pending=[] → OrderedPrefix plan s (stripWord tail labels) →
      RetainedMatches digits x root width s → MobileMatches digits x a seam tail labels →
      (∀ i sh,Region root a width seam tail i sh →
        (readLane (Sheet.index sh) (play origin whole i).long).mobile=.empty) ∧
      laneRead (rdRead (play origin whole) root width) 0 width=plan.reverse.map (Digit9.data ∘ digits) := by
  intro lead x y z bridge whole start turnEvent ret ackEvent idle11 pc11 G11 H11 pc12 all valid
  intro plan s labels size pend P old mobile
  have shape (w : List (Fin n)) :
      w9++ack9::(gap++w)=lead++w := by simp only [lead,List.append_assoc,List.cons_append]
  have wholeEq : whole=w9++ack9::(bridge++(w11++[ack11])) := by
    simp only [whole,List.append_assoc,List.cons_append]
  have gate := BStarCopyRightWrappedGates.right_gates_word hp chart sep w9 (bridge++(w11++[ack11])) ack9 .idle G9 event9 accepted9
    (wholeEq ▸ all) (fun u v E => valid u v (wholeEq.trans E)) root a width seam tail dest strip join own
  have before (pre rest : List (Fin n)) (E : back=pre++rest) :
      BStarCopyRightWrappedGates.Gates hp base (play (ring x turn) pre) root a width seam tail := by
    have S : bridge++(w11++[ack11])=(gap++turn::pre)++(rest++[ack10]++(w11++[ack11])) := by
      simp only [bridge,E,List.append_assoc,List.cons_append]
    have H := gate (gap++turn::pre) (rest++[ack10]++(w11++[ack11])) S
    rw [shape (turn::pre),BStarResetSchedule.run_append] at H
    exact H
  have atTurn : BStarCopyRightWrappedGates.Gates hp base x root a width seam tail := by
    have H := gate gap ((turn::back++[ack10])++(w11++[ack11])) (by
      simp only [bridge,List.append_assoc,List.cons_append])
    exact H
  have seat : ((lead++[turn])++back)++[ack10]=w9++ack9::bridge := by
    simp only [lead,bridge,List.append_assoc,List.cons_append,List.nil_append]
  have at11 : play origin (w9++ack9::bridge)=z := by
    rw [←seat,BStarResetSchedule.run_append,BStarResetSchedule.run_append,BStarResetSchedule.run_append]
    rfl
  obtain ⟨_,_,t,lab,_,Q,R,U⟩ := BStarCopyRightWrappedReturn.through_turn_return_ack hp digits chart sep root a width seam tail dest strip join own
    lead back [] turn ack10 start turnEvent ret ackEvent idle11 pc11 atTurn
    (before back [] (List.append_nil _).symm) (fun pre e v E => before pre (e::v) E)
    (fun pre e v E => by have J := congrArg List.length E; simp at J)
    plan size s labels pend P old mobile
  rw [List.append_nil,seat,at11] at R U
  obtain ⟨_,_,_,_,_,_,_,frame,read⟩ := BStarCopyRightWrappedFenceHold.hold_through_ack hp digits chart dest.pos inside notShort root a seam tail
    rootAt join sep w11 ack11 w9 bridge ack9 G9 event9 accepted9 all valid (by rw [at11,pc11]; decide)
    dest strip own z at11.symm G11 H11 plan size t lab Q R U pc12
  have endpoint : play origin whole=play z (w11++[ack11]) := by
    change play origin ((w9++ack9::bridge)++(w11++[ack11]))=_
    rw [BStarResetSchedule.run_append,at11]
  rw [endpoint]
  exact ⟨fun i sh I => (frame i sh I).1,read⟩

#print axioms finish_recovered
end L4.BStarCopyRightWrappedFinish
