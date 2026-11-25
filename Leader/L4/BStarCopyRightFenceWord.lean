import Leader.L4.BStarCopyRightFence

namespace L4.BStarCopyRightFenceWord
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets BStarLongWork
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarCopyRightStrip (addr addr_next)
open BStarCopyRightStrip BStarCopyRightMark BStarCopyRightRetained BStarCopyRightDataSweep
open BStarCopyRightReadyWord
open BStarCopyMarkedLedger BStarCopyFenceSaturation BStarCopyFIFO BStarSeparatingRail
open BStarFenceReceiverChart BStarClearanceDataChart BStarNativeReceiptTape

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

open BStarCopyRightFence BStarCopyGateAuthority BStarCopyAttemptBand BStarLongFixedRouting
open BStarGeneratedBandScan BStarLongDoor

theorem accepted_right_word {Tag : Type} (digits : Tag→BitVec 36)
    {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {width : Nat} (hw : 0<width)
    (inside : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1)
    (root a : Fin n) (seam tail : Nat) (rootAt : root=(S.getD len fall).1)
    (join : addr a 0=addr root (width-1))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (ack : Fin n)
    (w9 bridge : List (Fin n)) (ack9 : Fin n)
    (G9 : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w9 (.busy 9 (.back 0)))
    (event : Event hp (fun j=>S.getD j fall) len (play origin w9) ack9 (.busy 9 (.back 0)) .idle)
    (accepted : (ctrlOp.read (ring (play origin w9) ack9 (S.getD 0 fall).1).long).toNat=10)
    (hist : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle ((w9++ack9::bridge)++w)
      (.busy 11 (.back 0)))
    (valid : ∀ u v, ((w9++ack9::bridge)++w)=u++v →
      (∀ j, Layout B base j=Layout B (play origin u) j) ∧ Band (play origin u) (S.getD 0 fall).1)
    (late : 11≤pc (play origin (w9++ack9::bridge)) (S.getD 0 fall).1)
    (dest : Dest B base root width) (strip : Strip B base a seam tail)
    (ownHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (x : X) (xEq : x=play origin (w9++ack9::bridge))
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy 11 (.back 0)))
    (H : Hit hp base (fun j=>S.getD j fall) len (play x w) ack 11)
    (plan : List Tag) (size : plan.length=width) (s : Ledger Tag) (label : Nat→Option Tag)
    (P : OrderedPrefix plan s (stripWord tail label))
    (old : RetainedMatches digits x root width s)
    (mobile : MobileMatches digits x a seam tail label)
 :
    ∃ (pre gap back : List (Fin n)) (mark turn : Fin n) (t : Ledger Tag) (post : Nat→Option Tag),
      w=pre++mark::(gap++turn::back) ∧
      let y := play x ((pre++[mark])++gap)
      let read := rdRead y root width
      (∀ j<width,(read j).mobile=.empty) ∧
      laneRead read 0 width=plan.reverse.map (Digit9.data ∘ digits) ∧
      RetainedMatches digits y root width t ∧
      MobileMatches digits y a seam tail post ∧
      stripWord tail post=[] ∧ t.release.pending=[] := by
  have ready := right_ready_word hp chart sep w9 bridge w ack9 (.busy 11 (.back 0))
    G9 event accepted hist valid late root a width seam tail dest strip join ownHead
  rw [←xEq] at ready
  exact accepted_right hp digits chart hw inside notShort root a seam tail rootAt join sep w ack
    T H plan size s label P old mobile ready

end L4.BStarCopyRightFenceWord
