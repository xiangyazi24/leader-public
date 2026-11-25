import Leader.L4.BStarCopyLeftFenceHold
import Leader.L4.BStarCopyRightWrappedFenceHold
import Leader.L4.BStarCopyLeftReadyWord

namespace L4.BStarNativeCopyTransport
open AllSizeProtocol BStarTrace BStarLongWork BStarLongDoor BStarLongPackets BStarLongClaims
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarLongFixedRouting BStarGeneratedBandScan BStarClearanceDataChart
open BStarCopyRightStrip BStarCopyFenceSaturation
open BStarCopyRightRetained (Dest)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- On the one literal generated word, an accepted ENABLE9 and an already
drained ACK11 region keep all significant LD and RD lanes unchanged at
every subsequent cut in the compiler band. This frames the entire typed
lane, not merely the eventual retained payload. -/
theorem both_follow_on_tape {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w9 bridge data : List (Fin n)) (ack9 : Fin n) (endMode : Mode)
    (G9 : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w9 (.busy 9 (.back 0)))
    (event : Event hp (fun j=>S.getD j fall) len (play x w9) ack9 (.busy 9 (.back 0)) .idle)
    (accepted : (ctrlOp.read (step (play x w9) ack9 (S.getD 0 fall).1).long).toNat=10)
    (hist : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle ((w9++ack9::bridge)++data) endMode)
    (valid : ∀ u v, ((w9++ack9::bridge)++data)=u++v →
      (∀ j, Layout B base j=Layout B (play x u) j) ∧ Band (play x u) (S.getD 0 fall).1)
    (late : 11≤pc (play x (w9++ack9::bridge)) (S.getD 0 fall).1)
    (root source rightA : Fin n) (leftSeam rightSeam last : Nat)
    (left : BStarCopyLeftStrip.Strip B base source leftSeam r)
    (sourceAt : source=(S.getD 0 fall).1)
    (leftCenter : addr source leftSeam=root)
    (dest : Dest B base root r)
    (right : BStarCopyRightWrappedGeometry.WrappedStrip B base rightA rightSeam last)
    (join : addr rightA 0=addr root (r-1))
    (ownHead : dataOwner (oldH6 B base) (addr rightA 0) (rail rightSeam 0)=o.val)
    (drainL : ∀ i sh,BStarCopyLeftFenceHold.Region source leftSeam r i sh →
      (readLane (Sheet.index sh) (play x (w9++ack9::bridge) i).long).mobile=.empty)
    (drainR : ∀ i sh,BStarCopyRightWrappedFenceHold.Region root rightA r rightSeam last i sh →
      (readLane (Sheet.index sh) (play x (w9++ack9::bridge) i).long).mobile=.empty)
    (u v : List (Fin n)) (split : data=u++v) (j : Fin r) :
    let d := addr root j.val
    let entry := play x (w9++ack9::bridge)
    readLane 1 (play entry u d).long=readLane 1 (entry d).long ∧
    readLane 3 (play entry u d).long=readLane 3 (entry d).long := by
  let entry := play x (w9++ack9::bridge)
  have L := BStarCopyLeftReadyWord.left_ready_word hp chart sep w9 bridge data ack9 endMode
    G9 event accepted hist valid late source leftSeam r left sourceAt
  have R := BStarCopyRightWrappedReadyWord.right_ready_word hp chart sep w9 bridge data ack9 endMode
    G9 event accepted hist valid late root rightA r rightSeam last dest right join ownHead
  have hL := drained_word_frame hp (BStarCopyLeftFenceHold.Region source leftSeam r) entry u sep
    drainL (fun a e b E => BStarCopyLeftFenceHold.ready_frozen hp (play entry a) source e leftSeam r
      (L a e (b++v) (by rw [split,E,List.append_assoc]; rfl)))
  have hR := drained_word_frame hp (BStarCopyRightWrappedFenceHold.Region root rightA r rightSeam last) entry u sep
    drainR (fun a e b E => BStarCopyRightWrappedFenceHold.ready_frozen hp (play entry a) root rightA e
      r rightSeam last join (R a e (b++v) (by rw [split,E,List.append_assoc]; rfl)))
  have leftHere : BStarCopyLeftFenceHold.Region source leftSeam r (addr root j.val) .ld :=
    leftCenter ▸ BStarCopyLeftFenceHold.ld_member source leftSeam r j.val j.isLt
  have rightHere : BStarCopyRightWrappedFenceHold.Region root rightA r rightSeam last (addr root j.val) .rd :=
    .inl ⟨j.val,j.isLt,rfl,rfl⟩
  change readLane (Sheet.index .ld) (play entry u (addr root j.val)).long=
      readLane (Sheet.index .ld) (entry (addr root j.val)).long ∧
    readLane (Sheet.index .rd) (play entry u (addr root j.val)).long=
      readLane (Sheet.index .rd) (entry (addr root j.val)).long
  exact ⟨hL (addr root j.val) .ld leftHere,hR (addr root j.val) .rd rightHere⟩

end L4.BStarNativeCopyTransport
