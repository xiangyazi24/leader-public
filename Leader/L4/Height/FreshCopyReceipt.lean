import Leader.L4.Height.FreshAttempt
import Leader.L4.BStarNativeReceiptTape

namespace L4.Height.FreshCopyReceipt
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongCommand
open BStarLongDoor BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarResetMarkAdapter BStarGeneratedBandScan BStarLiteralPC BStarResetControllerProgress

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step


def unit (op : Nat) : Payload := ⟨0,BitVec.ofNat 9 op,0,0,0⟩

/-- The physical incoming door accepts a canonical unit ACK on every
ordinary COPY opcode from STOP through FENCE. -/
theorem ordinary {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (op : Nat) (lower : 6≤op) (upper : op≤11)
    {w : List (Fin n)}
    (ret : BusyOnly hp base (fun j=>S.getD j fall) len op x (.back len) w (.back 0))
    (receipt : project (fun j=>S.getD j fall) x len=.reply (unit op))
    (ack : Fin n)
    (event : Event hp (fun j=>S.getD j fall) len (run x w) ack (.busy op (.back 0)) .idle) :
    BStarNativeReceiptTape.Hit hp base (fun j=>S.getD j fall) len (run x w) ack op := by
  have copyOp : op=6 ∨ op=7 ∨ op=8 ∨ op=9 ∨ op=10 ∨ op=11 := by omega
  let slots := fun j=>S.getD j fall
  let y := run x w
  let i := (slots 0).1
  have canonical : BStarReplyBack.normal (unit op)=.reply (unit op) := by
    rcases copyOp with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  obtain ⟨j,J,returned⟩ := FreshAttempt.canonical_reply_returns hp chart sep ret _ canonical len rfl receipt
  have jEq : j=0 := (Cursor.back.inj J).symm
  subst j
  have old := BStarAcquireHistoryReturn.busy_end hp ret
  obtain ⟨header,slot⟩ := BStarResetChartService.root_header hp chart old.1.1
  have token : atSite (y i).long 0=.reply (unit op) := by
    change atSite (y i).long (slots 0).2=.reply (unit op) at returned
    rwa [slot] at returned
  have bound : bind (longGeometry B (y i)) 0 (atSite (y i).long 0)=.reply (unit op) := by
    rw [token,BStarReplyBack.normal_eq]
    exact canonical
  obtain ⟨f,F,installed⟩ := BStarGeneratedPCAncestry.consume_exact hp
    (base:=base) (x:=y) (addr:=slots) (len:=len) (op:=op) (e:=ack)
    slot header (sep ack) old event
  have equal := Token.reply.inj (F.symm.trans bound)
  subst f
  have oldPc : pc y i=op := old.1.2.2.2
  have next : pcNext (y i).long (unit op)=op+1 := by
    change (ctrlOp.read (y i).long).toNat=op at oldPc
    rcases copyOp with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [pcNext,oldPc,unit,show (arithKind 6).isSome=false by decide,
        show (arithKind 7).isSome=false by decide,show (arithKind 8).isSome=false by decide,show (arithKind 9).isSome=false by decide,
        show (arithKind 10).isSome=false by decide,show (arithKind 11).isSome=false by decide,nextOrdinary]
  have code := congrArg (fun t : (Token×BitVec 2)×BitVec 9=>t.2.toNat) installed
  change pc (step y ack) i=(BitVec.ofNat 9 (pcNext (y i).long (unit op))).toNat at code
  have newPc : pc (step y ack) i=op+1 := by
    rw [code,next]
    rcases copyOp with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have door : ack=RearTrace.predecessor i := by
    cases event <;> assumption
  have tag : (unit op).opcode.toNat=op := by rcases copyOp with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact ⟨old,event,oldPc,newPc,door,unit op,bound,rfl,tag⟩

#print axioms ordinary
end L4.Height.FreshCopyReceipt
