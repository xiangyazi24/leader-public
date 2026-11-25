import Leader.L4.BStarGeneratedPCAncestry
import Leader.L4.BStarCommitIssue

/-! Old-data source chronology for the PACE, ADMIT, and denied-tour
branches of the concrete joined pair. -/
namespace L4.BStarAdmissionPaceCore

open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongLayout
open BStarLongDoor BStarLongCommand BStarCommitIssue
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarH6WordChart
open BStarAcquireVisitOrder BStarLiteralPC
open BStarResetControllerProgress BStarArithmeticControllerReturn
open BStarResetControllerEntry BStarClearanceSource BStarAcquireWaitControl

theorem admit_successor (old : BitVec LW) (f : Payload)
    (op : (ctrlOp.read old).toNat=admit) (good : f.fault=0) (same : f.opcode.toNat=admit) :
    pcNext old f=(if f.argument.toNat%2=1 then acquire else 412) := by
  simp [pcNext,op,good,same,show (arithKind 4).isSome=false by decide,
    nextOrdinary,admit,acquire]

theorem acquire_successor (old : BitVec LW) (f : Payload)
    (op : (ctrlOp.read old).toNat=acquire) (good : f.fault=0) (same : f.opcode.toNat=acquire) :
    pcNext old f=(if f.outcome=1 then 412 else 6) := by
  simp [pcNext,op,good,same,show (arithKind 5).isSome=false by decide,nextOrdinary,acquire]


variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- On a genuine generated chronology, a consume that schedules
ISSUE ADMIT must consume the correctly matched, fault-free PACE reply.
No other op, including an arithmetic alias or a malformed reply, enters 4. -/

theorem actual_admit_consumes {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy admit (.back 0)))
    (evt : Event hp addr len x e (.busy admit (.back 0)) .idle)
    (f : Payload) (F : f.fault=0) (O : f.opcode.toNat=admit)
    (w : bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0)=.reply f) :
    snapshot (step x e (addr 0).1).long=
      ((.empty,1),BitVec.ofNat 9 (if f.argument.toNat%2=1 then acquire else 412)) := by
  obtain ⟨g,G,E⟩ := consume_exact hp H hh sep cur evt
  have eq := Token.reply.inj (G.symm.trans w)
  subst g
  rw [admit_successor _ _ cur.1.2.2.2 F O] at E
  exact E


theorem actual_acquire_consumes {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy acquire (.back 0)))
    (evt : Event hp addr len x e (.busy acquire (.back 0)) .idle)
    (f : Payload) (F : f.fault=0) (O : f.opcode.toNat=acquire)
    (w : bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0)=.reply f) :
    snapshot (step x e (addr 0).1).long=
      ((.empty,1),BitVec.ofNat 9 (if f.outcome=1 then 412 else 6)) := by
  obtain ⟨g,G,E⟩ := consume_exact hp H hh sep cur evt
  have eq := Token.reply.inj (G.symm.trans w)
  subst g
  rw [acquire_successor _ _ cur.1.2.2.2 F O] at E
  exact E


theorem pace_unit_packet (g : LongGeometry) (j : Fin 11) :
    let f : Payload := ⟨0,3,0,0,0⟩
    bind g j (.forward f)=.forward f ∧ depart g j f=some f ∧
      arrive g j f=.forward f ∧ finish f=.reply f ∧ bind g j (.reply f)=.reply f := by
  simp [BStarLongCommand.bind,depart,arrive,finish,gate,admit,bitOp,acquire,
    forwardWidth,replyWidth,arithKind,copyLoad,stageOp,sealOp,commitOp,cropped,low]

end L4.BStarAdmissionPaceCore
