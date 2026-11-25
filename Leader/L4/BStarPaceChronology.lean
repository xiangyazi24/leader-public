import Leader.L4.BStarSealAckLegal

/-! Old-data source chronology for the PACE, ADMIT, and denied-tour
branches of the concrete joined pair. -/
namespace L4.BStarPaceChronology

open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongLayout
open BStarLongDoor BStarLongCommand BStarCommitIssue BStarCommitChoiceHistory
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarH6WordChart
open BStarAcquireVisitOrder BStarCommitGeneratedTail BStarLiteralPC
open BStarResetControllerProgress BStarArithmeticControllerReturn
open BStarResetControllerEntry BStarClearanceSource BStarAcquireWaitControl BStarSealAckLegal

theorem pace_successor (old : BitVec LW) (f : Payload)
    (op : (ctrlOp.read old).toNat=3) (good : f.fault=0) (same : f.opcode.toNat=3) :
    pcNext old f=admit := by
  simp [pcNext,op,good,same,show (arithKind 3).isSome=false by decide,nextOrdinary,admit]

theorem admit_successor (old : BitVec LW) (f : Payload)
    (op : (ctrlOp.read old).toNat=admit) (good : f.fault=0) (same : f.opcode.toNat=admit) :
    pcNext old f=(if f.argument.toNat%2=1 then acquire else 412) := by
  simp [pcNext,op,good,same,show (arithKind 4).isSome=false by decide,
    nextOrdinary,admit,acquire]

theorem acquire_successor (old : BitVec LW) (f : Payload)
    (op : (ctrlOp.read old).toNat=acquire) (good : f.fault=0) (same : f.opcode.toNat=acquire) :
    pcNext old f=(if f.outcome=1 then 412 else 6) := by
  simp [pcNext,op,good,same,show (arithKind 5).isSome=false by decide,nextOrdinary,acquire]

theorem dummy_successor (old : BitVec LW) (f : Payload)
    (op : (ctrlOp.read old).toNat=412) (good : f.fault=0) (same : f.opcode.toNat=412) :
    pcNext old f=0 := by
  simp [pcNext,op,good,same,show (arithKind 412).isSome=false by decide,nextOrdinary]

theorem next_to_admit (old : BitVec LW) (f : Payload)
    (valid : LongDoorGuard.valid manifest old=true) (A : pcNext old f=admit) :
    (ctrlOp.read old).toNat=3 ∧ f.fault=0 ∧ f.opcode.toNat=3 := by
  let op := (ctrlOp.read old).toNat
  have range : op<413 := of_decide_eq_true (Bool.and_eq_true_iff.mp valid).2
  change (if f.fault != 0 || f.opcode.toNat != op then 0
    else if (arithKind op).isSome then successor old op else nextOrdinary old op f)=admit at A
  by_cases bad : (f.fault != 0 || f.opcode.toNat != op)=true
  · rw [if_pos bad] at A
    contradiction
  rw [if_neg bad] at A
  have clean := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr bad)
  have fg : f.fault=0 := by simpa using clean.1
  have fe : f.opcode.toNat=op := by simpa using clean.2
  by_cases ar : (arithKind op).isSome=true
  · rw [if_pos ar] at A
    have P := arithmetic_range op ar
    rcases successor_order old op P.2 with E|E
    · rw [E] at A; contradiction
    · unfold admit at A
      omega
  rw [if_neg ar] at A
  have small : op<4 := by
    rcases ordinary_progress old op f range with E|E
    · rw [E] at A; contradiction
    · unfold admit at A
      omega
  have E : op=0 ∨ op=1 ∨ op=2 ∨ op=3 := by omega
  have P : op=3 := by
    rcases E with e|e|e|e
    all_goals simp [e,nextOrdinary,admit] at A ⊢
  exact ⟨P,fg,fe.trans P⟩

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- On a genuine generated chronology, a consume that schedules
ISSUE ADMIT must consume the correctly matched, fault-free PACE reply.
No other op, including an arithmetic alias or a malformed reply, enters 4. -/
theorem actual_consume_to_admit {base x : X} {addr : Nat → Pos n} {len op : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy op (.back 0)))
    (evt : Event hp addr len x e (.busy op (.back 0)) .idle)
    (fresh : (ctrlOp.read (step x e (addr 0).1).long).toNat=admit) :
    op=3 ∧ ∃ f, bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0)=.reply f ∧
      f.fault=0 ∧ f.opcode.toNat=3 := by
  obtain ⟨f,F,E⟩ := consume_pc hp H hh sep cur evt
  obtain ⟨P,good,same⟩ := next_to_admit _ f cur.1.2.1 (E.symm.trans fresh)
  exact ⟨cur.1.2.2.2.symm.trans P,f,F,good,same⟩

/-- Exact source snapshot of the actual PACE consume. The controller
does not launch ADMIT on the same raw mark. -/
theorem actual_pace_consumes_to_admit {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy 3 (.back 0)))
    (evt : Event hp addr len x e (.busy 3 (.back 0)) .idle)
    (f : Payload) (F : f.fault=0) (O : f.opcode.toNat=3)
    (w : bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0)=.reply f) :
    snapshot (step x e (addr 0).1).long=((.empty,1),BitVec.ofNat 9 admit) := by
  obtain ⟨g,G,E⟩ := consume_exact hp H hh sep cur evt
  have eq := Token.reply.inj (G.symm.trans w)
  subst g
  rw [pace_successor _ _ cur.1.2.2.2 F O] at E
  exact E

/-- On a matching ADMIT reply the literal source chooses ACQUIRE for
the positive bit, or DUMMY for the denied bit. Both are later issues. -/
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

local notation "play" => BStarResetSchedule.run step

/-- Scope for the fixed zero-argument ordinary commands around ADMIT. -/
def paceBand (op : Nat) : Prop := op=3 ∨ op=admit ∨ op=412

theorem paceBand_initial (op : Nat) (h : paceBand op) (old : BitVec LW) :
    initial op old=some 0 := by
  rcases h with rfl|rfl|rfl <;> rfl

/-- A true matching PACE ACK schedules ADMIT only. The first subsequent
incoming owner mark, after any sequence that misses that incoming raw
bond, launches exactly canonical F(ADMIT) with bit zero. The general
statement applies also to the initial PACE and denied DUMMY launches. -/
theorem first_door_launches_paceBand (x : X) (i : Fin n) (wait : List (Fin n)) (door : Fin n)
    (sep : door≠rightNeighbor door) (D : rightNeighbor door=i)
    (away : ∀ e∈wait,rightNeighbor e≠i)
    (head : ∀ u e v,wait=u++e::v → oldH6 B (play x u) i=true)
    (lastHead : oldH6 B (play x wait) i=true)
    (ready : Issue (x i).long) (op : Nat) (oldPC : (ctrlOp.read (x i).long).toNat=op)
    (H : paceBand op) :
    let y := play x wait
    Launch (y i).long ((step y door) i).long ∧
      atSite ((step y door) i).long 0=forward op 0 := by
  dsimp only
  let y := play x wait
  let src : BitVec LW := (y i).long
  have ctrl := away_controller hp x i wait away head
  have P : (ctrlPhase.read src).toNat=1 := (congrArg (fun z => z.1.toNat) ctrl).trans ready.2
  have pc : (ctrlOp.read src).toNat=op := (congrArg (fun z => z.2.toNat) ctrl).trans oldPC
  have bound : op<manifest.opcodes := by rcases H with rfl|rfl|rfl <;> decide
  have V : LongDoorGuard.valid manifest src=true := by
    change ((((ctrlPhase.read src).toNat==1) || ((ctrlPhase.read src).toNat==2)) &&
      decide ((ctrlOp.read src).toNat<manifest.opcodes))=true
    simp [P,pc,bound]
  have init : initial (ctrlOp.read src).toNat src=some 0 := by
    rw [pc]
    exact paceBand_initial op H src
  let pair := (y door,y (rightNeighbor door))
  have localRow := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair
  have headPair : (oldHeaders B pair.2).h6=true := by
    change oldH6 B y (rightNeighbor door)=true
    rwa [D]
  have valPair : LongDoorGuard.valid manifest pair.2.long=true := by
    change LongDoorGuard.valid manifest (y (rightNeighbor door)).long=true
    rwa [D]
  have phasePair : (ctrlPhase.read pair.2.long).toNat=1 :=
    (congrArg (fun j => (ctrlPhase.read (y j).long).toNat) D).trans P
  have join := localRow headPair valPair phasePair
  have actual : (step y door) i=(largePair B pair).2 := by
    rw [←D]
    simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  have E := congrArg (fun v => snapshot v.long) actual
  have L : snapshot ((step y door) i).long=
      ((forward (ctrlOp.read src).toNat 0,2),ctrlOp.read src) := by
    rw [E,join]
    change (match initial (ctrlOp.read (y (rightNeighbor door)).long).toNat (y (rightNeighbor door)).long with
      | none => ((Token.empty,(1 : BitVec 2)),0)
      | some a => ((forward (ctrlOp.read (y (rightNeighbor door)).long).toNat a,2),
        ctrlOp.read (y (rightNeighbor door)).long))=_
    rw [D]
    rw [show initial (ctrlOp.read (y i).long).toNat (y i).long=some 0 from init]
  refine ⟨⟨⟨V,P⟩,0,init,L⟩,?_⟩
  have out : atSite ((step y door) i).long 0=forward (ctrlOp.read src).toNat 0 :=
    congrArg (fun v : (Token × BitVec 2) × BitVec 9 => v.1.1) L
  rwa [pc] at out

/-- Literal unit PACE packet: its outward payload does not depend on
the clock geometry, gate bits, or the particular occurrence. -/
theorem pace_unit_packet (g : LongGeometry) (j : Fin 11) :
    let f : Payload := ⟨0,3,0,0,0⟩
    bind g j (.forward f)=.forward f ∧ depart g j f=some f ∧
      arrive g j f=.forward f ∧ finish f=.reply f ∧ bind g j (.reply f)=.reply f := by
  simp [BStarLongCommand.bind,depart,arrive,finish,gate,admit,bitOp,acquire,
    forwardWidth,replyWidth,arithKind,copyLoad,stageOp,sealOp,commitOp,cropped,low]

/-- PACE ACK and subsequent own ADMIT ISSUE occur at strictly
different marks; the old prefix in between is not erased. -/
theorem actual_pace_ack_then_admit_launch {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy 3 (.back 0)))
    (evt : Event hp addr len x e (.busy 3 (.back 0)) .idle)
    (f : Payload) (F : f.fault=0) (O : f.opcode.toNat=3)
    (w : bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0)=.reply f)
    (wait : List (Fin n)) (door : Fin n)
    (sepDoor : door≠rightNeighbor door) (D : rightNeighbor door=(addr 0).1)
    (away : ∀ a∈wait,rightNeighbor a≠(addr 0).1)
    (head : ∀ u a v,wait=u++a::v → oldH6 B (play (step x e) u) (addr 0).1=true)
    (lastHead : oldH6 B (play (step x e) wait) (addr 0).1=true) :
    let y := play (step x e) wait
    Launch (y (addr 0).1).long ((step y door) (addr 0).1).long ∧
      atSite ((step y door) (addr 0).1).long 0=forward admit 0 := by
  dsimp only
  have S := actual_pace_consumes_to_admit hp H hh sep cur evt f F O w
  have I := issue_of_snapshot (by decide : admit<413) S
  have P := congrArg (fun z : (Token × BitVec 2) × BitVec 9=>z.2.toNat) S
  change (ctrlOp.read ((step x e) (addr 0).1).long).toNat=admit at P
  exact first_door_launches_paceBand hp (step x e) (addr 0).1 wait door
    sepDoor D away head lastHead I admit P (.inr (.inl rfl))

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

theorem actual_dummy_returns_to_reset {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy 412 (.back 0)))
    (evt : Event hp addr len x e (.busy 412 (.back 0)) .idle)
    (f : Payload) (F : f.fault=0) (O : f.opcode.toNat=412)
    (w : bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0)=.reply f) :
    snapshot (step x e (addr 0).1).long=((.empty,1),0) := by
  obtain ⟨g,G,E⟩ := consume_exact hp H hh sep cur evt
  have eq := Token.reply.inj (G.symm.trans w)
  subst g
  rw [dummy_successor _ _ cur.1.2.2.2 F O] at E
  exact E

#print axioms actual_consume_to_admit
#print axioms actual_pace_consumes_to_admit
#print axioms actual_admit_consumes
#print axioms first_door_launches_paceBand
#print axioms pace_unit_packet
#print axioms actual_pace_ack_then_admit_launch
#print axioms actual_acquire_consumes
#print axioms actual_dummy_returns_to_reset

end L4.BStarPaceChronology

