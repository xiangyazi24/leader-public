import Leader.L4.Height.FreshCopyReceipt
import Leader.L4.Height.AdmissionTour
import Leader.L4.Height.FreshPreparation
import Leader.L4.BStarCopyLoadHistory

namespace L4.Height.FreshSetupTours
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongEvents BStarLongPackets BStarLongTransport
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarLongFixedRouting BStarResetMarkAdapter BStarClearanceDataChart
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail BStarGeneratedBandScan
open BStarLongCommandData BStarLongPrep BStarLongLiteral BStarResetQuiet
open BStarResetRailRing (old_read new_read)
open BStarSeparatorControl (anyTag)
open BStarLongDoor BStarClearanceSource
open BStarGeneratedPCAncestry BStarResetChartTouch BStarAcquireForwardTrace

set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step


/-- STOP, CLEAR and ENABLE carry a unit through all old physical lane states. -/
def Setup (op : Nat) : Prop := op=6 ∨ op=7 ∨ op=9

def unit (op : Nat) : Payload := ⟨0,BitVec.ofNat 9 op,0,0,0⟩

private theorem row (op : Nat) (legal : Setup op) (g : LongGeometry) (j : Fin 11) :
    let f := unit op
    bind g j (.forward f)=.forward f ∧ depart g j f=some f ∧ arrive g j f=.forward f ∧
      finish f=.reply f ∧ bind g j (.reply f)=.reply f := by
  rcases legal with rfl|rfl|rfl <;>
    simp [unit,BStarLongCommand.bind,depart,arrive,finish,gate,admit,bitOp,acquire,
      forwardWidth,replyWidth,arithKind,copyLoad,stageOp,sealOp,commitOp,cropped,low]

private theorem offer (op : Nat) (legal : Setup op) (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (mem : C∈orderedCommands g) (nd : C.kind≠.door)
    (old : readK raw C.source=.forward (unit op)) : (C,.advance (unit op))∈actualOffers g raw := by
  let p := unit op
  have code : p.opcode.toNat=op := by rcases legal with rfl|rfl|rfl <;> rfl
  have matchesBound : bound g (readK raw) C.source=.forward p := by
    unfold bound
    rw [old]
    exact (row op legal _ _).1
  have classified : classifyOld g raw C=.advance p := by
    change classify C _ (bound g (readK raw) C.source) _=.advance p
    rw [matchesBound]
    simp [classify,nd,show depart (geometry g C.source.side) C.source.occurrence p=some p
      from (row op legal _ _).2.1]
  have gatedC : (C,.advance p)∈gated g raw := by
    apply (gated_mem g raw C _).mpr
    refine ⟨mem,?_⟩
    unfold gatedAt
    rw [classified]
    rcases legal with rfl|rfl|rfl <;> simp [checkOffer,checkFence,code]
  have noFault := FreshPreparation.setup_no_cancel g raw C p (code.symm ▸ legal) gatedC
  have prior : (C,.advance p)∈(round g raw).offered :=
    List.mem_map.mpr ⟨(C,.advance p),gatedC,by
      change cancel (round g raw).faults (C,BStarLongCommand.Offer.advance p) = _
      simp only [cancel,if_neg noFault]⟩
  unfold actualOffers BStarLongGrant.run
  refine List.mem_map.mpr ⟨(C,.advance p),prior,?_⟩
  have noAcquire : p.opcode.toNat≠acquire := by
    rw [code]; rcases legal with rfl|rfl|rfl <;> decide
  by_cases early : C.source.occurrence.val<3 <;> simp [BStarLongGrant.update,early,noAcquire,p]

private theorem carried (op : Nat) (legal : Setup op) (g : Pair LongGeometry)
    (raw : Pair (BitVec LW)) (C : CommandClaim) :
    BStarClearanceForward.carried g raw C (unit op)=unit op := by
  rcases legal with rfl|rfl|rfl <;>
    simp [unit,BStarClearanceForward.carried,BStarLongArithmetic.visit,
      show BStarLongArithmetic.nodeOf 6=none by decide,show BStarLongArithmetic.nodeOf 7=none by decide,
      show BStarLongArithmetic.nodeOf 9=none by decide,BStarLongOutgoing.execute,BStarLongOutgoing.hold,
      stageOp,sealOp,commitOp]
private theorem link (op : Nat) (legal : Setup op)
    (x : X) (e : Fin n) (sep : e≠rightNeighbor e) (C : CommandClaim) (dst : AtK)
    (mem : C∈orderedCommands (oldPair B x e)) (hd : C.destination=some dst)
    (before : readK ((x e).long,(x (rightNeighbor e)).long) C.source=.forward (unit op)) :
    atCursor (step x e) (address e dst)=.forward (unit op) := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have shape := BStarAcquireReturn.link_shape g C dst mem hd
  have selected := offer op legal g raw C mem (by rw [shape.2.1]; decide) before
  obtain ⟨_,arrived⟩ := BStarClearanceForward.move_lands g raw C (unit op) dst hd selected (Ne.symm shape.1)
  rw [carried op legal,(row op legal _ _).2.2.1] at arrived
  have paired := BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) dst
    (fun _ k=>.inl (BStarAcquireJoinedHop.k0_dest g C dst mem hd k).2)
  exact (new_read B x e sep dst).symm.trans (paired.trans ((congrArg decode arrived).trans (decode_encode _)))

private theorem turn (op : Nat) (legal : Setup op) {x : X} {slots : Nat→Pos n} {len : Nat}
    (e : Fin n) (sep : e≠rightNeighbor e) (T : onTerminal hp x e slots len)
    (F : project slots x len=.forward (unit op)) :
    project slots (step x e) len=.reply (unit op) := by
  obtain ⟨C,mem,kind,dst,occ,pos⟩ := T
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have old := (old_read x e C.source).trans ((congrArg (atCursor x) pos).symm.trans F)
  have selected := offer op legal g raw C mem (by rw [kind]; decide) old
  have new := terminal_finish g raw C (unit op) dst selected
  have paired := BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) C.source
    (by intro _ zero; omega)
  have read := (congrArg BStarLongToken.decode new).trans (decode_encode _)
  change readK (patchPair (longWork g raw) raw) C.source=finish (BStarClearanceForward.carried g raw C (unit op)) at read
  rw [carried op legal,(row op legal (geometry g C.source.side) C.source.occurrence).2.2.2.1] at read
  exact (congrArg (atCursor (step x e)) pos).trans ((new_read B x e sep C.source).symm.trans (paired.trans read))

private theorem one_advance {op : Nat} {slots : Nat→Pos n} {x : X} {e : Fin n} {len k j : Nat}
    (E : Event hp slots len x e (.busy op (.out k)) (.busy op (.out j))) :
    Advance len (.out k) (.out j) := by
  cases E with
  | transit _ _ _ _ S =>
    cases S with
    | cons _ _ A _ rest => cases rest; exact A

theorem setup_outward (op : Nat) (legal : Setup op) {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base (fun j=>S.getD j fall) len op x z w d) :
    ∀ k l,z=.out k → d=.out l →
      project (fun j=>S.getD j fall) x k=.forward (unit op) →
      project (fun j=>S.getD j fall) (run x w) l=.forward (unit op) := by
  induction P with
  | nil _ =>
    intro k l K L F
    have eq := Cursor.out.inj (K.symm.trans L)
    subst l
    exact F
  | @cons x z d final e w I E tail ih =>
    intro k l K L F
    subst z
    obtain ⟨j,J⟩ := BStarAcquireHistorySample.busy_no_back_to_out hp tail ⟨l,L⟩
    subst d
    let slots := fun t=>S.getD t fall
    have new := busy_start hp tail
    have unique : ∀ i≤len, anyTag.F (project slots (step x e) i) ↔ i=j :=
      BStarOwnerControlHistory.pointed_unique_forward _ _ _ new.2.1 new.2.2
    by_cases go : linkAt hp x e slots len k
    · obtain ⟨bound,C,dest,mem,dst,source,target⟩ := go
      have old : readK ((x e).long,(x (rightNeighbor e)).long) C.source=.forward (unit op) :=
        (old_read x e C.source).trans ((congrArg (atCursor x) source).symm.trans F)
      have moved : project slots (step x e) (k+1)=.forward (unit op) :=
        (congrArg (atCursor (step x e)) target).trans
          (link hp op legal x e (sep e) C dest mem dst old)
      have eq := (unique (k+1) (by omega)).mp ⟨_,moved⟩
      exact ih (k+1) l (congrArg Cursor.out eq.symm) L moved
    · have noT : k=len → ¬onTerminal hp x e slots len := by
        intro atEnd T
        have jEq : j=len := by
          have jl := new.2.1.1
          have A := one_advance hp E
          cases A <;> omega
        have corner : project slots x len=.forward (unit op) := by
          rw [←atEnd]; exact F
        have reply := turn hp op legal e (sep e) T corner
        obtain ⟨p,oldPoint⟩ := new.2.1.2.1
        rw [jEq] at oldPoint
        exact Token.noConfusion (reply.symm.trans oldPoint)
      have frame := AdmissionTour.silent hp chart e (sep e) op k I.1 I.2.1 (unit op) F rfl
        (row op legal _ _).1
        (by intro s; rcases legal with rfl|rfl|rfl <;> simp [unit,observe,gate,admit,bitOp])
        go noT
      have eq := (unique k I.2.1.1).mp ⟨_,frame⟩
      exact ih k l (congrArg Cursor.out eq.symm) L frame


open BStarLiteralPC BStarResetControllerProgress

/-- On the first completed STOP, CLEAR or ENABLE, the generated receipt
accepts the next regular opcode without assuming a successful poststate. -/
theorem setup_receipt {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (op : Nat) (legal : Setup op) (w : List (Fin n)) (ack : Fin n)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w (.busy op (.back 0)))
    (E : Event hp (fun j=>S.getD j fall) len (run origin w) ack (.busy op (.back 0)) .idle) :
    BStarNativeReceiptTape.Hit hp base (fun j=>S.getD j fall) len (run origin w) ack op := by
  let slot := fun j=>S.getD j fall
  let root := (slot 0).1
  obtain ⟨lead,tour,launch,W,_,launched,pcOp,flight⟩ := from_idle hp G
  let before := run origin lead
  let start := step before launch
  obtain ⟨out,mark,ret,tape,outG,_,back⟩ := BStarAcquireAckAncestry.split_turn hp flight
  have rootSlot := (BStarResetChartService.root_header hp C (busy_start hp flight).1.1).2
  have first : project slot start 0=.forward (unit op) := by
    obtain ⟨_,arg,init,snap⟩ := launched
    rw [pcOp] at init
    have zero : initial op (before root).long=some 0 := by rcases legal with rfl|rfl|rfl <;> rfl
    have eq : arg=0 := Option.some.inj (init.symm.trans zero)
    subst arg
    have point := congrArg (fun t : (Token×BitVec 2)×BitVec 9=>t.1.1) snap
    change atSite (start root).long 0=forward (ctrlOp.read (before root).long).toNat 0 at point
    rw [pcOp] at point
    change atSite (start root).long (slot 0).2=.forward (unit op)
    rw [rootSlot]
    exact point
  have F := setup_outward hp op legal C sep outG 0 len rfl rfl first
  have old := BStarAcquireHistoryReturn.busy_end hp outG
  have term : onTerminal hp (run start out) mark slot len := by
    apply Classical.byContradiction
    intro absent
    have here := AdmissionTour.silent hp C mark (sep mark) op len old.1 old.2.1 (unit op) F rfl
      (row op legal _ _).1 (by intro side; rcases legal with rfl|rfl|rfl <;> simp [unit,observe,gate,admit,bitOp])
      (fun H=>Nat.lt_irrefl _ H.1) (fun _=>absent)
    obtain ⟨q,H⟩ := (busy_start hp back).2.1.2.1
    exact Token.noConfusion (here.symm.trans H)
  have reply := turn hp op legal mark (sep mark) term F
  have replay : run origin w=run (step (run start out) mark) ret := by
    rw [W,BStarResetSchedule.run_append]
    change run start tour=_
    rw [tape,BStarResetSchedule.run_append]
    rfl
  rw [replay] at E ⊢
  apply FreshCopyReceipt.ordinary hp C sep op _ _ back reply ack E <;> rcases legal with rfl|rfl|rfl <;> decide

open BStarCopyLoadCarry BStarCopyLoadHistory BStarLongLayout

private theorem load_turn (x : X) (e : Fin n) (he : e≠rightNeighbor e)
    (cl : CommandClaim) (u : Nat) (width : u<64) (valid : selTriple u=true)
    (hc : cl∈orderedCommands (oldPair B x e)) (hT : cl.kind=.terminal)
    (dest : cl.destination=none) (idx : cl.source.occurrence.val=10)
    (old : atCursor x (address e cl.source)=.forward (payload u)) :
    atCursor (step x e) (address e cl.source)=.reply (unit 8) := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have gt := load_gated g raw cl u width valid hc (by simp [hT]) ((old_read x e _).trans old)
  have nf := valid_load_no_fault g raw cl u width valid gt
  have R : (cl,.advance (payload u))∈(round g raw).offered :=
    List.mem_map.mpr ⟨_,gt,by change (if cl.source∈(round g raw).faults then (cl,BStarLongCommand.Offer.advance failedPayload) else (cl,BStarLongCommand.Offer.advance (payload u)))=(cl,BStarLongCommand.Offer.advance (payload u)); rw [if_neg nf]⟩
  have A : (cl,.advance (payload u))∈actualOffers g raw := by
    unfold actualOffers BStarLongGrant.run
    apply List.mem_map.mpr
    exact ⟨_,R,by simp [BStarLongGrant.update,show ¬cl.source.occurrence.val<3 by omega]⟩
  have ds : BStarLongRouting.readRaw (patchPair (longWork g raw) raw) cl.source = encode (finish (BStarClearanceForward.carried g raw cl (payload u))) := terminal_finish g raw cl (payload u) dest A
  rw [load_carries] at ds
  have j := BStarAcquireReturn.joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) cl.source (fun _ h => by omega)
  have work : readK (patchPair (longWork g raw) raw) cl.source=finish (payload u) :=
    (congrArg decode ds).trans (decode_encode _)
  have eq := (new_read B x e he cl.source).symm.trans (j.trans work)
  rw [eq]
  simp [finish,payload,unit,replyWidth,arithKind,cropped,low,sealOp,admit,bitOp,acquire,Nat.mod_one]

/-- An actual LOAD return consumes the same legal selector triple that
its source launched, with a canonical zero-width ACK payload. -/
theorem load_receipt {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (ack : Fin n)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w (.busy 8 (.back 0)))
    (E : Event hp (fun j=>S.getD j fall) len (run origin w) ack (.busy 8 (.back 0)) .idle) :
    BStarNativeReceiptTape.Hit hp base (fun j=>S.getD j fall) len (run origin w) ack 8 := by
  let slot := fun j=>S.getD j fall
  let root := (slot 0).1
  obtain ⟨lead,tour,launch,W,_,L,pcOp,flight⟩ := from_idle hp G
  let before := run origin lead
  let start := step before launch
  let arg := (captures.read (before root).long).toNat
  obtain ⟨_,v,init,snap⟩ := L
  rw [pcOp] at init
  obtain ⟨value,valid⟩ := BStarCopyOperand.issue_load_operand _ _ init
  subst v
  have width : arg<64 := (captures.read (before root).long).isLt
  obtain ⟨out,mark,ret,tape,outG,_,back⟩ := BStarAcquireAckAncestry.split_turn hp flight
  have rootSlot := (BStarResetChartService.root_header hp C (busy_start hp flight).1.1).2
  have first : project slot start 0=.forward (payload arg) := by
    change atSite (start root).long (slot 0).2=_
    rw [rootSlot]
    have point := congrArg (fun t : (Token×BitVec 2)×BitVec 9 => t.1.1) snap
    change atSite (start root).long 0=forward (ctrlOp.read (before root).long).toNat arg at point
    rw [pcOp] at point
    exact point
  have trace := busy_load_word hp C sep outG arg width valid 0 len rfl rfl first
  have F := load_word_carries hp trace arg width valid first
  have prior := BStarAcquireHistoryReturn.busy_end hp outG
  have term : onTerminal hp (run start out) mark slot len := by
    apply Classical.byContradiction
    intro no
    have quiet := AdmissionTour.silent hp C mark (sep mark) 8 len prior.1 prior.2.1 (payload arg) F rfl
      (load_bind _ _ arg width valid)
      (by intro side; simp [payload,observe,gate,admit,bitOp])
      (fun J=>Nat.lt_irrefl _ J.1) (fun _=>no)
    obtain ⟨q,H⟩ := (busy_start hp back).2.1.2.1
    exact Token.noConfusion (quiet.symm.trans H)
  obtain ⟨cmd,selected,kind,dest,occ,pos⟩ := term
  have turned : project slot (step (run start out) mark) len=.reply (unit 8) :=
    (congrArg (atCursor _) pos).trans (load_turn hp _ mark (sep mark) cmd arg width valid selected kind dest occ
      ((congrArg (atCursor _) pos).symm.trans F))
  have replay : run origin w=run (step (run start out) mark) ret := by
    rw [W,BStarResetSchedule.run_append]
    change run start tour=_
    rw [tape,BStarResetSchedule.run_append]
    rfl
  rw [replay] at E ⊢
  exact FreshCopyReceipt.ordinary hp C sep 8 (by decide) (by decide) back turned ack E

#print axioms load_receipt
#print axioms setup_receipt
#print axioms setup_outward
end L4.Height.FreshSetupTours
