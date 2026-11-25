import Leader.L4.BStarSealSafeReplay

namespace L4.BStarSealTailReplay
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongGrant BStarH6WordChart BStarLongDoor
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarSealOwnerFrame BStarAcquireVisitOrder BStarAcquireForwardTrace
open BStarAcquireLiteralChain BStarResetChartTouch BStarSealModes BStarClearanceSource
open BStarSealSafeReplay

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Explicit literal itinerary of one successful NEED tail, from
immediately after that owner's SEAL center to its first COMMIT center.
There cannot be a RELEASE or an earlier latch-changing outgoing mark
on this itinerary. Only the matching physical visits, receipt
transitions, foreign waits, and actual launches are assumed. -/
theorem tail_replay {base x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (sealAck bitDoor bitAck commitDoor : Fin n)
    (sealTail wait1 bitTail wait2 commitTail : List (Fin n))
    (sealBusy : BusyOnly hp base (fun j=>S.getD j fall) len sealOp
      x (.out (k+1)) sealTail (.back 0))
    (sealConsume : Event hp (fun j=>S.getD j fall) len (play x sealTail)
      sealAck (.busy sealOp (.back 0)) .idle)
    (idle1 : let y:=step (play x sealTail) sealAck
      ∃ a, GeneratedOwner hp base (fun j=>S.getD j fall) len y .idle wait1 a)
    (foreign1 : ∀ e∈wait1,rightNeighbor e≠(S.getD 0 fall).1)
    (bitStart : let y:=play (step (play x sealTail) sealAck) wait1
      Event hp (fun j=>S.getD j fall) len y bitDoor .idle (.busy bitOp (.out 0)))
    (bitBusy : let y:=step (play (step (play x sealTail) sealAck) wait1) bitDoor
      BusyOnly hp base (fun j=>S.getD j fall) len bitOp y (.out 0) bitTail (.back 0))
    (bitConsume : let y:=play (step (play (step (play x sealTail) sealAck) wait1) bitDoor) bitTail
      Event hp (fun j=>S.getD j fall) len y bitAck (.busy bitOp (.back 0)) .idle)
    (idle2 : let y:=step (play (step (play (step (play x sealTail) sealAck) wait1) bitDoor) bitTail) bitAck
      ∃ a, GeneratedOwner hp base (fun j=>S.getD j fall) len y .idle wait2 a)
    (foreign2 : ∀ e∈wait2,rightNeighbor e≠(S.getD 0 fall).1)
    (commitEnter : commitDoor=RearTrace.predecessor (S.getD 0 fall).1)
    (commitPre : let s:=play (step (play (step (play (step (play x sealTail)
      sealAck) wait1) bitDoor) bitTail) bitAck) wait2
      (ctrlOp.read (s (S.getD 0 fall).1).long).toNat=commitOp ∧
      Launch (s (S.getD 0 fall).1).long ((step s commitDoor) (S.getD 0 fall).1).long ∧
      BusyOnly hp base (fun j=>S.getD j fall) len commitOp
        (step s commitDoor) (.out 0) commitTail (.out k)) :
    Replay hp base (fun j=>S.getD j fall) len i k x (.busy sealOp (.out (k+1)))
      (sealTail++sealAck::(wait1++bitDoor::(bitTail++bitAck::(wait2++commitDoor::commitTail))))
      (.busy commitOp (.out k)) := by
  obtain ⟨_,I1⟩ := idle1
  obtain ⟨_,I2⟩ := idle2
  obtain ⟨pc,launch,last⟩ := commitPre
  have W1 := foreign_idle_replay hp (k:=k) (i:=i) I1 foreign1
  have W2 := foreign_idle_replay hp (k:=k) (i:=i) I2 foreign2
  have R1 := seal_replay hp (i:=i) (k:=k) sealBusy (by
    intro j J
    have E := Cursor.out.inj J
    omega)
  have R2 := bit_replay hp (i:=i) (k:=k) bitBusy
  have R3 := precenter_commit_replay hp C sep commitDoor i commitTail k K idx head pc launch last
  have waiting := seal_after_center_safe k (.back 0) (by intro _ H; contradiction)
  apply append hp R1
  apply Replay.cons (BStarAcquireHistoryReturn.busy_end hp sealBusy) sealConsume
    ⟨waiting.2,fun _=>waiting.1⟩
  apply append hp W1
  apply Replay.cons (BStarGeneratedTapeCuts.at_end hp (generated hp W1)) bitStart
    (idle_safe_step i bitDoor k)
  apply append hp R2
  apply Replay.cons (BStarAcquireHistoryReturn.busy_end hp bitBusy) bitConsume
    ⟨(bit_safe k (.back 0)).2,fun _=>(bit_safe k (.back 0)).1⟩
  apply append hp W2
  exact .cons (BStarGeneratedTapeCuts.at_end hp (generated hp W2)) (pc ▸ Event.launch commitEnter launch)
    (idle_safe_step i commitDoor k) R3

open BStarAcquireAnchors BStarLongPublication BStarLongLayout
open BStarLongLiteral BStarLongEvents BStarBitNoAbort

private theorem append_generated_mark {base x : X} {addr : Nat→Pos n} {len : Nat}
    {a b c : Mode} {w : List (Fin n)} {e : Fin n}
    (G : GeneratedOwner hp base addr len x a w b)
    (E : Event hp addr len (play x w) e b c)
    (I : Current hp base addr len (step (play x w) e) c) :
    GeneratedOwner hp base addr len x a (w++[e]) c := by
  induction G with
  | endpoint F => exact .next F E (.endpoint I)
  | next F ev _ ih => exact .next F ev (ih E I)

/-- On the concrete tape, the genuine selected SEAL plus the joined
successful-tail replay retain the exact descriptor latches and live
writer up to the precenter COMMIT cut. No future successful publication
or terminal writer test is required. The old grant conflict condition
and the matching post-SEAL trace are inputs. -/
theorem seeded_tail_custody {base origin : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (k : Nat) (K : k≤len) (idx : S.getD k fall=(i,1))
    (lead w : List (Fin n)) (f : Payload) (d : Descriptor)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (selected : let x := play origin lead
      oldH6 B x i=true ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false ∧
      f.fault=0 ∧ f.opcode.toNat=sealOp ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (f.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧ readOptional (stage.read (x i).long)=some d ∧
      (centerLink (oldPair B x i),.advance f)∈actualOffers (oldPair B x i)
        ((x i).long,(x (rightNeighbor i)).long))
    (E : Event hp (fun j=>S.getD j fall) len (play origin lead) i
      (.busy sealOp (.out k)) (.busy sealOp (.out (k+1))))
    (R : Replay hp base (fun j=>S.getD j fall) len i k (step (play origin lead) i)
      (.busy sealOp (.out (k+1))) w (.busy commitOp (.out k)))
    (head : ∀ u e v,w=u++e::v →
      oldH6 B (play (step (play origin lead) i) u) i=true) :
    SealedCenter d (play (step (play origin lead) i) w i).long := by
  obtain ⟨H,coh,F,O,D,A,T,pick⟩ := selected
  have ⟨seed,fairGrant⟩ := BStarSealWriterInterval.after_selected_seal hp C sep i own k lead rfl
    G (BStarGeneratedTapeCuts.at_end hp G) H coh f d F O D A T pick
  have next := BStarGeneratedTapeCuts.at_start hp (generated hp R)
  have past := append_generated_mark hp G E next
  have landing : play origin (lead++[i])=step (play origin lead) i := by
    rw [BStarResetSchedule.run_append]
    rfl
  exact (keeps_sealed hp C sep i own k K idx (lead++[i]) w landing _ _ past R d seed fairGrant
    head w [] (List.append_nil _).symm).1

end L4.BStarSealTailReplay
