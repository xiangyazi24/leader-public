import Leader.L4.BStarSealAckLegal
import Leader.L4.BStarAcquireHistoryReturn

namespace L4.BStarSealBitDescriptor
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongLayout
open BStarLongDoor BStarLongCommand BStarCommitIssue
open BStarGeneratedOwner BStarH6WordChart BStarAcquireLiteralChain BStarResetChartTouch
open BStarAcquireVisitOrder BStarCommitGeneratedTail BStarOwnerLaunchOrigin
open BStarSeparatingRail BStarClearanceSource

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Source descriptor and bank choice frame throughout any actual
uninterrupted post-launch non-CLEAR tour, including its terminal turn,
reverse transport and waiting source before the consume edge. -/
theorem busy_preserves_descriptor {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {a b : Cursor} {w : List (Fin n)}
    (T : BusyOnly hp base (fun j=>S.getD j fall) len op x a w b) (notClear : op≠1) :
    let i := (S.getD 0 fall).1
    sourceDescriptor.read (play x w i).long=sourceDescriptor.read (x i).long ∧
      choice.read (play x w i).long=choice.read (x i).long := by
  induction T with
  | nil _ => exact ⟨rfl,rfl⟩
  | @cons x z d b e w I E tail ih =>
    have ⟨head,K⟩ := BStarResetChartService.root_header hp C I.1.1
    have N : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat≠1 :=
      fun Q => notClear (I.1.2.2.2.symm.trans Q)
    have notIdleZ : Mode.busy op z≠Mode.idle := by intro F; cases F
    have notIdleD : Mode.busy op d≠Mode.idle := by intro F; cases F
    have init := generated_flight hp (base:=base) (x:=x)
      (addr:=fun j=>S.getD j fall) (len:=len) (e:=e) (u:=.busy op z) (v:=.busy op d)
      K head (sep e) I E N (fun T => notIdleZ T.1) (fun _ => .inr notIdleD)
    obtain ⟨pick,descr⟩ := init
    exact ⟨ih.1.trans descr,ih.2.trans pick⟩

/-- One and the same validated descriptor survives the actual
successful NEED SEAL ACK, the foreign wait, the first own SEAL→BIT
door, and the uninterrupted BIT tour up to the BIT ACK. Neither
eventual COMMIT nor the BIT parity is supplied or used. -/
theorem seal_to_bit_descriptor {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (ack door : Fin n) (wait fly : List (Fin n)) (d : Desc) (f : Payload)
    (head : oldH6 B x (S.getD 0 fall).1=true)
    (current : Current hp base (fun j=>S.getD j fall) len x (.busy sealOp (.back 0)))
    (evt : Event hp (fun j=>S.getD j fall) len x ack (.busy sealOp (.back 0)) .idle)
    (ready : Current hp base (fun j=>S.getD j fall) len (step x ack) .idle)
    (F : f.fault=0) (O : f.opcode.toNat=sealOp)
    (R : BStarLongCommand.bind (longGeometry B (x (S.getD 0 fall).1)) 0
      (atSite (x (S.getD 0 fall).1).long 0)=.reply f)
    (D : BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d)
    (need : d.need=true) (parity : f.argument.toNat%2=1)
    (enters : rightNeighbor door=(S.getD 0 fall).1)
    (away : ∀ a∈wait,rightNeighbor a≠(S.getD 0 fall).1)
    (headers : ∀ u v,wait=u++v → oldH6 B (play (step x ack) u) (S.getD 0 fall).1=true)
    (walk : BusyOnly hp base (fun j=>S.getD j fall) len bitOp
      (step (play (step x ack) wait) door) (.out 0) fly (.back 0)) :
    let y := play (step (play (step x ack) wait) door) fly
    BStarLongPublication.decode (sourceDescriptor.read (y (S.getD 0 fall).1).long)=some d := by
  have headK : (S.getD 0 fall).2=0 := congrArg Prod.snd C.root
  obtain ⟨PC,frame,_⟩ := BStarSealAckLegal.actual_seal_ack_allows_bit hp
    (base:=base) (x:=x) (addr:=fun j=>S.getD j fall) headK head (sep ack) current evt
    d f F O R D need parity
  obtain ⟨_,_,desc⟩ := BStarSealAckLegal.first_door_launches_bit hp
    (step x ack) (S.getD 0 fall).1 wait door (sep door) enters away
    (fun u e v E => headers u (e::v) E) (headers wait [] (List.append_nil _).symm) ready.1 PC d frame
  have same := (busy_preserves_descriptor hp C sep walk (by decide)).1
  exact (congrArg BStarLongPublication.decode same).trans desc

end L4.BStarSealBitDescriptor
