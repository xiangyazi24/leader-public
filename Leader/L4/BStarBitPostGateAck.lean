import Leader.L4.BStarBitReplyToCommit
import Leader.L4.BStarBitPostGateReplay

namespace L4.BStarBitPostGateAck
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarGeneratedOwner
open BStarOwnerLaunchOrigin BStarAcquireForwardTrace BStarAcquireHistorySample BStarResetChartService
open BStarBitHealthyService BStarLongDoor BStarLongLayout BStarCommitChoiceHistory
open BStarH6Ordinal BStarClearanceOffset

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- After a healthy BIT clears its unique gate, the nominated whole
remaining service subsequence forces the actual same-wire ACK and
schedules 411. Interleaving may advance the rail before a nominated
mark; no future matching reply is needed as an input. -/
theorem after_gate_acks_of_sublist {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (ready : correct (oldH6 B base) hh 5 x)
    (g : Nat) (G : g<len) (gateK : (S.getD g fall).2=1)
    (gateH : oldOrdinal B base hh (S.getD g fall).1=4)
    (pay : Payload) (wire : Wire pay)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out (g+1))))
    (old : project (fun j=>S.getD j fall) x (g+1)=.forward pay)
    (t : Fin n) (turn : ∀ y : X,Q y→onTerminal hp y t (fun j=>S.getD j fall) len)
    (d : BStarLongPublication.Descriptor) (need : d.need=true)
    (desc : BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d)
    {ls back w : List (Fin n)}
    (sub : (ls++t::(back++[RearTrace.predecessor (S.getD 0 fall).1])).Sublist w)
    (size : g+1+ls.length=len) (backSize : len≤back.length)
    (nom : ∀ k (K : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun a=>S.getD a fall) len (g+1+k))
    (backNom : ∀ k (K : k<back.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y back[k] (fun a=>S.getD a fall) len (back.length-(k+1))) :
    ∃ pre tail, w=pre++RearTrace.predecessor (S.getD 0 fall).1::tail ∧
      BusyOnly hp base (fun j=>S.getD j fall) len bitOp x (.out (g+1)) pre (.back 0) ∧
      let y := play x pre
      let ack := RearTrace.predecessor (S.getD 0 fall).1
      let fresh := (step y ack (S.getD 0 fall).1).long
      Event hp (fun j=>S.getD j fall) len y ack (.busy bitOp (.back 0)) .idle ∧
      Current hp base (fun j=>S.getD j fall) len (step y ack) .idle ∧
      (ctrlOp.read fresh).toNat=commitOp ∧
      BStarLongPublication.decode (sourceDescriptor.read fresh)=some d ∧
      choice.read fresh=BitVec.ofNat 2 (pick d pay).val := by
  obtain ⟨first,rest,W,front,backward⟩ := List.append_sublist_iff.mp sub
  obtain ⟨pre,unused,E,R,F⟩ := BStarBitPostGateReplay.reaches_terminal_of_sublist hp
    C Q fiber closed sep g G gateK gateH pay wire front x (g+1) (g+1) size (Nat.le_refl _) (by omega)
    (Nat.lt_succ_self _) qx ready cur old nom
  let y := play x pre
  have stable (x : X) (u : List (Fin n)) (H : Q x) : Q (play x u) := by
    induction u generalizing x with
    | nil => exact H
    | cons a u ih => exact ih (step x a) (closed _ H a)
  have saved := (BStarSealBitDescriptor.busy_preserves_descriptor hp C sep R (by decide)).1
  have yD := (congrArg BStarLongPublication.decode saved).trans desc
  obtain ⟨suffix,tail,A,T,U⟩ := BStarBitReplyToCommit.schedule_commit_of_sublist hp
    C Q fiber closed sep (stable x pre qx) t pay wire (BStarAcquireHistoryReturn.busy_end hp R)
    F turn d need yD (List.sublist_append_of_sublist_right backward) backSize backNom
  refine ⟨pre++suffix,tail,?_,BStarReplyService.join_busy hp R T,?_⟩
  · rw [W,E,List.append_assoc,A,←List.append_assoc]
  · dsimp only
    rw [BStarResetSchedule.run_append]
    exact U

end L4.BStarBitPostGateAck
