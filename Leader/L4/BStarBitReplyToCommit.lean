import Leader.L4.BStarBitPositiveTerminal

namespace L4.BStarBitReplyToCommit
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarGeneratedOwner
open BStarOwnerLaunchOrigin BStarAcquireForwardTrace BStarAcquireHistorySample BStarResetChartService
open BStarBitHealthyService BStarLongDoor BStarLongLayout BStarCommitChoiceHistory

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- A terminal-ready canonical BIT on the actual replay is enough:
the nominated turn, backward links and incoming root edge as a
subsequence force its real ACK, and schedule the parity-selected 411.
No supplied healthy ACK, COMMIT body event or successful completion. -/
theorem schedule_commit_of_sublist {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (t : Fin n) (pay : Payload) (wire : Wire pay)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out len)))
    (old : project (fun j=>S.getD j fall) x len=.forward pay)
    (turn : ∀ y : X,Q y→onTerminal hp y t (fun j=>S.getD j fall) len)
    (d : BStarLongPublication.Descriptor) (need : d.need=true)
    (desc : BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d)
    {ls w : List (Fin n)} (sub : (t::(ls++[RearTrace.predecessor (S.getD 0 fall).1])).Sublist w)
    (size : len≤ls.length)
    (nom : ∀ k (K : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun a=>S.getD a fall) len (ls.length-(k+1))) :
    ∃ pre tail, w=pre++RearTrace.predecessor (S.getD 0 fall).1::tail ∧
      BusyOnly hp base (fun j=>S.getD j fall) len bitOp x (.out len) pre (.back 0) ∧
      let y := play x pre
      let ack := RearTrace.predecessor (S.getD 0 fall).1
      let fresh := (step y ack (S.getD 0 fall).1).long
      Event hp (fun j=>S.getD j fall) len y ack (.busy bitOp (.back 0)) .idle ∧
      Current hp base (fun j=>S.getD j fall) len (step y ack) .idle ∧
      (ctrlOp.read fresh).toNat=commitOp ∧
      BStarLongPublication.decode (sourceDescriptor.read fresh)=some d ∧
      choice.read fresh=BitVec.ofNat 2 (pick d pay).val := by
  obtain ⟨first,rest,W,hit,R⟩ := List.cons_sublist_iff.mp sub
  obtain ⟨wait,e,after,T,phase,D⟩ :=
    BStarBitPositiveTerminal.turns_in_word hp C Q fiber closed sep first t hit turn qx pay wire cur old
  let front := wait++[e]
  let y := play x front
  have stable (x : X) (u : List (Fin n)) (H : Q x) : Q (play x u) := by
    induction u generalizing x with
    | nil => exact H
    | cons a u ih => exact ih (step x a) (closed _ H a)
  have qY : Q y := stable x front qx
  obtain ⟨pre,tail,actual,busy,bound,ackCur,ack,ready⟩ :=
    BStarReplyService.reaches_consume hp C Q fiber closed sep
      qY bitOp len pay (BStarBitPositiveTerminal.bit_normal pay wire)
      (BStarAcquireHistoryReturn.busy_end hp phase) D (List.sublist_append_of_sublist_right R) size nom
  have Full := BStarReplyService.join_busy hp phase busy
  have align : play x (front++pre)=play y pre := BStarResetSchedule.run_append step x front pre
  have saved := (BStarSealBitDescriptor.busy_preserves_descriptor hp C sep Full (by decide)).1
  have oldDesc : BStarLongPublication.decode (sourceDescriptor.read ((play y pre) (S.getD 0 fall).1).long)=some d := by
    rw [align] at saved
    exact (congrArg BStarLongPublication.decode saved).trans desc
  have H := root_header hp C ackCur.1.1
  obtain ⟨pc,target,choice,_,_⟩ := BStarBitCommitLegal.actual_bit_ack_allows hp
    (base:=base) (x:=play y pre) (addr:=fun j=>S.getD j fall) H.2 H.1 (sep _)
    ackCur ack d pay wire.fault wire.op bound oldDesc need
  refine ⟨front++pre,tail,?_,Full,?_⟩
  · change w=(wait++[e])++pre++RearTrace.predecessor (S.getD 0 fall).1::tail
    rw [W,T]
    simpa only [List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using
      congrArg (fun u => wait++e::u) actual
  · dsimp only
    rw [align]
    exact ⟨ack,ready,pc,target,choice⟩

end L4.BStarBitReplyToCommit
