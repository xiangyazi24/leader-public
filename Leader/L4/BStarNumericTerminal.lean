import Leader.L4.BStarNumericReturn

namespace L4.BStarNumericTerminal
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongLayout BStarLongDoor BStarLongTransport BStarLongEvents
open BStarLongRouting BStarResetQuiet BStarClearanceForward BStarLongArithmetic
open BStarNumericCarry BStarNumericReceipt BStarNumericReturn
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetMarkAdapter BStarResetRailRing BStarOwnerLaunchOrigin BStarGeneratedOwner BStarSeparatingRail BStarAcquireForwardTrace

theorem joined_terminal (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (C : CommandClaim) (v : Payload) (K : C.source.occurrence.val=10) (hd : C.destination=none) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let dst : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    (C,.advance v)∈actualOffers g raw → Numeric v → readK dst C.source=.reply (output v) := by
  dsimp only
  intro sel health
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have valid : C.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro X _
    rw [X] at K
    contradiction
  change decode (readRaw _ C.source)=_
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x C.source valid]
  rw [terminal_finish g raw C v hd sel,decode_encode]
  have V := visit_padding (geometry g C.source.side) C.source.occurrence (atOld raw C.source) v
    (Or.inl (by omega))
  rw [V]
  dsimp only
  rw [outgoing_numeric _ _ _ v health]
  exact finish_numeric v health

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

theorem selected_return {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {e : Fin n} {w : List (Fin n)}
    (T : BusyOnly hp base (fun j => S.getD j fall) len op (step x e) (.back len) w (.back 0))
    (C : CommandClaim) (v : Payload) (K : C.source.occurrence.val=10) (hd : C.destination=none)
    (addr : S.getD len fall=address e C.source)
    (sel : (C,.advance v)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))
    (health : Numeric v) :
    (∃ q, project (fun j => S.getD j fall) x len=.forward q ∧
      Numeric q ∧ q.opcode=v.opcode) ∧
    (let y := BStarResetSchedule.run step (step x e) w
     let g := longGeometry B (y (S.getD 0 fall).1)
     bind g 0 (atSite (y (S.getD 0 fall).1).long 0)=.reply (output v)) := by
  have raw := BStarForwardProvenance.offer_origin _ _ C v sel health.1
  obtain ⟨q,Q,F,O⟩ := raw
  have readQ := (congrArg (atCursor x) addr).trans ((old_read x e C.source).symm.trans Q)
  refine ⟨⟨q,readQ,⟨F,by rw [O]; exact health.2.1,by rw [O]; exact health.2.2⟩,O⟩,?_⟩
  have j := joined_terminal k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) C v K hd sel health
  have eq := (congrArg (atCursor (step x e)) addr).trans ((new_read B x e (sep e) C.source).symm.trans j)
  obtain ⟨i,I,F⟩ := BStarNumericReturn.busy_return_payload hp chart sep T (output v)
    ⟨health.1,fun g j => output_bind g j v health⟩ len rfl eq
  have i0 : i=0 := (Cursor.back.inj I).symm
  subst i
  have H := (BStarResetChartService.root_header hp chart (busy_start hp T).1.1).2
  change (S.getD 0 fall).2=0 at H
  change atSite _ (S.getD 0 fall).2=.reply (output v) at F
  rw [H] at F
  dsimp only
  exact (congrArg (BStarLongCommand.bind _ 0) F).trans (output_bind _ _ v health)

/-- Compose an authenticated outward word, literal healthy terminal
selection and return tape with the actual matching source receipt.
The selected terminal's health, not every digit's health, is the
remaining premise of this bridge. -/
theorem hit_outward {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {turn door : Fin n} {pre ret : List (Fin n)}
    (F : Found hp base (fun j => S.getD j fall) len op x pre (.out len))
    (T : BusyOnly hp base (fun j => S.getD j fall) len op
      (step (BStarResetSchedule.run step x pre) turn) (.back len) ret (.back 0))
    (hit : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len
      (BStarResetSchedule.run step (step (BStarResetSchedule.run step x pre) turn) ret) door op)
    (C : CommandClaim) (v : Payload) (K : C.source.occurrence.val=10) (hd : C.destination=none)
    (addr : S.getD len fall=address turn C.source)
    (sel : let y := BStarResetSchedule.run step x pre
      (C,.advance v)∈actualOffers (oldPair B y turn) ((y turn).long,(y (rightNeighbor turn)).long))
    (health : Numeric v) :
    (output v).opcode.toNat=op ∧
    ∃ before launch after q, pre=before++launch::after ∧
      let y := step (BStarResetSchedule.run step x before) launch
      BusyOnly hp base (fun j => S.getD j fall) len op y (.out 0) after (.out len) ∧
      project (fun j => S.getD j fall) (BStarResetSchedule.run step y after) len=.forward q ∧
      Numeric q ∧ q.opcode=v.opcode := by
  obtain ⟨⟨q,Q,N,E⟩,R⟩ := selected_return hp chart sep T C v K hd addr sel health
  obtain ⟨_,_,_,_,_,f,B0,_Fh,O⟩ := hit
  have Eq := Token.reply.inj (R.symm.trans B0)
  refine ⟨Eq ▸ O,?_⟩
  obtain ⟨u,w,e,split,_,_,_,P⟩ := F
  have Y : BStarResetSchedule.run step x pre =
      BStarResetSchedule.run step (step (BStarResetSchedule.run step x u) e) w := by
    rw [split,BStarResetSchedule.run_append]
    rfl
  exact ⟨u,e,w,q,split,P,Y ▸ Q,N,E⟩

#print axioms joined_terminal
#print axioms selected_return
#print axioms hit_outward
end L4.BStarNumericTerminal
