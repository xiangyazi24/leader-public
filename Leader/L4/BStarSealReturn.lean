import Leader.L4.BStarSealParity
import Leader.L4.BStarStageTerminalHealth
import Leader.L4.BStarReplyBack

namespace L4.BStarSealReturn
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongLayout BStarLongDoor BStarLongTransport BStarLongEvents
open BStarLongRouting BStarResetQuiet BStarResetQuietTable BStarClearanceForward
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetMarkAdapter BStarResetRailRing BStarOwnerLaunchOrigin BStarGeneratedOwner
open BStarSeparatingRail BStarAcquireForwardTrace BStarSeparatorControl
open BStarSealParity

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- The actual physical turn at K10 lands the terminal SEAL reply with
the selected healthy offer's corresponding parity. -/
theorem turn_lands_polarity {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (_C : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (K : CommandClaim) (p : Payload)
    (idx : S.getD len fall=address e K.source)
    (at10 : K.source.occurrence.val=10) (dest : K.destination=none)
    (sel : (K,.advance p)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))
    (F : p.fault=0) (O : p.opcode.toNat=sealOp) :
    ∃ q : Payload, project (fun j=>S.getD j fall) (step x e) len=.reply q ∧
      q.fault=0 ∧ q.opcode.toNat=sealOp ∧ q.race=0 ∧ q.outcome=0 ∧ parity q=parity p := by
  let g := oldPair B x e
  let raw := ((x e).long,(x (rightNeighbor e)).long)
  have valid : K.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E _
    rw [E] at at10
    contradiction
  have landed := new_read B x e sep K.source
  change BStarLongToken.decode (readRaw _ K.source)=_ at landed
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) K.source valid] at landed
  change BStarLongToken.decode (readRaw (patchPair (longWork g raw) raw) K.source)=_ at landed
  rw [terminal_finish g raw K p dest sel,BStarLongToken.decode_encode] at landed
  have vEq : carried g raw K p=p := by
    have N : K.source.occurrence.val≠1 := by omega
    unfold carried BStarLongArithmetic.visit
    have M : (K.source.occurrence.val != 1)=true := bne_iff_ne.mpr N
    simp only [M,Bool.true_or,if_true]
    rw [BStarLongOutgoing.noncenter_hold _ _ _ _ N]
    rfl
  change finish (carried g raw K p)=atCursor (step x e) (address e K.source) at landed
  rw [vEq,←idx] at landed
  obtain ⟨q,Q,hq,op,race,out,par⟩ := finish_keeps_polarity p F O
  exact ⟨q,landed.symm.trans Q,hq,op,race,out,par⟩

/-- The actual healthy SEAL ACK's low bit equals its own selected
terminal offer's low bit through an arbitrary actual return word.
No eventual BIT launch or COMMIT is used. -/
theorem terminal_to_actual_ack {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (e : Fin n) (K : CommandClaim) (p f : Payload)
    (idx : S.getD len fall=address e K.source)
    (at10 : K.source.occurrence.val=10) (dest : K.destination=none)
    (sel : (K,.advance p)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))
    (F : p.fault=0) (O : p.opcode.toNat=sealOp)
    (back : List (Fin n))
    (ret : BusyOnly hp base (fun j=>S.getD j fall) len sealOp (step x e) (.back len) back (.back 0))
    (ack : let y := play (step x e) back (S.getD 0 fall).1
      bind (longGeometry B y) 0 (atSite y.long 0)=.reply f)
    (hF : f.fault=0) (hO : f.opcode.toNat=sealOp) : parity f=parity p := by
  obtain ⟨q,Q,qF,qO,qR,qU,P⟩ :=
    turn_lands_polarity hp C e (sep e) K p idx at10 dest sel F O
  have notAcquire : f.opcode.toNat≠acquire := hO.symm ▸ (by decide : sealOp≠acquire)
  obtain ⟨q',Y,A,_,_⟩ := BStarReplyBack.from_arrival hp C sep ret f hF notAcquire ack
  have eq := Token.reply.inj (Y.symm.trans Q)
  subst q'
  obtain ⟨v,V,_,_,_,_,Ve⟩ :=
    bind_keeps_reply_polarity (longGeometry B (x e)) 0 q qF qO qR qU
  change BStarReplyBack.normal q=.reply v at V
  have equality := Token.reply.inj (A.symm.trans V)
  exact (congrArg parity equality).trans (Ve.trans P)

end L4.BStarSealReturn
