import Leader.L4.BStarStageTerminalHealth
import Leader.L4.BStarBitSelectingTrace
import Leader.L4.BStarReplyBack
import Leader.L4.BStarSeparatorRing

namespace L4.BStarBitTerminalHealth
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongLayout BStarLongDoor BStarLongTransport BStarLongEvents
open BStarLongRouting BStarResetQuiet BStarResetQuietTable BStarClearanceForward
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetMarkAdapter BStarResetRailRing BStarOwnerLaunchOrigin BStarGeneratedOwner
open BStarSeparatingRail BStarAcquireForwardTrace BStarSeparatorControl
open BStarSeparatorTags BStarSeparatorJoinedTags BStarResetChartService BStarSeparatorQuiet
open BStarStageProvenance BStarNativeActualLoadAccepted BStarCommitReceiptAuth

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

def HealthyBit (p : Payload) : Prop := p.fault=0 ∧ p.opcode.toNat=bitOp

private theorem finish_health (p q : Payload) (R : finish p=.reply q) (H : HealthyBit q) :
    HealthyBit p := by
  unfold finish at R
  dsimp only at R
  split at R
  · change (.reply _ : Token)=.reply q at R
    cases R
    exact ((show (1 : BitVec 1)≠0 by decide) H.1).elim
  · rename_i N
    have healthy : p.fault=0 := by
      apply Classical.byContradiction
      intro ne
      exact N (bne_iff_ne.mpr ne)
    split at R
    · rename_i A
      have op : p.opcode.toNat=acquire := beq_iff_eq.mp A
      split at R <;> cases R <;> exact False.elim ((by decide : acquire≠bitOp) (op.symm.trans H.2))
    · split at R
      · change (.reply _ : Token)=.reply q at R
        cases R
        exact ((show (1 : BitVec 1)≠0 by decide) H.1).elim
      · cases R
        exact ⟨healthy,H.2⟩

theorem selected_terminal_health {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (old : Current hp base (fun j => S.getD j fall) len x (.busy bitOp (.out len)))
    (fresh : Current hp base (fun j => S.getD j fall) len (step x e) (.busy bitOp (.back len)))
    (q : Payload) (new : project (fun j => S.getD j fall) (step x e) len=.reply q) (H : HealthyBit q) :
    ∃ p C offer,
      project (fun j => S.getD j fall) x len=.forward p ∧ HealthyBit p ∧
      (C,.advance offer)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) ∧
      C.source.occurrence.val=10 ∧ HealthyBit offer ∧
      offer.argument.toNat%2=q.argument.toNat%2 := by
  obtain ⟨C,v,sel,kind,dest,tag,idx⟩ := BStarStageTerminalHealth.selected_turn hp chart e sep bitOp old fresh
  let g := oldPair B x e
  let raw := ((x e).long,(x (rightNeighbor e)).long)
  have D := (new_read B x e sep C.source).trans
    ((congrArg (atCursor (step x e)) idx).symm.trans new)
  have valid : C.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E _
    rw [E] at tag
    contradiction
  change BStarLongToken.decode (readRaw _ C.source)=_ at D
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) C.source valid] at D
  change BStarLongToken.decode (readRaw (patchPair (longWork g raw) raw) C.source)=.reply q at D
  rw [terminal_finish g raw C v dest sel,BStarLongToken.decode_encode] at D
  have vEq : carried g raw C v=v := by
    have N : C.source.occurrence.val≠1 := by omega
    unfold carried BStarLongArithmetic.visit
    have M : (C.source.occurrence.val != 1)=true := bne_iff_ne.mpr N
    simp only [M,Bool.true_or,if_true]
    rw [BStarLongOutgoing.noncenter_hold _ _ _ _ N]
    rfl
  change finish (carried g raw C v)=.reply q at D
  rw [vEq] at D
  have Hv := finish_health v q D H
  obtain ⟨p,P,Q,op⟩ := BStarForwardProvenance.offer_origin g raw C v sel Hv.1
  refine ⟨p,C,v,(congrArg (atCursor x) idx).trans ((old_read x e C.source).symm.trans P),
    ⟨Q,(congrArg BitVec.toNat op).trans Hv.2⟩,sel,tag,Hv,?_⟩
  exact (BStarBitParity.finish_parity v q Hv.1 Hv.2 D).symm

theorem normal_parity {p q : Payload} (R : BStarReplyBack.normal p=.reply q)
    (H : HealthyBit q) : p.argument.toNat%2=q.argument.toNat%2 := by
  have P : p.opcode.toNat=bitOp :=
    (congrArg BitVec.toNat (BStarReplyBack.normal_origin R H.1).2).trans H.2
  have Width : replyWidth p.opcode.toNat p.outcome.toNat p.argument.toNat=
        (if p.outcome.toNat=0 then some 1 else none) := by
    rw [P]
    by_cases Z : p.outcome.toNat=0
    · simp [replyWidth,bitOp,acquire,admit,Z]
    · by_cases O : p.outcome.toNat=1 <;> simp [replyWidth,bitOp,acquire,Z,O]
  unfold BStarReplyBack.normal at R
  rw [Width] at R
  split at R
  · cases R
    exact ((by decide : (1 : BitVec 1) ≠ 0) H.1).elim
  · by_cases Z : p.outcome.toNat=0
    · rw [if_pos Z] at R
      cases R
      unfold cropped low
      simp
    · rw [if_neg Z] at R
      cases R
      exact ((by decide : (1 : BitVec 1) ≠ 0) H.1).elim

/-- The actual healthy BIT ACK determines a healthy old outward
forward at the literal selected K10 turn. The returned parity agrees
with the selected terminal work payload, not an independent launch. -/
theorem terminal_of_ack {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (turn : Fin n) (back : List (Fin n)) (f : Payload)
    (old : Current hp base (fun j=>S.getD j fall) len y (.busy bitOp (.out len)))
    (ret : BusyOnly hp base (fun j=>S.getD j fall) len bitOp
      (step y turn) (.back len) back (.back 0))
    (bound : let x := BStarResetSchedule.run step (step y turn) back (S.getD 0 fall).1
      bind (longGeometry B x) 0 (atSite x.long 0)=.reply f)
    (H : HealthyBit f) :
    ∃ p K offer,
      project (fun j=>S.getD j fall) y len=.forward p ∧ HealthyBit p ∧
      (K,.advance offer)∈actualOffers (oldPair B y turn) ((y turn).long,(y (rightNeighbor turn)).long) ∧
      K.source.occurrence.val=10 ∧ HealthyBit offer ∧
      offer.argument.toNat%2=f.argument.toNat%2 := by
  have nonacq : f.opcode.toNat≠acquire := H.2.symm ▸ (by decide : bitOp≠acquire)
  obtain ⟨q,Q,normal,F,E⟩ := BStarReplyBack.from_arrival hp C sep ret f H.1 nonacq bound
  obtain ⟨p,K,offer,P,hP,sel,at10,hO,par⟩ := selected_terminal_health hp C turn (sep turn) old
    (busy_start hp ret) q Q ⟨F,(congrArg BitVec.toNat E).trans H.2⟩
  exact ⟨p,K,offer,P,hP,sel,at10,hO,par.trans (normal_parity normal H)⟩

/-- A needed BIT on the supplied actual COMMIT handoff has one literal
source/terminal/return history, and the terminal selected offer carries
the parity of its very own selecting reply. -/
theorem needed_commit_terminal {base old x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {rem rest : List (Fin n)} {mark center : Fin n}
    (H : CommitHandoff hp base old x (fun j=>S.getD j fall) len rem rest mark center)
    (need : H.descriptor.need=true) :
    let addr := fun j=>S.getD j fall
    let run := BStarResetSchedule.run step
    ∃ (start out back after : List (Fin n)) (issue turn ack : Fin n) (f q p : Payload),
      rem=start++issue::(out++turn::(back++ack::after)) ∧
      let issued := step (run x start) issue
      let atTurn := run issued out
      let atAck := run (step atTurn turn) back
      project addr issued 0=.forward q ∧ HealthyBit q ∧ q.race=0 ∧
      BusyOnly hp base addr len bitOp issued (.out 0) out (.out len) ∧
      project addr atTurn len=.forward p ∧ HealthyBit p ∧
      bind (longGeometry B (atAck (addr 0).1)) 0 (atSite (atAck (addr 0).1).long 0)=.reply f ∧
      ReceiptBank bitOp H.descriptor f H.bank ∧
      ∃ K offer, (K,.advance offer)∈actualOffers (oldPair B atTurn turn)
        ((atTurn turn).long,(atTurn (rightNeighbor turn)).long) ∧
        K.source.occurrence.val=10 ∧ HealthyBit offer ∧ offer.argument.toNat%2=f.argument.toNat%2 := by
  let K : (S.getD 0 fall).2=0 := congrArg Prod.snd C.root
  obtain ⟨start,out,back,after,issue,turn,ack,f,q,W,_,F,hq,opq,race,Out,_,ret,_,bound,hf,opf,A⟩ :=
    BStarBitSelectingTrace.needed_bit_route hp H K sep need
  obtain ⟨p,claim,offer,P,hp0,selected,tag,hO,par⟩ :=
    terminal_of_ack hp C sep turn back f (BStarAcquireHistoryReturn.busy_end hp Out) ret bound ⟨hf,opf⟩
  exact ⟨start,out,back,after,issue,turn,ack,f,q,p,W,F,⟨hq,opq⟩,race,Out,P,hp0,bound,A,claim,offer,
    selected,tag,hO,par⟩

end L4.BStarBitTerminalHealth
