import Leader.L4.BStarBitCarry
import Leader.L4.BStarBitUniqueGate
import Leader.L4.BStarBitSelectingTrace
import Leader.L4.BStarReplyBack
import Leader.L4.BStarSeparatorRing

namespace L4.BStarBitAckParity
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

open BStarBitTerminalHealth BStarBitCarry

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

theorem selected_terminal_parity {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (old : Current hp base (fun j => S.getD j fall) len x (.busy bitOp (.out len)))
    (fresh : Current hp base (fun j => S.getD j fall) len (step x e) (.busy bitOp (.back len)))
    (q : Payload) (new : project (fun j => S.getD j fall) (step x e) len=.reply q) (H : HealthyBit q) :
    ∃ p C offer,
      project (fun j => S.getD j fall) x len=.forward p ∧ HealthyBit p ∧
      (C,.advance offer)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) ∧
      C.source.occurrence.val=10 ∧ HealthyBit offer ∧
      parity p=parity q := by
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
  have NG : gate bitOp C.source.occurrence (geometry g C.source.side)=false := by
    simp [gate,show C.source.occurrence.val≠1 by omega]
  obtain ⟨p,P,Q,par⟩ := offer_parity g raw C v sel Hv NG
  refine ⟨p,C,v,(congrArg (atCursor x) idx).trans ((old_read x e C.source).symm.trans P),
    Q,sel,tag,Hv,?_⟩
  exact par.trans (BStarBitParity.finish_parity v q Hv.1 Hv.2 D).symm

theorem terminal_raw_of_ack {base y : X} {hh : ∃ i,oldH6 B base i=true}
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
      parity p=parity f := by
  have nonacq : f.opcode.toNat≠acquire := H.2.symm ▸ (by decide : bitOp≠acquire)
  obtain ⟨q,Q,normal,F,E⟩ := BStarReplyBack.from_arrival hp C sep ret f H.1 nonacq bound
  obtain ⟨p,K,offer,P,hP,sel,at10,hO,par⟩ := selected_terminal_parity hp C turn (sep turn) old
    (busy_start hp ret) q Q ⟨F,(congrArg BitVec.toNat E).trans H.2⟩
  exact ⟨p,K,offer,P,hP,sel,at10,hO,par.trans (normal_parity normal H)⟩

open BStarBitUniqueGate BStarClearanceOffset BStarBitGateGeometry

/-- At a literal healthy BIT exit, the landed forward argument equals
the actual later selected reply on the same remaining tour. The old
gate index and all later addresses belong to one chart; it is not
necessary to assume a second-gate exclusion separately. -/
theorem exit_to_ack {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (j : Nat) (J : j<len)
    {out back : List (Fin n)} (turn : Fin n) (p f : Payload)
    (start : project (fun k=>S.getD k fall) x (j+1)=.forward p)
    (Out : BusyOnly hp base (fun k=>S.getD k fall) len bitOp x (.out (j+1)) out (.out len))
    (Ret : BusyOnly hp base (fun k=>S.getD k fall) len bitOp
      (step (BStarResetSchedule.run step x out) turn) (.back len) back (.back 0))
    (Ack : let y := BStarResetSchedule.run step (step (BStarResetSchedule.run step x out) turn) back (S.getD 0 fall).1
      bind (longGeometry B y) 0 (atSite y.long 0)=.reply f)
    (Hf : HealthyBit f)
    (Ord : (S.getD j fall).2=1 ∧ BStarH6Ordinal.oldOrdinal B base hh (S.getD j fall).1=4)
    (fixed : ∀ u v,out=u++v → ∀ a,oldH6 B (BStarResetSchedule.run step x u) a=oldH6 B base a)
    (initial : correct (oldH6 B base) hh 5 x) : parity p=parity f := by
  obtain ⟨terminal,_,_,T,hT,_,_,_,PT⟩ := terminal_raw_of_ack hp C sep turn back f
    (BStarAcquireHistoryReturn.busy_end hp Out) Ret Ack Hf
  have NG (u v : List (Fin n)) (E : out=u++v) (k : Nat) (H : j<k) (K : k≤len) :
      gate bitOp (S.getD k fall).2
        (longGeometry B (BStarResetSchedule.run step x u (S.getD k fall).1))=false := by
    let y := BStarResetSchedule.run step x u
    have ready := BStarNativeOffsetTrace.closed_word hp _ hh sep x u initial
      (fun a b W => funext (fixed a (b++v) (by rw [E,W,List.append_assoc])))
    have G : gate bitOp (S.getD j fall).2 (longGeometry B (y (S.getD j fall).1))=true := by
      rw [Ord.1]
      exact (bit_gate_iff hp hh (fixed u v E) ready _ 1).mpr ⟨rfl,Ord.2⟩
    apply Bool.eq_false_iff.mpr
    intro D
    have eq := chart_no_second_gate hp C (fixed u v E) ready (Nat.le_of_lt J) K G D
    omega
  obtain ⟨q,Q,_,E⟩ := busy_parity hp C sep Out j (j+1) len terminal rfl rfl
      (Nat.lt_succ_self j) (Nat.le_refl len) T hT NG
  exact (congrArg parity (Token.forward.inj (start.symm.trans Q))).trans (E.trans PT)

end L4.BStarBitAckParity
