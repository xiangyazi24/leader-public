import Leader.L4.BStarBitHealthyService
import Leader.L4.BStarBitDepartRing
import Leader.L4.BStarBitFollowRing

namespace L4.BStarBitGateService
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken BStarLongCommand
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarClearanceOffset BStarBitGateGeometry BStarClearanceRaceMark
open BStarBitParity BStarBitDepart BStarBitHealthyService
open BStarResetChartNomination BStarAcquireRailCoverage BStarSeparatingProgress BStarLongLiteral

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem gate_bind (g : LongGeometry) (v : Payload)
    (G : gate bitOp 1 g=true) (F : v.fault=0) (P : v.opcode.toNat=bitOp) (O : v.outcome=0)
    (A : v.argument=0) (R : 1≤v.race.toNat ∧ v.race.toNat≤5) :
    BStarLongCommand.bind g 1 (.forward v)=.forward v := by
  cases v
  simp_all [BStarLongCommand.bind,bitOp,forwardWidth,admit,cropped,low]

private theorem infer_cursor {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (e : Fin n) (k j : Nat) (K : k<len) (J : j≤len)
    (I : Current hp base (fun t=>S.getD t fall) len x (.busy bitOp (.out k)))
    (v : Payload) (V : project (fun t=>S.getD t fall) (step x e) j=.forward v) :
    Event hp (fun t=>S.getD t fall) len x e (.busy bitOp (.out k)) (.busy bitOp (.out j)) ∧
      Current hp base (fun t=>S.getD t fall) len (step x e) (.busy bitOp (.out j)) := by
  obtain ⟨m,ev,U⟩ := current_step hp C Q fiber closed sep qx e (.busy bitOp (.out k)) I
  cases ev with
  | transit _ _ d live seen =>
    cases seen with
    | cons M go adv gd tail =>
      cases tail
      have endOut : ∃ u,d=.out u := by cases adv with
        | stay => exact ⟨_,rfl⟩
        | forward => exact ⟨_,rfl⟩
        | turn => exact (Nat.lt_irrefl _ K).elim
      obtain ⟨u,E⟩ := endOut
      subst d
      have eq := (BStarOwnerControlHistory.pointed_unique_forward _ len u U.2.1 U.2.2 j J).mp ⟨v,V⟩
      subst u
      exact ⟨.transit _ _ _ live (.cons M go adv gd (.nil _ _)),U⟩

/-- Both controlled first-side orders are possible. From the actual
pending gate, first, opposite and then outgoing generate a clean BIT
at the real successor and positively advance the actual cursor. -/
theorem handshake {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1))
    (O : oldOrdinal B base hh i=4) (q : Q x) (ready : correct (oldH6 B base) hh 5 x)
    (I : Current hp base (fun t=>S.getD t fall) len x (.busy bitOp (.out k)))
    (v : Payload) (old : atSite (x i).long 1=.forward v)
    (F : v.fault=0) (op : v.opcode.toNat=bitOp) (outcome : v.outcome=0)
    (arg : v.argument=0) (race : v.race=1)
    (s t : Side) (opp : t≠s) :
    let marks := [incident i s,incident i t,i]
    let pay := cleanBit v s
    BusyOnly hp base (fun j=>S.getD j fall) len bitOp x (.out k) marks (.out (k+1)) ∧
      Current hp base (fun j=>S.getD j fall) len (play x marks) (.busy bitOp (.out (k+1))) ∧
      project (fun j=>S.getD j fall) (play x marks) (k+1)=.forward pay ∧
      Wire pay := by
  dsimp only
  let x₁ := step x (incident i s)
  let x₂ := step x₁ (incident i t)
  have fixed (y : X) (hy : Q y) : ∀ j,oldH6 B y j=oldH6 B base j :=
    fun j => (congrArg Prod.fst (fiber y hy j)).symm
  have advanceReady (y : X) (hy : Q y) (e : Fin n) (H : correct (oldH6 B base) hh 5 y) :
      correct (oldH6 B base) hh 5 (step y e) :=
    stable hp _ hh y e (sep e) (fixed y hy) (BStarClearanceOffsetMask.leftFrame hp y e) H
  have q₁ : Q x₁ := closed _ q _
  have q₂ : Q x₂ := closed _ q₁ _
  have r₁ := advanceReady x q (incident i s) ready
  have r₂ := advanceReady x₁ q₁ (incident i t) r₁
  have getBound (y : X) (hy : Q y) (R : correct (oldH6 B base) hh 5 y)
      (w : Payload) (old : atSite (y i).long 1=.forward w)
      (hf : w.fault=0) (ho : w.opcode.toNat=bitOp) (hu : w.outcome=0) (ha : w.argument=0)
      (hr : 1≤w.race.toNat ∧ w.race.toNat≤5) :
      BStarLongCommand.bind (longGeometry B (y i)) 1 (atSite (y i).long 1)=.forward w := by
    rw [old]
    exact gate_bind _ _ ((bit_gate_iff hp hh (fixed y hy) R i 1).mpr ⟨rfl,O⟩) hf ho hu ha hr
  have raw (y : X) (w : Payload) (V : atSite (y i).long 1=.forward w) :
      project (fun j=>S.getD j fall) y k=.forward w := by
    change atCursor y (S.getD k fall)=_
    rw [idx]
    exact V
  let v₁ := {v with race:=firstCode s}
  let v₂ := {v with race:=finalCode s}
  have V₁ : atSite (x₁ i).long 1=.forward v₁ :=
    (BStarBitFirstRing.first_mark hp C (fixed x q) ready sep i k idx O I v
      (getBound x q ready v old F op outcome arg (by rw [race]; decide)) F op race).1 s
  obtain ⟨E₁,I₁⟩ := infer_cursor hp C Q fiber closed sep q (incident i s) k k K
    (Nat.le_of_lt K) I v₁ (raw x₁ _ V₁)
  have V₂ : atSite (x₂ i).long 1=.forward v₂ := by
    have S := (BStarBitFollowRing.follow_mark hp C (fixed x₁ q₁) r₁ sep i k idx O I₁ v₁
      (getBound x₁ q₁ r₁ v₁ V₁ F op outcome arg (by change 1≤(firstCode s).toNat ∧ (firstCode s).toNat≤5; cases s <;> decide))
      F op s rfl).1 t
    rwa [if_neg opp] at S
  obtain ⟨E₂,I₂⟩ := infer_cursor hp C Q fiber closed sep q₁ (incident i t) k k K
    (Nat.le_of_lt K) I₁ v₂ (raw x₂ _ V₂)
  have Dep := (BStarBitDepartRing.depart_mark hp hh (fixed x₂ q₂) r₂ i (sep i) O s v₂
    (getBound x₂ q₂ r₂ v₂ V₂ F op outcome arg (by change 1≤(finalCode s).toNat ∧ (finalCode s).toNat≤5; cases s <;> decide))
    F op rfl).2
  obtain ⟨e,N⟩ := nominate hp C head cont k (Nat.le_of_lt K)
  obtain ⟨_,cmd,a,mem,dst,src,land⟩ := (mem_link hp x₂ e _ len k).mp
    (by simpa only [if_pos K] using N x₂ (fiber x₂ q₂))
  change S.getD k fall=address e cmd.source at src
  have tag : cmd.source.occurrence.val=1 := congrArg (fun a : Pos n=>a.2.val) (src.symm.trans idx)
  have same := center_of _ cmd mem tag
  rw [same] at src dst
  have ei : e=i := congrArg Prod.fst (src.symm.trans idx)
  subst e
  let k' : Fin 11 := if oldH6 B base (rightNeighbor i) then 2 else 1
  have ad : a=R k' := by
    apply Option.some.inj
    have hh'' : (oldPair B x₂ i).2.axes.h6=oldH6 B base (rightNeighbor i) := fixed x₂ q₂ _
    simpa only [centerLink,link,hh''] using dst.symm
  subst a
  have destWire : project (fun j=>S.getD j fall) (step x₂ i) (k+1)=.forward (cleanBit v s) := by
    change atCursor (step x₂ i) (S.getD (k+1) fall)=_
    change S.getD (k+1) fall=address i (R k') at land
    rw [land]
    exact Dep
  obtain ⟨E₃,I₃⟩ := infer_cursor hp C Q fiber closed sep q₂ i k (k+1) K
    (by omega) I₂ (cleanBit v s) destWire
  have W : Wire (cleanBit v s) := ⟨F,op,rfl,outcome,by change ((BitVec.ofBool (firstBit s)).zeroExtend 34).toNat<2; cases s <;> decide⟩
  exact ⟨.cons I E₁ (.cons I₁ E₂ (.cons I₂ E₃ (.nil I₃))),I₃,destWire,W⟩

end L4.BStarBitGateService
