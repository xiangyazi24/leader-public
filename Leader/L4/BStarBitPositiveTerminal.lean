import Leader.L4.BStarBitHealthyIdle
import Leader.L4.BStarReplyService
import Leader.L4.BStarSealBitDescriptor

namespace L4.BStarBitPositiveTerminal
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarLongTransport BStarLongRouting
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarGeneratedOwner
open BStarOwnerLaunchOrigin BStarAcquireForwardTrace BStarAcquireHistorySample
open BStarLongFixedRouting BStarResetChartService BStarResetQuiet BStarResetQuietTable
open BStarBitHealthyService BStarLongDoor
open BStarClearanceForward

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem crop_self (p : Payload) (H : Wire p) : cropped p 1=p := by
  have argEq : BitVec.ofNat 34 (low p.argument.toNat 1)=p.argument := by
    rw [show low p.argument.toNat 1=p.argument.toNat from Nat.mod_eq_of_lt H.small]
    simp
  cases p
  simp_all [cropped]

theorem bit_normal (p : Payload) (H : Wire p) :
    BStarReplyBack.normal p=.reply p := by
  have D : BStarReplyBack.normal p=.reply (cropped p 1) := by
    simp [BStarReplyBack.normal,H.fault,H.op,H.race,H.outcome,replyWidth,bitOp,acquire,admit]
  exact D.trans (congrArg Token.reply (crop_self p H))

theorem bit_finish (p : Payload) (H : Wire p) : finish p=.reply p := by
  have Z : {p with race:=0,outcome:=0}=p := by
    have A:=H.race
    have C:=H.outcome
    cases p
    simp_all
  rw [BStarBitParity.finish_bit p H.fault H.op]
  change Token.reply (cropped {p with race:=0,outcome:=0} 1)=_
  rw [Z,crop_self p H]

/-- Positive real turning mark: a canonical BIT at the terminal is
selected by the nominated mark, and its exact packet starts the
return. No healthy terminal reply is assumed. -/
theorem nominated_turn {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (e : Fin n) (pay : Payload) (wire : Wire pay)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out len)))
    (old : project (fun j=>S.getD j fall) x len=.forward pay)
    (mark : onTerminal hp x e (fun j=>S.getD j fall) len) :
    Event hp (fun j=>S.getD j fall) len x e (.busy bitOp (.out len)) (.busy bitOp (.back len)) ∧
    Current hp base (fun j=>S.getD j fall) len (step x e) (.busy bitOp (.back len)) ∧
      project (fun j=>S.getD j fall) (step x e) len=.reply pay := by
  obtain ⟨K,mem,kind,dest,at10,idx⟩ := mark
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have addr : readK raw K.source=.forward pay :=
    (BStarResetRailRing.old_read x e K.source).trans ((congrArg (atCursor x) idx).symm.trans old)
  have nonGate : gate bitOp K.source.occurrence (geometry g K.source.side)=false := by simp [gate,at10]
  have isNotDoor : K.kind≠.door := by rw [kind]; decide
  have sw : forwardWidth bitOp pay.argument.toNat=some 1 := by simp [forwardWidth,bitOp,admit]
  have sel := raw_bit_selected g raw K pay mem isNotDoor wire.fault wire.op wire.race wire.outcome sw addr nonGate
  rw [crop_self pay wire] at sel
  have valid : K.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro J _
    rw [J] at at10
    contradiction
  have lands := BStarResetRailRing.new_read B x e (sep e) K.source
  change BStarLongToken.decode (readRaw _ K.source)=_ at lands
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) K.source valid] at lands
  change BStarLongToken.decode (readRaw (patchPair (longWork g raw) raw) K.source)=_ at lands
  rw [terminal_finish g raw K pay dest sel,BStarLongToken.decode_encode] at lands
  change finish (carried g raw K pay)=atCursor (step x e) (address e K.source) at lands
  rw [BStarBitCarry.carried_bit _ _ _ _ wire.op,bit_finish pay wire,←idx] at lands
  obtain ⟨m,E,I⟩ := current_step hp C Q fiber closed sep qx e (.busy bitOp (.out len)) cur
  cases E with
  | transit _ _ d live seen =>
    cases seen with
    | cons M go A G tail =>
      cases tail
      cases A with
      | stay _ =>
        obtain ⟨q,U⟩ := I.2.1.2.1
        exact Token.noConfusion (U.symm.trans lands.symm)
      | forward _ =>
        have bound := I.2.1.1
        omega
      | turn =>
        exact ⟨.transit _ _ _ live (.cons M go .turn G (.nil _ _)),I,lands.symm⟩

/-- Every other raw mark really stutters at the K10 terminal. -/
theorem terminal_hold {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (e : Fin n) (pay : Payload) (wire : Wire pay)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out len)))
    (old : project (fun j=>S.getD j fall) x len=.forward pay)
    (miss : ¬ onTerminal hp x e (fun j=>S.getD j fall) len) :
    Event hp (fun j=>S.getD j fall) len x e (.busy bitOp (.out len)) (.busy bitOp (.out len)) ∧
    Current hp base (fun j=>S.getD j fall) len (step x e) (.busy bitOp (.out len)) ∧
    project (fun j=>S.getD j fall) (step x e) len=.forward pay := by
  have K10 : (S.getD len fall).2=10 := congrArg Prod.snd C.terminal
  have away : gate bitOp (S.getD len fall).2 (longGeometry B (x (S.getD len fall).1))=false := by
    rw [K10]
    rfl
  have noL : ¬ linkAt hp x e (fun j=>S.getD j fall) len len := fun K=>Nat.lt_irrefl _ K.1
  have carry := (BStarBitHealthyIdle.silent_at_bit hp C e (sep e) bitOp len cur.1 pay cur.2.1
    old wire away noL (fun _=>miss)).2
  change project (fun j=>S.getD j fall) (step x e) len=project (fun j=>S.getD j fall) x len at carry
  have D := carry.trans old
  obtain ⟨m,E,I⟩ := current_step hp C Q fiber closed sep qx e (.busy bitOp (.out len)) cur
  cases E with
  | transit _ _ d live seen =>
    cases seen with
    | cons M go A G tail =>
      cases tail
      cases A with
      | stay _ => exact ⟨.transit _ _ _ live (.cons M go (.stay _) G (.nil _ _)),I,D⟩
      | forward _ =>
        have bound := I.2.1.1
        omega
      | turn =>
        obtain ⟨q,R⟩ := I.2.1.2.1
        exact Token.noConfusion (D.symm.trans R)

open BStarResetChartNomination BStarSeparatingProgress BStarAcquireRailCoverage

/-- The terminal nomination exists structurally; no terminal health or
later receipt is used to name the physical raw mark. -/
theorem nominate_terminal {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true) :
    ∃ e, ∀ y : X, (∀ i,Layout B base i=Layout B y i) →
      onTerminal hp y e (fun j=>S.getD j fall) len := by
  obtain ⟨e,N⟩ := nominate hp C head cont len (Nat.le_refl _)
  exact ⟨e,fun y H=>(mem_terminal hp y e _ len).mp (by simpa using N y H)⟩

/-- After K10 is reached, any raw word containing a fixed actual turn
nomination has a prefix that really performs the turn. The packet
and validity survive arbitrary earlier spectator marks. -/
theorem turns_in_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (t : Fin n) (ht : t∈w)
    (nom : ∀ y : X,Q y→onTerminal hp y t (fun j=>S.getD j fall) len)
    (qx : Q x) (pay : Payload) (wire : Wire pay)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out len)))
    (old : project (fun j=>S.getD j fall) x len=.forward pay) :
    ∃ wait e tail, w=wait++e::tail ∧
      BusyOnly hp base (fun j=>S.getD j fall) len bitOp x (.out len) (wait++[e]) (.back len) ∧
      project (fun j=>S.getD j fall) (play x (wait++[e])) len=.reply pay := by
  induction w generalizing x with
  | nil => simp at ht
  | cons e w ih =>
    by_cases H : onTerminal hp x e (fun j=>S.getD j fall) len
    · obtain ⟨E,I,P⟩ := nominated_turn hp C Q fiber closed sep qx e pay wire cur old H
      exact ⟨[],e,w,rfl,.cons cur E (.nil I),P⟩
    · have absent : t≠e := by
        intro K
        subst e
        exact H (nom x qx)
      have W := (List.mem_cons.mp ht).resolve_left absent
      obtain ⟨E,I,P⟩ := terminal_hold hp C Q fiber closed sep qx e pay wire cur old H
      obtain ⟨u,a,v,split,R,reply⟩ := ih W (closed _ qx e) I P
      exact ⟨e::u,a,v,congrArg (List.cons e) split,.cons cur E R,reply⟩

end L4.BStarBitPositiveTerminal
