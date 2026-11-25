import Leader.L4.BStarSealPostCenterReplay
import Leader.L4.BStarSealHealthyIdle
import Leader.L4.BStarPositiveReply

namespace L4.BStarSealPositiveTerminal
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarLongTransport BStarLongRouting
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarGeneratedOwner
open BStarOwnerLaunchOrigin BStarAcquireForwardTrace BStarAcquireHistorySample
open BStarLongFixedRouting BStarResetChartService BStarResetQuiet BStarResetQuietTable
open BStarSealHealthyHop BStarLongDoor
open BStarClearanceForward

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- The terminal reduces the acknowledged SEAL packet to its canonical low bit. -/
def sealReply (p : Payload) : Payload :=
  {p with argument:=BitVec.ofNat 34 (p.argument.toNat%2)}

theorem seal_finish (p : Payload) (H : Well p) : finish p=.reply (sealReply p) := by
  simp [finish,H.fault,H.opcode,H.race,H.outcome,sealReply,replyWidth,sealOp,admit,bitOp,acquire,cropped,low]

theorem seal_normal (p : Payload) (H : Well p) :
    BStarReplyBack.normal (sealReply p)=.reply (sealReply p) := by
  have A : (BitVec.ofNat 34 (p.argument.toNat%2)).toNat=p.argument.toNat%2 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have U := Nat.mod_lt p.argument.toNat (by decide : 0<2)
    omega
  simp [BStarReplyBack.normal,H.fault,H.opcode,H.race,H.outcome,sealReply,replyWidth,sealOp,
    admit,bitOp,acquire,cropped,low,A]

/-- Positive real turning mark: a canonical SEAL at the terminal is
selected by the nominated mark, and its canonical low-bit packet starts the
return. No healthy terminal reply is assumed. -/
theorem nominated_turn {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (e : Fin n) (pay : Payload) (wire : Well pay)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy sealOp (.out len)))
    (old : project (fun j=>S.getD j fall) x len=.forward pay)
    (mark : onTerminal hp x e (fun j=>S.getD j fall) len) :
    Event hp (fun j=>S.getD j fall) len x e (.busy sealOp (.out len)) (.busy sealOp (.back len)) ∧
    Current hp base (fun j=>S.getD j fall) len (step x e) (.busy sealOp (.back len)) ∧
      project (fun j=>S.getD j fall) (step x e) len=.reply (sealReply pay) := by
  obtain ⟨K,mem,kind,dest,at10,idx⟩ := mark
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have addr : readK raw K.source=.forward pay :=
    (BStarResetRailRing.old_read x e K.source).trans ((congrArg (atCursor x) idx).symm.trans old)
  have sel := selected_well g raw K pay mem (by rw [kind]; decide) wire addr
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
  have eq : carried g raw K pay=pay := by
    unfold carried BStarLongArithmetic.visit
    have M : (K.source.occurrence.val != 1)=true := bne_iff_ne.mpr (by omega)
    simp only [M,Bool.true_or,if_true]
    rw [BStarLongOutgoing.noncenter_hold _ _ _ _ (by omega)]
    rfl
  rw [eq,seal_finish pay wire,←idx] at lands
  obtain ⟨m,E,I⟩ := current_step hp C Q fiber closed sep qx e (.busy sealOp (.out len)) cur
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
    (qx : Q x) (e : Fin n) (pay : Payload) (wire : Well pay)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy sealOp (.out len)))
    (old : project (fun j=>S.getD j fall) x len=.forward pay)
    (miss : ¬ onTerminal hp x e (fun j=>S.getD j fall) len) :
    Event hp (fun j=>S.getD j fall) len x e (.busy sealOp (.out len)) (.busy sealOp (.out len)) ∧
    Current hp base (fun j=>S.getD j fall) len (step x e) (.busy sealOp (.out len)) ∧
    project (fun j=>S.getD j fall) (step x e) len=.forward pay := by
  have noL : ¬ linkAt hp x e (fun j=>S.getD j fall) len len := fun K=>Nat.lt_irrefl _ K.1
  have carry := (BStarSealHealthyIdle.silent_at_seal hp C e (sep e) sealOp len cur.1 pay cur.2.1
    old wire noL (fun _=>miss)).2
  change project (fun j=>S.getD j fall) (step x e) len=project (fun j=>S.getD j fall) x len at carry
  have D := carry.trans old
  obtain ⟨m,E,I⟩ := current_step hp C Q fiber closed sep qx e (.busy sealOp (.out len)) cur
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
    (qx : Q x) (pay : Payload) (wire : Well pay)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy sealOp (.out len)))
    (old : project (fun j=>S.getD j fall) x len=.forward pay) :
    ∃ wait e tail, w=wait++e::tail ∧
      BusyOnly hp base (fun j=>S.getD j fall) len sealOp x (.out len) (wait++[e]) (.back len) ∧
      project (fun j=>S.getD j fall) (play x (wait++[e])) len=.reply (sealReply pay) := by
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

private theorem split_sublist_end {α : Type} {u w : List α} {e : α}
    (T : (u++[e]).Sublist w) : ∃ a b,w=a++e::b ∧ u.Sublist a := by
  induction w generalizing u with
  | nil =>
    have L := T.length_le
    simp at L
  | cons a w ih =>
    cases u with
    | nil =>
      have E : e∈a::w := T.subset (by simp)
      obtain ⟨p,q,W,_⟩ := List.eq_append_cons_of_mem E
      exact ⟨p,q,W,List.nil_sublist _⟩
    | cons b u =>
      cases T with
      | cons _ T =>
        obtain ⟨p,q,E,before⟩ := ih T
        exact ⟨a::p,q,congrArg (List.cons a) E,before.cons a⟩
      | cons_cons _ T =>
        obtain ⟨p,q,E,before⟩ := ih T
        exact ⟨a::p,q,congrArg (List.cons a) E,before.cons_cons a⟩

private theorem join_busy {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {u v : List (Fin n)} {z a d : Cursor}
    (P : BusyOnly hp base addr len op x z u a)
    (R : BusyOnly hp base addr len op (play x u) a v d) :
    BusyOnly hp base addr len op x z (u++v) d := by
  induction P with
  | nil _ => exact R
  | cons I E _ ih => exact .cons I E (ih R)

open BStarSealPostCenterReplay

/-- A single arbitrary raw replay containing the nominated outward
links and terminal mark reaches the first real turn, with the exact
canonical low-bit SEAL reply ready for generic positive return. -/
theorem turns_of_sublist {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (c : Nat) (cL : c<len) (centerK : (S.getD c fall).2=1)
    (centerH : oldH6 B base (S.getD c fall).1=true)
    (j : Nat) (after : c<j) (J : j≤len) (qx : Q x)
    (pay : Payload) (well : Well pay)
    (cur : Current hp base (fun t=>S.getD t fall) len x (.busy sealOp (.out j)))
    (old : project (fun t=>S.getD t fall) x j=.forward pay)
    {ls w : List (Fin n)} (terminal : Fin n)
    (sub : (ls++[terminal]).Sublist w) (size : j+ls.length=len)
    (nom : ∀ k (hk : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y ls[k] (fun t=>S.getD t fall) len (j+k))
    (termNom : ∀ y : X,Q y→onTerminal hp y terminal (fun t=>S.getD t fall) len) :
    ∃ pre wait e tail, w=pre++wait++e::tail ∧
      BusyOnly hp base (fun t=>S.getD t fall) len sealOp x (.out j) pre (.out len) ∧
      BusyOnly hp base (fun t=>S.getD t fall) len sealOp x (.out j) (pre++wait++[e]) (.back len) ∧
      project (fun t=>S.getD t fall) (play x (pre++wait++[e])) len=.reply (sealReply pay) ∧
      BStarReplyBack.normal (sealReply pay)=.reply (sealReply pay) := by
  obtain ⟨u,v,W,Ssub⟩ := split_sublist_end sub
  obtain ⟨pre,rest,E,P,F⟩ := reaches_terminal_of_sublist hp C Q fiber closed sep c cL centerK centerH
    pay well Ssub x j j size (Nat.le_refl _) J after qx cur old nom
  let z := play x pre
  have qrun (w : List (Fin n)) (y : X) (q : Q y) : Q (play y w) := by
    induction w generalizing y with
    | nil => exact q
    | cons e w ih => exact ih (step y e) (closed _ q e)
  have hit : terminal∈rest++terminal::v := List.mem_append_right _ List.mem_cons_self
  obtain ⟨wait,e,tail,Z,T,R⟩ := turns_in_word hp C Q fiber closed sep (rest++terminal::v)
    terminal hit termNom (qrun pre x qx) pay well (BStarAcquireHistoryReturn.busy_end hp P) F
  refine ⟨pre,wait,e,tail,?_,P,?_,?_,seal_normal pay well⟩
  · rw [W,E,List.append_assoc,Z,←List.append_assoc]
  · rw [List.append_assoc]
    exact join_busy hp P T
  · rw [List.append_assoc,BStarResetSchedule.run_append]
    exact R

end L4.BStarSealPositiveTerminal
