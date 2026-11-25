import Leader.L4.BStarCommitServiceReplay
import Leader.L4.BStarBitCommitPublishes
import Leader.L4.BStarAcquireHistoryReturn

namespace L4.BStarCommitServiceCenter
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarCommitHealthyHop BStarCommitHealthyFlight BStarCommitService

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarLongLiteral BStarLongLayout BStarCommitServiceReplay
open BStarLongPublication BStarLongLandingFrame

/-- Reaching the owner center does not expose the canonical COMMIT to
any other mark. Its only structural departing claim is on its outgoing
physical edge. -/
theorem center_hold {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (l : Nat) (L : l<len) (center e : Fin n) (loc : S.getD l fall=(center,1))
    (other : e≠center) (qx : Q x) (pay : Payload) (well : Well pay)
    (cur : Current hp base (fun k=>S.getD k fall) len x (.busy commitOp (.out l)))
    (old : project (fun k=>S.getD k fall) x l=.forward pay) :
    Event hp (fun t=>S.getD t fall) len x e (.busy commitOp (.out l)) (.busy commitOp (.out l)) ∧
      Current hp base (fun t=>S.getD t fall) len (step x e) (.busy commitOp (.out l)) ∧
      project (fun t=>S.getD t fall) (step x e) l=.forward pay := by
  have notLink : ¬linkAt hp x e (fun t=>S.getD t fall) len l := by
    rintro ⟨_,K,a,mem,_,src,_⟩
    change S.getD l fall=address e K.source at src
    have tag : K.source.occurrence.val=1 := congrArg (fun q : Pos n => q.2.val) (src.symm.trans loc)
    rw [center_of _ K mem tag] at src
    exact other (congrArg Prod.fst (src.symm.trans loc))
  have hold := (BStarCommitHealthyIdle.silent_at_commit hp C e (sep e) commitOp l cur.1 pay
      cur.2.1 old well notLink (fun E => (Nat.ne_of_lt L E).elim)).2
  have F : project (fun t=>S.getD t fall) (step x e) l=.forward pay := hold.trans old
  obtain ⟨m,ev,nxt⟩ := current_step hp C Q fiber closed sep qx e (.busy commitOp (.out l)) cur
  cases ev with
  | transit _ _ d live seen =>
    cases seen with
    | cons M go adv gd tail =>
      cases tail
      cases adv with
      | stay => exact ⟨.transit _ _ _ live (.cons M go (.stay _) gd (.nil _ _)),nxt,F⟩
      | forward =>
        have E := (BStarOwnerControlHistory.pointed_unique_forward _ len (l+1) nxt.2.1 nxt.2.2 l (by omega)).mp ⟨pay,F⟩
        omega
      | turn => omega

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

private theorem first_occurrence {α : Type} {w : List α} {e : α} (h : e∈w) :
    ∃ a b,w=a++e::b ∧ e∉a := by
  classical
  induction w with
  | nil => simp at h
  | cons a w ih =>
    by_cases eq : a=e
    · subst a
      exact ⟨[],w,rfl,by simp⟩
    · obtain ⟨u,v,W,N⟩ := ih ((List.mem_cons.mp h).resolve_left (Ne.symm eq))
      exact ⟨a::u,v,congrArg (List.cons a) W,by simpa [Ne.symm eq] using N⟩

private theorem holds_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (l : Nat) (L : l<len) (center : Fin n) (loc : S.getD l fall=(center,1))
    (pay : Payload) (well : Well pay) (w : List (Fin n)) (away : center∉w) (qx : Q x)
    (cur : Current hp base (fun k=>S.getD k fall) len x (.busy commitOp (.out l)))
    (old : project (fun k=>S.getD k fall) x l=.forward pay) :
    BusyOnly hp base (fun k=>S.getD k fall) len commitOp x (.out l) w (.out l) ∧
      Current hp base (fun k=>S.getD k fall) len (play x w) (.busy commitOp (.out l)) ∧
      project (fun k=>S.getD k fall) (play x w) l=.forward pay := by
  induction w generalizing x with
  | nil => exact ⟨.nil cur,cur,old⟩
  | cons e w ih =>
    have N : center≠e ∧ center∉w := ⟨fun H => away (List.mem_cons.mpr (.inl H)),fun H => away (List.mem_cons_of_mem _ H)⟩
    obtain ⟨E,I,F⟩ := center_hold hp C Q fiber closed sep l L center e loc (Ne.symm N.1) qx pay well cur old
    obtain ⟨T,G,P⟩ := ih N.2 (closed _ qx e) I F
    exact ⟨.cons cur E T,G,P⟩

private theorem join_busy {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {u v : List (Fin n)} {z a d : Cursor}
    (P : BusyOnly hp base addr len op x z u a)
    (R : BusyOnly hp base addr len op (play x u) a v d) :
    BusyOnly hp base addr len op x z (u++v) d := by
  induction P with
  | nil _ => exact R
  | cons I E _ ih => exact .cons I E (ih R)

/-- Append the physical outgoing edge of the owner center to the
nominated subsequence. The witness cuts at the first such mark after
arrival (potentially earlier than the matched final subsequence mark). -/
theorem center_mark_of_sublist {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (l : Nat) (L : l<len) (center : Fin n) (loc : S.getD l fall=(center,1))
    (centerH : oldH6 B base center=true)
    (pay : Payload) (well : Well pay) (j : Nat) (J : j≤l)
    {ls w : List (Fin n)} (sub : (ls++[center]).Sublist w)
    (size : j+ls.length=l) (qx : Q x)
    (cur : Current hp base (fun k=>S.getD k fall) len x (.busy commitOp (.out j)))
    (old : project (fun k=>S.getD k fall) x j=.forward pay)
    (nom : ∀ k (hk : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y ls[k] (fun t=>S.getD t fall) len (j+k)) :
    ∃ (arrive idle tail : List (Fin n)),
      w=arrive++idle++center::tail ∧ center∉idle ∧
      BusyOnly hp base (fun t=>S.getD t fall) len commitOp x (.out j) arrive (.out l) ∧
      BusyOnly hp base (fun t=>S.getD t fall) len commitOp x (.out j) (arrive++idle) (.out l) ∧
      let y := play x (arrive++idle)
      Current hp base (fun t=>S.getD t fall) len y (.busy commitOp (.out l)) ∧
      project (fun t=>S.getD t fall) y l=.forward pay ∧
      (centerLink (oldPair B y center),.advance pay)∈actualOffers (oldPair B y center)
        ((y center).long,(y (rightNeighbor center)).long) ∧
      (∀ (d : Descriptor) (b : Fin 3),
        BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/4))=some d →
        pay.argument.toNat%4=b.val → (b=d.b0 ∨ (d.need=true ∧ b=d.b1)) →
        ((grant 1).read (y center).long).getLsbD 0=true →
        readSel (y center).long=d.old →
        readOptional (stage.read (y center).long)=some d →
        readOptional (sealField.read (y center).long)=some d →
        (longTrace (oldPair B y center) ((y center).long,(y (rightNeighbor center)).long)).publications=[⟨.left,b⟩] ∧
        readPublication (step y center center).long=(BitVec.ofNat 2 b.val,0,0)) := by
  obtain ⟨preWord,suffix,W,A⟩ := split_sublist_end sub
  have hhC : oldH6 B base (S.getD l fall).1=true := by rw [loc]; exact centerH
  obtain ⟨arrive,rest,E,P,F⟩ := reaches_center_of_sublist hp C Q fiber closed sep l L (congrArg Prod.snd loc)
    hhC pay well A x j j size (Nat.le_refl _) J qx cur old nom
  let z := play x arrive
  have qrun (w : List (Fin n)) (y : X) (q : Q y) : Q (play y w) := by
    induction w generalizing y with
    | nil => exact q
    | cons e w ih => exact ih (step y e) (closed _ q e)
  have qz : Q z := qrun arrive x qx
  have member : center∈rest++center::suffix := List.mem_append_right _ List.mem_cons_self
  obtain ⟨idle,tail,split,away⟩ := first_occurrence member
  have I := BStarAcquireHistoryReturn.busy_end hp P
  obtain ⟨T,Y,Z⟩ := holds_word hp C Q fiber closed sep l L center loc pay well idle away qz I F
  have G : play x (arrive++idle)=play z idle := BStarResetSchedule.run_append step x arrive idle
  have wire : BStarLongTransport.readK ((play z idle center).long,(play z idle (rightNeighbor center)).long)
      (centerLink (oldPair B (play z idle) center)).source=.forward pay := by
    change atCursor (play z idle) (S.getD l fall)=_ at Z
    rw [loc] at Z
    exact Z
  refine ⟨arrive,idle,tail,?_,away,P,join_busy hp P T,?_⟩
  · rw [W,E,List.append_assoc,split,←List.append_assoc]
  · dsimp only
    rw [G]
    have sel := selected_well _ _ _ pay (center_mem _) (show Cmd.link≠Cmd.door by decide) well wire
    refine ⟨Y,Z,sel,?_⟩
    intro d b decoded bank legal writer selector staged sealed
    have H := (congrArg Prod.fst (Y.1.1 center)).symm.trans centerH
    have result := BStarBitCommitPublishes.selected_center_publishes hp (play z idle) center
      (centerLink (oldPair B (play z idle) center)) pay d b H rfl sel well.fault well.opcode
      decoded bank legal writer selector staged sealed
    exact ⟨result.1,result.2.2⟩

end L4.BStarCommitServiceCenter
