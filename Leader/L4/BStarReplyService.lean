import Leader.L4.BStarPositiveReply
import Leader.L4.BStarResetChartNomination

namespace L4.BStarReplyService
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarGeneratedOwner
open BStarOwnerLaunchOrigin BStarAcquireForwardTrace BStarAcquireHistorySample
open BStarResetChartNomination BStarSeparatingProgress BStarResetChartService
open BStarAcquireRailCoverage

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem split_end {α : Type} {u w : List α} {e : α}
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

private theorem first_mark {α : Type} {w : List α} {e : α} (h : e∈w) :
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

private theorem word_keeps {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (op : Nat) (pay : Payload) (norm : BStarReplyBack.normal pay=.reply pay)
    (w : List (Fin n)) (away : RearTrace.predecessor (S.getD 0 fall).1∉w) (qx : Q x)
    (cur : Current hp base (fun k=>S.getD k fall) len x (.busy op (.back 0)))
    (old : project (fun k=>S.getD k fall) x 0=.reply pay) :
    BusyOnly hp base (fun k=>S.getD k fall) len op x (.back 0) w (.back 0) ∧
      Current hp base (fun k=>S.getD k fall) len (play x w) (.busy op (.back 0)) ∧
      project (fun k=>S.getD k fall) (play x w) 0=.reply pay := by
  induction w generalizing x with
  | nil => exact ⟨.nil cur,cur,old⟩
  | cons e w ih =>
    have N : e≠RearTrace.predecessor (S.getD 0 fall).1 := fun eq => away (List.mem_cons.mpr (.inl eq.symm))
    have A := BStarPositiveReply.at_root_step hp C Q fiber closed sep qx e op pay norm cur old
    dsimp only at A
    rw [if_neg N] at A
    obtain ⟨T,G,P⟩ := ih (fun h => away (List.mem_cons_of_mem _ h)) (closed _ qx e) A.2.1 A.2.2
    exact ⟨.cons cur A.1 T,G,P⟩

theorem join_busy {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {u v : List (Fin n)} {z a d : Cursor}
    (P : BusyOnly hp base addr len op x z u a)
    (R : BusyOnly hp base addr len op (play x u) a v d) :
    BusyOnly hp base addr len op x z (u++v) d := by
  induction P with
  | nil _ => exact R
  | cons I E _ ih => exact .cons I E (ih R)

/-- Reverse order of the fixed owner chart nominations. Its existence
uses only the fixed layout, not a hypothetical return trajectory. -/
theorem nominate_back {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (m : Nat) (M : m≤len) :
    ∃ ls : List (Fin n), ls.length=m ∧
      ∀ k (K : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun j=>S.getD j fall) len (ls.length-(k+1)) := by
  induction m with
  | zero =>
    refine ⟨[],rfl,?_⟩
    intro k K; exact (Nat.not_lt_zero _ K).elim
  | succ m ih =>
    have L : m<len := by omega
    obtain ⟨e,N⟩ := nominate hp C head cont m (Nat.le_of_lt L)
    obtain ⟨ls,lsLen,T⟩ := ih (by omega)
    refine ⟨e::ls,by simp [lsLen],?_⟩
    intro k K y H
    cases k with
    | zero =>
      have W := (mem_link hp y e _ len m).mp (by simpa only [if_pos L] using N y H)
      simpa [lsLen] using W
    | succ k =>
      have K' : k<ls.length := by simpa using K
      simpa using T k K' y H

/-- A fixed backwards service subsequence followed by the root's
incoming mark positively yields an actual root consume of the exact
same canonical reply, with correctly bound old payload. -/
theorem reaches_consume {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (op j : Nat) (pay : Payload) (norm : BStarReplyBack.normal pay=.reply pay)
    (cur : Current hp base (fun a=>S.getD a fall) len x (.busy op (.back j)))
    (D : project (fun a=>S.getD a fall) x j=.reply pay)
    {ls w : List (Fin n)} (sub : (ls++[RearTrace.predecessor (S.getD 0 fall).1]).Sublist w)
    (size : j≤ls.length)
    (nom : ∀ k (K : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun t=>S.getD t fall) len (ls.length-(k+1))) :
    ∃ pre tail, w=pre++RearTrace.predecessor (S.getD 0 fall).1::tail ∧
      BusyOnly hp base (fun a=>S.getD a fall) len op x (.back j) pre (.back 0) ∧
      let y := play x pre
      let s := y (S.getD 0 fall).1
      bind (longGeometry B s) 0 (atSite s.long 0)=.reply pay ∧
      Current hp base (fun a=>S.getD a fall) len y (.busy op (.back 0)) ∧
      Event hp (fun a=>S.getD a fall) len y (RearTrace.predecessor (S.getD 0 fall).1)
        (.busy op (.back 0)) .idle ∧
      Current hp base (fun a=>S.getD a fall) len (step y (RearTrace.predecessor (S.getD 0 fall).1)) .idle := by
  let door := RearTrace.predecessor (S.getD 0 fall).1
  obtain ⟨prior,suffix,W,Svc⟩ := split_end sub
  obtain ⟨arrive,left,E,R,F⟩ := BStarPositiveReply.root_of_sublist hp C Q fiber closed sep
    op pay norm Svc x j size qx cur D nom
  have stable (z : X) (word : List (Fin n)) (q : Q z) : Q (play z word) := by
    induction word generalizing z with
    | nil => exact q
    | cons e word ih => exact ih (step z e) (closed _ q e)
  obtain ⟨wait,tail,split,noDoor⟩ := first_mark (List.mem_append_right left (List.mem_cons_self (a:=door) (l:=suffix)))
  have qA := stable x arrive qx
  obtain ⟨Extra,I,P⟩ := word_keeps hp C Q fiber closed sep op pay norm wait noDoor qA
    (BStarAcquireHistoryReturn.busy_end hp R) F
  have same : play x (arrive++wait)=play (play x arrive) wait := BStarResetSchedule.run_append step x arrive wait
  refine ⟨arrive++wait,tail,?_,join_busy hp R Extra,?_⟩
  · rw [W,E,List.append_assoc,split,←List.append_assoc]
  · dsimp only
    rw [same]
    have At := BStarPositiveReply.at_root_step hp C Q fiber closed sep (stable _ wait qA)
      door op pay norm I P
    dsimp only at At
    rw [if_pos rfl] at At
    have K0 : (S.getD 0 fall).2=0 := congrArg Prod.snd C.root
    change atCursor (play (play x arrive) wait) (S.getD 0 fall)=.reply pay at P
    change atSite (play (play x arrive) wait (S.getD 0 fall).1).long (S.getD 0 fall).2=.reply pay at P
    rw [K0] at P
    exact ⟨(congrArg (bind _ 0) P).trans norm,I,At⟩

end L4.BStarReplyService
