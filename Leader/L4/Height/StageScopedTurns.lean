import Leader.L4.Height.StagePositiveTerminal
import Leader.L4.Height.StageScopedReplay
namespace L4.Height.StageScopedTurns
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarLongTransport BStarLongRouting
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarGeneratedOwner
open BStarOwnerLaunchOrigin BStarAcquireForwardTrace BStarAcquireHistorySample
open BStarLongFixedRouting BStarResetChartService BStarResetQuiet BStarResetQuietTable
open BStarSealHealthyHop BStarLongDoor
open BStarClearanceForward BStarLongLayout StageHealthyIdle StageScopedReplay

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem terminal_hold {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (e : Fin n) (source : BitVec LW) (d : BStarLongPublication.Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy stageOp (.out len)))
    (old : project (fun j=>S.getD j fall) x len=.forward (BStarStageIssue.payload source))
    (miss : ¬ onTerminal hp x e (fun j=>S.getD j fall) len) :
    Event hp (fun j=>S.getD j fall) len x e (.busy stageOp (.out len)) (.busy stageOp (.out len)) ∧
    Current hp base (fun j=>S.getD j fall) len (step x e) (.busy stageOp (.out len)) ∧
    project (fun j=>S.getD j fall) (step x e) len=.forward (BStarStageIssue.payload source) := by
  have noL : ¬ linkAt hp x e (fun j=>S.getD j fall) len len := fun K=>Nat.lt_irrefl _ K.1
  have carry := (silent_at_stage hp C e (sep e) stageOp len cur.1 _ cur.2.1
    old (canonical source d D) noL (fun _=>miss)).2
  change project (fun j=>S.getD j fall) (step x e) len=project (fun j=>S.getD j fall) x len at carry
  have kept := carry.trans old
  obtain ⟨m,E,I⟩ := current_step hp C Q fiber closed sep qx e (.busy stageOp (.out len)) cur
  cases E with
  | transit _ _ d live seen =>
    cases seen with
    | cons M go A G tail =>
      cases tail
      cases A with
      | stay _ => exact ⟨.transit _ _ _ live (.cons M go (.stay _) G (.nil _ _)),I,kept⟩
      | forward _ =>
        have bound := I.2.1.1
        omega
      | turn =>
        obtain ⟨q,R⟩ := I.2.1.2.1
        exact Token.noConfusion (kept.symm.trans R)

theorem turns_in_word {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w : List (Fin n)) (t : Fin n) (ht : t∈w)
    (nom : ∀ y : X,Q y→onTerminal hp y t (fun j=>S.getD j fall) len)
    (qx : Q x) (source : BitVec LW) (d : BStarLongPublication.Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy stageOp (.out len)))
    (old : project (fun j=>S.getD j fall) x len=.forward (BStarStageIssue.payload source)) :
    ∃ wait e tail, w=wait++e::tail ∧
      BusyOnly hp base (fun j=>S.getD j fall) len stageOp x (.out len) (wait++[e]) (.back len) ∧
      project (fun j=>S.getD j fall) (play x (wait++[e])) len=.reply StageReplyForm.reply := by
  induction w generalizing x with
  | nil => simp at ht
  | cons e w ih =>
    by_cases H : onTerminal hp x e (fun j=>S.getD j fall) len
    · obtain ⟨E,I,P⟩ := StagePositiveTerminal.nominated_turn hp C Q fiber closed sep qx e source d D cur old H
      exact ⟨[],e,w,rfl,.cons cur E (.nil I),P⟩
    · have absent : t≠e := by
        intro K
        subst e
        exact H (nom x qx)
      have W := (List.mem_cons.mp ht).resolve_left absent
      obtain ⟨E,I,P⟩ := terminal_hold hp C Q fiber closed sep qx e source d D cur old H
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

theorem turns_of_sublist {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (j : Nat) (J : j≤len) (qx : Q x)
    (source : BitVec LW) (d : BStarLongPublication.Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (cur : Current hp base (fun t=>S.getD t fall) len x (.busy stageOp (.out j)))
    (old : project (fun t=>S.getD t fall) x j=.forward (BStarStageIssue.payload source))
    {ls w : List (Fin n)} (terminal : Fin n)
    (sub : (ls++[terminal]).Sublist w) (size : j+ls.length=len)
    (auth : PrefixAuth hp base x (fun t=>S.getD t fall) len j source d w)
    (nom : ∀ k (hk : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y ls[k] (fun t=>S.getD t fall) len (j+k))
    (termNom : ∀ y : X,Q y→onTerminal hp y terminal (fun t=>S.getD t fall) len) :
    ∃ pre wait e tail, w=pre++wait++e::tail ∧
      BusyOnly hp base (fun t=>S.getD t fall) len stageOp x (.out j) pre (.out len) ∧
      BusyOnly hp base (fun t=>S.getD t fall) len stageOp x (.out j) (pre++wait++[e]) (.back len) ∧
      project (fun t=>S.getD t fall) (play x (pre++wait++[e])) len=.reply StageReplyForm.reply ∧
      BStarReplyBack.normal StageReplyForm.reply=.reply StageReplyForm.reply := by
  obtain ⟨u,v,W,Ssub⟩ := split_sublist_end sub
  obtain ⟨pre,rest,E,P,F⟩ := reaches_terminal_of_sublist hp C Q fiber closed sep source d D Ssub x j j size (Nat.le_refl _) J qx (auth.take hp u (terminal::v) W) cur old nom
  let z := play x pre
  have qrun (w : List (Fin n)) (y : X) (q : Q y) : Q (play y w) := by
    induction w generalizing y with
    | nil => exact q
    | cons e w ih => exact ih (step y e) (closed _ q e)
  have hit : terminal∈rest++terminal::v := List.mem_append_right _ List.mem_cons_self
  obtain ⟨wait,e,tail,Z,T,R⟩ := turns_in_word hp C Q fiber closed sep (rest++terminal::v)
    terminal hit termNom (qrun pre x qx) source d D (BStarAcquireHistoryReturn.busy_end hp P) F
  refine ⟨pre,wait,e,tail,?_,P,?_,?_,rfl⟩
  · rw [W,E,List.append_assoc,Z,←List.append_assoc]
  · rw [List.append_assoc]
    exact join_busy hp P T
  · rw [List.append_assoc,BStarResetSchedule.run_append]
    exact R

end L4.Height.StageScopedTurns
