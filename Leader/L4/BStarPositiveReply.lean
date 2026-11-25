import Leader.L4.BStarReplyBack
import Leader.L4.BStarCommitServiceCenter

namespace L4.BStarPositiveReply
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarGeneratedOwner
open BStarOwnerLaunchOrigin BStarAcquireForwardTrace BStarAcquireHistorySample
open BStarLongFixedRouting BStarResetChartService

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Positive actual step for the canonical normalized return. Any
edge before back-zero keeps the same reply; the nominated reverse
link actually decrements the cursor. No supplied future receipt. -/
theorem reverse_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (e : Fin n) (op k : Nat) (pay : Payload)
    (norm : BStarReplyBack.normal pay=.reply pay)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy op (.back (k+1))))
    (D : project (fun j=>S.getD j fall) x (k+1)=.reply pay) :
    ∃ j, k≤j ∧ j≤k+1 ∧
      Event hp (fun a=>S.getD a fall) len x e (.busy op (.back (k+1))) (.busy op (.back j)) ∧
      Current hp base (fun a=>S.getD a fall) len (step x e) (.busy op (.back j)) ∧
      project (fun a=>S.getD a fall) (step x e) j=.reply pay ∧
      (linkAt hp x e (fun a=>S.getD a fall) len k → j=k) := by
  classical
  obtain ⟨m,E,I⟩ := current_step hp C Q fiber closed sep qx e (.busy op (.back (k+1))) cur
  have stepData := BStarReplyBack.reverse_or_hold hp C e (sep e) op k cur.1 pay cur.2.1 D
  dsimp only at stepData
  rw [norm] at stepData
  cases E with
  | transit _ _ next live seen =>
    cases seen with
    | cons M go A Good tail =>
      cases tail
      cases A with
      | stay _ =>
        by_cases link : linkAt hp x e (fun a=>S.getD a fall) len k
        · have marked := (if_pos link) ▸ stepData
          have trail := I.2.1.2.2.1 k (by omega)
          exact Token.noConfusion (trail.symm.trans marked.1)
        · have marked := (if_neg link) ▸ stepData
          exact ⟨k+1,by omega,Nat.le_refl _,
            .transit _ _ _ live (.cons M go (.stay _) Good (.nil _ _)),I,
            marked.elim id id,fun l => (link l).elim⟩
      | reverse a =>
        by_cases link : linkAt hp x e (fun a=>S.getD a fall) len k
        · have marked := (if_pos link) ▸ stepData
          exact ⟨k,Nat.le_refl _,by omega,
            .transit _ _ _ live (.cons M go (.reverse k) Good (.nil _ _)),I,marked.1,fun _=>rfl⟩
        · have marked := (if_neg link) ▸ stepData
          have empty := I.2.1.2.2.2 (k+1) (by omega) cur.2.1.1
          exact Token.noConfusion (empty.symm.trans (marked.elim id id))

/-- Once back-zero is reached, all other marks retain the canonical
reply, and the actual next incoming root mark consumes it. -/
theorem at_root_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (e : Fin n) (op : Nat) (pay : Payload)
    (norm : BStarReplyBack.normal pay=.reply pay)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy op (.back 0)))
    (D : project (fun j=>S.getD j fall) x 0=.reply pay) :
    let addr := fun j=>S.getD j fall
    if e=RearTrace.predecessor (addr 0).1 then
       Event hp addr len x e (.busy op (.back 0)) .idle ∧
       Current hp base addr len (step x e) .idle
    else Event hp addr len x e (.busy op (.back 0)) (.busy op (.back 0)) ∧
       Current hp base addr len (step x e) (.busy op (.back 0)) ∧
       project addr (step x e) 0=.reply pay := by
  dsimp only
  obtain ⟨m,E,I⟩ := current_step hp C Q fiber closed sep qx e (.busy op (.back 0)) cur
  cases E with
  | transit _ _ _ live _ => exact (live rfl).elim
  | consume _ own hit =>
    rw [if_pos own]
    exact ⟨.consume _ own hit,I⟩
  | arrived_hold _ off =>
    rw [if_neg off]
    have held := BStarReplyBack.arrived_payload hp C cur.1.1 e (sep e) off pay
      ⟨cur.2.1.2.1,cur.2.1.2.2.2⟩ D
    rw [norm] at held
    exact ⟨.arrived_hold _ off,I,held.elim id id⟩

/-- A backward service subsequence reaches back-zero on an actual
prefix, preserving the exact canonical reply. Arbitrary interleaving
may help, but cannot erase the reply or cause an early root consume. -/
theorem root_of_sublist {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (op : Nat) (pay : Payload) (norm : BStarReplyBack.normal pay=.reply pay)
    {ls w : List (Fin n)} (sub : ls.Sublist w) :
    ∀ (x : X) (j : Nat), j≤ls.length → Q x →
      Current hp base (fun a=>S.getD a fall) len x (.busy op (.back j)) →
      project (fun a=>S.getD a fall) x j=.reply pay →
      (∀ k (hk : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun t=>S.getD t fall) len (ls.length-(k+1))) →
      ∃ pre post, w=pre++post ∧
        BusyOnly hp base (fun a=>S.getD a fall) len op x (.back j) pre (.back 0) ∧
        project (fun a=>S.getD a fall) (play x pre) 0=.reply pay := by
  induction sub with
  | slnil =>
    intro x j J _ I D _
    have eq : j=0 := by simp at J; omega
    subst j
    exact ⟨[],[],rfl,.nil I,D⟩
  | @cons ls w e sub ih =>
    intro x j J q I D nominate
    cases j with
    | zero => exact ⟨[],e::w,rfl,.nil I,D⟩
    | succ j =>
      obtain ⟨k,lo,hi,E,cur,data,_⟩ := reverse_step hp C Q fiber closed sep q e op j pay norm I D
      obtain ⟨pre,post,W,T,P⟩ := ih (step x e) k (by omega) (closed _ q e) cur data nominate
      exact ⟨e::pre,post,congrArg (List.cons e) W,.cons I E T,P⟩
  | @cons_cons ls w e sub ih =>
    intro x j J q I D nominate
    cases j with
    | zero => exact ⟨[],e::w,rfl,.nil I,D⟩
    | succ j =>
      obtain ⟨k,lo,hi,E,cur,data,served⟩ := reverse_step hp C Q fiber closed sep q e op j pay norm I D
      have lower : k≤ls.length := by
        by_cases A : j=ls.length
        · subst j
          have nominated := nominate 0 (by simp) x (fiber x q)
          have exactIndex : (e::ls).length-(0+1)=ls.length := by simp
          rw [exactIndex] at nominated
          exact Nat.le_of_eq (served nominated)
        · simp only [List.length_cons] at J
          omega
      have tailN (t : Nat) (ht : t<ls.length) (y : X) (H : ∀ i,Layout B base i=Layout B y i) :
          linkAt hp y ls[t] (fun j=>S.getD j fall) len (ls.length-(t+1)) := by
        have link := nominate (t+1) (by simp; omega) y H
        have eq : (e::ls).length-(t+1+1)=ls.length-(t+1) := by simp only [List.length_cons]; omega
        simpa only [List.getElem_cons_succ,eq] using link
      obtain ⟨pre,post,W,T,P⟩ := ih (step x e) k lower (closed _ q e) cur data tailN
      exact ⟨e::pre,post,congrArg (List.cons e) W,.cons I E T,P⟩

#print axioms reverse_step
#print axioms at_root_step
#print axioms root_of_sublist
end L4.BStarPositiveReply
