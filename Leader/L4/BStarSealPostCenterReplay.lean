import Leader.L4.BStarSealHealthyFlight
import Leader.L4.BStarResetChartNomination

namespace L4.BStarSealPostCenterReplay
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarSealHealthyHop BStarCommitHealthyFlight BStarH6Ordinal
open BStarResetRailRing

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Every earlier physical mark either stutters or advances one slot,
retaining the exact well-formed SEAL. No scheduler premise. -/
theorem arbitrary_postcenter_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (g : Nat) (G : g<len) (gateK : (S.getD g fall).2=1)
    (gateH : oldH6 B base (S.getD g fall).1=true)
    (j : Nat) (J : j<len) (after : g<j) (qx : Q x) (e : Fin n) (pay : Payload) (well : Well pay)
    (cur : Current hp base (fun k=>S.getD k fall) len x (.busy sealOp (.out j)))
    (old : project (fun k=>S.getD k fall) x j=.forward pay) :
    ∃ k, j≤k ∧ k≤j+1 ∧
      Event hp (fun t=>S.getD t fall) len x e (.busy sealOp (.out j)) (.busy sealOp (.out k)) ∧
      Current hp base (fun t=>S.getD t fall) len (step x e) (.busy sealOp (.out k)) ∧
      project (fun t=>S.getD t fall) (step x e) k=.forward pay ∧
      (linkAt hp x e (fun t=>S.getD t fall) len j → k=j+1) := by
  have fixed : ∀ i,oldH6 B x i=oldH6 B base i := fun i => (congrArg Prod.fst (fiber x qx i)).symm
  have away : (S.getD j fall).2.val≠1 ∨ oldH6 B x (S.getD j fall).1=false := by
    by_cases tag : (S.getD j fall).2.val=1
    · right
      apply Bool.eq_false_iff.mpr
      intro H
      have E := unique_center_index hp C fixed g j (by omega) (by omega) gateK gateH (Fin.ext tag) H
      omega
    · exact .inl tag
  by_cases link : linkAt hp x e (fun t=>S.getD t fall) len j
  · obtain ⟨jLen,K,a,mem,dest,src,dst⟩ := link
    have away' : K.source.occurrence.val≠1 ∨ (geometry (oldPair B x e) K.source.side).axes.h6=false := by
      rw [show S.getD j fall=address e K.source from src] at away
      cases hs : K.source.side <;> simpa [address,site,oldPair,oldH6,geometry,hs,longGeometry] using away
    have R := (old_read x e K.source).trans ((congrArg (atCursor x) src).symm.trans old)
    have out := joined_before_center k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
      K a pay mem dest away' R well
    have post := (congrArg (atCursor (step x e)) dst).trans ((new_read B x e (sep e) a).symm.trans out)
    obtain ⟨m,ev,nxt⟩ := current_step hp C Q fiber closed sep qx e (.busy sealOp (.out j)) cur
    cases ev with
    | transit _ _ d live seen =>
      cases seen with
      | cons M go adv gd tail =>
        cases tail
        cases adv with
        | stay =>
          have empty := nxt.2.2 (j+1) (by omega) jLen
          exact Token.noConfusion (empty.symm.trans post)
        | forward =>
          exact ⟨j+1,by omega,Nat.le_refl _,.transit _ _ _ live (.cons M go (.forward j) gd (.nil _ _)),
            nxt,post,fun _ => rfl⟩
        | turn => omega
  · obtain ⟨m,ev,nxt⟩ := current_step hp C Q fiber closed sep qx e (.busy sealOp (.out j)) cur
    have K : j<len := by omega
    have silent := (BStarSealHealthyIdle.silent_at_seal hp C e (sep e) sealOp j cur.1 pay
      cur.2.1 old well link (fun E => (Nat.ne_of_lt K E).elim)).2
    have F : project (fun t=>S.getD t fall) (step x e) j=.forward pay := silent.trans old
    cases ev with
    | transit _ _ d live seen =>
      cases seen with
      | cons M go adv gd tail =>
        cases tail
        cases adv with
        | stay => exact ⟨j,Nat.le_refl _,by omega,.transit _ _ _ live (.cons M go (.stay _) gd (.nil _ _)),nxt,F,
            fun H => (link H).elim⟩
        | forward =>
          have E := (BStarOwnerControlHistory.pointed_unique_forward _ len (j+1) nxt.2.1 nxt.2.2 j (by omega)).mp ⟨pay,F⟩
          omega
        | turn => omega

#print axioms arbitrary_postcenter_step

/-- A replay with the nominated ordered subsequence reaches the terminal
on some prefix. Intervening marks may help but cannot undo progress or
change the well-formed SEAL before that first terminal cut. -/
theorem reaches_terminal_of_sublist {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (g : Nat) (G : g<len) (gateK : (S.getD g fall).2=1)
    (gateH : oldH6 B base (S.getD g fall).1=true)
    (pay : Payload) (well : Well pay)
    {ls w : List (Fin n)} (sub : ls.Sublist w) :
    ∀ (x : X) (a j : Nat), a+ls.length=len → a≤j → j≤len → g<j → Q x →
      Current hp base (fun t=>S.getD t fall) len x (.busy sealOp (.out j)) →
      project (fun t=>S.getD t fall) x j=.forward pay →
      (∀ k (hk : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun t=>S.getD t fall) len (a+k)) →
      ∃ pre post, w=pre++post ∧
        BusyOnly hp base (fun t=>S.getD t fall) len sealOp x (.out j) pre (.out len) ∧
        project (fun t=>S.getD t fall) (play x pre) len=.forward pay := by
  induction sub with
  | slnil =>
    intro state a j J A U _ _ I F _
    have eq : j=len := by simp at J; omega
    subst j
    exact ⟨[],[],rfl,.nil I,F⟩
  | @cons ls w e sub ih =>
    intro state a j J A U later q I F nominate
    by_cases eqa : j=len
    · subst j
      exact ⟨[],e::w,rfl,.nil I,F⟩
    have jl : j<len := by omega
    obtain ⟨k,jk,K,E,now,new,_⟩ := arbitrary_postcenter_step hp C Q fiber closed sep g G
      gateK gateH j jl later q e pay well I F
    obtain ⟨pre,post,W,T,P⟩ := ih (step state e) a k J (by omega) (by omega) (by omega) (closed _ q e)
      now new nominate
    exact ⟨e::pre,post,congrArg (List.cons e) W,.cons I E T,P⟩
  | @cons_cons ls w e sub ih =>
    intro state a j J A U later q I F nominate
    by_cases eqa : j=len
    · subst j
      exact ⟨[],e::w,rfl,.nil I,F⟩
    have jl : j<len := by omega
    obtain ⟨k,jk,K,E,now,new,served⟩ := arbitrary_postcenter_step hp C Q fiber closed sep g G
      gateK gateH j jl later q e pay well I F
    have kA : a+1≤k := by
      by_cases same : a=j
      · subst a
        have link := nominate 0 (by simp) state (fiber state q)
        have eq := served (by simpa using link)
        omega
      · omega
    have nom' (t : Nat) (ht : t<ls.length) (y : X) (H : ∀ i,Layout B base i=Layout B y i) :
        linkAt hp y ls[t] (fun t=>S.getD t fall) len ((a+1)+t) := by
      have link := nominate (t+1) (by simp; omega) y H
      have eq : a+(t+1)=(a+1)+t := by omega
      simpa only [List.getElem_cons_succ,eq] using link
    obtain ⟨pre,post,W,T,P⟩ := ih (step state e) (a+1) k (by simp at J; omega) kA (by omega) (by omega)
      (closed _ q e) now new nom'
    exact ⟨e::pre,post,congrArg (List.cons e) W,.cons I E T,P⟩

#print axioms reaches_terminal_of_sublist
end L4.BStarSealPostCenterReplay
