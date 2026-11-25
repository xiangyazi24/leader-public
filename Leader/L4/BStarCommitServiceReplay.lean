import Leader.L4.BStarCommitService

namespace L4.BStarCommitServiceReplay
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

/-- Every earlier physical mark either stutters or advances one slot,
retaining the exact well-formed COMMIT. No scheduler premise. -/
theorem arbitrary_precenter_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (l : Nat) (L : l<len) (centerK : (S.getD l fall).2=1)
    (centerH : oldH6 B base (S.getD l fall).1=true)
    (j : Nat) (J : j<l) (qx : Q x) (e : Fin n) (pay : Payload) (well : Well pay)
    (cur : Current hp base (fun k=>S.getD k fall) len x (.busy commitOp (.out j)))
    (old : project (fun k=>S.getD k fall) x j=.forward pay) :
    ∃ k, j≤k ∧ k≤j+1 ∧
      Event hp (fun t=>S.getD t fall) len x e (.busy commitOp (.out j)) (.busy commitOp (.out k)) ∧
      Current hp base (fun t=>S.getD t fall) len (step x e) (.busy commitOp (.out k)) ∧
      project (fun t=>S.getD t fall) (step x e) k=.forward pay ∧
      (linkAt hp x e (fun t=>S.getD t fall) len j → k=j+1) := by
  have away : (S.getD j fall).2.val≠1 ∨ oldH6 B x (S.getD j fall).1=false := by
    by_cases token : (S.getD j fall).2.val=1
    · right
      apply Bool.eq_false_iff.mpr
      intro H
      have eq := unique_center_index hp C (fun i => (congrArg Prod.fst (fiber x qx i)).symm)
        l j (by omega) (by omega) centerK centerH (Fin.ext token) H
      omega
    · exact .inl token
  by_cases link : linkAt hp x e (fun t=>S.getD t fall) len j
  · obtain ⟨E,I,F⟩ := nominated_step hp C Q fiber closed sep qx e j pay cur old well link away
    exact ⟨j+1,by omega,Nat.le_refl _,E,I,F,fun _ => rfl⟩
  · obtain ⟨m,ev,nxt⟩ := current_step hp C Q fiber closed sep qx e (.busy commitOp (.out j)) cur
    have K : j<len := by omega
    have silent := (BStarCommitHealthyIdle.silent_at_commit hp C e (sep e) commitOp j cur.1 pay
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

#print axioms arbitrary_precenter_step

/-- A replay with the nominated ordered subsequence reaches the center
on some prefix. Intervening marks may help but cannot undo progress or
change the well-formed COMMIT before that first center cut. -/
theorem reaches_center_of_sublist {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (l : Nat) (L : l<len) (centerK : (S.getD l fall).2=1)
    (centerH : oldH6 B base (S.getD l fall).1=true)
    (pay : Payload) (well : Well pay)
    {ls w : List (Fin n)} (sub : ls.Sublist w) :
    ∀ (x : X) (a j : Nat), a+ls.length=l → a≤j → j≤l → Q x →
      Current hp base (fun t=>S.getD t fall) len x (.busy commitOp (.out j)) →
      project (fun t=>S.getD t fall) x j=.forward pay →
      (∀ k (hk : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun t=>S.getD t fall) len (a+k)) →
      ∃ pre post, w=pre++post ∧
        BusyOnly hp base (fun t=>S.getD t fall) len commitOp x (.out j) pre (.out l) ∧
        project (fun t=>S.getD t fall) (play x pre) l=.forward pay := by
  induction sub with
  | slnil =>
    intro state a j J A U _ I F _
    have eq : j=l := by simp at J; omega
    subst j
    exact ⟨[],[],rfl,.nil I,F⟩
  | @cons ls w e sub ih =>
    intro state a j J A U q I F nominate
    by_cases eqa : j=l
    · subst j
      exact ⟨[],e::w,rfl,.nil I,F⟩
    have jl : j<l := by omega
    obtain ⟨k,jk,K,E,now,new,_⟩ := arbitrary_precenter_step hp C Q fiber closed sep l L
      centerK centerH j jl q e pay well I F
    obtain ⟨pre,post,W,T,P⟩ := ih (step state e) a k J (by omega) (by omega) (closed _ q e)
      now new nominate
    exact ⟨e::pre,post,congrArg (List.cons e) W,.cons I E T,P⟩
  | @cons_cons ls w e sub ih =>
    intro state a j J A U q I F nominate
    by_cases eqa : j=l
    · subst j
      exact ⟨[],e::w,rfl,.nil I,F⟩
    have jl : j<l := by omega
    obtain ⟨k,jk,K,E,now,new,served⟩ := arbitrary_precenter_step hp C Q fiber closed sep l L
      centerK centerH j jl q e pay well I F
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
    obtain ⟨pre,post,W,T,P⟩ := ih (step state e) (a+1) k (by simp at J; omega) kA (by omega)
      (closed _ q e) now new nom'
    exact ⟨e::pre,post,congrArg (List.cons e) W,.cons I E T,P⟩

#print axioms reaches_center_of_sublist
end L4.BStarCommitServiceReplay
