import Leader.L4.BStarCommitHealthyFlight
import Leader.L4.BStarResetChartNomination

namespace L4.BStarCommitService
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongTransport BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarCommitHealthyHop BStarCommitHealthyFlight

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- A nominated physical mark actually advances a canonical precenter
COMMIT. The new cursor and its exact payload are conclusions, not a
supplied future BusyOnly history. -/
theorem nominated_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (e : Fin n) (j : Nat) (pay : Payload)
    (cur : Current hp base (fun k=>S.getD k fall) len x (.busy commitOp (.out j)))
    (old : project (fun k=>S.getD k fall) x j=.forward pay) (well : Well pay)
    (link : linkAt hp x e (fun k=>S.getD k fall) len j)
    (away : (S.getD j fall).2.val≠1 ∨ oldH6 B x (S.getD j fall).1=false) :
    Event hp (fun k=>S.getD k fall) len x e (.busy commitOp (.out j)) (.busy commitOp (.out (j+1))) ∧
      Current hp base (fun k=>S.getD k fall) len (step x e) (.busy commitOp (.out (j+1))) ∧
      project (fun k=>S.getD k fall) (step x e) (j+1)=.forward pay := by
  obtain ⟨J,K,a,mem,dest,src,dst⟩ := link
  have A : K.source.occurrence.val≠1 ∨ (geometry (oldPair B x e) K.source.side).axes.h6=false := by
    rw [show S.getD j fall=address e K.source from src] at away
    cases hs : K.source.side <;> simpa [address,site,oldPair,oldH6,geometry,hs,longGeometry] using away
  have R := (old_read x e K.source).trans ((congrArg (atCursor x) src).symm.trans old)
  have out := joined_before_center k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
    K a pay mem dest A R well
  have post : project (fun k=>S.getD k fall) (step x e) (j+1)=.forward pay :=
    (congrArg (atCursor (step x e)) dst).trans ((new_read B x e (sep e) a).symm.trans out)
  obtain ⟨m,ev,nxt⟩ := current_step hp C Q fiber closed sep qx e (.busy commitOp (.out j)) cur
  cases ev with
  | transit _ _ d live seen =>
    cases seen with
    | cons M go advance gd tail =>
      cases tail
      cases advance with
      | stay =>
        have empty := nxt.2.2 (j+1) (by omega) J
        exact Token.noConfusion (empty.symm.trans post)
      | forward => exact ⟨.transit _ _ _ live (.cons M go (.forward j) gd (.nil _ _)),nxt,post⟩
      | turn => exact (Nat.lt_irrefl _ J).elim

open BStarResetChartNomination BStarAcquireRailCoverage BStarSeparatingProgress

/-- Ordered service certificate. The word uses one structurally
nominated physical mark for each successive chart index; each
nomination is valid on every equal-layout snapshot. -/
theorem ordered_to_center {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (l : Nat) (L : l<len)
    (centerK : (S.getD l fall).2=1)
    (centerH : oldH6 B base (S.getD l fall).1=true)
    (pay : Payload) (well : Well pay)
    (m : Nat) :
    ∀ (x : X) (j : Nat), j+m=l → Q x →
    Current hp base (fun k=>S.getD k fall) len x (.busy commitOp (.out j)) →
    project (fun k=>S.getD k fall) x j=.forward pay →
    ∃ w : List (Fin n), w.length=m ∧
      BusyOnly hp base (fun k=>S.getD k fall) len commitOp x (.out j) w (.out l) ∧
      project (fun k=>S.getD k fall) (play x w) l=.forward pay ∧
      ∀ (k : Nat) (h : k<w.length) (y : X), (∀ i, Layout B base i=Layout B y i) →
        linkAt hp y w[k] (fun t=>S.getD t fall) len (j+k) := by
  induction m with
  | zero =>
    intro state j J _ I F
    have eq : j=l := by omega
    subst j
    refine ⟨[],rfl,.nil I,F,?_⟩
    intro k hk
    exact (Nat.not_lt_zero _ hk).elim
  | succ m ih =>
    intro state j J qx I F
    have Jl : j<l := by omega
    have Jn : j<len := by omega
    obtain ⟨e,N⟩ := nominate hp C head cont j (Nat.le_of_lt Jn)
    have nom (y : X) (H : ∀ i,Layout B base i=Layout B y i) :
        linkAt hp y e (fun k=>S.getD k fall) len j :=
      (mem_link hp y e _ len j).mp (by simpa only [if_pos Jn] using N y H)
    have fixed := fiber state qx
    have away : (S.getD j fall).2.val≠1 ∨ oldH6 B state (S.getD j fall).1=false := by
      by_cases token : (S.getD j fall).2.val=1
      · right
        apply Bool.eq_false_iff.mpr
        intro H
        have eq := unique_center_index hp C (fun i => (congrArg Prod.fst (fixed i)).symm)
          l j (Nat.le_of_lt L) (Nat.le_of_lt Jn) centerK centerH (Fin.ext token) H
        omega
      · exact .inl token
    obtain ⟨E,I',F'⟩ := nominated_step hp C Q fiber closed sep qx e j pay I F well (nom state fixed) away
    obtain ⟨w,sz,T,out,labels⟩ := ih (step state e) (j+1) (by omega) (closed _ qx e) I' F'
    refine ⟨e::w,by simp [sz],.cons I E T,out,?_⟩
    intro k hk y H
    cases k with
    | zero => exact nom y H
    | succ k =>
      have hk' : k<w.length := by simpa using hk
      have M := labels k hk' y H
      have E : j+k.succ=(j+1)+k := by omega
      simpa only [List.getElem_cons_succ,E] using M

end L4.BStarCommitService
