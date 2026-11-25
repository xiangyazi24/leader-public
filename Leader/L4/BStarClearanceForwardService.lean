import Leader.L4.BStarClearanceSource
import Leader.L4.BStarClearanceIndexedRace
import Leader.L4.BStarClearanceRaceOwner
import Leader.L4.BStarResetChartNomination
import Leader.L4.BStarClearanceMobileRing
import Leader.L4.BStarClearanceIndexedSum

namespace L4.BStarClearanceForwardService
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongTransport BStarLongCommand BStarLongEvents BStarLongWork
open BStarH6WordChart BStarLongFiberOwner BStarLongFixedRouting
open BStarAcquireVisitOrder BStarAcquireAnchors BStarResetChartTouch BStarAcquireLiteralChain BStarAcquireRailCoverage
open BStarResetMarkAdapter BStarSeparatingProgress BStarClearanceDataChart
open BStarClearanceRightmost BStarClearanceIndexedSum
open BStarClearanceOffset BStarClearanceCommandSum

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

def Forward (x : X) (a : Pos n) : Prop :=
  ∃ u, atSite (x a.1).long a.2=.forward u

private theorem bind_F (g : LongGeometry) (j : Fin 11) (p : Payload) :
    ∃ q, BStarLongCommand.bind g j (.forward p)=.forward q := by
  unfold BStarLongCommand.bind
  dsimp only
  split <;> split <;> first | exact ⟨_,rfl⟩ | (split <;> exact ⟨_,rfl⟩)

private theorem observe_counter (g : LongGeometry) (a : AtK) (q v : Payload)
    (O : observe a g q=some v) :
    q.race.toNat=1 ∨ q.race.toNat=2 ∨ q.race.toNat=3 := by
  unfold observe at O
  split at O
  · dsimp only at O
    let n := if a.side==.left then 3 else 2
    change (if q.race.toNat==1 then some {q with race:=BitVec.ofNat 3 n}
      else if (q.race.toNat==2 || q.race.toNat==3) && q.race.toNat != n
        then some {q with race:=BitVec.ofNat 3 (q.race.toNat+2)} else none)=some v at O
    split at O
    · exact .inl (by simpa using ‹(q.race.toNat==1)=true›)
    · split at O
      · rename_i t
        exact .inr (by simpa using (Bool.and_eq_true_iff.mp t).1)
      · contradiction
  · contradiction

/-- Choose the actual selected non-door departure for any chart F.
Transport faults count as advancing. The only residual alternatives
are a legal gate race at the same physical slot or an occupied active
mobile of its same owner. -/
theorem classify_at {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (same : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (j : Nat) (hj : j≤len) (F : Forward x (S.getD j fallback)) :
    let a := S.getD j fallback
    (∃ e C q, (C,.advance q)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) ∧
      physicalOwner (oldH6 B base) e cmdDispl C.source=o.val) ∨
    (∃ q, BStarLongCommand.bind (longGeometry B (x a.1)) a.2 (atSite (x a.1).long a.2)=.forward q ∧
      (q.fault==0 && gate q.opcode.toNat a.2 (longGeometry B (x a.1)))=true ∧
      (q.race.toNat=1 ∨ q.race.toNat=2 ∨ q.race.toNat=3)) ∨
    (∃ i s, activeSheet (longGeometry B (base i)) s=true ∧
      dataOwner (oldH6 B base) i s=o.val ∧ mobile x i s≠.empty) := by
  dsimp only
  let adr := fun k => S.getD k fallback
  let a := adr j
  obtain ⟨e,E⟩ := BStarResetChartNomination.nominate _ chart head cont j hj
  have M := E x same
  have Nom : ∃ C, C∈orderedCommands (oldPair B x e) ∧ C.kind≠.door ∧ a=address e C.source := by
    by_cases jlt : j<len
    · rw [if_pos jlt] at M
      obtain ⟨_,C,d,Cm,hd,A,_⟩ := (mem_link hp x e adr len j).mp M
      have K := (BStarAcquireReturn.link_shape _ C d Cm hd).2.1
      exact ⟨C,Cm,by rw [K]; decide,A⟩
    · have J : j=len := by omega
      rw [if_neg jlt] at M
      obtain ⟨C,Cm,K,_,_,A⟩ := (mem_terminal hp x e adr len).mp M
      exact ⟨C,Cm,by rw [K]; decide,by simpa [a,adr,J] using A⟩
  obtain ⟨C,Cm,Cnd,A⟩ := Nom
  have hn := chart.length
  have S₀ : a∈S := by
    change S.getD j fallback∈S
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  have own := (chart.entries a S₀).2
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have onSite (z : At (Fin 11)) : geometry g z.side=longGeometry B (x (site e z.side)) ∧
      readK raw z=atSite (x (site e z.side)).long z.occurrence := by
    obtain ⟨side,k⟩ := z
    cases side <;> exact ⟨rfl,rfl⟩
  have view : geometry g C.source.side=longGeometry B (x a.1) ∧
      readK raw C.source=atSite (x a.1).long a.2 := by
    rw [A]
    exact onSite C.source
  have own' : physicalOwner (oldH6 B base) e cmdDispl C.source=o.val := by
    rw [show a=address e C.source from A] at own
    exact own
  obtain ⟨p,P⟩ := F
  obtain ⟨q,Q⟩ := bind_F (longGeometry B (x a.1)) a.2 p
  have qs : BStarLongCommand.bind (longGeometry B (x a.1)) a.2 (atSite (x a.1).long a.2)=.forward q := by
    change atSite (x a.1).long a.2=.forward p at P
    rwa [P]
  have aj : a.2=C.source.occurrence := congrArg Prod.snd A
  have Qb : bound g (readK raw) C.source=.forward q := by
    unfold bound
    rw [view.1,view.2,←aj]
    exact qs
  rcases BStarClearanceBlockade.nominated_forward g raw C q Cm Cnd Qb with H|H|H
  · obtain ⟨p,Hp⟩ := H
    exact .inl ⟨e,C,p,Hp,own'⟩
  · obtain ⟨side,v,_,_,O⟩ := H.2
    have gates : (q.fault==0 && gate q.opcode.toNat a.2 (longGeometry B (x a.1)))=true := by
      unfold observe at O
      split at O
      · rename_i W
        rwa [aj,←view.1]
      · contradiction
    have R := observe_counter _ _ _ _ O
    exact .inr (.inl ⟨q,qs,gates,R⟩)
  · obtain ⟨s,M,Aactive,D,_,_,occ⟩ := H.2
    let i := site e C.source.side
    have active₀ : activeSheet (longGeometry B (base i)) s=true := by
      have V : geometry g C.source.side=longGeometry B (x i) := (onSite C.source).1
      rw [V] at Aactive
      have S := same i
      have I : (longGeometry B (base i)).inside=(longGeometry B (x i)).inside :=
        congrArg (fun a : Bool × Bool × Bool => a.2.1) S
      cases s <;> simp_all [activeSheet]
    have dOwn : dataOwner (oldH6 B base) i s=o.val := by
      change owner _ _ (dataDispl s)=_
      rw [←D]
      exact own'
    have packet : mobile x i s≠.empty := by
      have H (side : Side) :
          (BStarLongPrep.view raw ⟨side,s⟩).mobile = mobile x (site e side) s := by
        cases side <;> rfl
      rw [H] at occ
      exact occ
    exact .inr (.inr ⟨i,s,active₀,dOwn,packet⟩)

#print axioms classify_at

open BStarClearanceIndexedWait BStarAcquireLiteralChain
open BStarClearanceAggregate

/-- Every arbitrary old chart F has a one-mark first-coordinate or
mobile payment, unless the very nominated mark is the owner's
source boundary. No assumption is made about foreign source doors. -/
theorem nominate {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (same : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (cb : correct (oldH6 B base) hh 5 base) (cx : correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (headx : ∀ i, let g := longGeometry B (x i); (!g.axes.h6 || g.inside)=true)
    (contx : ∀ i, let g := oldPair B x i; continuation g.1 g.2=true)
    (j : Nat) (hj : j≤len) (F : Forward x (S.getD j fallback)) :
    ∃ e : Fin n, let y := AllSizeS1Geometry.step B x e
      ¬BeforeOwnService hp x (endpoint (oldH6 B base) hh o 0).1 e ∨
      BStarClearanceAggregate.total (physicalRank B base y (distance S)) S <
        BStarClearanceAggregate.total (physicalRank B base x (distance S)) S ∨
      BStarClearanceMobileRing.ringRank hp base hh y o.val <
        BStarClearanceMobileRing.ringRank hp base hh x o.val := by
  classical
  let root := (endpoint (oldH6 B base) hh o 0).1
  let f (x : X) := BStarClearanceAggregate.total (physicalRank B base x (distance S)) S
  let m (x : X) := BStarClearanceMobileRing.ringRank hp base hh x o.val
  have advance (e : Fin n) (H : ∃ C q, (C,.advance q)∈actualOffers (oldPair B x e)
      ((x e).long,(x (rightNeighbor e)).long) ∧
      physicalOwner (oldH6 B base) e cmdDispl C.source=o.val) :
      ¬BeforeOwnService hp x root e ∨ f (AllSizeS1Geometry.step B x e)<f x := by
    by_cases W : BeforeOwnService hp x root e
    · exact .inr ((pre_service_sum hp chart same cb cx e (sep e) W).2 H)
    · exact .inl W
  have H6 : oldH6 B x=oldH6 B base := funext (fun i => (congrArg Prod.fst (same i)).symm)
  rcases classify_at hp chart same head cont j hj F with ⟨e,C,q,A,O⟩|⟨q,Q,G,R⟩|O
  · rcases advance e ⟨C,q,A,O⟩ with W|P
    · exact ⟨e,.inl W⟩
    · exact ⟨e,.inr (.inl P)⟩
  · let a := S.getD j fallback
    have ls := chart.length
    have am : a∈S := by
      change S.getD j fallback∈S
      rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
      exact List.getElem_mem _
    obtain ⟨F0,G0⟩ := Bool.and_eq_true_iff.mp G
    rw [gate_at_ordinal hp (oldH6 B base) hh x (congrFun H6) cx a.1 q.opcode.toNat a.2] at G0
    obtain ⟨s,_,_,P⟩ := BStarClearanceIndexedRace.nominate hp chart same cb cx sep a.1 a.2 q
      am Q (beq_iff_eq.mp F0) G0 R
    let e := BStarClearanceRaceMark.incident a.1 s
    by_cases W : BeforeOwnService hp x root e
    · exact ⟨e,.inr (.inl (P W))⟩
    · exact ⟨e,.inl W⟩
  · obtain ⟨e,P⟩ := BStarClearanceMobileRing.rightmost_fixed hp base x hh same o.val sep headx contx O
    rcases P with K|H
    · exact ⟨e,.inr (.inr K)⟩
    · rcases advance e H with W|P
      · exact ⟨e,.inl W⟩
      · exact ⟨e,.inr (.inl P)⟩

#print axioms nominate

/-- In the exact held-source domain, the source-boundary alternative
cannot occur, so an old forward always gets a strict service mark. -/
theorem nominate_held {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (same : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (cb : correct (oldH6 B base) hh 5 base) (cx : correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (headx : ∀ i, let g := longGeometry B (x i); (!g.axes.h6 || g.inside)=true)
    (contx : ∀ i, let g := oldPair B x i; continuation g.1 g.2=true)
    (held : BStarClearanceSource.Held (x (endpoint (oldH6 B base) hh o 0).1).long)
    (j : Nat) (hj : j≤len) (F : Forward x (S.getD j fallback)) :
    ∃ e : Fin n, let y := AllSizeS1Geometry.step B x e
      BStarClearanceAggregate.total (physicalRank B base y (distance S)) S <
        BStarClearanceAggregate.total (physicalRank B base x (distance S)) S ∨
      BStarClearanceMobileRing.ringRank hp base hh y o.val <
        BStarClearanceMobileRing.ringRank hp base hh x o.val := by
  obtain ⟨e,W⟩ := nominate hp chart same cb cx sep head cont headx contx j hj F
  refine ⟨e,?_⟩
  exact W.resolve_left (fun N => N (BStarClearanceSource.held_before hp x _ e held))

#print axioms nominate_held
end L4.BStarClearanceForwardService
