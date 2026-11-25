import Leader.L4.DirtyPrepWeak
import Leader.L4.DirtyPrepRacePay

namespace L4.DirtyPrepStrict
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongEvents BStarLongTransport BStarLongCommand BStarLongRouting
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarH6WordChart BStarResetMarkAdapter BStarResetCycle BStarLongFixedRouting
open BStarClearanceIndexedSum BStarClearanceOffset BStarClearanceForward
open BStarClearanceCommandSum (physicalRank)
open BStarClearanceRaceMark DirtyLeastForward DirtyPrepRank DirtyPrepWeak DirtyForwardAdvance

private theorem observe_live (g : LongGeometry) (a : AtK) (p v : Payload)
    (O : observe a g p=some v) :
    (p.fault==0 && gate p.opcode.toNat a.occurrence g)=true ∧
      (p.race.toNat=1 ∨ p.race.toNat=2 ∨ p.race.toNat=3) := by
  unfold observe at O
  split at O
  · rename_i G
    refine ⟨G,?_⟩
    dsimp only at O
    let n := if a.side==.left then 3 else 2
    change (if p.race.toNat==1 then some {p with race:=BitVec.ofNat 3 n}
      else if (p.race.toNat==2 || p.race.toNat==3) && p.race.toNat != n
        then some {p with race:=BitVec.ofNat 3 (p.race.toNat+2)} else none)=some v at O
    split at O
    · exact .inl (by simpa using ‹(p.race.toNat==1)=true›)
    · split at O
      · rename_i t
        exact .inr (by simpa using (Bool.and_eq_true_iff.mp t).1)
      · contradiction
  · contradiction

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- A real nomination pays the least prep slot, not merely some other
simultaneous advancing block in the same owner's aggregate. -/
theorem prep_least_pays
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ j,Layout B base j=Layout B x j)
    (head : ∀ j,let g:=longGeometry B (base j); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ j,let g:=oldPair B base j; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base) (cx : correct (oldH6 B base) hh 5 x)
    (i : Nat) (il : i<len) :
    let u := S.getD i fall
    u.2.val≤5 → ringF x u → (∀ j,j<i→¬ringF x (S.getD j fall)) →
    ∃ e,ringF (step x e) u → debt hp base (step x e) u<debt hp base x u := by
  dsimp only
  let u := S.getD i fall
  intro prep F least
  have lenS := chart.length
  have iS : i<S.length := by omega
  have mem : u∈S := by
    dsimp only [u]
    rw [←List.getElem_eq_getD (h:=iS) fall]
    exact List.getElem_mem iS
  have noEarlier : ∀ v∈S,distance S u<distance S v → ¬ringF x v := by
    intro v vS lt
    obtain ⟨j,jS,ev⟩ := List.mem_iff_getElem.mp vS
    have eq : u=S[i] := (List.getElem_eq_getD (h:=iS) fall).symm
    rw [eq,←ev,distance_idx chart.nodup iS,distance_idx chart.nodup jS] at lt
    have E : S.getD j fall = v := (List.getElem_eq_getD (h:=jS) fall).symm.trans ev
    exact E ▸ least j (by omega)
  obtain ⟨edge,links,_⟩ := fixed_nominations hp chart head cont
  let e := edge (.link i)
  obtain ⟨C,d,sel,hd,src,_⟩ := links x layout i il
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have loc : u=address e C.source := src
  have old : (∃ q,bound g (readK raw) C.source=.forward q) ↔ ringF x u := by
    rw [loc]
    rcases a : C.source with ⟨side,j⟩
    cases side <;> exact isForward_iff _ _ _
  obtain ⟨q,oldF⟩ := old.mpr F
  have small : C.source.occurrence.val≤5 := by
    have E := congrArg Prod.snd loc
    change u.2=C.source.occurrence at E
    simpa only [←E] using prep
  have nd : C.kind≠.door := by rw [(BStarAcquireReturn.link_shape g C d sel hd).2.1]; decide
  rcases DirtyPrepFrontier.nominate_prep g raw C q sel nd small oldF with ⟨q',A⟩|⟨_,side,v,_,_,obs⟩
  · exact ⟨e,fun Fnew=>(ring_advance_removes_forward hp x e (sep e) C q' A nd (loc ▸ Fnew)).elim⟩
  · let k := incident u.1 side
    let a : AtK := ⟨side,u.2⟩
    let z := (x k,x (rightNeighbor k))
    let G := oldPair B x k
    let O : Pair (BitVec LW) := Pair.map LargeSite.long z
    have onSite : site k side=u.1 := incident_site _ _
    have addr : address k a=u := Prod.ext onSite rfl
    have gOld : geometry g C.source.side=longGeometry B (x u.1) := by
      rw [congrArg Prod.fst loc]
      cases Cs : C.source.side <;> simp [g,geometry,oldPair,site,Cs]
    have gNew : geometry G a.side=longGeometry B (x u.1) := by
      change geometry (oldPair B x k) side=_
      rw [←onSite]
      cases side <;> rfl
    have occ : C.source.occurrence=u.2 := (congrArg Prod.snd loc).symm
    have Rold : readK raw C.source=atSite (x u.1).long u.2 := by
      rw [loc]
      cases Cs : C.source.side <;> simp [Cs,raw,readK,lane,site] <;> rfl
    have Rnew : readK O a=atSite (x u.1).long u.2 := by
      rw [←addr]
      cases side <;> rfl
    have Hnew : bound G (readK O) a=.forward q := by
      unfold bound at oldF ⊢
      rw [gOld,Rold,occ] at oldF
      rw [gNew,Rnew]
      exact oldF
    have obs' : observe a (geometry G a.side) q=some v := by
      rw [gOld,occ] at obs
      rw [gNew]
      exact obs
    have live := observe_live _ _ _ _ obs'
    have K1 : a.occurrence.val=1 := by
      have A := (Bool.and_eq_true_iff.mp live.1).2
      unfold gate at A
      exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp A).1
    have ret := DirtyPrepRacePay.race_pays_or_touching_advance k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      z a q v K1 Hnew (beq_iff_eq.mp (Bool.and_eq_true_iff.mp live.1).1) live.1 live.2 obs'
    refine ⟨k,fun still=>?_⟩
    rcases ret with strict|⟨C',pay,offer,touch⟩
    · have cur (y : X) := rank_fixed hp (oldH6 B base) hh base x y (fun _=>rfl)
          (fun t=>(congrArg Prod.fst (layout t)).symm) cb cx (fun _=>0) u
      rw [debt_rank hp,debt_rank hp,cur _,cur _,←addr]
      dsimp only [a] at strict ⊢
      cases side
      · simp only [physicalRank,site,AllSizeS1Geometry.step,if_true]
        exact strict
      · simp only [physicalRank,site,AllSizeS1Geometry.step,if_neg (Ne.symm (sep k)),if_true]
        exact strict
    · exact (touching_advance_clears_least hp chart layout k (sep k) a (addr.symm ▸ mem)
        (addr.symm ▸ noEarlier) C' pay offer touch (addr.symm ▸ still)).elim

#print axioms prep_least_pays
end L4.DirtyPrepStrict
