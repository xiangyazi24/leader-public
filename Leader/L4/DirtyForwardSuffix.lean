import Leader.L4.DirtyForwardAdvance
import Leader.L4.DirtyTrailSuffix
import Leader.L4.BStarClearanceForwardService
import Leader.L4.BStarFenceCoverage

namespace L4.DirtyForwardSuffix
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken
open BStarLongTransport BStarLongCommand BStarLongEvents BStarLongWork
open BStarH6WordChart BStarH6Ordinal BStarLongFiberOwner BStarLongFixedRouting
open BStarAcquireVisitOrder BStarAcquireAnchors BStarResetChartTouch BStarAcquireLiteralChain
open BStarAcquireRailCoverage BStarResetMarkAdapter BStarClearanceDataChart
open BStarClearanceOffset BStarClearanceIndexedSum BStarClearanceIndexedWait
open BStarFenceLineGeometry BStarClearanceSource DirtyLeastForward
open BStarClearanceForwardService BStarClearanceCommandFrame

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- After the two lines are empty, a forward at a non-K1 chart occurrence
has a literal selected advance; transport faults still count. -/
theorem nominate_empty {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (same : ∀ i,Layout B base i=Layout B x i)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; continuation g.1 g.2=true)
    {l d w : Nat} (dp : 0<d)
    (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l w)
    (RF : RightFrame B base (S.getD len fall).1 d w)
    (seam : BStarCopyRightStrip.addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<w))
    (E : BStarFenceSweepClock.Empty (BStarFenceEmptySuffix.ownedLines
      (S.getD 0 fall).1 (S.getD len fall).1 l d w x))
    (j : Nat) (hj : j≤len) (late : (S.getD j fall).2.val≠1)
    (F : ringF x (S.getD j fall)) :
    ∃ e C q, address e C.source=S.getD j fall ∧ C.kind≠.door ∧
      (C,.advance q)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) := by
  let adr := fun k=>S.getD k fall
  let a := adr j
  obtain ⟨e,M⟩ := BStarResetChartNomination.nominate hp chart head cont j hj
  have H := M x same
  have Nom : ∃ C, C∈orderedCommands (oldPair B x e) ∧ C.kind≠.door ∧ a=address e C.source := by
    by_cases jlt : j<len
    · rw [if_pos jlt] at H
      obtain ⟨_,C,dst,Cm,hd,A,_⟩ := (mem_link hp x e adr len j).mp H
      have K := (BStarAcquireReturn.link_shape _ C dst Cm hd).2.1
      exact ⟨C,Cm,by rw [K]; decide,A⟩
    · have J : j=len := by omega
      rw [if_neg jlt] at H
      obtain ⟨C,Cm,K,_,_,A⟩ := (mem_terminal hp x e adr len).mp H
      exact ⟨C,Cm,by rw [K]; decide,by simpa [a,adr,J] using A⟩
  obtain ⟨C,Cm,Cnd,A⟩ := Nom
  have lenS := chart.length
  have own : address e C.source∈S := by
    rw [←A]
    change S.getD j fall∈S
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have FF : IsForward g C.source (BStarLongRouting.readRaw raw C.source) := by
    rw [isForward_iff]
    change ringF x a at F
    rw [A] at F
    rcases hh' : C.source with ⟨s,k⟩
    rw [hh'] at F
    cases s <;> exact F
  obtain ⟨pay,P⟩ := FF
  change bound g (readK raw) C.source=.forward pay at P
  rcases BStarClearanceBlockade.nominated_forward g raw C pay Cm Cnd P with Av|Race|Block
  · obtain ⟨q,Q⟩ := Av
    exact ⟨e,C,q,A.symm,Cnd,Q⟩
  · obtain ⟨side,v,_,_,O⟩ := Race.2
    have nz : C.source.occurrence.val≠1 := by
      exact fun Z => late ((congrArg (fun k : Pos n=>k.2.val) A).trans Z)
    unfold observe at O
    simp [gate,nz] at O
  · obtain ⟨sh,T,_,_,_,_,N⟩ := Block.2
    have cov := BStarFenceCoverage.chart_cover hp chart same dp LF RF seam flags e C own sh T
    have M := BStarFenceNominatedClear.mobile_empty x _ _ l d w E _ sh cov
    exfalso
    apply N
    cases Ls : C.source.side
    · change (BStarLongPackets.readLane (BStarLongPackets.Sheet.index sh) (x e).long).mobile=.empty
      simpa only [Ls,site] using M
    · change (BStarLongPackets.readLane (BStarLongPackets.Sheet.index sh) (x (rightNeighbor e)).long).mobile=.empty
      simpa only [Ls,site] using M

/-- A post-drain forward suffix pays by the highest remaining forward
distance, not by total traffic. If the supplied phase predicate exits
before the source releases, the theorem stops at that literal exit. -/
theorem forward_suffix_expected {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (head : ∀ i,let g:=longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair B base i; continuation g.1 g.2=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    {l d w : Nat} (dp : 0<d)
    (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l w)
    (RF : RightFrame B base (S.getD len fall).1 d w)
    (seam : BStarCopyRightStrip.addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<w))
    (Phase : X→Prop)
    (empty : ∀ y,Q y→Phase y→BStarFenceSweepClock.Empty (BStarFenceEmptySuffix.ownedLines
      (S.getD 0 fall).1 (S.getD len fall).1 l d w y))
    (late : ∀ y,Q y→Phase y→∀ j,j≤len→ringF y (S.getD j fall)→(S.getD j fall).2.val≠1) :
    let root := (endpoint (oldH6 B base) hh o 0).1
    Height.IIDExpectedHittingTimeAtMost step
      (fun y=>¬Held (y root).long ∨ ¬Phase y ∨ ∀u∈S,¬ringF y u) x (n*S.length) := by
  classical
  dsimp only
  let root := (endpoint (oldH6 B base) hh o 0).1
  let stop := fun y=>¬Held (y root).long ∨ ¬Phase y ∨ ∀u∈S,¬ringF y u
  let Bound := fun (y : X) (a : Nat)=>∀ u∈S,ringF y u→distance S u≤a
  let Live := fun y a=>Q y ∧ ¬stop y ∧ Bound y a
  have lenS := chart.length
  have dist_pos {u} (U : u∈S) : 0<distance S u := by
    obtain ⟨i,hi,_,H⟩ := DirtyReplyOrigin.reply_distance_mem chart.nodup U
    change S.length+1-distance S u=i+1 at H
    have d := Nat.sub_le S.length (S.idxOf u)
    change distance S u≤S.length at d
    omega
  have pos (y : X) (a : Nat) (Y : Live y a) : 0<a := by
    apply Classical.byContradiction
    intro N
    apply Y.2.1
    exact .inr (.inr (fun u U F => by have D := dist_pos U; have M := Y.2.2 u U F; omega))
  have advance (y : X) (a : Nat) (Y : Live y a) : ∃ d : Fin n,∀ e : Fin n,
      stop (step y e) ∨ ∃ a',Live (step y e) a' ∧ a'≤a ∧ (e=d→a'<a) := by
    have H : Held (y root).long := Classical.not_not.mp (fun h=>Y.2.1 (.inl h))
    have phase : Phase y := Classical.not_not.mp (fun h=>Y.2.1 (.inr (.inl h)))
    have origin (e : Fin n) (u : Pos n) (U : u∈S) (F : ringF (step y e) u) :=
      ring_origin hp chart (layout _ Y.1) e (sep e) (held_before hp y root e H) u U F
    have weak (e : Fin n) : Bound (step y e) a := by
      intro u U F
      rcases origin e u U F with same|⟨v,V,old,T⟩
      · exact Y.2.2 u U same
      · have M := Y.2.2 v V old
        omega
    suffices Pay : ∃ d : Fin n,Bound (step y d) (a-1) by
      obtain ⟨d,J⟩ := Pay
      refine ⟨d,fun e=>?_⟩
      by_cases Hit : stop (step y e)
      · exact .inl Hit
      by_cases E : e=d
      · subst e
        exact .inr ⟨a-1,⟨closed _ _ Y.1,Hit,J⟩,Nat.sub_le _ _,fun _=>by have := pos y a Y; omega⟩
      · exact .inr ⟨a,⟨closed _ _ Y.1,Hit,weak _⟩,Nat.le_refl _,fun F=>(E F).elim⟩
    by_cases top : ∃ u∈S,ringF y u ∧ distance S u=a
    · obtain ⟨u,U,F,rEq⟩ := top
      obtain ⟨i,hi,Id,Ieq⟩ := DirtyReplyOrigin.reply_distance_mem chart.nodup U
      have uid : S.getD i fall=u := (List.getElem_eq_getD (h:=hi) fall).symm.trans Id
      have iv : i≤len := by omega
      have Fi : ringF y (S.getD i fall) := uid.symm ▸ F
      obtain ⟨e,C,q,A,ND,Actual⟩ := nominate_empty hp chart (layout _ Y.1) head cont dp LF RF seam flags
        (empty y Y.1 phase) i iv (late y Y.1 phase i iv Fi) Fi
      have erase := DirtyForwardAdvance.ring_advance_removes_forward hp y e (sep e) C q Actual ND
      rw [A,uid] at erase
      refine ⟨e,fun v V VF=>?_⟩
      rcases origin e v V VF with same|⟨z,Z,old,T⟩
      · obtain ⟨k,hk,Idk,keq⟩ := DirtyReplyOrigin.reply_distance_mem chart.nodup V
        have M := Y.2.2 v V same
        change S.length+1-distance S u=i+1 at Ieq
        change S.length+1-distance S v=k+1 at keq
        have Du : distance S u≤S.length := Nat.sub_le _ _
        have Dv : distance S v≤S.length := Nat.sub_le _ _
        by_cases ki : k=i
        · subst k
          exact (erase (Id ▸ (Idk.symm ▸ VF))).elim
        · omega
      · have M := Y.2.2 z Z old
        omega
    · obtain ⟨e,_⟩ := hh
      refine ⟨e,fun u U F=>?_⟩
      rcases origin e u U F with same|⟨v,V,old,T⟩
      · have M := Y.2.2 u U same
        have N : distance S u≠a := fun N=>top ⟨u,U,same,N⟩
        omega
      · have M := Y.2.2 v V old
        omega
  apply ResetReturnIID.iid_of_relational_rank step stop Live pos advance
  by_cases Hit : stop x
  · exact .inl Hit
  · exact .inr ⟨I,Hit,fun u _ _=>Nat.sub_le _ _⟩

end L4.DirtyForwardSuffix
