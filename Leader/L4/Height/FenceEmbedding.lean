import Leader.L4.Height.FenceProduction
import Leader.L4.BStarCopyLeftStrip
import Leader.L4.BStarCopyRightAuthority
import Leader.L4.Height.FenceFlow

namespace L4.Height.FenceEmbedding
open AllSizeProtocol BStarTrace BStarH6WordChart BStarLongClaims BStarLongWork
open BStarCopyLeftStrip BStarCopyRightStrip FenceProduction

def returnRail (seam i : Nat) : Sheet := if i<seam then .rd else .rs

private theorem paired {g : Pair LongGeometry} (a b : Bool)
    (edge : hop (L (if a then .ls else .ld)) (R (if b then .ls else .ld)) ∈ dataClaims g) :
    hop (R (if b then .rd else .rs)) (L (if a then .rd else .rs)) ∈ dataClaims g := by
  cases a <;> cases b <;> cases I : g.1.inside <;> cases D : ends g.1 <;>
    cases H : g.2.axes.h6 <;> cases J : g.2.inside <;>
    simp_all [dataClaims,hop,ending,L,R]

/-- One physical geometry strip supplies both directed copies of every
internal bond. A strip based at V gives the complete right line in reverse,
including the RD prefix at V itself. -/
theorem strip_bond {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {root : Fin n} {seam width : Nat}
    (S : BStarCopyLeftStrip.Strip b x root seam width)
    (k : Nat) (interior : k+1<seam+width) :
    let g := oldPair b x (addr root k)
    hop (L (BStarCopyLeftStrip.rail seam k)) (R (BStarCopyLeftStrip.rail seam (k+1)))∈orderedData g [] ∧
    hop (R (returnRail seam (k+1))) (L (returnRail seam k))∈orderedData g [] := by
  let left := hop (L (BStarCopyLeftStrip.rail seam k)) (R (BStarCopyLeftStrip.rail seam (k+1)))
  have raw := (BStarCopyLeftStrip.raw_hop S k interior left rfl).mpr rfl
  refine ⟨BStarCopyRightAuthority.raw_is_selected_empty _ _ raw,?_⟩
  apply BStarCopyRightAuthority.raw_is_selected_empty
  simpa only [returnRail,decide_eq_true_eq] using
    paired (g:=oldPair b x (addr root k)) (decide (k<seam)) (decide (k+1<seam))
      (by simpa only [left,BStarCopyLeftStrip.rail,decide_eq_true_eq] using raw)

private theorem left_exit (g : Pair LongGeometry) (d : ends g.1=true) :
    ending (L .ld)∈orderedData g [] := by
  apply BStarCopyRightAuthority.raw_is_selected_empty
  simp [dataClaims,d]

private theorem right_exit (g : Pair LongGeometry) (d : g.2.axes.h6=true) :
    ending (R .rd)∈orderedData g [] := by
  apply BStarCopyRightAuthority.raw_is_selected_empty
  simp [dataClaims,d]

theorem strip_ends {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {root : Fin n} {seam width : Nat}
    (S : BStarCopyLeftStrip.Strip b x root seam width) :
    ending (L .ld) ∈ orderedData (oldPair b x (addr root (seam+width-1))) [] ∧
    ending (R .rd) ∈ orderedData (oldPair b x (RearTrace.predecessor root)) [] := by
  refine ⟨left_exit _ S.last,right_exit _ ?_⟩
  change oldH6 b x (rightNeighbor (RearTrace.predecessor root))=true
  rw [RearTrace.right_predecessor]
  exact S.source_header

private theorem no_left_root (g : Pair LongGeometry) (h : g.2.axes.h6=true)
    (d : DataClaim) (m : d∈orderedData g []) : R .ls∉d.slots := by
  have raw := BStarLongFenceTopology.selected_data_raw _ _ _ m
  cases I : g.2.inside <;> cases E : ends g.1 <;>
    simp [dataClaims,h,I,E] at raw <;> grind [Claim.slots,hop,ending,L,R]

private theorem no_right_root (g : Pair LongGeometry) (h : ends g.1=true)
    (d : DataClaim) (m : d∈orderedData g []) : L .rs∉d.slots := by
  have raw := BStarLongFenceTopology.selected_data_raw _ _ _ m
  cases H : g.2.axes.h6 <;> cases I : g.2.inside <;> cases J : g.1.inside <;>
    simp [dataClaims,h,H,I,J] at raw <;> grind [Claim.slots,hop,ending,L,R]

private theorem frame_at {g : Pair LongGeometry} (old : At Sheet → Bool) (z : At Sheet)
    (absent : ∀ d, d∈orderedData g [] → z∉d.slots) : comparisonAt g old z=old z := by
  classical
  have ne : ¬ ∃ d,d∈orderedData g [] ∧ z∈d.slots := fun ⟨d,m,t⟩ => absent d m t
  simp [comparisonAt,ne]

theorem open_sources {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n → LargeSite a} {root : Fin n} {seam width : Nat}
    (S : BStarCopyLeftStrip.Strip b x root seam width) (old : At Sheet → Bool) :
    comparisonAt (oldPair b x (RearTrace.predecessor root)) old (R .ls)=old (R .ls) ∧
    comparisonAt (oldPair b x (addr root (seam+width-1))) old (L .rs)=old (L .rs) := by
  refine ⟨frame_at old _ (no_left_root _ ?_),frame_at old _ (no_right_root _ S.last)⟩
  change oldH6 b x (rightNeighbor (RearTrace.predecessor root))=true
  rw [RearTrace.right_predecessor]
  exact S.source_header

/-- Both changing slots at an actual nominal hop, read in its travel direction. -/
theorem hop_update (g : Pair LongGeometry) (old : At Sheet → Bool) (a b : At Sheet)
    (different : a≠b) (selected : hop a b ∈ orderedData g []) :
    comparisonAt g old a=(old a && old b) ∧ comparisonAt g old b=(old a || old b) := by
  have atSource := comparisonAt_on_claim g old a (hop a b) selected (by simp [hop,Claim.slots])
  have atDest := comparisonAt_on_claim g old b (hop a b) selected (by simp [hop,Claim.slots])
  exact ⟨by simpa [hop] using atSource,by simpa [hop,Ne.symm different] using atDest⟩

theorem exit_update (g : Pair LongGeometry) (old : At Sheet → Bool) (a : At Sheet)
    (selected : ending a ∈ orderedData g []) : comparisonAt g old a=false := by
  exact comparisonAt_on_claim g old a (ending a) selected (by simp [ending,Claim.slots])

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- A single physical label simultaneously updates the forward and reflected
line slots on any interior bond, with old occupancies from the same ring. -/
theorem paired_updates {x : X} {base : Fin n} {seam width : Nat}
    (S : BStarCopyLeftStrip.Strip B x base seam width) (k : Nat) (K : k+1<seam+width)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (u : Fin n → Sheet → Bool) :
    let e := addr base k
    let j := addr base (k+1)
    let a := BStarCopyLeftStrip.rail seam k
    let b := BStarCopyLeftStrip.rail seam (k+1)
    let c := returnRail seam k
    let d := returnRail seam (k+1)
    let v := comparisonNext hp x e u
    v e a=(u e a && u j b) ∧ v j b=(u e a || u j b) ∧
    v j d=(u j d && u e c) ∧ v e c=(u j d || u e c) := by
  dsimp only
  let e := addr base k
  let old (a : At Sheet) := u (site e a.side) a.occurrence
  obtain ⟨left,right⟩ := strip_bond S k K
  obtain ⟨ls,ld⟩ := hop_update _ old _ _ (by simp [L,R]) left
  obtain ⟨rs,rd⟩ := hop_update _ old _ _ (by simp [L,R]) right
  have ne : rightNeighbor e≠e := Ne.symm (sep e)
  simpa only [BStarCopyRightStrip.addr_next,comparisonNext,if_pos rfl,if_neg ne,ite_true,
    old,site,L,R,e] using And.intro ls (And.intro ld (And.intro rs rd))

def leftBond {n : Nat} (base : Fin n) (k : Nat) : Fin n := addr base (k-1)

def rightBond {n : Nat} (base : Fin n) (h k : Nat) : Fin n :=
  RearTrace.predecessor (addr base (h-k))

def leftStock {n : Nat} (base : Fin n) (seam : Nat)
    (u : Fin n → Sheet → Bool) (k : Nat) : Bool :=
  u (addr base (k-1)) (BStarCopyLeftStrip.rail seam (k-1))

def rightStock {n : Nat} (base : Fin n) (seam h : Nat)
    (u : Fin n → Sheet → Bool) (k : Nat) : Bool :=
  u (addr base (h-k)) (returnRail seam (h-k))

private theorem first_site (base : Fin n) : addr base 0=base :=
  Fin.ext (Nat.mod_eq_of_lt base.isLt)

private theorem predecessor_of_next (base : Fin n) (i : Nat) :
    RearTrace.predecessor (addr base (i+1))=addr base i := by
  rw [addr_next,RearTrace.predecessor_right]

private theorem comparison_left (x : X) (e : Fin n) (u : Fin n → Sheet → Bool) (s : Sheet) :
    comparisonNext hp x e u e s =
      comparisonAt (oldPair B x e) (fun a => u (site e a.side) a.occurrence) (L s) := by
  simp only [comparisonNext,if_pos rfl]

private theorem comparison_right (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (u : Fin n → Sheet → Bool) (s : Sheet) :
    comparisonNext hp x e u (rightNeighbor e) s =
      comparisonAt (oldPair B x e) (fun a => u (site e a.side) a.occurrence) (R s) := by
  simp only [comparisonNext,if_neg (Ne.symm sep),ite_true]

private theorem comparison_off_pair (x : X) (e i : Fin n) (u : Fin n → Sheet → Bool)
    (s : Sheet) (l : i≠e) (r : i≠rightNeighbor e) :
    comparisonNext hp x e u i s=u i s := by
  simp only [comparisonNext,if_neg l,if_neg r]

/-- The clockwise LS/LD strip obeys exact open-exclusion flow under
the assembled comparison on each physical mark. -/
theorem left_balance {x : X} {base : Fin n} {seam width : Nat}
    (S : BStarCopyLeftStrip.Strip B x base seam width)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (e : Fin n) (u : Fin n → Sheet → Bool)
    (k : Nat) (pos : 0<k) (small : k≤seam+width) :
    let v := leftStock base seam (comparisonNext hp x e u)
    let a := leftStock base seam u
    (v k).toNat + FenceLineTransfer.flow (seam+width) (leftBond base) e a k =
      (a k).toNat + FenceLineTransfer.flow (seam+width) (leftBond base) e a (k-1) := by
  dsimp only
  have idx : k-1+1=k := by omega
  have previous (p : 1<k) : k-1-1+1=k-1 := by omega
  have predecessor (p : 1<k) :
      RearTrace.predecessor (addr base (k-1))=leftBond base (k-1) := by
    change RearTrace.predecessor (addr base (k-1))=addr base (k-1-1)
    have H := predecessor_of_next base (k-1-1)
    rwa [previous p] at H
  apply FenceLineTransfer.balance_of_updates (leftBond base) e (leftStock base seam u)
    (leftStock base seam (comparisonNext hp x e u)) k pos small
  · intro p
    change addr base (k-1)≠addr base (k-1-1)
    have A := addr_next base (k-1-1)
    rw [previous p] at A
    rw [A]
    exact Ne.symm (sep _)
  · intro hit
    change e=addr base (k-1) at hit
    subst e
    by_cases last : k=seam+width
    · have isLD : BStarCopyLeftStrip.rail seam (k-1)=.ld := by
        have W := S.width_pos
        simp [BStarCopyLeftStrip.rail,show ¬k-1<seam by omega]
      have term := (strip_ends S).1
      rw [←last] at term
      have empty := exit_update _ (fun a => u (site (addr base (k-1)) a.side) a.occurrence) _ term
      rw [if_pos last]
      change comparisonNext hp x (addr base (k-1)) u (addr base (k-1))
        (BStarCopyLeftStrip.rail seam (k-1))=false
      rw [isLD,comparison_left]
      exact empty
    · have h := (paired_updates hp S (k-1) (by omega) sep u).1
      simpa only [leftStock,idx,Nat.add_sub_cancel,if_neg last] using h
  · intro p hit
    change e=addr base (k-1-1) at hit
    subst e
    have H := (paired_updates hp S (k-1-1) (by omega) sep u).2.1
    simpa only [leftStock,previous p] using H
  · intro noDeparture noArrival
    change e≠addr base (k-1) at noDeparture
    by_cases p : 1<k
    · have other : addr base (k-1)≠rightNeighbor e := by
        intro E
        have ep := congrArg RearTrace.predecessor E
        rw [predecessor p,RearTrace.predecessor_right] at ep
        exact noArrival p ep.symm
      exact comparison_off_pair hp x e _ u _ (Ne.symm noDeparture) other
    · have one : k=1 := by omega
      subst k
      by_cases he : e=RearTrace.predecessor base
      · subst e
        have A := (open_sources S (fun a => u (site (RearTrace.predecessor base) a.side) a.occurrence)).1
        have Hr := comparison_right hp x (RearTrace.predecessor base) (sep _) u .ls
        rw [RearTrace.right_predecessor] at Hr
        simpa [leftStock,first_site,BStarCopyLeftStrip.rail,S.seam_pos,site,R,RearTrace.right_predecessor]
          using Hr.trans A
      · have other : base≠rightNeighbor e := by
          intro E
          have ep := congrArg RearTrace.predecessor E
          rw [RearTrace.predecessor_right] at ep
          exact he ep.symm
        have first : addr base (1-1)=base := first_site base
        rw [first] at noDeparture
        have H := comparison_off_pair hp x e base u .ls (Ne.symm noDeparture) other
        simpa [leftStock,first_site,BStarCopyLeftStrip.rail,S.seam_pos] using H

/-- The reflected RD/RS strip obeys the same open-exclusion flow on
the same physical tape, with predecessor-edge service labels. -/
theorem right_balance {x : X} {base : Fin n} {seam width : Nat}
    (S : BStarCopyLeftStrip.Strip B x base seam width)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (e : Fin n) (u : Fin n → Sheet → Bool)
    (k : Nat) (pos : 0<k) (small : k≤seam+width) :
    let h := seam+width
    let v := rightStock base seam h (comparisonNext hp x e u)
    let a := rightStock base seam h u
    (v k).toNat + FenceLineTransfer.flow h (rightBond base h) e a k =
      (a k).toNat + FenceLineTransfer.flow h (rightBond base h) e a (k-1) := by
  dsimp only
  let h := seam+width
  have prior (p : 1<k) : h-k+1=h-(k-1) := by omega
  have incoming (p : 1<k) : rightBond base h (k-1)=addr base (h-k) := by
    change RearTrace.predecessor (addr base (h-(k-1)))=addr base (h-k)
    rw [←prior p,predecessor_of_next]
  apply FenceLineTransfer.balance_of_updates (rightBond base h) e
    (rightStock base seam h u) (rightStock base seam h (comparisonNext hp x e u)) k pos small
  · intro p
    rw [incoming p]
    intro E
    have Q := congrArg rightNeighbor E
    change rightNeighbor (RearTrace.predecessor (addr base (h-k)))=
      rightNeighbor (addr base (h-k)) at Q
    rw [RearTrace.right_predecessor] at Q
    exact sep _ Q
  · intro hit
    by_cases last : k=h
    · have index : h-k=0 := by omega
      change e=RearTrace.predecessor (addr base (h-k)) at hit
      rw [index,first_site] at hit
      subst e
      have term := (strip_ends S).2
      have empty := exit_update _ (fun a => u (site (RearTrace.predecessor base) a.side) a.occurrence) _ term
      have Hr := comparison_right hp x (RearTrace.predecessor base) (sep _) u .rd
      rw [RearTrace.right_predecessor] at Hr
      rw [if_pos last]
      change comparisonNext hp x (RearTrace.predecessor base) u (addr base (h-k))
        (returnRail seam (h-k))=false
      rw [index,first_site]
      simpa [returnRail,S.seam_pos] using Hr.trans empty
    · have N : h-(k+1)+1=h-k := by omega
      change e=RearTrace.predecessor (addr base (h-k)) at hit
      rw [←N,predecessor_of_next] at hit
      subst e
      have H := (paired_updates hp S (h-(k+1)) (by change h-(k+1)+1<h; omega) sep u).2.2.1
      have off : k≠seam+width := last
      simpa only [rightStock,if_neg off,N,h] using H
  · intro p hit
    have hit' : e=addr base (h-k) := hit.trans (incoming p)
    rw [hit']
    have H := (paired_updates hp S (h-k) (by change h-k+1<h; omega) sep u).2.2.2
    simpa only [rightStock,prior p,h] using H
  · intro noDeparture noArrival
    have other : addr base (h-k)≠rightNeighbor e := by
      intro E
      have ep := congrArg RearTrace.predecessor E
      rw [RearTrace.predecessor_right] at ep
      exact noDeparture ep.symm
    by_cases p : 1<k
    · have no : addr base (h-k)≠e := by
        rw [←incoming p]
        exact Ne.symm (noArrival p)
      exact comparison_off_pair hp x e _ u _ no other
    · have one : k=1 := by omega
      subst k
      by_cases he : e=addr base (h-1)
      · subst e
        have W := S.width_pos
        have isRS : returnRail seam (h-1)=.rs := by
          simp [returnRail,show ¬h-1<seam by dsimp [h]; omega]
        have A := (open_sources S (fun a => u (site (addr base (h-1)) a.side) a.occurrence)).2
        have H := comparison_left hp x (addr base (h-1)) u .rs
        simpa only [rightStock,isRS,site,L,h] using H.trans A
      · exact comparison_off_pair hp x e _ u _ (Ne.symm he) other

open BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain BStarResetChartTouch

private theorem strip_length {x : X} {hh : ∃ i,oldH6 B x i=true}
    {root : Fin n} {seam width W : Nat} (S : BStarCopyLeftStrip.Strip B x root seam width)
    (minBound : ∀ i,oldH6 B x (rightNeighbor i)=true → width≤oldOrdinal B x hh i+1)
    (maxBound : ∀ i,oldH6 B x (rightNeighbor i)=true → oldOrdinal B x hh i+1≤W) :
    seam+width≤2*W := by
  let h := oldH6 B x
  have atIndex (j : Nat) (small : j<seam) : ordinal h hh (addr root j)=j := by
    induction j with
    | zero =>
      have first : addr root 0=root := Fin.ext (Nat.mod_eq_of_lt root.isLt)
      rw [first]
      exact (ordinal_zero h hh root).mpr S.source_header
    | succ j ih =>
      have body := S.ls_body (j+1) (by omega) small
      rw [addr_next] at body ⊢
      rw [ordinal_body h hh _ body,ih (by omega)]
  have lastIndex : seam-1+1=seam := by have := S.seam_pos; omega
  have head : oldH6 B x (rightNeighbor (addr root (seam-1)))=true := by
    rw [←addr_next,lastIndex]
    exact S.dest_header
  have big := maxBound _ head
  have little := minBound _ head
  have numbered := atIndex (seam-1) (by have := S.seam_pos; omega)
  change width≤ordinal h hh (addr root (seam-1))+1 at little
  change ordinal h hh (addr root (seam-1))+1≤W at big
  omega

/-- The owner's left line is based at its command door. Its whole reflected
right line is based at the terminal header of that same chart. Both geometric
strips and their width bounds follow from actual owner charts. -/
theorem two_strips {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (width W : Nat) (positive : 0<width)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=width))
    (low : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1)
    (high : ∀ i,oldH6 B base (rightNeighbor i)=true → oldOrdinal B base hh i+1≤W)
    (charts : ∀ j : Owners (oldH6 B base), ∃ A l f,Chart hp base hh j A l f) :
    ∃ u v, BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 u width ∧
      BStarCopyLeftStrip.Strip B base (S.getD len fall).1 v width ∧
      BStarCopyRightStrip.addr (S.getD 0 fall).1 u=(S.getD len fall).1 ∧
      u+width≤2*W ∧ v+width≤2*W := by
  obtain ⟨u,L,join,_,_⟩ := BStarCopyLeftStrip.of_chart hp C positive flags low
  let h := oldH6 B base
  let mid := (S.getD len fall).1
  have header : h mid=true := by
    have t := (endpoint_spec h hh o 10).1
    rw [←C.terminal] at t
    exact t
  let j : Owners h := ⟨commandOwner h mid 0,commandOwner_range h hh mid 0⟩
  obtain ⟨A,l,f,D⟩ := charts j
  have pos : A.getD 0 f=(mid,0) :=
    D.root.trans ((endpoint_spec h hh j 0).2.2 mid header rfl).symm
  have projected := congrArg Prod.fst pos
  have same : (A.getD 0 f).1=mid := projected
  obtain ⟨v,R,_,_,_⟩ := BStarCopyLeftStrip.of_chart hp D positive flags low
  rw [same] at R
  exact ⟨u,v,L,R,join,strip_length hp L low high,strip_length hp R low high⟩

end L4.Height.FenceEmbedding
