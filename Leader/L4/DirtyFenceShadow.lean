import Leader.L4.BStarFenceRightShadow
import Leader.L4.DirtyFencePrep

namespace L4.DirtyFenceShadow
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarLongPrep BStarLongCommandData BStarLongFiberOwner BStarH6WordChart
open BStarAcquireAnchors BStarAcquireVisitOrder BStarResetChartTouch BStarGeneratedOwner BStarGeneratedBandScan BStarClearanceMobile
open BStarCopyUpstreamCredit BStarCopyFIFO BStarClearanceDataChart BStarAcquireLiteralChain

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "play" => BStarResetSchedule.run (AllSizeS1Geometry.step (n:=n) B)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

open BStarFenceOccupancy BStarFencePorts BStarFenceShadow BStarFenceFootprint BStarFenceLineGeometry
open BStarCopyRightStrip (addr addr_next)
open BStarH6Ordinal

theorem owner_nomination_selected
    {base x : X}
    {o : Owners (oldH6 B base)}
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (noRes : ∀ e (s : At Sheet), dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val →
      s∉reserved (round (oldPair B x e) ((x e).long,((x (rightNeighbor e)).long))).prep)
    (e : Fin n) (D : DataClaim)
    (nom : D∈orderedData (oldPair B x e) [])
    (own : dataOwner (oldH6 B base) (site e D.source.side) D.source.occurrence=o.val) :
    D∈orderedData (oldPair B x e) (reserved (round (oldPair B x e)
      ((x e).long,(x (rightNeighbor e)).long)).prep) := by
  apply select_unreserved _ _ _ nom
  intro s hs
  apply noRes e s
  have slots : s=D.source ∨ D.destination=some s := by
    cases h : D.destination with
    | none => exact Or.inl (by simpa [Claim.slots,h] using hs)
    | some a =>
      have H : s=D.source ∨ s=a := by simpa [Claim.slots,h] using hs
      exact H.imp id (fun eq => by rw [eq])
  rcases slots with hs | hs
  · simpa only [hs] using own
  · have eq := actual_data_owner B x e [] D s nom hs
    have H : oldH6 B x=oldH6 B base :=
      funext fun t => (congrArg Prod.fst (layout t)).symm
    rw [H] at eq
    change dataOwner (oldH6 B base) (site e D.source.side) D.source.occurrence =
      dataOwner (oldH6 B base) (site e s.side) s.occurrence at eq
    exact eq.symm.trans own

theorem ring_owner_hop
    {base x : X}
    {o : Owners (oldH6 B base)}
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (noRes : ∀ e (s : At Sheet), dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val →
      s∉reserved (round (oldPair B x e) ((x e).long,((x (rightNeighbor e)).long))).prep)
    (e : Fin n) (D : DataClaim) (v : At Sheet)
    (nom : D∈orderedData (oldPair B x e) [])
    (own : dataOwner (oldH6 B base) (site e D.source.side) D.source.occurrence=o.val)
    (hd : D.destination=some v) (hk : D.kind=.hop) (ne : D.source≠v) (a b : Bool) :
    let q := x
    let y := AllSizeS1Geometry.step B q e
    let old := view ((q e).long,(q (rightNeighbor e)).long)
    let nxt := view ((y e).long,(y (rightNeighbor e)).long)
    (occupied (old D.source)=true → a=true) →
    (occupied (old v)=true → b=true) →
    (occupied (nxt D.source)=true → (a && b)=true) ∧
    (occupied (nxt v)=true → (a || b)=true) := by
  dsimp only
  intro hu hv
  rw [ring_view hp _ e (sep e)]
  apply compare_hop _ _ D D.source v rfl hd hk ne _ a b hu hv
  exact owner_nomination_selected hp layout noRes e D nom own

theorem ring_owner_end
    {base x : X}
    {o : Owners (oldH6 B base)}
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (noRes : ∀ e (s : At Sheet), dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val →
      s∉reserved (round (oldPair B x e) ((x e).long,((x (rightNeighbor e)).long))).prep)
    (e : Fin n) (s : At Sheet)
    (nom : ending s∈orderedData (oldPair B x e) [])
    (own : dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val) :
    let q := x
    let y := AllSizeS1Geometry.step B q e
    occupied (view ((y e).long,(y (rightNeighbor e)).long) s)=false := by
  dsimp only
  rw [ring_view hp _ e (sep e)]
  apply compare_end
  exact owner_nomination_selected hp layout noRes e (ending s) nom own

theorem ring_owner_quiet
    {base x : X}
    {o : Owners (oldH6 B base)}
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (noRes : ∀ e (s : At Sheet), dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val →
      s∉reserved (round (oldPair B x e) ((x e).long,((x (rightNeighbor e)).long))).prep)
    (e : Fin n) (s : At Sheet)
    (own : dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val)
    (quiet : ∀ D∈orderedData (oldPair B x e) [], s∉D.slots) :
    let q := x
    let y := AllSizeS1Geometry.step B q e
    view ((y e).long,(y (rightNeighbor e)).long) s =
      view ((q e).long,(q (rightNeighbor e)).long) s := by
  dsimp only
  rw [ring_view hp _ e (sep e)]
  apply BStarClearanceMobileWeak.quiet_lane
  · exact noRes e s own
  · intro D h
    rw [BStarClearancePrepOwner.orderedData_filter] at h
    exact quiet D (List.mem_filter.mp h).1

open BStarFenceLeftShadow (leftOcc)
open BStarFenceRightShadow (rightOcc right_tail_from_flags)

theorem left_mark
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (noRes : ∀ e (s : At Sheet), dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val →
      s∉reserved (round (oldPair B x e) ((x e).long,((x (rightNeighbor e)).long))).prep)
    {d r' : Nat}
    (F : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 d r') (e : Fin n) :
    let root := (S.getD 0 fall).1
    Mark (leftPort root) e (leftOcc x root d r') (leftOcc (step x e) root d r') := by
  let q := x
  let y := step q e
  let root := (S.getD 0 fall).1
  let sh := BStarCopyLeftStrip.rail d
  have rootOwner : commandOwner (oldH6 B base) root 0=o.val := by
    dsimp [root]
    rw [chart.root]
    exact (endpoint_spec _ hh o 0).2.1
  have own (j : Fin (d+r')) : dataOwner (oldH6 B base) (addr root j.val) (sh j.val)=o.val :=
    (left_owner F j.val j.isLt).trans rootOwner
  constructor
  · intro j h E
    change e=addr root j.val at E
    subst e
    let e := addr root j.val
    let src := L (sh j.val)
    let dst := R (sh (j.val+1))
    have N : hop src dst∈orderedData (oldPair B q e) [] := by
      rw [←data_eq B base q layout e]
      exact left_adjacent F j.val h
    have V := ring_owner_hop hp sep layout noRes e (hop src dst) dst N
      (own j) rfl rfl (by intro eq; have S := congrArg At.side eq; contradiction) (leftOcc q root d r' j)
      (leftOcc q root d r' (succIdx j h))
    have link : rightNeighbor e=addr root (j.val+1) := (addr_next _ _).symm
    simp only [leftOcc] at V
    dsimp [src,dst] at V
    change
      (occupied (readLane (BStarLongPackets.Sheet.index (sh j.val)) (q e).long)=true→_) →
      (occupied (readLane (BStarLongPackets.Sheet.index (sh (j.val+1))) (q (rightNeighbor e)).long)=true→_) →
      (occupied (readLane (BStarLongPackets.Sheet.index (sh j.val)) ((step q e) e).long)=true→_) ∧
      (occupied (readLane (BStarLongPackets.Sheet.index (sh (j.val+1))) ((step q e) (rightNeighbor e)).long)=true→_) at V
    rw [link] at V
    exact V id id
  · intro j J E
    change e=addr root j.val at E
    subst e
    let e := addr root j.val
    have iEq : j.val=d+r'-1 := by have := j.isLt; omega
    have shEq : sh j.val=.ld := if_neg (by have := F.width_pos; have := j.isLt; omega)
    have N : ending (L .ld)∈orderedData (oldPair B q e) [] := by
      rw [←data_eq B base q layout e,show e=addr root (d+r'-1) by rw [←iEq]]
      exact left_terminal F
    have O := own j
    rw [shEq] at O
    have H := ring_owner_end hp sep layout noRes e (L .ld) N O
    change occupied (readLane (BStarLongPackets.Sheet.index (sh j.val)) ((step q e) e).long)=false
    rw [shEq]
    exact H
  · intro j H noIn
    have offL : addr root j.val≠e := Ne.symm H
    by_cases R' : rightNeighbor e=addr root j.val
    · have prev : ¬0<j.val := by
        intro P
        have H' : rightNeighbor (addr root (j.val-1))=addr root j.val := by
          rw [←addr_next,show j.val-1+1=j.val by omega]
        have eq : e=addr root (j.val-1) := by
          have eq := congrArg RearTrace.predecessor (R'.trans H'.symm)
          simpa only [RearTrace.predecessor_right] using eq
        exact noIn P eq
      have O : dataOwner (oldH6 B base) (site e .right) (sh j.val)=o.val := by
        change dataOwner _ (rightNeighbor e) _=_
        rw [R']
        exact own j
      have quiet (D : DataClaim) (N : D∈orderedData (oldPair B q e) []) :
          R (sh j.val)∉D.slots := by
        intro P
        have T := (left_footprint_layout .right F j.isLt layout R' D).mp ⟨N,P⟩
        simp [leftClaim,prev] at T
      have W := ring_owner_quiet hp sep noRes e (R (sh j.val)) O quiet
      change readLane (BStarLongPackets.Sheet.index (sh j.val)) (y (rightNeighbor e)).long=
        readLane (BStarLongPackets.Sheet.index (sh j.val)) (q (rightNeighbor e)).long at W
      rw [R'] at W
      exact congrArg occupied W
    · have W := quiet_outside_mark B q e (addr root j.val) offL (Ne.symm R')
      change occupied (readLane (BStarLongPackets.Sheet.index (sh j.val)) (y (addr root j.val)).long)=
        occupied (readLane (BStarLongPackets.Sheet.index (sh j.val)) (q (addr root j.val)).long)
      rw [show y (addr root j.val)=q (addr root j.val) from W]

private theorem addr_zero {n : Nat} (root : Fin n) : addr root 0=root :=
  Fin.ext (Nat.mod_eq_of_lt root.isLt)

theorem right_mark
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (noRes : ∀ e (s : At Sheet), dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val →
      s∉reserved (round (oldPair B x e) ((x e).long,((x (rightNeighbor e)).long))).prep)
    {d r' : Nat}
    (F : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (tail : ends (longGeometry B (base (addr (S.getD len fall).1 (d+r'-1))))=true)
    (e : Fin n) :
    let root := (S.getD len fall).1
    Mark (rightPort root) e (rightOcc x root d r') (rightOcc (step x e) root d r') := by
  let q := x
  let y := step q e
  let root := (S.getD len fall).1
  let sh := rightRail d
  have rootOwner : commandOwner (oldH6 B base) root 10=o.val := by
    dsimp [root]
    rw [chart.terminal]
    exact (endpoint_spec _ hh o 10).2.1
  have own (i : Nat) (I : i<d+r') : dataOwner (oldH6 B base) (addr root i) (sh i)=o.val :=
    (right_owner F dp i I).trans rootOwner
  constructor
  · intro j h E
    let k := succIdx j h
    have L := (right_hop_endpoints root j h).1
    have R := (right_hop_endpoints root j h).2
    change e=rightPort root j at E
    have eL : e=addr root (rightCoord k) := E.trans L
    have eR : rightNeighbor e=addr root (rightCoord j) := by rw [E]; exact R
    have K : rightCoord k+1=rightCoord j := by
      have := j.isLt
      unfold rightCoord k succIdx
      dsimp only
      omega
    have J : rightCoord j<d+r' := by
      have := j.isLt
      unfold rightCoord
      omega
    let src := BStarLongClaims.R (sh (rightCoord j))
    let dst := BStarLongClaims.L (sh (rightCoord k))
    have N : hop src dst∈orderedData (oldPair B q e) [] := by
      rw [←data_eq B base q layout e,eL]
      have H := F.adjacent (rightCoord k) (by omega)
      rwa [K] at H
    have O : dataOwner (oldH6 B base) (rightNeighbor e) (sh (rightCoord j))=o.val := by
      rw [eR]
      exact own _ J
    have V := ring_owner_hop hp sep layout noRes e (hop src dst) dst N O
      rfl rfl (by intro eq; have T := congrArg At.side eq; contradiction)
      (rightOcc q root d r' j) (rightOcc q root d r' k)
    simp only [rightOcc] at V
    dsimp [src,dst] at V
    change
      (occupied (readLane (BStarLongPackets.Sheet.index (sh (rightCoord j))) (q (rightNeighbor e)).long)=true→_) →
      (occupied (readLane (BStarLongPackets.Sheet.index (sh (rightCoord k))) (q e).long)=true→_) →
      (occupied (readLane (BStarLongPackets.Sheet.index (sh (rightCoord j))) (y (rightNeighbor e)).long)=true→_) ∧
      (occupied (readLane (BStarLongPackets.Sheet.index (sh (rightCoord k))) (y e).long)=true→_) at V
    rw [eR,eL] at V
    exact V id id
  · intro j last E
    obtain ⟨port,idx⟩ := right_outlet root j last
    have mark := E.trans port
    have cell : rightNeighbor e=addr root (rightCoord j) := by
      rw [mark,RearTrace.right_predecessor,idx,addr_zero]
    have sheet : sh (rightCoord j)=.rd := by rw [idx]; exact if_pos dp
    have N : ending (R .rd)∈orderedData (oldPair B q e) [] := by
      rw [←data_eq B base q layout e,mark]
      exact right_terminal F
    have O : dataOwner (oldH6 B base) (rightNeighbor e) .rd=o.val := by
      rw [cell,←sheet]
      exact own _ (by have := j.isLt; unfold rightCoord; omega)
    have H := ring_owner_end hp sep layout noRes e (R .rd) N O
    change occupied (readLane (BStarLongPackets.Sheet.index .rd) (y (rightNeighbor e)).long)=false at H
    rw [cell,←sheet] at H
    exact H
  · intro j H noIn
    let p := rightCoord j
    have J := j.isLt
    have Q : p<d+r' := by dsimp [p,rightCoord]; omega
    have offR : rightNeighbor e≠addr root p := by
      intro E
      by_cases further : j.val+1<d+r'
      · have R := (right_hop_endpoints root j further).2
        have C := congrArg RearTrace.predecessor (E.trans R.symm)
        exact H (by simpa only [RearTrace.predecessor_right] using C)
      · obtain ⟨mark,idx⟩ := right_outlet root j further
        rw [show p=0 from idx,addr_zero] at E
        exact H ((RearTrace.predecessor_right e).symm.trans
          ((congrArg RearTrace.predecessor E).trans mark.symm))
    by_cases E : e=addr root p
    · have notIncoming : ¬p+1<d+r' := by
        intro I
        have P : 0<j.val := by dsimp [p,rightCoord] at I; omega
        have A : (predIdx j P).val+1<d+r' := by
          change j.val-1+1<d+r'
          omega
        have K : rightPort root (predIdx j P)=addr root p := by
          rw [rightPort,if_pos A]
          change addr root (d+r'-2-(j.val-1))=addr root p
          congr 1
          dsimp [p,rightCoord]
          omega
        exact noIn P (E.trans K.symm)
      have ownL : dataOwner (oldH6 B base) e (sh p)=o.val := by rw [E]; exact own _ Q
      have quiet (D : DataClaim) (N : D∈orderedData (oldPair B q e) []) :
          L (sh p)∉D.slots := by
        intro P
        have T := (right_footprint_layout .left F dp tail Q layout E D).mp ⟨N,P⟩
        simp [rightClaim,notIncoming] at T
      have W := ring_owner_quiet hp sep noRes e (L (sh p)) ownL quiet
      change readLane (BStarLongPackets.Sheet.index (sh p)) (y e).long=
        readLane (BStarLongPackets.Sheet.index (sh p)) (q e).long at W
      rw [E] at W
      exact congrArg occupied W
    · have W := quiet_outside_mark B q e (addr root p) (Ne.symm E) (Ne.symm offR)
      change occupied (readLane (BStarLongPackets.Sheet.index (sh p)) (y (addr root p)).long)=
        occupied (readLane (BStarLongPackets.Sheet.index (sh p)) (q (addr root p)).long)
      rw [show y (addr root p)=q (addr root p) from W]

/-- All literal clauses on both open-shadow lines for a single mark.
Unlike the generated-FENCE induction, the mark only needs owner-local
unreservation supplied separately. -/
theorem both_marks
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (noRes : ∀ e (s : At Sheet), dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val →
      s∉reserved (round (oldPair B x e) ((x e).long,((x (rightNeighbor e)).long))).prep)
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (e : Fin n) :
    Mark (leftPort (S.getD 0 fall).1) e
      (leftOcc x (S.getD 0 fall).1 l r') (leftOcc (step x e) (S.getD 0 fall).1 l r') ∧
    Mark (rightPort (S.getD len fall).1) e
      (rightOcc x (S.getD len fall).1 d r') (rightOcc (step x e) (S.getD len fall).1 d r') :=
  ⟨left_mark hp chart sep layout noRes LF e,
   right_mark hp chart sep layout noRes RF dp (right_tail_from_flags hp RF flags notShort) e⟩

theorem both_mark
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (noRes : ∀ e (s : At Sheet), dataOwner (oldH6 B base) (site e s.side) s.occurrence=o.val →
      s∉reserved (round (oldPair B x e) ((x e).long,((x (rightNeighbor e)).long))).prep)
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (e : Fin n) (z : Two (l:=l+r') (r:=d+r')) :
    let Lroot := (S.getD 0 fall).1
    let Rroot := (S.getD len fall).1
    let phys := fun q : X => (⟨BStarFenceLeftShadow.leftOcc q Lroot l r',rightOcc q Rroot d r'⟩ :
      Two (l:=l+r') (r:=d+r'))
    (phys x).below z →
      (phys (step x e)).below (Two.advance (leftPort Lroot) (rightPort Rroot) e z) := by
  dsimp only
  intro dom
  exact same_emitted _ _ e (left_mark hp chart sep layout noRes LF e)
    (right_mark hp chart sep layout noRes RF dp (right_tail_from_flags hp RF flags notShort) e) dom


open DirtyLeastForward DirtyFencePrep BStarClearanceIndexedWait
open BStarClearanceIndexedSum (distance)
open BStarClearanceCommandFrame (forwardCount)
open BStarLongCommand (bind)

/-- The sufficient cutoff is uniform over all preparation-capable slots
of the owner chart, not merely for a single sheet. This constructs
owner-local unreservation under any mark of the current raw state. -/
theorem owner_reservation_free_of_cutoff
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (cutoff : Nat)
    (onPrep : ∀ u∈S, (∃ sh op,sh∈prepSites (longGeometry B (base u.1)) u.2 op) →
      cutoff<distance S u)
    (clear : ∀ u∈S, cutoff<distance S u → ¬ringF x u) :
    ∀ e (a : At Sheet), dataOwner (oldH6 B base) (site e a.side) a.occurrence=o.val →
      a∉reserved (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep := by
  intro e a own res
  obtain ⟨u,U,_,_,⟨op,P⟩,pay,F⟩ := chart_reservation_origin hp chart layout e a own res
  have sameI : (longGeometry B (base u.1)).inside=(longGeometry B (x u.1)).inside :=
    congrArg (fun z : Bool × Bool × Bool => z.2.1) (layout u.1)
  have oldP : a.occurrence∈prepSites (longGeometry B (base u.1)) u.2 op := by
    cases op <;> simpa only [prepSites,sameI] using P
  apply clear u U (onPrep u U ⟨_,op,oldP⟩)
  change forwardCount _ = 1
  have E := congrArg Prod.fst (BStarClearanceCommandFrame.bind_counts
    (longGeometry B (x u.1)) u.2 (BStarLongToken.atSite (x u.1).long u.2))
  change forwardCount (bind _ _ _)=forwardCount _ at E
  erw [F] at E
  exact E.symm

/-- Both shadow-line mark clauses hold at every marked split of the
same physical tape before own service. The initial cutoff must exclude
forward tokens at every preparation-capable address of the chart. -/
theorem both_marks_along
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {l d r' : Nat} (LF : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 l r')
    (RF : RightFrame B base (S.getD len fall).1 d r') (dp : 0<d)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r') ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r'))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r'≤oldOrdinal B base hh i+1)
    (tape : List (Fin n)) (cutoff : Nat)
    (onPrep : ∀ u∈S, (∃ sh op,sh∈prepSites (longGeometry B (base u.1)) u.2 op) →
      cutoff<distance S u)
    (clear : ∀ u∈S, cutoff<distance S u → ¬ringF x u)
    (good : ∀ pre e post, tape=pre++e::post →
      let z := pre.foldl step x
      (∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B z i) ∧
      BeforeOwnService hp z (endpoint (oldH6 B base) hh o 0).1 e) :
    ∀ pre e post, tape=pre++e::post →
      let z := pre.foldl step x
      Mark (leftPort (S.getD 0 fall).1) e
        (leftOcc z (S.getD 0 fall).1 l r') (leftOcc (step z e) (S.getD 0 fall).1 l r') ∧
      Mark (rightPort (S.getD len fall).1) e
        (rightOcc z (S.getD len fall).1 d r') (rightOcc (step z e) (S.getD len fall).1 d r') := by
  intro pre e post E
  have layout := (good pre e post E).1
  have live := ring_frontier_run hp chart sep pre cutoff
    (fun u k v split => good u k (v++e::post) (by rw [E,split]; simp [List.append_assoc])) clear
  exact both_marks hp chart sep layout
    (owner_reservation_free_of_cutoff hp chart layout cutoff onPrep live) LF RF dp flags notShort e

#print axioms both_marks
#print axioms both_mark
#print axioms owner_reservation_free_of_cutoff
#print axioms both_marks_along
end L4.DirtyFenceShadow
