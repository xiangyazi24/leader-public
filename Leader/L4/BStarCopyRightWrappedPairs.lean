import Leader.L4.BStarCopyRightWrappedGeometry

namespace L4.BStarCopyRightWrappedPairs
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarCopyRightStrip BStarCopyRightRetained BStarCopyRightWrappedGeometry
open BStarFenceReceiverChart
open BStarCopyRightMark (rightNeighbor_inj)
open BStarLongPackets

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

private theorem addr_zero {n : Nat} (a : Fin n) : addr a 0=a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

/-- At the predecessor of the aliased head/tail, both old claims
are present under genuine inside/last geometry. Their slot sets
are disjoint even though they use the same two physical sites. -/
theorem predecessor_distinct_claims {base : X} {hh : ∃ i,oldH6 B base i=true}
    {root a : Fin n} {width seam tail : Nat} (C : Dest B base root width)
    (U : WrappedStrip B base a seam tail) (hw : 2≤width) (wrap : tail=n)
    (join : addr a 0=addr root (width-1))
    (flags : ∀ i,(longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤oldOrdinal B base hh j+1) :
    let e := addr a (tail-1)
    let g := oldPair B base e
    let d := hop (R .rd) (L .rd)
    let s := hop (R .rs) (L .rs)
    d∈dataClaims g ∧ s∈dataClaims g ∧ ∀ q,q∈d.slots → q∉s.slots := by
  dsimp only
  let e := addr a (tail-1)
  let g := oldPair B base e
  have lands : rightNeighbor e=addr root (width-1) := by
    dsimp [e]
    rw [←addr_next,show tail-1+1=tail by have := U.seam_pos; have := U.seam_le_tail; omega,wrap]
    have eq : addr a n=addr a 0 := by
      apply Fin.ext
      change (a.val+n)%n=(a.val+0)%n
      rw [Nat.add_mod_right,Nat.add_zero]
    exact eq.trans join
  have oldLeft : e=addr root (width-2) := by
    apply rightNeighbor_inj
    rw [lands,←addr_next,show width-2+1=width-1 by omega]
  have noHeader : g.2.axes.h6=false := by
    change oldH6 B base (rightNeighbor e)=false
    rw [lands]
    exact C.body _ (by omega) (by omega)
  have rightIn : g.2.inside=true := by
    change (longGeometry B (base (rightNeighbor e))).inside=true
    rw [lands]
    exact C.inside _ (by omega)
  have leftIn : g.1.inside=true := by
    change (longGeometry B (base e)).inside=true
    rw [oldLeft]
    exact C.inside _ (by omega)
  have rootH : oldH6 B base root=true := by
    have H := C.header
    rwa [addr_zero] at H
  have dEq : addr root (width-2)=digitFrom root (width-2) := by
    have K := BStarCopyLeftStrip.addr_from root 0 (width-2)
    rwa [Nat.zero_add,addr_zero] at K
  have notLast : ends g.1=false := by
    unfold ends
    rw [leftIn]
    change (true && (longGeometry B (base e)).last)=false
    rw [flags,oldLeft,dEq,(digit_from hp rootH width notShort (width-2) (by omega)).1]
    simp [show width-2+1≠width by omega]
  change hop (R .rd) (L .rd)∈dataClaims g ∧ hop (R .rs) (L .rs)∈dataClaims g ∧ _
  constructor
  · simp [dataClaims,noHeader,leftIn,rightIn,notLast]
  constructor
  · simp [dataClaims,noHeader,leftIn,rightIn,notLast]
  · decide +kernel

open BStarLongPrep BStarLongCommandData BStarCopyRightMark
open BStarClearanceMobileJoined

/-- The exact replacement for the ingress branch's old exterior test.
An upstream slot can hit the right vertex only at coordinate 1, and
the left vertex only at full wrap coordinate n. -/
theorem ingress_upstream_touch {n : Nat} (a : Fin n) {j : Nat} (J : 0<j) (N : j≤n)
    (s : Side) (touch : addr a j=site (addr a 0) s) :
    (s=.left ∧ j=n) ∨ (s=.right ∧ j=1) := by
  cases s with
  | left =>
    left
    refine ⟨rfl,?_⟩
    by_cases E : j=n
    · exact E
    · have H := addr_inj a (by omega : j<n) (Nat.zero_lt_of_lt a.isLt) touch
      omega
  | right =>
    right
    refine ⟨rfl,?_⟩
    have H : addr a j=addr a 1 := touch.trans (addr_next a 0).symm
    exact upstream_addr_inj a J (by decide) N (Nat.zero_lt_of_lt a.isLt) H

/-- Full literal joined pair at ingress: the aliased upstream tail
retains its whole lane while the independent RD ingress can act. -/
theorem ingress_tail_frame (x : X) (a : Fin n) (seam : Nat)
    (U : WrappedStrip B x a seam n)
    (sep : addr a 0≠rightNeighbor (addr a 0))
    (noPrep : let e:=addr a 0
      L .rs∉reserved (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep) :
    let e := addr a 0
    let post := AllSizeS1Geometry.step B x e
    readLane (Sheet.index .rs) (post (addr a n)).long =
      readLane (Sheet.index .rs) (x (addr a n)).long := by
  dsimp only
  let e := addr a 0
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let rv := reserved (round g raw).prep
  have off (d : DataClaim) (D : d∈orderedData g rv) : L .rs∉d.slots :=
    wrapped_tail_untouched_ingress hp x a seam U d (BStarLongFenceTopology.selected_data_raw _ _ _ D)
  have keep := joined_spectator hp (x e,x (rightNeighbor e)) (L .rs) noPrep (fun d D v M =>
    off d D (data_lane_claim g _ d _ _ M))
  change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) (L .rs)=
    view raw (L .rs) at keep
  rw [new_access hp x e (L .rs) sep,old_access x e (L .rs)] at keep
  have eq : addr a n=e := by
    apply Fin.ext
    change (a.val+n)%n=(a.val+0)%n
    rw [Nat.add_mod_right,Nat.add_zero]
  rw [eq]
  exact keep

end L4.BStarCopyRightWrappedPairs
