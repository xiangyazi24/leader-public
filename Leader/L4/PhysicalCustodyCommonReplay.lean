import Leader.L4.PhysicalCustodyReplay
import Leader.L4.PhysicalCustodyCreditCuts
import Leader.L4.PhysicalCustodySettledFlags

namespace L4.PhysicalCustody
open AllSizeProtocol BStarTrace BStarH6WordChart BStarClearanceOffset
open BStarLongWork BStarH6Ordinal BStarLongFixedRouting BStarAcquireLiteralChain
open BStarAcquireVisitOrder BStarResetChartTouch BStarCustodyCuts
local notation "hp" => (show 0<2 by decide)

set_option maxRecDepth 4096

/-- The settled post-cover seed needed by the deterministic replay adapter.
Neither the entrance time nor a future recovery is included in this record. -/
structure ReadyAfterCovers {s n : Nat} (z : Raw s n) where
  Q : Raw s n→Prop
  qz : Q z
  clean : ∀ i,GrantClean z i
  closed : ∀ y e,Q y→Q (rawNext s y e)
  fiber : ∀ y,Q y→∀ i,Layout (rows s) z i=Layout (rows s) y i
  hh : ∃ i,oldH6 (rows s) z i=true
  offset : correct (oldH6 (rows s) z) hh 5 z
  flags : ∀ i,
    (longGeometry (rows s) (z i)).inside=decide (oldOrdinal (rows s) z hh i<radWidth s) ∧
    (longGeometry (rows s) (z i)).last=decide (oldOrdinal (rows s) z hh i+1=radWidth s)
  notShort : ∀ i,oldH6 (rows s) z (rightNeighbor i)=true →
    radWidth s≤oldOrdinal (rows s) z hh i+1
  head : ∀ i,let g:=longGeometry (rows s) (z i); (!g.axes.h6 || g.inside)=true
  cont : ∀ i,let g:=oldPair (rows s) z i; BStarAcquireRailCoverage.continuation g.1 g.2=true
  packed : total (oldH6 (rows s) z)*radWidth s≤n
  upperWidth : ∀ i,oldH6 (rows s) z (rightNeighbor i)=true →
    oldOrdinal (rows s) z hh i+1≤1024*radWidth s
  widthRatio : ∀ e f,
    oldH6 (rows s) z (rightNeighbor e)=true → oldH6 (rows s) z (rightNeighbor f)=true →
    4*(oldOrdinal (rows s) z hh e+1)<81*(oldOrdinal (rows s) z hh f+1)
  charts : ∀ o : Owners (oldH6 (rows s) z),
    ∃ (S : List (Pos n)) (len : Nat) (fall : Pos n), Chart hp z hh o S len fall
  sep : ∀ e : Fin n,e≠rightNeighbor e

/-- Only the fixed-geometry inputs to custody, with no offset or grants. -/
structure CustodyGeometry {s n : Nat} (z : Raw s n) where
  hh : ∃ i,oldH6 (rows s) z i=true
  flags : ∀ i,
    (longGeometry (rows s) (z i)).inside=decide (oldOrdinal (rows s) z hh i<radWidth s) ∧
    (longGeometry (rows s) (z i)).last=decide (oldOrdinal (rows s) z hh i+1=radWidth s)
  notShort : ∀ i,oldH6 (rows s) z (rightNeighbor i)=true →
    radWidth s≤oldOrdinal (rows s) z hh i+1
  head : ∀ i,let g:=longGeometry (rows s) (z i); (!g.axes.h6 || g.inside)=true
  cont : ∀ i,let g:=oldPair (rows s) z i; BStarAcquireRailCoverage.continuation g.1 g.2=true
  packed : total (oldH6 (rows s) z)*radWidth s≤n
  upperWidth : ∀ i,oldH6 (rows s) z (rightNeighbor i)=true →
    oldOrdinal (rows s) z hh i+1≤1024*radWidth s
  widthRatio : ∀ e f,
    oldH6 (rows s) z (rightNeighbor e)=true → oldH6 (rows s) z (rightNeighbor f)=true →
    4*(oldOrdinal (rows s) z hh e+1)<81*(oldOrdinal (rows s) z hh f+1)
  charts : ∀ o : Owners (oldH6 (rows s) z),
    ∃ (S : List (Pos n)) (len : Nat) (fall : Pos n), Chart hp z hh o S len fall

/-- Reduce geometry data to the actual ordinal flags and width bounds:
the header/continuation guards and owner charts are derived. -/
theorem geometry_of_settled_flags {s n : Nat} {z : Raw s n}
    (hh : ∃ i,oldH6 (rows s) z i=true) (hw : 0 < radWidth s)
    (flags : ∀ i,
      (longGeometry (rows s) (z i)).inside=decide (oldOrdinal (rows s) z hh i<radWidth s) ∧
      (longGeometry (rows s) (z i)).last=decide (oldOrdinal (rows s) z hh i+1=radWidth s))
    (notShort : ∀ i,oldH6 (rows s) z (rightNeighbor i)=true →
      radWidth s≤oldOrdinal (rows s) z hh i+1)
    (packed : total (oldH6 (rows s) z)*radWidth s≤n)
    (upperWidth : ∀ i,oldH6 (rows s) z (rightNeighbor i)=true →
      oldOrdinal (rows s) z hh i+1≤1024*radWidth s)
    (widthRatio : ∀ e f,
      oldH6 (rows s) z (rightNeighbor e)=true → oldH6 (rows s) z (rightNeighbor f)=true →
      4*(oldOrdinal (rows s) z hh e+1)<81*(oldOrdinal (rows s) z hh f+1)) :
    CustodyGeometry z :=
  let H := settled_flags_guards hh hw flags notShort
  ⟨hh, flags, notShort, H.1, H.2, packed, upperWidth, widthRatio,
    settled_flags_charts hh hw flags notShort⟩

/-- Five complete actual covers earn offset correctness and grant coherence.
Geometry is provided on the closed settled fibre, not on arbitrary bytes. -/
theorem ready_of_actual_five_covers {s n : Nat} {x : Raw s n}
    (Q : Raw s n → Prop) (qx : Q x) (closed : ∀ y e, Q y → Q (rawNext s y e))
    (layout : ∀ y, Q y → ∀ i, Layout (rows s) x i = Layout (rows s) y i)
    (geom : ∀ y, Q y → CustodyGeometry y)
    (sep : ∀ e : Fin n, e ≠ rightNeighbor e)
    (blocks : List (List (Fin n))) (five : blocks.length = 5)
    (full : ∀ w ∈ blocks, ∀ e, e ∈ w) :
    Nonempty (ReadyAfterCovers (rawRun x blocks.flatten)) := by
  let h := oldH6 (rows s) x
  have same (y : Raw s n) (hy : Q y) (i : Fin n) : oldH6 (rows s) y i = h i := by
    exact (congrArg Prod.fst (layout y hy i)).symm
  let z := rawRun x blocks.flatten
  obtain ⟨qz,off,clean⟩ := historical_init h (geom x qx).hh sep Q closed same x qx blocks five full
  let G := geom z qz
  have hEq : h = oldH6 (rows s) z := (funext (same z qz)).symm
  have O : ∃ hh : ∃ i, h i = true, correct h hh 5 z := ⟨(geom x qx).hh, off⟩
  rw [hEq] at O
  obtain ⟨_,offZ⟩ := O
  refine ⟨{
    Q := Q
    qz := qz
    clean := clean
    closed := closed
    fiber := fun y hy i => (layout z qz i).symm.trans (layout y hy i)
    hh := G.hh
    offset := offZ
    flags := G.flags
    notShort := G.notShort
    head := G.head
    cont := G.cont
    packed := G.packed
    upperWidth := G.upperWidth
    widthRatio := G.widthRatio
    charts := G.charts
    sep := sep }⟩

def CommonCommutedCuts {s n : Nat} (z : Raw s n) (w : List (Fin n)) : Prop :=
  ∃ u v u' v', w=u++v ∧ Commuted u u' ∧ Commuted v v' ∧ CutFacts hp z z u' v'

theorem common_replay_implies_custody {s n : Nat} {z : Raw s n} {w : List (Fin n)}
    (g : ReadyAfterCovers z) (H : CommonCommutedCuts z w) :
    Custody (rawRun z w) := by
  obtain ⟨u,v,u',v',rfl,hu,hv,cut⟩ := H
  have C := custody_of_cuts z g.Q g.qz g.clean g.closed g.fiber g.hh g.offset g.flags
    g.notShort g.head g.cont g.packed g.upperWidth g.widthRatio g.charts g.sep u' v' cut
  rwa [←List.append_nil (u++v), (replay_same_cuts z hu hv).2 [], List.append_nil]

#print axioms geometry_of_settled_flags
#print axioms ready_of_actual_five_covers
#print axioms common_replay_implies_custody
end L4.PhysicalCustody
