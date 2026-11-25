import Leader.L4.BStarFencePorts
import Leader.L4.BStarFenceFootprint

namespace L4.BStarFenceLeftShadow
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets BStarLongPrep
open BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarH6WordChart BStarClearanceDataChart BStarGeneratedOwner BStarResetChartTouch
open BStarGeneratedBandScan BStarFenceOccupancy BStarFenceShadow BStarFencePorts
open BStarFenceFootprint BStarFenceLineGeometry
open BStarCopyRightStrip (addr addr_next)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

def leftOcc (x : X) (root : Fin n)
    (d r' : Nat) (j : Fin (d+r')) : Bool :=
  occupied (readLane (BStarLongPackets.Sheet.index (BStarCopyLeftStrip.rail d j.val)) (x (addr root j.val)).long)

/-- A literal generated FENCE owner implements each clause of the
open-exclusion comparison along its full left line, on every raw mark. -/
theorem left_mark {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (hist : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (play x w) m)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x w) i)
    (pc11 : pc (play x w) (S.getD 0 fall).1=11)
    {d r' : Nat}
    (F : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 d r') (e : Fin n) :
    let root := (S.getD 0 fall).1
    Mark (leftPort root) e (leftOcc (play x w) root d r') (leftOcc (step (play x w) e) root d r') := by
  let q := play x w
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
    have V := ring_owner_hop hp chart sep hist now layout pc11 e (hop src dst) dst N
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
    have H := ring_owner_end hp chart sep hist now layout pc11 e (L .ld) N O
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
      have W := ring_owner_quiet hp chart sep hist now layout pc11 e (R (sh j.val)) O quiet
      change readLane (BStarLongPackets.Sheet.index (sh j.val)) (y (rightNeighbor e)).long=
        readLane (BStarLongPackets.Sheet.index (sh j.val)) (q (rightNeighbor e)).long at W
      rw [R'] at W
      exact congrArg occupied W
    · have W := quiet_outside_mark B q e (addr root j.val) offL (Ne.symm R')
      change occupied (readLane (BStarLongPackets.Sheet.index (sh j.val)) (y (addr root j.val)).long)=
        occupied (readLane (BStarLongPackets.Sheet.index (sh j.val)) (q (addr root j.val)).long)
      rw [show y (addr root j.val)=q (addr root j.val) from W]

#print axioms left_mark
end L4.BStarFenceLeftShadow
