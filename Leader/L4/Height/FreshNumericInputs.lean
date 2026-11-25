import Leader.L4.BStarNativeCopyReadback
import Leader.L4.BStarNativeCopyTransport
import Leader.L4.BStarFreshNumericLaunch
import Leader.L4.BStarFreshNumericConsume
import Leader.L4.Height.FreshStripGeometry
import Leader.L4.BStarCopyFenceCuts

namespace L4.Height.FreshNumericInputs
open AllSizeProtocol BStarTrace BStarLongWork BStarLongPackets BStarLongClaims BStarLongDoor
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarResetChartTouch BStarGeneratedOwner BStarLongFixedRouting BStarGeneratedBandScan
open BStarClearanceDataChart BStarCopyRightStrip BStarCopyFenceSaturation BStarFenceReceiverChart
open BStarCopyRightRetained (Dest)
open BStarFreshNumericTrace BStarFreshNumeric BStarCopyFenceCuts
open BStarCopyLeftFence (ldRead)
open BStarCopyRightFence (rdRead)
open BStarCopyLeftPending (pending)
open BStarCopyRightMixed (planOf)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Every significant old K1 site in the owner's chart is the physical
digit of its terminal header at that ordinal, including wrapped words. -/
theorem digit_at_displacement {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r≤oldOrdinal B base hh i+1)
    (frame : ∀ i,Layout B base i=Layout B y i) (k : Nat) (K : k≤len)
    (one : BStarLongFiberOwner.cmdDispl (S.getD k fall).2=1) (inside : (longGeometry B (y (S.getD k fall).1)).inside=true) :
    ∃ d : Fin r,(S.getD k fall).1=addr (S.getD len fall).1 d.val := by
  let i := (S.getD k fall).1
  let root := (S.getD len fall).1
  have start := endpoint_spec (oldH6 B base) hh o 10
  rw [←chart.terminal] at start
  have rightRoot : commandOwner (oldH6 B base) root 1=o.val := start.2.1
  have small : oldOrdinal B base hh i<r :=
    of_decide_eq_true ((flags i).symm.trans
      ((congrArg (fun t : Bool×Bool×Bool => t.2.1) (frame i)).trans inside))
  let d : Fin r := ⟨_,small⟩
  have eq : addr root d.val=digitFrom root d.val := by
    have q := BStarCopyLeftStrip.addr_from root 0 d.val
    have zero : addr root 0=root := Fin.ext (Nat.mod_eq_of_lt root.isLt)
    simpa only [Nat.zero_add,zero] using q
  obtain ⟨ord,wordAt⟩ := digit_from hp start.1 r notShort d.val d.isLt
  have actual : S.getD k fall∈S := by
    have size := chart.length
    rw [←List.getElem_eq_getD (h:=show k<S.length by omega)]
    exact List.getElem_mem _
  have own := (chart.entries _ actual).2
  have atOne : commandOwner (oldH6 B base) i 1=o.val := by
    change BStarLongFiberOwner.owner _ _ (BStarLongFiberOwner.cmdDispl (S.getD k fall).2)=_ at own
    rw [one] at own
    exact own
  have other : commandOwner (oldH6 B base) (digitFrom root d.val) 1=o.val := by
    unfold commandOwner at rightRoot ⊢
    rw [wordAt]
    exact rightRoot
  refine ⟨d,?_⟩
  rw [eq]
  exact FreshStripGeometry.same_position _ hh _ _ 1 ord.symm (atOne.trans other.symm)

theorem digit_at {base y : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r≤oldOrdinal B base hh i+1)
    (frame : ∀ i,Layout B base i=Layout B y i) (k : Nat) (K : k≤len)
    (one : (S.getD k fall).2.val=1) (inside : (longGeometry B (y (S.getD k fall).1)).inside=true) :
    ∃ d : Fin r,(S.getD k fall).1=addr (S.getD len fall).1 d.val := by
  have same : (S.getD k fall).2=1 := Fin.ext one
  apply digit_at_displacement hp chart flags notShort frame k K _ inside
  rw [same]
  rfl

/-- A pair of packed FENCE images and the drained original regions at
the same cut supply the OperandTape on every subsequent in-band subword. -/
theorem operand_tape {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → r≤oldOrdinal B base hh i+1)
    (w9 bridge later : List (Fin n)) (ack : Fin n) (m : Mode)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w9 (.busy 9 (.back 0)))
    (E : Event hp (fun j=>S.getD j fall) len (play x w9) ack (.busy 9 (.back 0)) .idle)
    (pcTen : pc (step (play x w9) ack) (S.getD 0 fall).1=10)
    (gen : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle ((w9++ack::bridge)++later) m)
    (live : LiveAt hp C x ((w9++ack::bridge)++later))
    (floor : 11≤pc (play x (w9++ack::bridge)) (S.getD 0 fall).1)
    (a : Fin n) (ls rs top : Nat)
    (L : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 ls r)
    (join : addr (S.getD 0 fall).1 ls=(S.getD len fall).1)
    (D : Dest B base (S.getD len fall).1 r)
    (R : BStarCopyRightWrappedGeometry.WrappedStrip B base a rs top)
    (head : addr a 0=addr (S.getD len fall).1 (r-1))
    (owner : dataOwner (oldH6 B base) (addr a 0) (rail rs 0)=o.val) (size : top+1=rs+r)
    (left right : Nat→BitVec 36)
    (drainL : ∀ i sh,BStarCopyLeftFenceHold.Region (S.getD 0 fall).1 ls r i sh →
      (readLane (Sheet.index sh) (play x (w9++ack::bridge) i).long).mobile=.empty)
    (drainR : ∀ i sh,BStarCopyRightWrappedFenceHold.Region (S.getD len fall).1 a r rs top i sh →
      (readLane (Sheet.index sh) (play x (w9++ack::bridge) i).long).mobile=.empty)
    (imageL : laneRead (ldRead (play x (w9++ack::bridge)) (S.getD len fall).1) 0 r=
      (pending id r).reverse.map (Digit9.data ∘ left))
    (imageR : laneRead (rdRead (play x (w9++ack::bridge)) (S.getD len fall).1 r) 0 r=
      (planOf (fun i=>i-rs) rs top).reverse.map (Digit9.data ∘ right))
    (pre tour post : List (Fin n)) (W : later=pre++tour++post) :
    OperandTape hp (fun k=>S.getD k fall) len (play (play x (w9++ack::bridge)) pre) tour := by
  let lead := w9++ack::bridge
  let entry := play x lead
  let root := (S.getD len fall).1
  intro u e v T k K
  dsimp only
  intro one inside
  let cut := pre++u
  let tail := (e::v)++post
  have full : later=cut++tail := by simp only [cut,tail,W,T,List.append_assoc,List.cons_append]
  have replay : play (play entry pre) u=play x (lead++cut) := by
    rw [BStarResetSchedule.run_append step x lead cut]
    exact (BStarResetSchedule.run_append step entry pre u).symm
  have frame := (live (lead++cut) tail (by simp only [lead,full,List.append_assoc,List.cons_append])).1
  rw [←replay] at frame
  obtain ⟨d,loc⟩ := digit_at hp C flags notShort frame k K one inside
  obtain ⟨A,Bx⟩ := BStarNativeCopyTransport.both_follow_on_tape hp C sep w9 bridge later ack m G E pcTen
    gen live floor root (S.getD 0 fall).1 a ls rs top L rfl join D R head owner drainL drainR cut tail full d
  obtain ⟨Xl,Xr⟩ := BStarNativeCopyReadback.both_at_digit entry root rs top left right size imageL imageR d
  change operands ((play (play entry pre) u) (S.getD k fall).1).long
  rw [loc,←BStarResetSchedule.run_append step entry pre u]
  exact ⟨⟨_,(congrArg Lane.retained A).trans Xl⟩,_,(congrArg Lane.retained Bx).trans Xr⟩

end L4.Height.FreshNumericInputs
