import Leader.L4.Height.ProductionCustody
import Leader.L4.BStarCopyLeftReadyWord
import Leader.L4.BStarCopyRightWrappedReleaseClass
import Leader.L4.BStarNativeOffsetPhysical

namespace L4.Height.FreshStripGeometry
open AllSizeProtocol PhysicalCustody ProductionCustody BStarTrace BStarLongClaims
open BStarH6WordChart BStarH6Ordinal BStarAcquireLiteralChain BStarAcquireVisitOrder BStarAcquireAnchors
open BStarResetChartTouch BStarClearanceDataChart BStarFenceReceiverChart
open BStarCopyRightStrip (addr addr_next rail)
open BStarLongFiberOwner (address_inverse)
variable {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
local notation "B" => rows s
local notation "h" => oldH6 B g.base
local notation "hp" => (show 0<2 by decide)
local notation "r" => radWidth s

/-- Cancel the common command displacement, then use the physical word
and ordinal to identify a unique site. -/
theorem same_position {n : Nat} (family : Fin n→Bool) (heads : ∃ i,family i=true)
    (i j : Fin n) (k : Fin 11) (offset : ordinal family heads i=ordinal family heads j)
    (same : commandOwner family i k=commandOwner family j k) : i=j := by
  apply BStarNativeOffsetPhysical.same_ordinal_same_word family heads i j offset
  have cancel (v : Fin n) :
      BStarLongFiberOwner.addressWord (total family) (commandOwner family v k)
        (BStarLongFiberOwner.cmdDispl k)=word family v := by
    exact (address_inverse (total family) (word family v) _).trans
      (Int.emod_eq_of_lt (word_range family v heads).1 (word_range family v heads).2)
  rw [←cancel i,←cancel j,same]

/-- The two complete physical strips and coverage of every inside LS/RS source of the owner. -/
theorem strips_cover (P : Production g)
    {o : Owners h} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall) :
    let left := (S.getD 0 fall).1
    let dest := (S.getD len fall).1
    ∃ ls a rs top,
      BStarCopyLeftStrip.Strip B g.base left ls r ∧ addr left ls=dest ∧ r≤ls ∧
      (∀ j<ls,(longGeometry B (g.base (addr left j))).inside=true ↔ j<r) ∧
      BStarCopyRightWrappedGeometry.WrappedStrip B g.base a rs top ∧
      BStarCopyRightRetained.Dest B g.base dest r ∧ addr a 0=addr dest (r-1) ∧
      dataOwner h (addr a 0) (rail rs 0)=o.val ∧ top+1=rs+r ∧
      (∀ i,dataOwner h i .ls=o.val → (longGeometry B (g.base i)).inside=true →
        ∃ j,j<ls ∧ i=addr left j) ∧
      (∀ i,dataOwner h i .rs=o.val → (longGeometry B (g.base i)).inside=true →
        ∃ j,rs≤j ∧ j≤top ∧ i=addr a j) := by
  let left := (S.getD 0 fall).1
  obtain ⟨ls,L,join,_,_⟩ := BStarCopyLeftStrip.of_chart hp C (radius_pos P) g.flags g.notShort
  obtain ⟨a,rs,top,D,R,head,size,firstOwner⟩ :=
    BStarCopyRightWrappedGeometry.wrapped_of_chart hp C (radius_pos P) g.flags g.notShort
  have ord (j : Nat) (inside : j<ls) : oldOrdinal B g.base g.hh (addr left j)=j := by
    induction j with
    | zero =>
      have zero : addr left 0=left := Fin.ext (Nat.mod_eq_of_lt left.isLt)
      rw [zero]
      exact (ordinal_zero h g.hh left).mpr L.source_header
    | succ j ih =>
      have body : h (rightNeighbor (addr left j))=false := by
        rw [←addr_next]
        exact L.ls_body _ (by omega) inside
      rw [addr_next]
      exact (ordinal_body h g.hh _ body).trans (congrArg (·+1) (ih (by omega)))
  have pos := L.seam_pos
  have endDoor : h (rightNeighbor (addr left (ls-1)))=true := by
    rw [←addr_next,show ls-1+1=ls by omega]
    exact L.dest_header
  have width : r≤ls := by
    have q := g.notShort _ endDoor
    rw [ord _ (by omega)] at q
    omega
  refine ⟨ls,a,rs,top,L,join,width,?_,R,D,head,firstOwner,size,?_,?_⟩
  · intro j inside
    rw [(g.flags _).1,ord j inside,decide_eq_true_eq]
  · intro i own inside
    let j := oldOrdinal B g.base g.hh i
    have small : j<r := of_decide_eq_true ((g.flags i).1.symm.trans inside)
    have bound : j<ls := Nat.lt_of_lt_of_le small width
    have track := BStarCopyLeftReadyWord.all_owner hp C left ls r L rfl j (by omega)
    rw [BStarCopyLeftStrip.rail,if_pos bound] at track
    exact ⟨j,bound,same_position h g.hh i (addr left j) 0 (ord j bound).symm (own.trans track.symm)⟩
  · intro i own inside
    let j := oldOrdinal B g.base g.hh i
    have small : j<r := of_decide_eq_true ((g.flags i).1.symm.trans inside)
    have bound : rs+j≤top := by omega
    have track := (BStarCopyRightWrappedReleaseClass.strip_same_owner R (rs+j) bound).trans firstOwner
    rw [rail,if_neg (show ¬rs+j<rs by omega)] at track
    have ordR : oldOrdinal B g.base g.hh (addr a (rs+j))=j := by
      rw [BStarCopyLeftStrip.addr_from]
      exact (digit_from hp R.rs_header r g.notShort j small).1
    exact ⟨rs+j,by omega,bound,same_position h g.hh i (addr a (rs+j)) 2 ordR.symm (own.trans track.symm)⟩

#print axioms strips_cover
end L4.Height.FreshStripGeometry
