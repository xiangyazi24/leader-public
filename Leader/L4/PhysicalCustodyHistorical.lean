import Leader.L4.PhysicalCustodyCovers
import Leader.L4.PhysicalCustodyCoherence

set_option maxRecDepth 4096
namespace L4.PhysicalCustody
open AllSizeProtocol BStarTrace BStarH6WordChart BStarClearanceOffset
open BStarLongWork BStarH6Ordinal BStarLongFixedRouting BStarAcquireLiteralChain
open BStarAcquireVisitOrder BStarResetChartTouch BStarCustodyCuts
local notation "hp" => (show 0<2 by decide)

theorem historical_init {s n : Nat} (h : Fin n→Bool) (hh : ∃ i,h i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : Raw s n→Prop) (closed : ∀ y e,Q y→Q (rawNext s y e))
    (same : ∀ y,Q y→∀ i,oldH6 (rows s) y i=h i)
    (x : Raw s n) (qx : Q x) (blocks : List (List (Fin n)))
    (H : blocks.length=5) (full : ∀ w∈blocks,∀ e,e∈w) :
    let z := rawRun x blocks.flatten
    Q z ∧ correct h hh 5 z ∧ ∀ i,GrantClean z i := by
  have off := actual_offset_covers h hh sep Q closed same x qx blocks (by omega) full
  refine ⟨off.1,H ▸ off.2,?_⟩
  apply grant_coherent_after_cover x blocks.flatten sep
  intro e
  cases blocks with
  | nil => cases H
  | cons w rest =>
    rw [List.flatten_cons]
    exact List.mem_append_left _ (full w List.mem_cons_self e)

theorem custody_of_cuts {s n : Nat} (z : Raw s n)
    (Q : Raw s n→Prop) (qz : Q z) (clean : ∀ i,GrantClean z i)
    (closed : ∀ y e,Q y→Q (rawNext s y e))
    (fiber : ∀ y,Q y→∀ i,Layout (rows s) z i=Layout (rows s) y i)
    (hh : ∃ i,oldH6 (rows s) z i=true)
    (offset : correct (oldH6 (rows s) z) hh 5 z)
    (flags : ∀ i,
      (longGeometry (rows s) (z i)).inside=decide (oldOrdinal (rows s) z hh i<radWidth s) ∧
      (longGeometry (rows s) (z i)).last=decide (oldOrdinal (rows s) z hh i+1=radWidth s))
    (notShort : ∀ i,oldH6 (rows s) z (rightNeighbor i)=true →
      radWidth s≤oldOrdinal (rows s) z hh i+1)
    (head : ∀ i,let g:=longGeometry (rows s) (z i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair (rows s) z i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (packed : total (oldH6 (rows s) z)*radWidth s≤n)
    (upperWidth : ∀ i,oldH6 (rows s) z (rightNeighbor i)=true →
      oldOrdinal (rows s) z hh i+1≤1024*radWidth s)
    (widthRatio : ∀ e f,
      oldH6 (rows s) z (rightNeighbor e)=true → oldH6 (rows s) z (rightNeighbor f)=true →
      4*(oldOrdinal (rows s) z hh e+1)<81*(oldOrdinal (rows s) z hh f+1))
    (charts : ∀ o : Owners (oldH6 (rows s) z),
      ∃ (S : List (Pos n)) (len : Nat) (fall : Pos n), Chart hp z hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (u v : List (Fin n)) (cuts : CutFacts hp z z u v) :
    Custody (rawRun z (u++v)) := by
  refine ⟨{ base := z, initial := z, u := u, v := v, past := []
            Q := fun y=>Q y ∧ ∀ i,GrantClean y i
            init := ⟨qz,clean⟩
            closed := fun y e H=>⟨closed y e H.1,grant_coherent_closed y e (sep e) H.2⟩
            fiber := fun y H => fiber y H.1
            here := by rw [List.append_nil]
            hh := hh, baseOffset := offset, offset := offset
            flags := flags, notShort := notShort, heads := head, cont := cont
            packed := packed, upperWidth := upperWidth, widthRatio := widthRatio
            charts := charts, cuts := cuts, coherent := fun _ H=>H.2 }⟩


theorem cuts_after_init {s n : Nat} (z : Raw s n)
    (Q : Raw s n→Prop) (qz : Q z) (clean : ∀ i,GrantClean z i)
    (closed : ∀ y e,Q y→Q (rawNext s y e))
    (fiber : ∀ y,Q y→∀ i,Layout (rows s) z i=Layout (rows s) y i)
    (hh : ∃ i,oldH6 (rows s) z i=true)
    (offset : correct (oldH6 (rows s) z) hh 5 z)
    (head : ∀ i,let g:=longGeometry (rows s) (z i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair (rows s) z i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (charts : ∀ o : Owners (oldH6 (rows s) z),
      ∃ (S : List (Pos n)) (len : Nat) (fall : Pos n), Chart hp z hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) :
    ∃ u v, CutFacts hp z z u v := by
  let Q' := fun y=>Q y ∧ ∀ i,GrantClean y i
  have heads (y : Raw s n) (hy : Q' y) (i : Fin n) :
      let g:=longGeometry (rows s) (y i); (!g.axes.h6 || g.inside)=true := by
    change (!(Layout (rows s) y i).1 || (Layout (rows s) y i).2.1)=true
    rw [←fiber y hy.1 i]
    exact head i
  have conts (y : Raw s n) (hy : Q' y) (i : Fin n) :
      let g:=oldPair (rows s) y i; BStarAcquireRailCoverage.continuation g.1 g.2=true := by
    let good := fun (a b : Bool × Bool × Bool) =>
      (!(a.2.1 && !a.2.2) || (!b.1 && b.2.1)) &&
        (!(!b.1 && b.2.1) || (a.2.1 && !a.2.2))
    change good (Layout (rows s) y i) (Layout (rows s) y (rightNeighbor i))=true
    rw [←fiber y hy.1 i,←fiber y hy.1 (rightNeighbor i)]
    exact cont i
  let h := oldH6 (rows s) z
  let own : Fin (total h) → Owners h := fun j=>⟨(j.val : Int),by omega,by omega⟩
  let owners := List.ofFn own
  have allPorts (i : Fin n) (j : Fin 3) :
      ∃ o∈owners,BStarAcquireAnchors.commandOwner h i (BStarResetNoAcquire.slot j)=o.val := by
    let a := BStarAcquireAnchors.commandOwner h i (BStarResetNoAcquire.slot j)
    have r : 0≤a ∧ a<(total h : Int) := BStarAcquireAnchors.commandOwner_range h hh i _
    let f : Fin (total h) := ⟨a.toNat,by omega⟩
    refine ⟨own f,?_,?_⟩
    · exact List.mem_ofFn.mpr ⟨f,rfl⟩
    · change a=(a.toNat : Int)
      omega
  obtain ⟨u,v,_,_,C⟩ := compatible_cuts hp hh charts sep head cont Q'
    (fun y e H=>⟨closed y e H.1,grant_coherent_closed y e (sep e) H.2⟩)
    (fun y H=>fiber y H.1) heads conts offset owners allPorts ⟨qz,clean⟩ offset
  exact ⟨u,v,C⟩

#print axioms cuts_after_init
#print axioms historical_init
#print axioms custody_of_cuts
end L4.PhysicalCustody
