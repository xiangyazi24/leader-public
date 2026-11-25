import Leader.L4.BStarNativeOffsetDigitAt

namespace L4.BStarNativeScanPosition
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetMarkAdapter BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarNumericChartCoverage BStarNumericConsecutive BStarAcquireForwardTrace
open BStarH6Ordinal BStarPhysicalDigitSem
open BStarNumericChronology BStarResetChartTouch BStarLongFixedRouting BStarSeparatorControl BStarNumericHitSweep

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

/-- After actual PC13, all later significant visits have the
canonical numerical SCAN5 predicates. Does not assume cached
offsets initially or use the value refreshed by the current mark. -/
theorem later_scan_positions {base x : X}
    {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {door : Fin n} {w : List (Fin n)}
    (F : Found hp base (fun j => S.getD j fall) len 13 x w (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len (run x w) door 13)
    (between later : List (Fin n)) {op : Nat} {ds : List D}
    (A : Aligned hp base (fun j => S.getD j fall) len op
      (run (step (run x w) door) between) 0 later len ds)
    (same : ∀ u v,w++door::(between++later)=u++v →
      ∀ i, Layout B (run x u) i=Layout B base i)
    {width : Nat}
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1) :
    let visits := ds.filter (significant hp base (fun j => S.getD j fall))
    ∀ j : Fin visits.length, ScanPosition (geom hp visits[j.val]) j.val := by
  dsimp only
  intro j
  let visits := ds.filter (significant hp base (fun j => S.getD j fall))
  let d := visits[j.val]
  have M : d∈visits := List.getElem_mem j.isLt
  have offEq := BStarNativeOffsetDigitAt.later_offset hp chart sep F H between later A same flags notShort d M
  have O := aligned_ordinals hp chart A flags notShort
  rw [←aligned_sites hp A,List.map_map] at O
  have J := congrArg (fun t : List Nat => t[j.val]?) O
  have order : oldOrdinal B base hh d.mark=j.val := by
    have jw : j.val<width := by
      have eq := congrArg List.length O
      simp only [List.length_map,List.length_range] at eq
      change visits.length=width at eq
      exact eq ▸ j.isLt
    change (visits.map (oldOrdinal B base hh ∘ Departure.mark))[j.val]? = (List.range width)[j.val]? at J
    rw [List.getElem?_map,List.getElem?_eq_getElem j.isLt] at J
    simpa only [List.getElem?_range jw,Option.map_some,Function.comp_apply,Option.some.injEq] using J
  unfold ScanPosition
  change (off (geom hp d)=0 ↔ j.val=0) ∧ (off (geom hp d)=1 ↔ j.val=1)
  rw [offEq,order]
  omega

#print axioms later_scan_positions
end L4.BStarNativeScanPosition
