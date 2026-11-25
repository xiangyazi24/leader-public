import Leader.L4.BStarEndCacheFrame
import Leader.L4.BStarNativeZeroHead

namespace L4.BStarNativeEndCache
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetMarkAdapter BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarNumericChartCoverage BStarNumericChronology BStarNumericConsecutive
open BStarResetChartTouch BStarNumericHitSweep BStarAcquireForwardTrace
open BStarNativeZeroHead BStarEndCacheFrame BStarLongFixedRouting

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

/-- The completed first arithmetic receipt (literal PC13 CONST zero)
initializes old successor-END for the rest of the same fixed-layout
attempt. The first semantic row never needs inherited cache bits. -/
theorem after_first {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {door : Fin n} {w : List (Fin n)}
    (F : Found hp base (fun j => S.getD j fall) len 13 x w (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len (run x w) door 13)
    (suffix : List (Fin n))
    (same : ∀ u v,w++door::suffix=u++v → ∀ i, Layout B (run x u) i=Layout B base i)
    (i : Fin n) (I : i∈significantSites hp base (fun j => S.getD j fall) len) :
    let y := run (step (run x w) door) suffix
    (longGeometry B (y i)).successorEnd=endAt hp y (rightNeighbor i) := by
  dsimp only
  obtain ⟨pre,turn,ret,ds,before,launch,after,W,P,align,_⟩ := first_actual_zero hp chart sep F H
  let left := before++[launch]
  let right := turn::(ret++door::suffix)
  have split : w++door::suffix=left++(after++right) := by
    rw [W,P]
    simp [left,right,List.append_assoc]
  have beforeEq : run x left=step (run x before) launch := by
    rw [BStarResetSchedule.run_append]
    rfl
  have finalEq : run x (w++door::suffix)=run (step (run x w) door) suffix := by
    rw [BStarResetSchedule.run_append]
    rfl
  have layout : ∀ u v, after++right=u++v →
      Layout B (run (step (run x before) launch) u) (rightNeighbor i)=
        Layout B base (rightNeighbor i) := by
    intro u v E
    have Q : w++door::suffix=(left++u)++v := by rw [split,E]; simp [left,List.append_assoc]
    have L := same (left++u) v Q (rightNeighbor i)
    rw [BStarResetSchedule.run_append,beforeEq] at L
    exact L
  have keep := after_aligned hp align right i I sep layout
  have rest : run (step (run x before) launch) (after++right)=
      run (step (run x w) door) suffix := by
    rw [←beforeEq,← BStarResetSchedule.run_append,←split,finalEq]
  rw [rest] at keep
  have endLayout := same (w++door::suffix) [] (List.append_nil _).symm (rightNeighbor i)
  rw [finalEq] at endLayout
  exact keep.trans (endAt_of_layout hp _ endLayout).symm

/-- The premark geometry of each later genuine significant visit is
already correct. It does not use that visit's own refresh. Applies to
the literal CONST(B−1) and MASKB visits without a code-specific premise. -/
theorem later_significant {base x : X} {hh : ∃ i,oldH6 B base i=true}
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
    (d : D) (M : d∈ds.filter (significant hp base (fun j => S.getD j fall))) :
    (longGeometry B (d.old d.mark)).successorEnd=endAt hp d.old (rightNeighbor d.mark) := by
  have site_mem : d.mark∈significantSites hp base (fun j => S.getD j fall) len := by
    rw [←aligned_sites hp A]
    exact List.mem_map.mpr ⟨d,M,rfl⟩
  obtain ⟨pre,post,W,_,old⟩ := Aligned.prefix_to hp A d (List.mem_filter.mp M).1
  have layout : ∀ u v,w++door::(between++pre)=u++v →
      ∀ i, Layout B (run x u) i=Layout B base i := by
    intro u v E
    apply same u (v++d.mark::post)
    rw [W]
    have EE := congrArg (fun z => z++d.mark::post) E
    simpa only [List.append_assoc,List.cons_append] using EE
  have R := after_first hp chart sep F H (between++pre) layout d.mark site_mem
  rw [BStarResetSchedule.run_append,old] at R
  exact R

open BStarLongClaims BStarLongLiteral BStarLongEvents BStarLongTransport

theorem later_digit_at {base x : X} {hh : ∃ i,oldH6 B base i=true}
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
    (d : D) (M : d∈ds.filter (significant hp base (fun j => S.getD j fall)))
    (now : ∃ i,oldH6 B d.old i=true) (radix : Nat) (hr : 1<radix)
    (inPrefix : BStarH6Ordinal.oldOrdinal B d.old now d.mark<radix)
    (off : BStarPhysicalDigitSem.off (geom hp d)=
      min 5 (BStarH6Ordinal.oldOrdinal B d.old now d.mark))
    (flags : ∀ i, (longGeometry B (d.old i)).inside=
        decide (BStarH6Ordinal.oldOrdinal B d.old now i<radix) ∧
      (longGeometry B (d.old i)).last=decide (BStarH6Ordinal.oldOrdinal B d.old now i+1=radix))
    (notShort : oldH6 B d.old (rightNeighbor d.mark)=true →
      radix≤BStarH6Ordinal.oldOrdinal B d.old now d.mark+1) :
    BStarLongSector.DigitAt (geom hp d) radix (BStarH6Ordinal.oldOrdinal B d.old now d.mark) := by
  have inDs := (List.mem_filter.mp M).1
  have sig := (List.mem_filter.mp M).2
  have V := (Aligned.record_facts hp A d inDs).1
  have one := (Aligned.record_significant hp A d inDs sig).1
  have main : d.claim∈orderedCommands (oldPair B d.old d.mark) := by
    rw [←actualOffers_claims _ ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)]
    exact List.mem_map.mpr ⟨_,V.1,rfl⟩
  have axis : d.claim.source.side=.left := by
    rw [BStarLongLiteral.center_of _ _ main one]
    rfl
  have W : geom hp d=longGeometry B (d.old d.mark) := by
    unfold geom
    rw [axis]
    rfl
  rw [W] at off ⊢
  exact BStarH6Ordinal.digitAt_of_accurate B d.old now d.mark radix hr inPrefix off flags
    (later_significant hp chart sep F H between later A same d M) notShort

#print axioms later_digit_at
#print axioms after_first
#print axioms later_significant
end L4.BStarNativeEndCache
