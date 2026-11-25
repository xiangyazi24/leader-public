import Leader.L4.BStarNativeOffsetPhysical
import Leader.L4.BStarNativeEndCache
namespace L4.BStarNativeOffsetDigitAt
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetMarkAdapter BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarNumericChartCoverage BStarNumericChronology BStarNumericConsecutive
open BStarResetChartTouch BStarNumericHitSweep BStarAcquireForwardTrace
open BStarNativeEndCache BStarNativeZeroHead BStarEndCacheFrame BStarLongFixedRouting

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

open BStarH6Ordinal

theorem later_offset {base x : X} {hh : ∃ i,oldH6 B base i=true}
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
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1)
    (d : D) (M : d∈ds.filter (significant hp base (fun j => S.getD j fall))) :
    BStarPhysicalDigitSem.off (geom hp d)=min 5 (oldOrdinal B base hh d.mark) := by
  obtain ⟨pre,turn,ret,rs,before,launch,after,W,P,align,_⟩ := first_actual_zero hp chart sep F H
  let start := before++[launch]
  let gap := turn::(ret++door::between)
  have T : w++door::(between++later)=start++((after++gap)++later) := by
    rw [W,P]
    simp only [start,gap,List.append_assoc,List.cons_append,List.nil_append]
  have init : run x start=step (run x before) launch := by
    rw [BStarResetSchedule.run_append]; rfl
  have endpoint : run (step (run x before) launch) (after++gap)=run (step (run x w) door) between := by
    rw [←init,←BStarResetSchedule.run_append]
    have eq : start++(after++gap)=(w++[door])++between := by
      rw [W,P]
      simp [start,gap,List.append_assoc]
    rw [eq,BStarResetSchedule.run_append,BStarResetSchedule.run_append]
    rfl
  have fixed (u v : List (Fin n)) (E : (after++gap)++later=u++v) :
      oldH6 B (run (step (run x before) launch) u)=oldH6 B base := by
    have eq : w++door::(between++later)=(start++u)++v := by
      exact T.trans ((congrArg (start++·) E).trans (List.append_assoc start u v).symm)
    have L := same (start++u) v eq
    rw [BStarResetSchedule.run_append,init] at L
    exact funext fun i => congrArg Prod.fst (L i)
  exact BStarNativeOffsetPhysical.later_offset hp chart sep align flags notShort gap later
    (endpoint.symm ▸ A) fixed d M

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
    (baseFlags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<radix))
    (baseNotShort : ∀ i,oldH6 B base (rightNeighbor i)=true → radix≤oldOrdinal B base hh i+1)
    (flags : ∀ i, (longGeometry B (d.old i)).inside=
        decide (BStarH6Ordinal.oldOrdinal B d.old now i<radix) ∧
      (longGeometry B (d.old i)).last=decide (BStarH6Ordinal.oldOrdinal B d.old now i+1=radix))
    (notShort : oldH6 B d.old (rightNeighbor d.mark)=true →
      radix≤BStarH6Ordinal.oldOrdinal B d.old now d.mark+1) :
    BStarLongSector.DigitAt (geom hp d) radix (BStarH6Ordinal.oldOrdinal B d.old now d.mark) := by
  have offset := later_offset hp chart sep F H between later A same baseFlags baseNotShort d M
  have L := (Aligned.record_facts hp A d (List.mem_filter.mp M).1).2.1
  have fixed : oldH6 B d.old=oldH6 B base :=
    funext fun i => (congrArg Prod.fst (L i)).symm
  have compat (h g : Fin n→Bool) (E : h=g) (H : ∃ i,h i=true)
      (G : ∃ i,g i=true) (i : Fin n) : ordinal h H i=ordinal g G i := by
    subst g
    rfl
  have ordEq (i : Fin n) : oldOrdinal B d.old now i=oldOrdinal B base hh i :=
    compat _ _ fixed now hh i
  exact BStarNativeEndCache.later_digit_at hp chart sep F H between later A same d M now radix hr
    inPrefix (by rwa [ordEq]) flags notShort

end L4.BStarNativeOffsetDigitAt
