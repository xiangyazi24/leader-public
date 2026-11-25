import Leader.L4.PhysicalCustodyHistorical
import Leader.L4.BStarResetChartTouch

namespace L4.PhysicalCustody
open AllSizeProtocol BStarH6WordChart BStarH6Ordinal BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarResetChartTouch

/-- Ordinal-correct flags and minimum sector width give the local
structural header and continuation guards, without assuming them as
separate producers. -/
theorem settled_flags_guards {s n : Nat} {z : Raw s n}
    (hh : ∃ i,oldH6 (rows s) z i=true) (hw : 0 < radWidth s)
    (flags : ∀ i,
      (longGeometry (rows s) (z i)).inside=decide (oldOrdinal (rows s) z hh i<radWidth s) ∧
      (longGeometry (rows s) (z i)).last=decide (oldOrdinal (rows s) z hh i+1=radWidth s))
    (notShort : ∀ i,oldH6 (rows s) z (rightNeighbor i)=true →
      radWidth s≤oldOrdinal (rows s) z hh i+1) :
    (∀ i,let g:=longGeometry (rows s) (z i); (!g.axes.h6 || g.inside)=true) ∧
    (∀ i,let g:=oldPair (rows s) z i; continuation g.1 g.2=true) := by
  constructor
  · intro i
    change (!oldH6 (rows s) z i || (longGeometry (rows s) (z i)).inside)=true
    rw [(flags i).1]
    cases H : oldH6 (rows s) z i
    · rfl
    · have O : oldOrdinal (rows s) z hh i=0 := (ordinal_zero _ hh i).mpr H
      simp [O,hw]
  · intro i
    let j := rightNeighbor i
    let k := oldOrdinal (rows s) z hh i
    let r := radWidth s
    change ((!((longGeometry (rows s) (z i)).inside && !(longGeometry (rows s) (z i)).last) ||
        (!oldH6 (rows s) z j && (longGeometry (rows s) (z j)).inside)) &&
      (!(!oldH6 (rows s) z j && (longGeometry (rows s) (z j)).inside) ||
        ((longGeometry (rows s) (z i)).inside && !(longGeometry (rows s) (z i)).last)))=true
    rw [(flags i).1,(flags i).2,(flags j).1]
    cases H : oldH6 (rows s) z j
    · have O : oldOrdinal (rows s) z hh j=k+1 := ordinal_body _ hh i H
      rw [O]
      change ((!((decide (k<r)) && !(decide (k+1=r))) || (!false && decide (k+1<r))) &&
        (!(!false && decide (k+1<r)) || (decide (k<r) && !(decide (k+1=r)))))=true
      by_cases A : k+1<r
      · have B : k<r := by omega
        have C : k+1≠r := by omega
        simp [A,B,C]
      · by_cases B : k<r
        · have C : k+1=r := by omega
          simp [B,C]
        · simp [A,B]
    · have W : r≤k+1 := notShort i H
      change ((!((decide (k<r)) && !(decide (k+1=r))) ||
        (!true && decide (oldOrdinal (rows s) z hh j<r))) &&
        (!(!true && decide (oldOrdinal (rows s) z hh j<r)) ||
          (decide (k<r) && !(decide (k+1=r)))))=true
      by_cases K : k<r
      · have E : k+1=r := by omega
        simp [K,E]
      · simp [K]

/-- The same minimal geometry constructs every physical command chart. -/
theorem settled_flags_charts {s n : Nat} {z : Raw s n}
    (hh : ∃ i,oldH6 (rows s) z i=true) (hw : 0 < radWidth s)
    (flags : ∀ i,
      (longGeometry (rows s) (z i)).inside=decide (oldOrdinal (rows s) z hh i<radWidth s) ∧
      (longGeometry (rows s) (z i)).last=decide (oldOrdinal (rows s) z hh i+1=radWidth s))
    (notShort : ∀ i,oldH6 (rows s) z (rightNeighbor i)=true →
      radWidth s≤oldOrdinal (rows s) z hh i+1)
    (o : Owners (oldH6 (rows s) z)) :
    ∃ (S : List (Pos n)) (len : Nat) (fall : Pos n),
      Chart (show 0 < 2 by decide) z hh o S len fall := by
  let i := Classical.choose hh
  obtain ⟨S,len,C⟩ := chart_exists (show 0 < 2 by decide) z hh (radWidth s)
    hw flags notShort o (i,0)
  exact ⟨S,len,(i,0),C⟩

/-- On a cleaned, settled fiber the physical owner charts and local
routing guards need not be supplied separately to obtain an access word.
This is finite deterministic access, not a uniform mean bound. -/
theorem settled_flags_access {s n : Nat} (z : Raw s n)
    (Q : Raw s n → Prop) (qz : Q z) (clean : ∀ i, GrantClean z i)
    (closed : ∀ y e, Q y → Q (rawNext s y e))
    (fiber : ∀ y, Q y → ∀ i, BStarLongFixedRouting.Layout (rows s) z i =
      BStarLongFixedRouting.Layout (rows s) y i)
    (hh : ∃ i,oldH6 (rows s) z i=true) (hw : 0 < radWidth s)
    (offset : BStarClearanceOffset.correct (oldH6 (rows s) z) hh 5 z)
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
      4*(oldOrdinal (rows s) z hh e+1)<81*(oldOrdinal (rows s) z hh f+1))
    (sep : ∀ e : Fin n,e≠rightNeighbor e) :
    ∃ w : List (Fin n), Custody (rawRun z w) := by
  obtain ⟨head,cont⟩ := settled_flags_guards hh hw flags notShort
  have charts := settled_flags_charts hh hw flags notShort
  obtain ⟨u,v,C⟩ := cuts_after_init z Q qz clean closed fiber hh offset head cont charts sep
  exact ⟨u++v,custody_of_cuts z Q qz clean closed fiber hh offset flags notShort head cont
    packed upperWidth widthRatio charts sep u v C⟩

private theorem ordinal_congr {n : Nat} {h k : Fin n → Bool} (E : h=k)
    (hh : ∃ i,h i=true) (kk : ∃ i,k i=true) :
    ordinal h hh=ordinal k kk := by
  subst k
  rfl

/-- From a settled lower geometry cut, any five full physical covers
enable a finite access tape to amended custody. This does not assert a
uniform probability or mean for the access tape. -/
theorem settled_cover_access {s n : Nat} (x : Raw s n)
    (Q : Raw s n → Prop) (qx : Q x)
    (closed : ∀ y e, Q y → Q (rawNext s y e))
    (fiber : ∀ y, Q y → ∀ i, BStarLongFixedRouting.Layout (rows s) x i =
      BStarLongFixedRouting.Layout (rows s) y i)
    (hh : ∃ i,oldH6 (rows s) x i=true) (hw : 0 < radWidth s)
    (flags : ∀ i,
      (longGeometry (rows s) (x i)).inside=decide (oldOrdinal (rows s) x hh i<radWidth s) ∧
      (longGeometry (rows s) (x i)).last=decide (oldOrdinal (rows s) x hh i+1=radWidth s))
    (notShort : ∀ i,oldH6 (rows s) x (rightNeighbor i)=true →
      radWidth s≤oldOrdinal (rows s) x hh i+1)
    (packed : total (oldH6 (rows s) x)*radWidth s≤n)
    (upperWidth : ∀ i,oldH6 (rows s) x (rightNeighbor i)=true →
      oldOrdinal (rows s) x hh i+1≤1024*radWidth s)
    (widthRatio : ∀ e f,
      oldH6 (rows s) x (rightNeighbor e)=true → oldH6 (rows s) x (rightNeighbor f)=true →
      4*(oldOrdinal (rows s) x hh e+1)<81*(oldOrdinal (rows s) x hh f+1))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (blocks : List (List (Fin n))) (five : blocks.length=5)
    (full : ∀ w∈blocks,∀ e,e∈w) :
    ∃ w : List (Fin n), Custody (rawRun x (blocks.flatten++w)) := by
  let z := rawRun x blocks.flatten
  have same (y : Raw s n) (hy : Q y) (i : Fin n) :
      oldH6 (rows s) y i=oldH6 (rows s) x i :=
    (congrArg Prod.fst (fiber y hy i)).symm
  obtain ⟨qz,off,clean⟩ := historical_init (oldH6 (rows s) x) hh sep Q closed same x qx blocks five full
  change Q z at qz
  change ∀ i, GrantClean z i at clean
  have headEq : oldH6 (rows s) z=oldH6 (rows s) x := funext (same z qz)
  have hz : ∃ i,oldH6 (rows s) z i=true := by rw [headEq]; exact hh
  have ho (i : Fin n) : oldOrdinal (rows s) z hz i=oldOrdinal (rows s) x hh i :=
    congrFun (ordinal_congr headEq hz hh) i
  have ofz : BStarClearanceOffset.correct (oldH6 (rows s) z) hz 5 z := by
    intro i
    have H := off i
    change _ = min 5 (oldOrdinal (rows s) z hz i)
    rw [ho,headEq]
    exact H
  have flagsZ (i : Fin n) :
      (longGeometry (rows s) (z i)).inside=decide (oldOrdinal (rows s) z hz i<radWidth s) ∧
      (longGeometry (rows s) (z i)).last=decide (oldOrdinal (rows s) z hz i+1=radWidth s) := by
    have F := fiber z qz i
    have I := congrArg (fun q : Bool × Bool × Bool => q.2.1) F
    have L := congrArg (fun q : Bool × Bool × Bool => q.2.2) F
    change (longGeometry (rows s) (x i)).inside=(longGeometry (rows s) (z i)).inside at I
    change (longGeometry (rows s) (x i)).last=(longGeometry (rows s) (z i)).last at L
    rw [←I,←L,ho]
    exact flags i
  obtain ⟨w,hit⟩ := settled_flags_access z Q qz clean closed
    (fun y qy i => (fiber z qz i).symm.trans (fiber y qy i)) hz hw ofz flagsZ
    (fun i h => by rw [ho]; exact notShort i (by simpa only [headEq] using h))
    (by simpa only [headEq] using packed)
    (fun i h => by rw [ho]; exact upperWidth i (by simpa only [headEq] using h))
    (fun e f he hf => by
      rw [ho,ho]
      exact widthRatio e f (by simpa only [headEq] using he) (by simpa only [headEq] using hf)) sep
  refine ⟨w,?_⟩
  unfold rawRun at hit ⊢
  rw [BStarResetSchedule.run_append]
  exact hit

#print axioms settled_flags_guards
#print axioms settled_flags_charts
#print axioms settled_flags_access
#print axioms settled_cover_access
end L4.PhysicalCustody
