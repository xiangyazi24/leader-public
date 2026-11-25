import Leader.L4.BStarNumericConsecutive

namespace L4.BStarNumericChartCoverage
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarResetChartTouch BStarResetMarkAdapter BStarNumericChronology BStarNumericConsecutive
open BStarH6Ordinal BStarLongEvents BStarLongLiteral BStarLongTransport

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁)
  (J₂:=J₂) (r:=r) (c:=c) (p:=p) (c₁:=c₁)

def significantIndex (base : X) (addr : Nat → Pos n) (j : Nat) : Bool :=
  ((addr j).2.val==1) && (longGeometry B (base (addr j).1)).inside

/-- Chronological list of physically significant owner K1 addresses,
computed from the fixed chart alone, not from the scheduler word. -/
def significantSites (base : X) (addr : Nat → Pos n) (len : Nat) : List (Fin n) :=
  ((List.range len).filter (significantIndex hp base addr)).map (fun j => (addr j).1)

theorem aligned_sites {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base addr len op x 0 w len ds) :
    (ds.filter (significant hp base addr)).map Departure.mark =
      significantSites hp base addr len := by
  have one (d : D) (M : d∈ds.filter (significant hp base addr)) :
      d.mark=(addr d.index).1 := by
    obtain ⟨inT,S⟩ := List.mem_filter.mp M
    obtain ⟨V,_,_⟩ := Aligned.record_facts hp A d inT
    have one := (Aligned.record_significant hp A d inT S).1
    have main : d.claim∈orderedCommands (oldPair B d.old d.mark) := by
      rw [←actualOffers_claims _ ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)]
      exact List.mem_map.mpr ⟨_,V.1,rfl⟩
    have left : d.claim.source.side=.left := by rw [center_of _ _ main one]; rfl
    have E := congrArg Prod.fst V.2.2.1
    change (addr d.index).1=site d.mark d.claim.source.side at E
    rw [left] at E
    exact E.symm
  have I : ds.map Departure.index=List.range len := by
    simpa only [Nat.sub_zero,List.range_eq_range'] using (OutTape.indices hp (Aligned.to_tape hp A)).2
  unfold significantSites
  rw [←I,List.filter_map,List.map_map]
  apply List.map_congr_left
  intro d M
  exact one d M

theorem significant_site_coverage {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) {op : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j => S.getD j fall) len op x 0 w len ds)
    (i : Fin n) (inside : (longGeometry B (base i)).inside=true)
    (owner : commandOwner (oldH6 B base) i 1=o.val) :
    ∃ d∈ds.filter (significant hp base (fun j => S.getD j fall)), d.mark=i := by
  have active : BStarAcquireRailCoverage.active (longGeometry B (base i)) 1=true := rfl
  obtain ⟨k,kb,K⟩ := List.getElem_of_mem (C.cover (i,1) active owner)
  have lenS := C.length
  have loc : S.getD k fall=(i,1) := (List.getElem_eq_getD _).symm.trans K
  have kb' : k<len := by
    by_cases eq : k=len
    · subst k
      have E := congrArg (fun u : Pos n => u.2.val) (loc.symm.trans C.terminal)
      change (1:Nat)=10 at E
      omega
    · omega
  have mem : i∈significantSites hp base (fun j => S.getD j fall) len := by
    apply List.mem_map.mpr
    refine ⟨k,List.mem_filter.mpr ⟨List.mem_range.mpr kb',?_⟩,congrArg Prod.fst loc⟩
    unfold significantIndex
    dsimp only
    rw [loc]
    simp [inside]
  rw [←aligned_sites hp A] at mem
  exact List.mem_map.mp mem

private theorem singleton_filter {α β : Type} (us : List α) (keep : α → Bool) (f : α → β) :
    us.flatMap (fun a => if keep a then [f a] else [])=(us.filter keep).map f := by
  induction us with
  | nil => rfl
  | cons h t ih =>
    cases E : keep h <;> simp [E,ih]

/-- Significant sites have precisely the little-endian physical
ordinals 0 through width−1, in the fixed chart order. -/
theorem aligned_ordinals {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) {op width : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j => S.getD j fall) len op x 0 w len ds)
    (flags : ∀ i, (longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1) :
    (significantSites hp base (fun j => S.getD j fall) len).map
      (oldOrdinal B base hh)=List.range width := by
  let adr := fun j => S.getD j fall
  have root : (adr 0).2.val=0 := congrArg (fun u : Pos n => u.2.val) C.root
  have terminal : (adr len).2.val=10 := congrArg (fun u : Pos n => u.2.val) C.terminal
  have T := Aligned.to_tape hp A
  have P := tape_digits hp T flags notShort root terminal
  have per (d : D) (M : d∈ds) :
      actualDigit hp base hh d=
        if significant hp base adr d then [oldOrdinal B base hh d.mark] else [] := by
    obtain ⟨V,L,_⟩ := Aligned.record_facts hp A d M
    have E : adr d.index=address d.mark d.claim.source := V.2.2.1
    have II : (oldPair B d.old d.mark).1.inside=(longGeometry B (base d.mark)).inside :=
      (congrArg (fun z : Bool × Bool × Bool => z.2.1) (L d.mark)).symm
    have J : d.claim∈orderedCommands (oldPair B d.old d.mark) := by
      rw [←actualOffers_claims _ ((d.old d.mark).long,(d.old (rightNeighbor d.mark)).long)]
      exact List.mem_map.mpr ⟨_,V.1,rfl⟩
    unfold actualDigit significant
    rw [E,II]
    by_cases one : d.claim.source.occurrence.val=1
    · have side : d.claim.source.side=.left := by rw [center_of _ _ J one]; rfl
      change (if d.claim.source.occurrence.val=1 ∧ _ then _ else []) =
        if (((d.claim.source.occurrence.val==1) &&
          (longGeometry B (base (site d.mark d.claim.source.side))).inside)) then _ else _
      rw [side]
      simp [one,site]
    · simp [one]
  have mapEq (dd : List D) (inc : ∀ d∈dd,d∈ds) :
      dd.flatMap (actualDigit hp base hh)=
      dd.flatMap (fun d => if significant hp base adr d then [oldOrdinal B base hh d.mark] else []) := by
    induction dd with
    | nil => rfl
    | cons d tail ih =>
      simp only [List.flatMap_cons,per d (inc d List.mem_cons_self),
        ih (fun v h => inc v (List.mem_cons_of_mem _ h))]
  have M := mapEq ds (fun _ h => h)
  rw [M,singleton_filter] at P
  rw [←aligned_sites hp A,List.map_map]
  exact P

/-- Canonical little-endian length is a theorem of the actual
selected itinerary under the same fixed IN/no-short geometry. -/
theorem significant_length {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) {op width : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j => S.getD j fall) len op x 0 w len ds)
    (flags : ∀ i, (longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<width))
    (notShort : ∀ i,oldH6 B base (rightNeighbor i)=true → width≤oldOrdinal B base hh i+1) :
    (significantSites hp base (fun j => S.getD j fall) len).length=width := by
  have H := congrArg List.length (aligned_ordinals hp C A flags notShort)
  simpa using H

/-- Read the fixed physical digit list as a Fin-indexed site map. -/
def digitSite (base : X) (addr : Nat → Pos n) (len width : Nat)
    (L : (significantSites hp base addr len).length=width) (j : Fin width) : Fin n :=
  (significantSites hp base addr len)[j.val]'(by omega)

theorem digitSite_of_visit {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base addr len op x 0 w len ds) (width : Nat)
    (L : (significantSites hp base addr len).length=width) (j : Fin width) :
    let visits := ds.filter (significant hp base addr)
    ∃ bound : j.val<visits.length,
      digitSite hp base addr len width L j=(visits[j.val]'bound).mark := by
  dsimp only
  have E := aligned_sites hp A
  have sz := congrArg List.length E
  rw [List.length_map,L] at sz
  have H : j.val<(ds.filter (significant hp base addr)).length := by omega
  refine ⟨H,?_⟩
  have eq := congrArg (fun a : List (Fin n) => a[j.val]?) E
  have hr : j.val<(significantSites hp base addr len).length := by omega
  rw [List.getElem?_map,List.getElem?_eq_getElem H,List.getElem?_eq_getElem hr] at eq
  exact (Option.some.inj eq).symm

#print axioms digitSite_of_visit
#print axioms aligned_ordinals
#print axioms aligned_sites
#print axioms significant_site_coverage
end L4.BStarNumericChartCoverage
