import Leader.L4.BStarClearanceCommandSum
import Leader.L4.BStarClearanceOffset

namespace L4.BStarClearanceIndexedSum
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarH6WordChart BStarLongFiberOwner BStarAcquireAnchors
open BStarResetChartIndex BStarResetChartTouch BStarClearanceCommandSum
open BStarClearanceChartFootprint BStarLongEvents BStarLongFixedRouting
open BStarClearanceOffset BStarResetMarkAdapter BStarLongRouting BStarClearanceForward
open BStarLongCommand BStarClearanceGate
open BStarLongTransport BStarAcquireRailCoverage

def distance {n : Nat} (S : List (Pos n)) (u : Pos n) : Nat :=
  S.length-S.findIdx (fun v => v == u)

theorem distance_idx {n : Nat} {S : List (Pos n)} (nd : S.Nodup)
    {i : Nat} (hi : i<S.length) : distance S S[i]=S.length-i := by
  let pred := fun v : Pos n => v == S[i]
  have lt : S.findIdx pred<S.length :=
    List.findIdx_lt_length_of_exists ⟨S[i],List.getElem_mem _,by simp [pred]⟩
  have eq : S[S.findIdx pred]=S[i] := beq_iff_eq.mp (List.findIdx_getElem (w:=lt))
  have K := (List.getElem_inj nd).mp eq
  change S.length-S.findIdx pred=S.length-i
  rw [K]

private theorem raw_rank_geometry (g h : LongGeometry) (j : Fin 11) (d : Nat) (t : Token)
    (H : ∀ op, gate op j g=gate op j h) :
    forwardRank g j d (bind g j t)=forwardRank h j d (bind h j t) := by
  have B : bind g j t=bind h j t := by
    cases t <;> simp [BStarLongCommand.bind,H]
  rw [B]
  generalize bind h j t=w
  cases w <;> simp [forwardRank,weight,H]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => X k₁ k₂ t₂ J₁ J₂ r c p c₁ n

/-- Offset certification gives equality of the actual rank evaluation
against any fixed certified geometry snapshot. -/
theorem rank_fixed (h : Fin n → Bool) (hh : ∃ i,h i=true)
    (base x raw : X)
    (HB : ∀ i, oldH6 B base i=h i) (HX : ∀ i, oldH6 B x i=h i)
    (cb : correct h hh 5 base) (cx : correct h hh 5 x)
    (dist : Pos n → Nat) (u : Pos n) :
    physicalRank B base raw dist u = physicalRank B x raw dist u := by
  apply raw_rank_geometry
  intro op
  change gate op u.2 (longGeometry B (base u.1))=gate op u.2 (longGeometry B (x u.1))
  rw [gate_at_ordinal hp h hh base HB cb,gate_at_ordinal hp h hh x HX cx]

/-- Ownership and exact remaining distance of selected footprints,
independent of the packed controller snapshot and of its door stage. -/
theorem chart_owner_hypotheses {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i) (e : Fin n) :
    let g := oldPair B x e
    let adr := address e
    (ownerBlocks B x e o.val).flatten ⊆ S ∧
    (∀ a, adr a∈S → physicalOwner (oldH6 B x) e cmdDispl a=o.val) ∧
    (∀ C∈orderedCommands g, physicalOwner (oldH6 B x) e cmdDispl C.source=o.val →
      (∀ a, C.destination=some a → distance S (adr C.source)=distance S (adr a)+1) ∧
      (C.destination=none → C.kind≠.door → 0<distance S (adr C.source))) := by
  dsimp only
  let g := oldPair B x e
  let adr := address e
  have hs : oldH6 B x=oldH6 B base := funext (fun i => (congrArg Prod.fst (same i)).symm)
  have part : (ownerBlocks B x e o.val).flatten ⊆ S := by
    intro u hu
    change u∈((orderedCommands g).filter _ |>.flatMap (footprint e)) at hu
    obtain ⟨C,HC,hu⟩ := List.mem_flatMap.mp hu
    obtain ⟨hc,own⟩ := List.mem_filter.mp HC
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hu
    have ow := (footprint_owner B x e C hc a ha).trans (beq_iff_eq.mp own)
    rw [hs] at ow
    apply chart.cover (adr a) _ (show commandOwner (oldH6 B base) (adr a).1 (adr a).2=o.val from ow)
    have AZ : a=C.source ∨ C.destination=some a := by
      cases D : C.destination <;> simpa [Claim.slots,D,eq_comm] using ha
    have hcB : C∈orderedCommands (oldPair B base e) :=
      (command_eq B base x same e).symm ▸ hc
    rcases AZ with rfl|D
    · cases E : C.destination with
      | some t =>
        have K := (BStarAcquireChainEndpoints.link_endpoints _ C t hcB E).1
        cases Z : C.source.side <;> simpa [BStarLongCommand.geometry,oldPair,site,Z,adr] using K
      | none =>
        have O : C.source.occurrence.val=0 ∨ C.source.occurrence.val=10 := by
          by_cases J : C.kind=.door
          · exact .inl (congrArg (fun z : AtK => z.occurrence.val) (selected_door _ C hcB J).1)
          · exact .inr (BStarAcquireChainEndpoints.terminal _ C hcB E J).2.2.2
        unfold active
        change (_ && _ || _)=true
        rcases O with O|O <;> simp [O,adr]
    · have K := (BStarAcquireChainEndpoints.link_endpoints _ C a hcB D).2.1
      cases Z : a.side <;> simpa [BStarLongCommand.geometry,oldPair,site,Z,adr] using K
  have owns (a : AtK) (h : adr a∈S) : physicalOwner (oldH6 B x) e cmdDispl a=o.val := by
    rw [hs]
    exact (chart.entries _ h).2
  refine ⟨part,owns,?_⟩
  intro C hc own
  have Cmem : adr C.source∈S := part (by
    apply List.mem_flatten.mpr
    refine ⟨footprint e C,?_,List.mem_map.mpr ⟨_,by simp [Claim.slots],rfl⟩⟩
    exact List.mem_map.mpr ⟨C,List.mem_filter.mpr ⟨hc,beq_iff_eq.mpr own⟩,rfl⟩)
  refine ⟨?_,?_⟩
  · intro a E
    have F : Edge B x (adr C.source) (adr a) := ⟨e,C,a,hc,E,rfl,rfl⟩
    obtain ⟨j,hj,U,V⟩ := chart.edge _ _ Cmem ((edge_fixed B base x same _ _).mpr F)
    change distance S (adr C.source)=distance S (adr a)+1
    rw [←U,←V,distance_idx chart.nodup,distance_idx chart.nodup]
    omega
  · intro _ _
    change 0 < distance S (adr C.source)
    exact Nat.sub_pos_of_lt (List.findIdx_lt_length_of_exists ⟨_,Cmem,by simp⟩)

/-- Actual owner first coordinate on a chosen indexed chart, with
distance equal to the remaining length INCLUDING terminal service. -/
theorem indexed_sum {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (chart : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (cb : correct (oldH6 B base) hh 5 base) (cx : correct (oldH6 B base) hh 5 x)
    (e : Fin n) (he : e≠rightNeighbor e) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let post := AllSizeS1Geometry.step B x e
    let adr := address e
    let rank := physicalRank B base
    let dist := distance S
    (∀ a, adr a∈S → BStarResetQuietTable.DoorSafe g raw a) →
    (∀ C∈orderedCommands g, physicalOwner (oldH6 B base) e cmdDispl C.source=o.val →
      C.kind=.door → rank post dist (adr C.source)≤rank x dist (adr C.source)) →
    BStarClearanceAggregate.total (rank post dist) S≤BStarClearanceAggregate.total (rank x dist) S ∧
    ((∃ C q, (C,.advance q)∈actualOffers g raw ∧
          physicalOwner (oldH6 B base) e cmdDispl C.source=o.val) →
      BStarClearanceAggregate.total (rank post dist) S<BStarClearanceAggregate.total (rank x dist) S) := by
  dsimp only
  intro safe door
  let g := oldPair B x e
  let adr := address e
  let post := AllSizeS1Geometry.step B x e
  have hs : oldH6 B x=oldH6 B base := funext (fun i => (congrArg Prod.fst (same i)).symm)
  have R (raw : X) : physicalRank B base raw (distance S)=physicalRank B x raw (distance S) :=
    funext (rank_fixed hp _ hh base x raw (fun _ => rfl) (congrFun hs) cb cx _)
  rw [R x,R post]
  obtain ⟨part,owns,links⟩ := chart_owner_hypotheses hp chart same e
  have rr := owner_sum hp x e he o.val S (distance S) chart.nodup part owns safe
  rw [hs] at rr
  apply rr
  intro C hc own
  obtain ⟨N,P⟩ := links C hc (by rwa [hs])
  refine ⟨N,P,?_⟩
  intro D
  rw [← R post,← R x]
  exact door C hc own D

end L4.BStarClearanceIndexedSum
