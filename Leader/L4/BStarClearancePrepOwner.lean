import Leader.L4.BStarClearanceDataChart
import Leader.L4.BStarLongEvents

namespace L4.BStarClearancePrepOwner
open AllSizeProtocol BStarTrace BStarLongClaims BStarH6WordChart BStarLongFiberOwner
open BStarLongEvents BStarLongCommandData BStarLongToken BStarLongCommand
open BStarClearanceDataChart

/-- A checked old advance remains an actual selected departure,
although prep arbitration may replace its payload by a fault. -/
theorem gated_still_departs (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (h : (c,.advance p) ∈ gated g x) :
    ∃ q, (c,.advance q) ∈ actualOffers g x := by
  let faults := (round g x).faults
  have A : cancel faults (c,.advance p) ∈ (round g x).offered := by
    change _ ∈ (gated g x).map (cancel faults)
    exact List.mem_map.mpr ⟨_,h,rfl⟩
  have B (q : Payload) (H : (c,.advance q) ∈ (round g x).offered) :
      ∃ t, (c,.advance t) ∈ actualOffers g x := by
    have M : BStarLongGrant.update g x (round g x).offered (c,.advance q) ∈ actualOffers g x :=
      List.mem_map.mpr ⟨_,H,rfl⟩
    simp only [BStarLongGrant.update] at M
    split at M
    · split at M
      · exact ⟨_,M⟩
      · exact ⟨q,M⟩
    · exact ⟨q,M⟩
  by_cases H : c.source∈faults
  · rw [cancel_hit _ _ _ H] at A
    exact B _ A
  · simp [cancel,H] at A
    exact B _ A

/-- If a real preparation reservation meets a would-be physical
data service claim, a checked prep command of the same physical
owner actually departs on this mark. This also covers an END
claim's sole address and a canceled/faulted preparation departure. -/
theorem shared_reservation_actual {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e : Fin n) (raw : Pair (BitVec LW))
    (s : At Sheet) (D : DataClaim)
    (hr : s∈BStarLongPrep.reserved (round (oldPair b x e) raw).prep)
    (hD : D∈orderedData (oldPair b x e) [])
    (hit : s=D.source ∨ D.destination=some s) :
    ∃ c p q op, (c,.advance p)∈gated (oldPair b x e) raw ∧
      p.fault=0 ∧ prepOf p.opcode.toNat=some op ∧
      (c,.advance q) ∈ actualOffers (oldPair b x e) raw ∧
      physicalOwner (oldH6 b x) e cmdDispl c.source =
      dataOwner (oldH6 b x) (site e D.source.side) D.source.occurrence := by
  let g := oldPair b x e
  let h := oldH6 b x
  obtain ⟨c,p,op,hc,hf,hop,own⟩ := reserved_overlap_owner g (total h) (word h e)
    raw s hr D (BStarLongFenceTopology.selected_data_raw g [] D hD) hit
  obtain ⟨q,hq⟩ := gated_still_departs g raw c p hc
  refine ⟨c,p,q,op,hc,hf,hop,hq,?_⟩
  change physicalOwner h e cmdDispl c.source=physicalOwner h e dataDispl D.source
  rw [physical_pair_owner,physical_pair_owner]
  exact own

private theorem select_all_free {α C : Type} [DecidableEq α]
    (slots : C → List α) (U : List α) (L : List C)
    (P : L.Pairwise (fun a b => ∀ s∈slots b, s∉slots a)) :
    select slots U L = L.filter (fun c => free U (slots c)) := by
  induction L generalizing U with
  | nil => rfl
  | cons c L ih =>
    have A := List.pairwise_cons.mp P
    unfold select
    rw [List.filter_cons]
    split <;> rename_i H
    · rw [ih _ A.2]
      congr 1
      apply List.filter_congr
      intro d hd
      have E : ∀ s∈slots d, s∉slots c := A.1 d hd
      cases h : free U (slots d)
      · apply Bool.eq_false_iff.mpr
        intro j
        have q := (free_iff _ _).mp j
        have k := (free_iff _ _).mpr (fun s hs hu => q s hs (List.mem_append_right _ hu))
        simp [h] at k
      · apply (free_iff _ _).mpr
        intro s hs hm
        exact (List.mem_append.mp hm).elim (E s hs) ((free_iff _ _).mp h s hs)
    · skip
      exact ih U A.2

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

private theorem offers_disjoint (g : Pair LongGeometry) :
    (offers dataKey (dataClaims g)).Pairwise (fun a b => ∀ s∈b.slots, s∉a.slots) := by
  obtain ⟨x,y⟩ := g
  change (offers dataKey (dataClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false))).Pairwise _
  generalize x.inside=i
  generalize x.last=l
  generalize y.axes.h6=h
  generalize y.inside=j
  cases i <;> cases l <;> cases h <;> cases j <;> decide +kernel

/-- Geometric data claims never contend with another data claim.
Thus every suppressed nominal service genuinely intersects a prep
reservation, not a competing geometric service. -/
theorem orderedData_filter (g : Pair LongGeometry) (Rsv : List (At Sheet)) :
    orderedData g Rsv=(orderedData g []).filter (fun D => free Rsv D.slots) := by
  have K := offers_disjoint g
  have H := select_all_free Claim.slots Rsv _ K
  have E := select_all_free Claim.slots [] _ K
  have Z : ∀ A : DataClaim, free [] A.slots=true := by
    intro A
    exact (free_iff _ _).mpr (by simp)
  simp [Z] at E
  unfold orderedData
  rw [H,E]
  simp

/-- An absent nominal service gives a same-owner actual prep departure,
without separately assuming an overlapping reservation. -/
theorem suppressed_nomination_actual {a : LargeParams} {n : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (e : Fin n) (raw : Pair (BitVec LW)) (D : DataClaim)
    (hD : D∈orderedData (oldPair b x e) [])
    (miss : D∉orderedData (oldPair b x e) (BStarLongPrep.reserved (round (oldPair b x e) raw).prep)) :
    ∃ c q, (c,.advance q) ∈ actualOffers (oldPair b x e) raw ∧
      physicalOwner (oldH6 b x) e cmdDispl c.source =
      dataOwner (oldH6 b x) (site e D.source.side) D.source.occurrence := by
  let U := BStarLongPrep.reserved (round (oldPair b x e) raw).prep
  have C : ¬ free U D.slots=true := by
    intro H
    apply miss
    rw [orderedData_filter]
    exact List.mem_filter.mpr ⟨hD,H⟩
  have X : ∃ s∈D.slots, s∈U := by
    classical
    apply Classical.byContradiction
    intro N
    exact C ((free_iff _ _).mpr (fun s hs hu => N ⟨s,hs,hu⟩))
  obtain ⟨s,H,M⟩ := X
  have hit : s=D.source ∨ D.destination=some s := by
    cases E : D.destination <;> simpa [Claim.slots,E,eq_comm] using H
  obtain ⟨c,_,q,_,_,_,_,depart,own⟩ := shared_reservation_actual b x e raw s D M hD hit
  exact ⟨c,q,depart,own⟩

end L4.BStarClearancePrepOwner
