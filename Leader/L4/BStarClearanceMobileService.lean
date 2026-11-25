import Leader.L4.BStarClearanceRightmost
import Leader.L4.BStarClearanceMobileCharges

/-! The finite-ring rightmost nomination pays at one actual joined
mark, at the selected footprint. Other disjoint footprints still need
nonincrease to lift this to the complete owner-restricted rank. -/
namespace L4.BStarClearanceMobileService
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarLongPrep BStarLongCommandData BStarLongEvents BStarH6WordChart
open BStarAcquireRailCoverage BStarLongFiberOwner BStarClearanceDataChart
open BStarClearanceRightmost BStarClearanceMobile BStarClearanceMobileCharges

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

private theorem data_shape (g : Pair LongGeometry) (Rsv : List (At Sheet))
    (D : DataClaim) (H : D∈orderedData g Rsv) :
    (D.destination=none ∧ D=ending D.source) ∨
      (∃ t, D.destination=some t ∧ D.kind=.hop) := by
  obtain ⟨l,r⟩ := g
  let test (d : DataClaim) : Bool :=
    match d.destination with
    | none => decide (d=ending d.source)
    | some _ => decide (d.kind=.hop)
  have A (I T H J : Bool) : (dataClaims (geo false I T,geo H J false)).all test=true := by
    cases I <;> cases T <;> cases H <;> cases J <;> decide +kernel
  have M := BStarLongFenceTopology.selected_data_raw (l,r) Rsv D H
  change D∈dataClaims (geo false l.inside l.last,geo r.axes.h6 r.inside false) at M
  have S := List.all_eq_true.mp (A l.inside l.last r.axes.h6 r.inside) D M
  cases E : D.destination with
  | none => exact .inl ⟨rfl, by simpa [test,E] using S⟩
  | some t => exact .inr ⟨t,rfl,by simpa [test,E] using S⟩

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}

theorem mobile_service (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (hh : ∃ i, oldH6 (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x i=true) (o : Int) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let h := oldH6 b x
    (∀ i, let g := longGeometry b (x i); (!g.axes.h6 || g.inside)=true) →
    (∀ i, let g := oldPair b x i; continuation g.1 g.2=true) →
    (∃ i s, activeSheet (longGeometry b (x i)) s=true ∧ dataOwner h i s=o ∧ mobile x i s≠.empty) →
    ∃ (e : Fin n) (C : DataClaim),
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      let g := oldPair b x e
      let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b (x e,x (rightNeighbor e)))
      let d := fun (a : At Sheet) => distance h hh (site e a.side) a.occurrence + 1
      dataOwner h (site e C.source.side) C.source.occurrence=o ∧
      ((C.destination=none ∧ rank (d C.source) (view y C.source) < rank (d C.source) (view raw C.source)) ∨
      (∃ a, C.destination=some a ∧
        rank (d C.source) (view y C.source)+rank (d a) (view y a) <
        rank (d C.source) (view raw C.source)+rank (d a) (view raw a)) ∨
      ∃ cmd q, (cmd,.advance q)∈actualOffers g raw ∧ physicalOwner h e cmdDispl cmd.source=o) := by
  dsimp only
  intro head cont occ
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  obtain ⟨e,C,M,O,U,V,H⟩ := nominate hp x hh o head cont occ
  refine ⟨e,C,O,?_⟩
  rcases H with H|H
  · let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair b x e
    let d := fun (a : At Sheet) => distance (oldH6 b x) hh (site e a.side) a.occurrence + 1
    have OU : (view raw C.source).mobile≠.empty := fun J =>
      U ((pair_mobile hp x e C.source).1.symm.trans J)
    rcases data_shape g _ C H with ⟨Z,E⟩ | ⟨a,Z,K⟩
    · have S : ending C.source∈orderedData g (reserved (round g raw).prep) := E ▸ H
      exact .inl ⟨Z,joined_terminal k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
        C.source (d C.source) (Nat.zero_lt_succ _) S OU⟩
    · have OV : (view raw a).mobile=.empty := (pair_mobile hp x e a).1.trans (V a Z)
      have D := hop_decreases b x hh e [] C a M Z
      have HD : d a < d C.source := Nat.succ_lt_succ D
      have N : C.source≠a := fun E => (Nat.ne_of_lt HD) (congrArg d E.symm)
      exact .inr (.inl ⟨a,Z,joined_vacant_hop k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
        (x e,x (rightNeighbor e)) C.source a C rfl Z K N (d C.source) (d a) HD H OU OV⟩)
  · exact .inr (.inr H)

end L4.BStarClearanceMobileService
