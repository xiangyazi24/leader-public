import Leader.L4.BStarClearanceMobileJoined
import Leader.L4.BStarClearanceMobile

/-! Actual joined mobile charges at the physical chart's strict
distance, which need not differ by one across sheet boundaries. -/
namespace L4.BStarClearanceMobileCharges
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongPackets BStarLongWork
open BStarLongPrep BStarLongCommandData BStarCopyFIFO BStarCopyUpstreamCredit
open BStarClearanceMobile BStarClearanceMobileJoined

theorem joined_vacant_hop (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (u v : At Sheet) (D : DataClaim)
    (hs : D.source=u) (hd : D.destination=some v) (hh : D.kind=.hop)
    (ne : u≠v) (a d : Nat) (drop : d<a) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    D∈orderedData g (reserved (round g raw).prep) →
    (view raw u).mobile≠.empty → (view raw v).mobile=.empty →
    rank a (view y u)+rank d (view y v)<rank a (view raw u)+rank d (view raw v) := by
  dsimp only
  intro H U V
  rw [joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x]
  let g := Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  change rank a (post g raw u)+rank d (post g raw v)<rank a (view raw u)+rank d (view raw v)
  change (view raw u).mobile≠.empty at U
  change (view raw v).mobile=.empty at V
  have W := vacant_hop_charge g raw u v D hs hd hh H ne U V d
  have L : (post g raw u).mobile=.empty := by
    apply Classical.byContradiction
    intro S
    simp [rank,mass,U,V,S] at W
    omega
  simp [rank,mass,U,V,L] at W ⊢
  omega

theorem joined_terminal (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (u : At Sheet) (a : Nat) (ha : 0<a) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    ending u∈orderedData g (reserved (round g raw).prep) →
    (view raw u).mobile≠.empty →
    rank a (view y u)<rank a (view raw u) := by
  dsimp only
  intro H U
  rw [joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x]
  exact terminal_charge _ _ u H U a ha

end L4.BStarClearanceMobileCharges
