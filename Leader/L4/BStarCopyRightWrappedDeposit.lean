import Leader.L4.BStarCopyRightWrappedPairs
import Leader.L4.BStarCopyRightScopedDeposit

namespace L4.BStarCopyRightWrappedDeposit
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongCommand
open BStarH6WordChart BStarCopyRightStrip BStarCopyRightWrappedGeometry
open BStarLongPackets BStarLongPrep BStarLongCommandData BStarCopyInjection
open BStarCopyFenceSaturation BStarCopyMarkedLedger BStarCopyFIFO BStarCopyUpstreamTags
open BStarCopyRightWrappedPairs

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

/-- Both selected rows on the *same* old ingress pair: consume an
already released head tag to L.RD while INJECT places the newest
tag in aliased L.RS. The ordered ledger uses old crossing credit,
before appending the new tag at the tail, never forwarding it on
the same mark. Reservation and actual selection are explicit. -/
theorem ingress_release_and_cross {Tag : Type} (digits : Tag→BitVec 36) (x : X) (a : Fin n) (seam : Nat)
    (U : WrappedStrip B x a seam n)
    (prior : Tag) (newTag : Tag) (up todo : List Tag) (s : Ledger Tag) (plan : List Tag)
    (P : OrderedPrefix plan s (prior::up))
    (pending : s.release.pending=newTag::todo) :
    let e := addr a 0
    let v := L Sheet.rd
    let q := R (rail seam 1)
    let raw := ((x e).long,(x (rightNeighbor e)).long)
    let g := oldPair B x e
    let laneAt := fun (y : X) (p : At Sheet) =>
      readLane (Sheet.index p.occurrence) (y (site e p.side)).long
    e≠rightNeighbor e →
    injection .left true∈(arbitration (round g raw).prep).1 →
    hop q v∈orderedData g (reserved (round g raw).prep) →
    (laneAt x (L .rs)).gate=true →
    (laneAt x (L .rs)).frozen=.data (digits newTag) →
    (laneAt x (L .rs)).mobile=.empty →
    (((laneAt x q).gate && (laneAt x v).gate)=true) →
    (laneAt x q).mobile=encode digits (some prior) →
    Compatible digits (s.cells 0) (laneAt x v) → (s.cells 0).mobile=none →
    let t := (s.receiveFirst prior).releaseOne newTag todo
    let post := ring x e
    OrderedPrefix plan t (up++[newTag]) ∧
      (laneAt post q).mobile=.empty ∧
      Compatible digits (t.cells 0) (laneAt post v) ∧
      (laneAt post (L .rs)).mobile=.data (digits newTag) ∧
      (laneAt post (L .rs)).frozen=.empty := by
  dsimp only
  intro sep win selected gate frozen vacant gates old agrees empty
  let e := addr a 0
  let q := R (rail seam 1)
  let v := L Sheet.rd
  have retaining : retains (oldPair B x e) v=true := by
    simp [retains,v,L,show (oldPair B x e).1.inside=true from U.head_in]
  obtain ⟨advance,source,recv⟩ :=
    ring_cross_head hp digits prior up P x e sep (hop q v) v rfl rfl selected
      (by intro H; have := congrArg At.side H; contradiction) retaining gates old agrees empty
  have dep := BStarCopyOperand.ring_inject hp x e sep .left true (digits newTag) win gate frozen vacant
  exact ⟨.mark advance (.issue _ up newTag todo pending),source,recv,
    congrArg Lane.mobile dep,congrArg Lane.frozen dep⟩

#print axioms ingress_release_and_cross
end L4.BStarCopyRightWrappedDeposit
